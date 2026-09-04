#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

use vstd::prelude::*;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::resource::*;
use vstd::resource::ghost_var::*;
use vstd::iset::ISet;

verus! {

type ReadAU = AtomicUpdate<FlagToken, Commit<FlagToken>, ReadPred>;
type FlipAU = AtomicUpdate<FlagToken, Commit<FlagToken>, FlipPred>;

pub enum Protocol {
    Empty(GhostVarAuth<Option<FlipAU>>),
    Offering(Tracked<FlipAU>),
    Accepted,
}

use Protocol::*;

impl Protocol {
    proof fn take_empty(tracked self) -> (tracked out: GhostVarAuth<Option<FlipAU>>)
        requires self is Empty,
        ensures self == Empty(out),
    {
        match self {
            Empty(gva) => gva,
            _ => proof_from_false(),
        }
    }

    proof fn take_offer(tracked self) -> (tracked out: Tracked<FlipAU>)
        requires self is Offering,
        ensures self == Offering(out),
    {
        match self {
            Offering(au) => au,
            _ => proof_from_false(),
        }
    }
}

type K = (int, int, Loc, Loc);
type V = (PermissionBool, PermissionU32, GhostVarAuth<bool>, GhostVar<Option<FlipAU>>, Protocol);

pub struct FlagInv;
pub open spec const FLAG_INV: int = 2;
impl InvariantPredicate<K, V> for FlagInv {
    open spec fn inv(k: K, v: V) -> bool {
        let (value_id, pend_id, state_id, gv_id) = k;
        let (value_perm, pend_perm, state, gv, proto) = v;
        &&& value_perm.id() == value_id
        &&& pend_perm.id() == pend_id
        &&& state.id() == state_id
        &&& gv.id() == gv_id
        &&& state@ == value_perm.value()
        &&& pend_perm.value() < 3
        &&& match proto {
            Empty(gva) => {
                &&& pend_perm.value() == 0
                &&& gva.id() == gv_id
                &&& gv@ is None
                &&& gva@ is None
                &&& gv@ == gva@
            }
            Offering(au) => {
                &&& pend_perm.value() == 1
                &&& gv@ is Some
                &&& gv@->0 == au@
            },
            Accepted => {
                &&& pend_perm.value() == 2
                &&& gv@ is Some
                &&& gv@->0.resolves()
            }
        }
    }
}

pub struct FlagToken {
    pub value: GhostVar<bool>,
}

impl FlagToken {
    pub open spec fn id(self) -> Loc {
        self.value.id()
    }
}

pub struct Flag {
    pub value: PAtomicBool,
    pub pending: PAtomicU32,
    pub inv: Tracked<AtomicInvariant<K, V, FlagInv>>,
}

impl Flag {
    pub open spec fn wf(self) -> bool {
        &&& self.inv@.constant().0 == self.value.id()
        &&& self.inv@.constant().1 == self.pending.id()
        &&& self.inv@.namespace() == FLAG_INV
    }

    pub open spec fn token_id(self) -> Loc {
        self.inv@.constant().2
    }

    pub fn new(init: bool) -> (out: (Self, Tracked<FlagToken>))
        ensures
            out.0.wf(),
            out.0.token_id() == out.1@.id(),
            out.1@.value@ == init,
    {
        let (value, Tracked(value_perm)) = PAtomicBool::new(init);
        let (pending, Tracked(pending_perm)) = PAtomicU32::new(0);
        let tracked (state_auth, state_var) = GhostVarAuth::new(init);
        let tracked (au_auth, au_var) = GhostVarAuth::new(None);
        let tracked inv = AtomicInvariant::new(
            (value.id(), pending.id(), state_auth.id(), au_auth.id()),
            (value_perm, pending_perm, state_auth, au_var, Empty(au_auth)),
            FLAG_INV,
        );

        let this = Self { value, pending, inv: Tracked(inv) };
        let tracked token = FlagToken { value: state_var };
        (this, Tracked(token))
    }

    pub fn read(&self) -> (out: bool)
        atomically (atomic_update) {
            type ReadPred,
            (old_token: FlagToken) -> (new_token: Commit<FlagToken>),
            requires
                old_token.id() == self.token_id(),
            ensures
                new_token@ == old_token,

            outer_mask ISet::<int>::full().remove(FLAG_INV),
            inner_mask none,
        },
        requires self.wf(),
        ensures out == old_token.value@,
    {
        let out;
        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            out = self.value.load(Tracked(&value_perm));

            proof {
                try_open_atomic_update!(atomic_update, token=> {
                    auth.agree(&token.value);
                    assert(value_perm.value() == token.value@);
                    Tracked(Commit(token))
                });

                v = (value_perm, pend_perm, auth, gv, proto);
            }
        });

        return out;
    }

    pub fn flip(&self)
        atomically (atomic_update) {
            type FlipPred,
            (old_token: FlagToken) -> (new_token: Commit<FlagToken>),
            requires
                old_token.id() == self.token_id(),
            ensures
                new_token@.value@ == !old_token.value@,
                new_token@.id() == old_token.id(),

            outer_mask any / [FLAG_INV],
            inner_mask none,
        },
        requires self.wf(),
    {
        let tracked mut au = atomic_update;

        loop invariant
            self.wf(),
            au == atomic_update,
        {
            match self.try_cancel_two_flips(Tracked(au)) {
                Some(upd) => proof { au = upd.get() },
                None => return,
            }

            match self.try_simple_flip(Tracked(au)) {
                Some(upd) => proof { au = upd.get() },
                None => return,
            }

            match self.try_handshake(Tracked(au)) {
                Some(upd) => proof { au = upd.get() },
                None => return,
            }
        }
    }

    fn try_cancel_two_flips(&self, Tracked(au): Tracked<FlipAU>) -> (out: Option<Tracked<FlipAU>>)
        requires
            self.wf(),
            au.pred().args(self),
        ensures
            match out {
                Some(ret_au) => ret_au == au,
                None => au.resolves(),
            }
    {
        let tracked mut maybe_au = Some(au);
        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 1, 2);

            proof {
                if res.is_ok() {
                    // CAS 1→2 succeeded: state was Offering(au_other), now transition to Accepted
                    // We cancel two flips: commit the offered AU and our own AU
                    let tracked au_curr = maybe_au.tracked_take();

                    // Extract the offered AU from the Offering protocol
                    let tracked offered_tracked = proto.take_offer();
                    let tracked au_other = offered_tracked.get();

                    // Commit the offered AU (the other thread's flip linearizes here)
                    // Before: state@ = v (= value_perm.value())
                    // After update: state@ = !v
                    let tracked _ = try_open_atomic_update!(au_other, mut token_other => {
                        auth.agree(&token_other.value);
                        let old_val = token_other.value@;
                        auth.update(&mut token_other.value, !old_val);
                        Tracked(Commit(token_other))
                    });

                    // Now state@ = !v (invariant temporarily broken: state@ != value_perm.value())
                    // Commit our own AU (our flip linearizes here)
                    // After update: state@ = v (two flips cancel)
                    let tracked _ = try_open_atomic_update!(au_curr, mut token_curr => {
                        auth.agree(&token_curr.value);
                        let old_val = token_curr.value@;
                        auth.update(&mut token_curr.value, !old_val);
                        Tracked(Commit(token_curr))
                    });

                    // Now state@ = v = value_perm.value() - invariant restored
                    // Transition to Accepted state
                    proto = Accepted;
                }
                v = (value_perm, pend_perm, auth, gv, proto);
            }
        });

        if res.is_ok() {
            return None;
        }

        Some(Tracked(maybe_au.tracked_take()))
    }

    fn try_simple_flip(&self, Tracked(au): Tracked<FlipAU>) -> (out: Option<Tracked<FlipAU>>)
        requires
            self.wf(),
            au.pred().args(self),
        ensures
            match out {
                Some(ret_au) => ret_au == au,
                None => au.resolves(),
            }
    {
        let tracked mut maybe_au = Some(au);
        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            res = self.value.compare_exchange(Tracked(&mut value_perm), true, false);
            proof {
                if res.is_ok() {
                    // CAS true→false succeeded: physically flipped the value
                    // Commit our AU: update ghost state from true to false
                    let tracked au_curr = maybe_au.tracked_take();
                    let tracked _ = try_open_atomic_update!(au_curr, mut token => {
                        auth.agree(&token.value);
                        auth.update(&mut token.value, false);
                        Tracked(Commit(token))
                    });
                }
                v = (value_perm, pend_perm, auth, gv, proto);
            }
        });

        if res.is_ok() {
            return None;
        }

        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            res = self.value.compare_exchange(Tracked(&mut value_perm), false, true);
            proof {
                if res.is_ok() {
                    // CAS false→true succeeded: physically flipped the value
                    // Commit our AU: update ghost state from false to true
                    let tracked au_curr = maybe_au.tracked_take();
                    let tracked _ = try_open_atomic_update!(au_curr, mut token => {
                        auth.agree(&token.value);
                        auth.update(&mut token.value, true);
                        Tracked(Commit(token))
                    });
                }
                v = (value_perm, pend_perm, auth, gv, proto);
            }
        });

        if res.is_ok() {
            return None;
        }

        Some(Tracked(maybe_au.tracked_take()))
    }

    fn try_handshake(&self, Tracked(au): Tracked<FlipAU>) -> (out: Option<Tracked<FlipAU>>)
        requires
            self.wf(),
            au.pred().args(self),
        ensures
            match out {
                Some(ret_au) => ret_au == au,
                None => au.resolves(),
            }
    {
        let tracked mut maybe_au = Some(au);
        let tracked mut auth_au: Option<GhostVarAuth<Option<FlipAU>>> = None;
        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 0, 1);

            proof {
                if res.is_ok() {
                    // CAS 0→1 succeeded: transition from Empty to Offering
                    // Extract GhostVarAuth from Empty protocol
                    let tracked mut gva = proto.take_empty();
                    // Take our AU from maybe_au
                    let tracked au_curr = maybe_au.tracked_take();
                    // Update gv to record that au_curr is being offered
                    gva.update(&mut gv, Some(au_curr));
                    // au_curr == au (from tracked_take ensures), and gva@ = Some(au_curr)
                    // so gva@ == Some(au)
                    assert(au_curr == au);
                    assert(gva@ == Some(au));
                    // Set protocol to Offering, depositing the AU
                    proto = Offering(Tracked(au_curr));
                    // Save gva for later retraction
                    auth_au = Some(gva);
                }
                v = (value_perm, pend_perm, auth, gv, proto);
            }
        });

        if res.is_err() {
            return Some(Tracked(maybe_au.tracked_take()));
        }

        assert(auth_au is Some);

        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 1, 0);

            proof {
                if res.is_ok() {
                    // CAS 1→0 succeeded: retract our offer (nobody helped us)
                    // Extract our AU from the Offering protocol
                    let tracked offered_tracked = proto.take_offer();
                    let tracked au_retracted = offered_tracked.get();
                    // Retrieve the gva from auth_au
                    let tracked mut gva = auth_au.tracked_take();
                    // Update gv from Some(au) back to None
                    gva.update(&mut gv, None);
                    // Restore Empty protocol
                    proto = Empty(gva);
                    // Restore our AU to maybe_au so we can return it
                    maybe_au = Some(au_retracted);
                } else {
                    // CAS 1→0 failed: someone accepted our offer (pending was NOT 1)
                    // pend_perm.value() != 1 (from CAS failure postcondition: current == 1 failed)
                    // We hold gva (via auth_au), so invariant can't be Empty (gv@ is Some)
                    // Hence proto is Accepted
                    // From Accepted: gv@->0.resolves()
                    // From gva@ == Some(au): gv@ == Some(au), so gv@->0 == au
                    // Therefore: au.resolves()
                    let tracked gva_ref = auth_au.tracked_borrow();
                    gva_ref.agree(&gv);
                    // Now gv@ == gva_ref@ == Some(au)
                    assert(gv@ == Some(au));
                    assert(proto is Accepted);
                    assert(au.resolves());
                }
                v = (value_perm, pend_perm, auth, gv, proto);
            }
        });

        if res.is_err() {
            open_atomic_invariant!(self.inv.borrow() => v => {
                let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
                self.pending.store(Tracked(&mut pend_perm), 0);

                proof {
                    // Transition Accepted (or Offering, if somehow) → Empty
                    // Retrieve the gva from auth_au and reset to Empty
                    let tracked mut gva = auth_au.tracked_take();
                    // Update gv from Some(resolved_au) back to None
                    gva.update(&mut gv, None);
                    // Restore Empty protocol
                    proto = Empty(gva);
                    v = (value_perm, pend_perm, auth, gv, proto);
                }
            });

            return None;
        }

        Some(Tracked(maybe_au.tracked_take()))
    }
}

pub struct UserInv;
pub open spec const USER_INV: int = 5;
impl InvariantPredicate<Loc, FlagToken> for UserInv {
    open spec fn inv(id: Loc, token: FlagToken) -> bool {
        &&& token.id() == id
    }
}

fn main() {
}

} 
