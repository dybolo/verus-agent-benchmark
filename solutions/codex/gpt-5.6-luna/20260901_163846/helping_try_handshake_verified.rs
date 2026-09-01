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
                    let tracked au = maybe_au.tracked_take();
                    let tracked other_au = proto.take_offer();

                    assert(gv@ is Some);
                    assert(gv@->0 == other_au);

                    try_open_atomic_update!(au, mut token => {
                        let ghost old_auth = auth@;
                        auth.update(&mut token.value, !old_auth);
                        Tracked(Commit(token))
                    });

                    try_open_atomic_update!(other_au.get(), mut token => {
                        let ghost old_auth = auth@;
                        auth.update(&mut token.value, !old_auth);
                        Tracked(Commit(token))
                    });

                    assert(gv@ is Some);
                    assert(gv@->0.resolves());

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
                    let tracked au = maybe_au.tracked_take();
                    try_open_atomic_update!(au, mut token => {
                        let ghost old_auth = auth@;
                        auth.update(&mut token.value, !old_auth);
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
                    let tracked au = maybe_au.tracked_take();
                    try_open_atomic_update!(au, mut token => {
                        let ghost old_auth = auth@;
                        auth.update(&mut token.value, !old_auth);
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
        let ghost original_au = au;
        let tracked mut maybe_au = Some(au);
        let tracked mut auth_au: Option<GhostVarAuth<Option<FlipAU>>> = None;
        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 0, 1);

            proof {
                if res.is_ok() {
                    let tracked mut au_auth = proto.take_empty();
                    let tracked offer = maybe_au.tracked_take();
                    assert(offer == original_au);
                    au_auth.update(&mut gv, Some(offer));
                    auth_au = Some(au_auth);
                    proto = Offering(Tracked(offer));
                    assert(pend_perm.value() == 1);
                }
                v = (value_perm, pend_perm, auth, gv, proto);
            }
        });

        if res.is_err() {
            return Some(Tracked(maybe_au.tracked_take()));
        }

        assert(auth_au is Some);
        assert(res.is_ok());

        let res;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            assert(FlagInv::inv(self.inv@.constant(),
                (value_perm, pend_perm, auth, gv, proto)));
            let ghost pend_before = pend_perm.value();
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 1, 0);

            proof {
                if res.is_ok() {
                    let tracked offer = proto.take_offer();
                    let tracked mut au_auth = auth_au.tracked_take();
                    au_auth.update(&mut gv, None);
                    proto = Empty(au_auth);
                    maybe_au = Some(offer.get());
                } else {
                    assert(res is Err);
                    assert(pend_before != 1);
                }
                v = (value_perm, pend_perm, auth, gv, proto);
            }
        });

        if res.is_err() {
            assert(res.is_err());
            open_atomic_invariant!(self.inv.borrow() => v => {
                let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
                assert(FlagInv::inv(self.inv@.constant(),
                    (value_perm, pend_perm, auth, gv, proto)));

                proof {
                    assert(res.is_err());
                    let tracked mut au_auth = auth_au.tracked_take();
                    au_auth.agree(&gv);
                    assert(au_auth@ == Some(original_au));
                    assert(proto is Offering ==> pend_perm.value() == 1);
                    assert(proto is Accepted ==> pend_perm.value() == 2);
                    match proto {
                        Empty(gva) => {
                            gva.agree(&gv);
                            assert(gva@ == gv@);
                            assert(gv@ is None);
                            assert(false);
                        },
                        Offering(offer) => {
                            try_open_atomic_update!(offer.get(), mut token => {
                                let ghost old_auth = auth@;
                                auth.update(&mut token.value, !old_auth);
                                Tracked(Commit(token))
                            });
                        },
                        Accepted => {
                            assert(pend_perm.value() == 2);
                            assert(gv@ is Some);
                            assert(gv@->0 == original_au);
                            assert(original_au.resolves());
                        },
                    }
                    au_auth.update(&mut gv, None);
                    proto = Empty(au_auth);
                }
                self.pending.store(Tracked(&mut pend_perm), 0);
                proof {
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
