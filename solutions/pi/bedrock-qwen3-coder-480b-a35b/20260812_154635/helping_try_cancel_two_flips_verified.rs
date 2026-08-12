use vstd::prelude::*;
use vstd::atomic::*;
use vstd::invariant::*;

verus! {

#[derive(PartialEq, Eq)]
enum Protocol {
    Empty(Ghost<GhostVarAuth<bool>>),
    Offering(Tracked<AtomicUpdate<FlagToken, Commit<FlagToken>, FlipPred>>),
    Accepted,
}


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
}

struct Flag {
    inv: PCell<FlagInv>,
    value: AtomicU32,
    pending: AtomicU32,
    token_id: usize,
}

impl Flag {
    pub open spec fn wf(self) -> bool {
        &&& self.inv@.inv(self.inv.id()) == self.inv.wf_footprint()
        &&& self.inv@.is_init()
    }

    pub open spec fn wf_footprint(self) -> FlagInv {
        self.inv@
    }

    spec fn token_id(&self) -> usize;

    pub closed spec fn inv_contents(v: (AtomicU32, AtomicU32, GhostVarAuth<bool>, Ghost<Option<AtomicUpdate<FlagToken, Commit<FlagToken>, FlipPred>>>, Protocol)) -> bool
        recommends
            (v.0).id() == v.4.id(),
            (v.1).id() == v.4.id() + 1,
    {
        let (value_perm, pend_perm, auth, gv, proto) = v;
        let state = State {
            id: value_perm.id(),
            value: value_perm.view(),
        };
        &&& state.id() == state.id() // trivially true
        &&& state@ == value_perm.value()
        &&& match proto {
            Empty(empty_auth) => {
                &&& pend_perm.value() == 0
                &&& gv@ is None
                &&& auth@ == state@
                &&& empty_auth@ == auth@
            }
            Offering(au) => {
                &&& pend_perm.value() == 1
                &&& gv@ is Some
                &&& gv@->0 == au@
                &&& auth@ == state@
            }
            Accepted => {
                &&& pend_perm.value() == 2
                &&& gv@ is Some
                &&& gv@->0.resolves()
                &&& auth@ == state@
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
        let res: Result<u32, u32>;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked (mut value_perm, mut pend_perm, mut auth, mut gv, mut proto) = v;
            res = self.pending.compare_exchange(Tracked(&mut pend_perm), 1, 2);

            proof {
                if res.is_ok() {
                    // Successfully changed from 1 to 2 (there were two concurrent flips)
                    let tracked au_to_resolve = maybe_au.tracked_take();
                    
                    // Extract the atomic update that was already stored (if any)
                    // This represents the OTHER concurrent flip that we're cancelling along with ours
                    if proto is Offering {
                        let tracked au_already_stored = proto.take_offer();
                        
                        // Cancel both atomic updates by resolving them with flip semantics
                        try_open_atomic_update!(au_already_stored.get(), mut token => {
                            // Satisfy FlipPred's ensures: new_token@.value@ == !old_token.value@
                            let ghost old_value = auth@;
                            auth.update(&mut token.value, !old_value);
                            Tracked(Commit(token))
                        });
                        
                        try_open_atomic_update!(au_to_resolve, mut token => {
                            // Satisfy FlipPred's ensures: new_token@.value@ == !old_token.value@
                            let ghost old_value = auth@;
                            auth.update(&mut token.value, !old_value);
                            Tracked(Commit(token))
                        });
                        
                        // Transition protocol to Accepted - matching pending.value() == 2
                        // After this transition, the invariant requires gv@->0.resolves()
                        // Since we stored au_already_stored in gv originally, and we just resolved
                        // au_already_stored, we now have gv@->0.resolves() as needed
                        proto = Accepted;
                    } else {
                        // If not in Offering state, only resolve OUR atomic update
                        // This case probably shouldn't occur given the timing, but handle gracefully  
                        try_open_atomic_update!(au_to_resolve, mut token => {
                            let ghost old_value = auth@;
                            auth.update(&mut token.value, !old_value);
                            Tracked(Commit(token))
                        });
                    }
                }
                v = (value_perm, pend_perm, auth, gv, proto);
            }
        });

        if res.is_ok() {
            return None;
        }

        Some(Tracked(maybe_au.tracked_take()))
    }
}

type FlipAU = AtomicUpdate<FlagToken, Commit<FlagToken>, FlipPred>;
type FlagInv = Invariant<(AtomicU32, AtomicU32, GhostVarAuth<bool>, Ghost<Option<AtomicUpdate<FlagToken, Commit<FlagToken>, FlipPred>>>, Protocol)>;

#[verifier::external_body]
struct State {
    id: usize,
    value: bool,  
}

impl State {
    #[verifier::inline]
    open spec fn id(self) -> usize {
        self.id
    }

    #[verifier::inline]  
    open spec fn view(self) -> bool {
        self.value
    }
}

}