#![allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::prelude::*;

pub mod oneshot {
    use verus_builtin::*;
    use verus_builtin_macros::*;
    use vstd::prelude::*;
    use vstd::resource::algebra::ResourceAlgebra;
    use vstd::resource::pcm;
    use vstd::resource::pcm::PCM;
    use vstd::resource::Loc;

    verus! {

    pub enum OneShotResourceValue {
        FullRightToComplete,
        HalfRightToComplete,
        Complete,
        Empty,
        Invalid,
    }

    impl ResourceAlgebra for OneShotResourceValue {
        open spec fn valid(self) -> bool {
            !(self is Invalid)
        }

        open spec fn op(a: Self, b: Self) -> Self {
            match (a, b) {
                (OneShotResourceValue::Empty, _) => b,
                (_, OneShotResourceValue::Empty) => a,
                (
                    OneShotResourceValue::HalfRightToComplete,
                    OneShotResourceValue::HalfRightToComplete,
                ) => OneShotResourceValue::FullRightToComplete {  },
                (
                    OneShotResourceValue::Complete,
                    OneShotResourceValue::Complete,
                ) => OneShotResourceValue::Complete {  },
                (_, _) => OneShotResourceValue::Invalid {  },
            }
        }

        #[verifier::external_body]
        proof fn valid_op(a: Self, b: Self) {
            unimplemented!()
        }

        #[verifier::external_body]
        proof fn commutative(a: Self, b: Self) {
            unimplemented!()
        }

        #[verifier::external_body]
        proof fn associative(a: Self, b: Self, c: Self) {
            unimplemented!()
        }
    }

    impl PCM for OneShotResourceValue {
        open spec fn unit() -> Self {
            OneShotResourceValue::Empty {  }
        }

        #[verifier::external_body]
        proof fn op_unit(self) {
            unimplemented!()
        }

        #[verifier::external_body]
        proof fn unit_valid() {
            unimplemented!()
        }
    }

    pub struct OneShotResource {
        r: pcm::Resource<OneShotResourceValue>,
    }

    impl OneShotResource {
        pub closed spec fn id(self) -> Loc {
            self.r.loc()
        }

        pub closed spec fn view(self) -> OneShotResourceValue {
            self.r.value()
        }

        #[verifier::external_body]
        pub proof fn alloc() -> (tracked resource: Self)
            ensures
                resource@ is FullRightToComplete,
        {
            unimplemented!()
        }

        #[verifier::external_body]
        pub proof fn split(tracked self) -> (tracked return_value: (Self, Self))
            requires
                self@ is FullRightToComplete,
            ensures
                ({
                    let (half1, half2) = return_value;
                    &&& half1@ is HalfRightToComplete
                    &&& half2@ is HalfRightToComplete
                    &&& half1.id() == self.id()
                    &&& half2.id() == self.id()
                }),
        {
            unimplemented!()
        }

        #[verifier::external_body]
        pub proof fn perform(tracked &mut self)
            requires
                old(self)@ is FullRightToComplete,
            ensures
                final(self)@ is Complete,
        {
            unimplemented!()
        }

        #[verifier::external_body]
        pub proof fn perform_using_two_halves(tracked &mut self, tracked other: &mut Self)
            requires
                old(other).id() == old(self).id(),
                old(self)@ is HalfRightToComplete,
                !(old(other)@ is Empty),
            ensures
                old(other)@ is HalfRightToComplete,
                final(self).id() == old(self).id(),
                final(other).id() == old(self).id(),
                final(self)@ is Complete,
                final(other)@ is Complete,
        {
            unimplemented!()
        }

        #[verifier::external_body]
        pub proof fn duplicate(tracked &self) -> (tracked other: Self)
            requires
                self@ is Complete,
            ensures
                other.id() == self.id(),
                other@ is Complete,
        {
            unimplemented!()
        }

        #[verifier::external_body]
        pub proof fn lemma_is_complete_if_other_is(tracked &mut self, tracked other: &Self)
            requires
                other.id() == old(self).id(),
                other@ is Complete,
                !(old(self)@ is Empty),
            ensures
                final(self).id() == old(self).id(),
                final(self)@ == old(self)@,
                final(self)@ is Complete,
        {
            unimplemented!()
        }
    }

    } 
}

use crate::oneshot::*;
use std::sync::Arc;
use vstd::atomic::*;
use vstd::atomic_ghost::*;
use vstd::invariant::*;
use vstd::resource::Loc;

verus! {

pub struct CounterTrackedState {
    pub x_perm: PermissionU32,
    pub oneshot0_inv_half: OneShotResource,
    pub oneshot1_inv_half: OneShotResource,
}

pub struct CounterInvariantConstants {
    pub x_id: int,
    pub oneshot0_id: Loc,
    pub oneshot1_id: Loc,
}

pub struct CounterInvariantPredicate {}

impl InvariantPredicate<
    CounterInvariantConstants,
    CounterTrackedState,
> for CounterInvariantPredicate {
    open spec fn inv(c: CounterInvariantConstants, cts: CounterTrackedState) -> bool {
        &&& cts.x_perm@.patomic == c.x_id
        &&& cts.oneshot0_inv_half.id() == c.oneshot0_id
        &&& cts.oneshot1_inv_half.id()
            == c.oneshot1_id
        &&& cts.oneshot0_inv_half@ is HalfRightToComplete || cts.oneshot0_inv_half@ is Complete
        &&& cts.oneshot1_inv_half@ is HalfRightToComplete
            || cts.oneshot1_inv_half@ is Complete
        &&& cts.x_perm@.value == (if cts.oneshot0_inv_half@ is Complete {
            1int
        } else {
            0int
        }) + (if cts.oneshot1_inv_half@ is Complete {
            1int
        } else {
            0int
        })
    }
}

pub struct CounterSharedState {
    pub x: PAtomicU32,
    pub inv: Tracked<
        AtomicInvariant<CounterInvariantConstants, CounterTrackedState, CounterInvariantPredicate>,
    >,
}

impl CounterSharedState {
    pub open spec fn wf(self) -> bool {
        &&& self.x.id() == self.inv@.constant().x_id
        &&& self.inv@.namespace() == 888
    }

    pub open spec fn get_oneshot_id(self, which_thread: int) -> Loc
        recommends
            which_thread == 0 || which_thread == 1,
    {
        let c = self.inv@.constant();
        if which_thread == 0 {
            c.oneshot0_id
        } else {
            c.oneshot1_id
        }
    }

    pub fn new(
        Tracked(oneshot0_inv_half): Tracked<OneShotResource>,
        Tracked(oneshot1_inv_half): Tracked<OneShotResource>,
    ) -> (result: Arc<Self>)
        requires
            oneshot0_inv_half@ is HalfRightToComplete,
            oneshot1_inv_half@ is HalfRightToComplete,
        ensures
            result.wf(),
            result.get_oneshot_id(0) == oneshot0_inv_half.id(),
            result.get_oneshot_id(1) == oneshot1_inv_half.id(),
    {
        let (x, Tracked(x_perm)): (PAtomicU32, Tracked<PermissionU32>) = PAtomicU32::new(0);
        let tracked cts = CounterTrackedState { x_perm, oneshot0_inv_half, oneshot1_inv_half };
        let ghost c = CounterInvariantConstants {
            x_id: x.id(),
            oneshot0_id: oneshot0_inv_half.id(),
            oneshot1_id: oneshot1_inv_half.id(),
        };
        assert(CounterInvariantPredicate::inv(c, cts));  
        let inv = Tracked(AtomicInvariant::new(c, cts, 888));
        Arc::new(CounterSharedState { x, inv })
    }

    pub fn read_x(
        self: &Arc<Self>,
        Tracked(oneshot0_complete): Tracked<OneShotResource>,
        Tracked(oneshot1_complete): Tracked<OneShotResource>,
    ) -> (x: u32)
        requires
            self.wf(),
            oneshot0_complete.id() == self.get_oneshot_id(0),
            oneshot1_complete.id() == self.get_oneshot_id(1),
            oneshot0_complete@ is Complete,
            oneshot1_complete@ is Complete,
        ensures
            x == 2,
    {
        let tracked mut oneshot0_complete = oneshot0_complete;
        let tracked mut oneshot1_complete = oneshot1_complete;
        let x_value: u32;
        open_atomic_invariant!(self.inv.borrow() => inner => {
            proof {
                inner.oneshot0_inv_half.lemma_is_complete_if_other_is(&oneshot0_complete);
                inner.oneshot1_inv_half.lemma_is_complete_if_other_is(&oneshot1_complete);
            }
            x_value = self.x.load(Tracked(&inner.x_perm));
            assert(x_value == 2); 
        });
        x_value
    }
}

pub fn thread_routine(
    shared_state: Arc<CounterSharedState>,
    Tracked(oneshot_thread_half): Tracked<OneShotResource>,
    Ghost(which_thread): Ghost<int>,
) -> (return_permission: Tracked<OneShotResource>)
    requires
        which_thread == 0 || which_thread == 1,
        oneshot_thread_half@ is HalfRightToComplete,
        shared_state.wf(),
        oneshot_thread_half.id() == shared_state.get_oneshot_id(which_thread),
    ensures
        return_permission@.id() == shared_state.get_oneshot_id(which_thread),
        return_permission@@ is Complete,
{
    let tracked mut oneshot_thread_half = oneshot_thread_half;
    open_atomic_invariant!(shared_state.inv.borrow() => inner => {
        shared_state.x.fetch_add_wrapping(Tracked(&mut inner.x_perm), 1);
        proof {
            if which_thread == 0 {
                oneshot_thread_half.perform_using_two_halves(
                    &mut inner.oneshot0_inv_half,
                );
            } else {
                oneshot_thread_half.perform_using_two_halves(
                    &mut inner.oneshot1_inv_half,
                );
            }
        }
    });
    Tracked(oneshot_thread_half)
}

pub fn count_to_two() -> (result: Result<u32, ()>)
    ensures
        result is Ok ==> result.unwrap() == 2,
{
    let tracked (mut oneshot0_inv_half, mut oneshot0_thread_half) =
        OneShotResource::alloc().split();
    let tracked (mut oneshot1_inv_half, mut oneshot1_thread_half) =
        OneShotResource::alloc().split();
    let shared_state = CounterSharedState::new(
        Tracked(oneshot0_inv_half),
        Tracked(oneshot1_inv_half),
    );
    let shared_state_clone = shared_state.clone();
    let join_handle0 = vstd::thread::spawn(
        move || -> (return_value: Tracked<OneShotResource>)
            ensures
                return_value@.id() == shared_state.get_oneshot_id(0),
                return_value@@ is Complete,
            { thread_routine(shared_state_clone, Tracked(oneshot0_thread_half), Ghost(0)) }
    );
    let shared_state_clone = shared_state.clone();
    let join_handle1 = vstd::thread::spawn(
        move || -> (return_value: Tracked<OneShotResource>)
            ensures
                return_value@.id() == shared_state.get_oneshot_id(1),
                return_value@@ is Complete,
            { thread_routine(shared_state_clone, Tracked(oneshot1_thread_half), Ghost(1)) }
    );
    if let (Ok(oneshot0_complete), Ok(oneshot1_complete)) = (
        join_handle0.join(),
        join_handle1.join(),
    ) {
        Ok(shared_state.read_x(oneshot0_complete, oneshot1_complete))
    } else {
        Err(())
    }
}

pub fn main() {
}

} 
