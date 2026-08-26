fn main() {}


verus! {

pub trait Inv {
    spec fn inv(self) -> bool;
}

impl<T: Inv> Inv for Option<T> {
    open spec fn inv(self) -> bool {
        match self {
            Some(t) => t.inv(),
            None => true,
        }
    }
}

} 


use core::ops::Deref;

use vstd::{predicate::Predicate as DataPredicate, prelude::*};

verus! {

#[repr(transparent)]
#[allow(repr_transparent_non_zst_fields)]
pub struct AtomicDataWithOwner<V, Own> {
    pub data: V,
    pub permission: Tracked<Own>,
}

} 

#[verus_verify]
impl<V, Own> Deref for AtomicDataWithOwner<V, Own> {
    type Target = V;

    #[inline]
    #[verus_spec(returns self.data)]
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

verus! {

impl<V, Own> AtomicDataWithOwner<V, Own> {
    #[inline]
    pub fn new(data: V, permission: Tracked<Own>) -> Self {
        Self { data, permission }
    }
}

impl<V, Own> !Copy for AtomicDataWithOwner<V, Own> {

}

impl<V, Own> !Clone for AtomicDataWithOwner<V, Own> {

}

impl<V, Own: DataPredicate<V>> Inv for AtomicDataWithOwner<V, Own> {
    #[verifier::inline]
    open spec fn inv(self) -> bool {
        &&& self.permission.predicate(self.data)
    }
}

impl<T, Own> View for AtomicDataWithOwner<T, Own> {
    type V = T;

    #[verifier::inline]
    open spec fn view(&self) -> Self::V {
        self.data
    }
}

} 


mod once {
use vstd::{
    atomic_with_ghost,
    cell::pcell::{PCell, PointsTo},
    modes::tracked_static_ref,
    prelude::*,
};

use super::AtomicDataWithOwner;

verus! {

pub const UNINIT: u64 = 0;

pub const OCCUPIED: u64 = 1;

pub const INITED: u64 = 2;

pub tracked enum OnceState<V: 'static> {
    Uninit(PointsTo<Option<V>>),
    Occupied,
    Init(&'static PointsTo<Option<V>>),
}

pub trait Predicate<V> {
    spec fn inv(self, v: V) -> bool;
}

pub struct TrivialPred;

impl<V> Predicate<V> for TrivialPred {
    open spec fn inv(self, v: V) -> bool {
        true
    }
}

struct_with_invariants! {
#[verifier::reject_recursive_types(V)]
pub struct OnceImpl<V: 'static, F: Predicate<V>> {
    cell: PCell<Option<V>>,
    state: vstd::atomic_ghost::AtomicU64<_, OnceState<V>, _>,
    f: Ghost<F>,
}

#[verifier::type_invariant]
pub closed spec fn wf(&self) -> bool {
    invariant on state with (cell, f) is (v: u64, g: OnceState<V>) {
        match g {
            OnceState::Uninit(points_to) => {
                &&& v == UNINIT
                &&& points_to.id() == cell.id()
                &&& points_to.value() is None
            }
            OnceState::Occupied => {
                &&& v == OCCUPIED
            }
            OnceState::Init(points_to) => {
                &&& v == INITED
                &&& points_to.id() == cell.id()
                &&& points_to.value() is Some
                &&& f@.inv(points_to.value()->0)
            }
        }
    }
}

}

#[verifier::external]
unsafe impl<V, F: Predicate<V>> Send for OnceImpl<V, F> {

}

#[verifier::external]
unsafe impl<V, F: Predicate<V>> Sync for OnceImpl<V, F> {

}

impl<V, F: Predicate<V>> OnceImpl<V, F> {
    pub closed spec fn inv(&self) -> F {
        self.f@
    }

    pub const fn new(Ghost(f): Ghost<F>) -> (r: Self)
        ensures
            r.wf(),
            r.inv() == f,
    {
        let (cell, Tracked(points_to)) = PCell::new(None);
        let tracked state = OnceState::Uninit(points_to);
        let state = vstd::atomic_ghost::AtomicU64::new(
            Ghost((cell, Ghost(f))),
            UNINIT,
            Tracked(state),
        );

        Self { cell, state, f: Ghost(f) }
    }

    pub fn init(&self, v: V)
        requires
            self.inv().inv(v),
            self.wf(),
    {
        let cur_state =
            atomic_with_ghost! {
            &self.state => load(); ghost g => {}
        };

        if cur_state != UNINIT {
            return;
        } else {
            let tracked mut points_to = None;
            let res =
                atomic_with_ghost! {
                &self.state => compare_exchange(UNINIT, OCCUPIED);
                returning res; ghost g => {
                    if res.is_ok() {
                        let tracked old_points_to = match g {
                            OnceState::Uninit(points_to) => points_to,
                            _ => proof_from_false(),
                        };
                        points_to = Some(old_points_to);
                        g = OnceState::Occupied;
                    }
                }
            };

            if !res.is_err() {
                let tracked mut points_to = points_to.tracked_unwrap();
                self.cell.replace(Tracked(&mut points_to), Some(v));
                let tracked static_points_to = tracked_static_ref(points_to);
                atomic_with_ghost! {
                    &self.state => store(INITED); ghost g => {
                        assert(self.inv().inv(v));
                        g = OnceState::Init(static_points_to);
                    }
                }
                return;
            } else {
                return;
            }
        }
    }

    pub fn get<'a>(&'a self) -> (r: Option<&'a V>)
        requires
            self.wf(),
        ensures
            self.wf(),
            r matches Some(res) ==> self.inv().inv(*res),
    {
        let tracked mut points_to = None;
        let res =
            atomic_with_ghost! {
            &self.state => load(); ghost g => {
                admit();
            }
        };

        if res == INITED {
            let tracked points_to = points_to.tracked_unwrap();
            let tracked static_points_to = tracked_static_ref(points_to);

            self.cell.borrow(Tracked(static_points_to)).as_ref()
        } else {
            None
        }
    }
}

pub type Once<V, Own, F> = OnceImpl<AtomicDataWithOwner<V, Own>, F>;

} 
} 

pub use once::*;
