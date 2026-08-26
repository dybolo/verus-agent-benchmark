

fn main() {}

verus! {

pub assume_specification[ core::hint::spin_loop ]();

}

use vstd::atomic_ghost::*;
use vstd::cell::{self, CellId, pcell::*};
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::storage_protocol::*;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::imap::*;
use vstd::map::*;
use vstd::math::add;
use vstd::modes::tracked_swap;
use std::ops::Deref;
use std::ops::DerefMut;
use std::marker::PhantomData;



verus! {

#[verus_verify]
pub trait GuardTransfer: Sized {
    fn transfer_to(&mut self) -> Self
        no_unwind
    ;
}

#[verus_verify]
pub trait SpinGuardian {
    type Guard: GuardTransfer;
    type ReadGuard: GuardTransfer;

    fn guard() -> Self::Guard;
    fn read_guard() -> Self::ReadGuard;
}

}

#[verifier::external]
pub enum PreemptDisabled {}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPreemptDisabled(PreemptDisabled);

verus! {

    #[verus_verify]
    pub struct DummyGuard;

    #[verus_verify]
    impl GuardTransfer for DummyGuard {
        fn transfer_to(&mut self) -> Self {
            DummyGuard
        }
    }

    #[verus_verify]
    impl SpinGuardian for PreemptDisabled {
        type Guard = DummyGuard;
        type ReadGuard = DummyGuard;

        fn guard() -> Self::Guard {
            DummyGuard
        }
        fn read_guard() -> Self::Guard {
            DummyGuard
        }
    }

}


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


verus! {

pub tracked enum Sum<L, R> {
    Left(L),
    Right(R),
}

impl<L, R> Sum<L, R> {
    pub open spec fn left(self) -> L {
        self->Left_0
    }

    pub open spec fn right(self) -> R {
        self->Right_0
    }

    pub proof fn tracked_new_left(tracked left: L) -> (tracked res: Self)
        returns
            Self::Left(left),
    {
        Self::Left(left)
    }

    pub proof fn tracked_new_right(tracked right: R) -> (tracked res: Self)
        returns
            Self::Right(right),
    {
        Self::Right(right)
    }

    pub proof fn tracked_take_left(tracked self) -> (tracked res: L)
        requires
            self is Left,
        returns
            self->Left_0,
    {
        match self {
            Self::Left(left) => left,
            Self::Right(_) => proof_from_false(),
        }
    }

    pub proof fn tracked_take_right(tracked self) -> (tracked res: R)
        requires
            self is Right,
        returns
            self->Right_0,
    {
        match self {
            Self::Left(_) => proof_from_false(),
            Self::Right(right) => right,
        }
    }

    pub proof fn tracked_borrow_left(tracked &self) -> (tracked res: &L)
        requires
            self is Left,
        ensures
            *res == self->Left_0,
    {
        match self {
            Self::Left(left) => left,
            Self::Right(_) => proof_from_false(),
        }
    }

    pub proof fn tracked_borrow_right(tracked &self) -> (tracked res: &R)
        requires
            self is Right,
        ensures
            *res == self->Right_0,
    {
        match self {
            Self::Left(_) => proof_from_false(),
            Self::Right(right) => right,
        }
    }

    pub open spec fn lift_map_left<K>(m: Map<K, L>) -> Map<K, Self> {
        m.map_values(|w| Sum::<L, R>::Left(w))
    }

    pub open spec fn lift_map_right<K>(m: Map<K, R>) -> Map<K, Self> {
        m.map_values(|v| Sum::<L, R>::Right(v))
    }

    pub proof fn tracked_swap_left(tracked &mut self, tracked new_left: L) -> (tracked res: L)
        requires
            *old(self) is Left,
        ensures
            res == old(self)->Left_0,
            *final(self) is Left,
            final(self)->Left_0 == new_left,
    {
        let tracked mut tmp = Self::tracked_new_left(new_left);
        tracked_swap(self, &mut tmp);
        tmp.tracked_take_left()
    }

    pub proof fn tracked_swap_right(tracked &mut self, tracked new_right: R) -> (tracked res: R)
        requires
            *old(self) is Right,
        ensures
            res == old(self)->Right_0,
            *final(self) is Right,
            final(self)->Right_0 == new_right,
    {
        let tracked mut tmp = Self::tracked_new_right(new_right);
        tracked_swap(self, &mut tmp);
        tmp.tracked_take_right()
    }
}

impl<L: Inv, R: Inv> Inv for Sum<L, R> {
    open spec fn inv(self) -> bool {
        match self {
            Self::Left(left) => left.inv(),
            Self::Right(right) => right.inv(),
        }
    }
}

impl<L: View, R: View> View for Sum<L, R> {
    type V = Sum<L::V, R::V>;

    open spec fn view(&self) -> Self::V {
        match self {
            Self::Left(left) => Sum::Left(left.view()),
            Self::Right(right) => Sum::Right(right.view()),
        }
    }
}


pub ghost enum SumSP<A, B, const TOTAL: u64> {
    Unit,
    Left(Option<A>, int, bool),
    Right(Option<B>, int, bool),
    CsumInvalid,
}

impl<A, B, const TOTAL: u64> Protocol<(), Sum<A, B>> for SumSP<A, B, TOTAL> {
    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (SumSP::Unit, x) => x,
            (x, SumSP::Unit) => x,
            (SumSP::Left(ov1, n1, b1), SumSP::Left(ov2, n2, b2)) => {
                if !self.is_valid() || !other.is_valid() || n1 + n2 > TOTAL || b1 && b2
                    || ov1 is Some && ov2 is Some {
                    SumSP::CsumInvalid
                } else {
                    SumSP::Left(
                        if ov1 is Some { ov1 } else { ov2 },
                        n1 + n2,
                        b1 || b2,
                    )
                }
            },
            (SumSP::Right(ov1, n1, b1), SumSP::Right(ov2, n2, b2)) => {
                if !self.is_valid() || !other.is_valid() || n1 + n2 > TOTAL || b1 && b2
                    || ov1 is Some && ov2 is Some {
                    SumSP::CsumInvalid
                } else {
                    SumSP::Right(
                        if ov1 is Some { ov1 } else { ov2 },
                        n1 + n2,
                        b1 || b2,
                    )
                }
            },
            _ => SumSP::CsumInvalid,
        }
    }

    open spec fn rel(self, s: IMap<(), Sum<A, B>>) -> bool {
        match self {
            SumSP::Unit => s.is_empty(),
            SumSP::Left(None, n, true) => 0 <= n <= TOTAL && s.is_empty(),
            SumSP::Left(Some(a), n, true) => 0 <= n <= TOTAL && s.contains_key(()) && s[()]
                == Sum::<A, B>::Left(a),
            SumSP::Right(None, n, true) => 0 <= n <= TOTAL && s.is_empty(),
            SumSP::Right(Some(b), n, true) => 0 <= n <= TOTAL && s.contains_key(()) && s[()]
                == Sum::<A, B>::Right(b),
            _ => false,
        }
    }

    open spec fn unit() -> Self {
        SumSP::Unit
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }
}

impl<A, B, const TOTAL: u64> SumSP<A, B, TOTAL> {
    pub open spec fn is_left(self) -> bool {
        self is Left
    }

    pub open spec fn is_right(self) -> bool {
        self is Right
    }

    pub open spec fn is_resource_owner(self) -> bool {
        match self {
            SumSP::Left(_, _, b) | SumSP::Right(_, _, b) => b,
            _ => false,
        }
    }

    pub open spec fn has_resource(self) -> bool {
        match self {
            SumSP::Left(ov, n, true) => ov is Some,
            SumSP::Right(ov, n, true) => ov is Some,
            _ => false,
        }
    }

    pub open spec fn has_no_resource(self) -> bool {
        match self {
            SumSP::Left(ov, n, true) => ov is None,
            SumSP::Right(ov, n, true) => ov is None,
            _ => false,
        }
    }

    pub open spec fn resource(self) -> Sum<A, B> {
        match self {
            SumSP::Left(Some(a), n, true) => Sum::Left(a),
            SumSP::Right(Some(b), n, true) => Sum::Right(b),
            _ => arbitrary(),
        }
    }

    pub open spec fn frac(self) -> int {
        match self {
            SumSP::Left(_, n, _) | SumSP::Right(_, n, _) => n,
            _ => 1,
        }
    }

    pub open spec fn is_valid(self) -> bool {
        match self {
            SumSP::Unit => true,
            SumSP::Left(ov, n, b) => 0 < n <= TOTAL && (ov is Some ==> b),
            SumSP::Right(ov, n, b) => 0 < n <= TOTAL && (ov is Some ==> b),
            _ => false,
        }
    }

    pub proof fn lemma_withdraws_left(self)
        requires
            self.is_left(),
            self.is_resource_owner(),
            self.has_resource(),
            self.is_valid(),
        ensures
            withdraws(self, SumSP::Left(None, self.frac(), true), imap![()=>self.resource()]),
    {
    }

    pub proof fn lemma_withdraws_right(self)
        requires
            self.is_resource_owner(),
            self.is_right(),
            self.has_resource(),
            self.is_valid(),
        ensures
            withdraws(self, SumSP::Right(None, self.frac(), true), imap![()=>self.resource()]),
    {
    }

    pub proof fn lemma_deposit_left(self, a: A)
        requires
            self.is_resource_owner(),
            self.is_left(),
            self.has_no_resource(),
            self.is_valid(),
        ensures
            deposits(self, imap![()=>Sum::Left(a)], SumSP::Left(Some(a), self.frac(), true)),
    {
    }

    pub proof fn lemma_deposit_right(self, b: B)
        requires
            self.is_resource_owner(),
            self.is_right(),
            self.has_no_resource(),
            self.is_valid(),
        ensures
            deposits(self, imap![()=>Sum::Right(b)], SumSP::Right(Some(b), self.frac(), true)),
    {
    }

    pub proof fn lemma_updates_none(self)
        requires
            self.is_left() || self.is_right(),
            self.frac() == TOTAL,
            self.is_resource_owner(),
            self.has_no_resource(),
        ensures
            updates(self, SumSP::Left(None, self.frac(), true)),
            updates(self, SumSP::Right(None, self.frac(), true)),
    {
    }
}


ghost enum FractionalCarrier<T, const TOTAL: u64> {
    Value { v: T, n: int },
    Empty,
    Invalid,
}

impl<T, const TOTAL: u64> FractionalCarrier<T, TOTAL> {
    spec fn new(v: T) -> Self {
        FractionalCarrier::Value { v, n: TOTAL as int }
    }
}

impl<T, const TOTAL: u64> ResourceAlgebra for FractionalCarrier<T, TOTAL> {
    closed spec fn valid(self) -> bool {
        match self {
            FractionalCarrier::Invalid => false,
            FractionalCarrier::Empty => true,
            FractionalCarrier::Value { v: _, n } => 0 < n <= TOTAL,
        }
    }

    closed spec fn op(a: Self, b: Self) -> Self {
        match a {
            FractionalCarrier::Invalid => FractionalCarrier::Invalid,
            FractionalCarrier::Empty => b,
            FractionalCarrier::Value { v: sv, n: sn } => match b {
                FractionalCarrier::Invalid => FractionalCarrier::Invalid,
                FractionalCarrier::Empty => a,
                FractionalCarrier::Value { v: ov, n: on } => {
                    if sv != ov {
                        FractionalCarrier::Invalid
                    } else if sn <= 0 || on <= 0 {
                        FractionalCarrier::Invalid
                    } else {
                        FractionalCarrier::Value { v: sv, n: sn + on }
                    }
                },
            },
        }
    }

    proof fn valid_op(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }
}

impl<T, const TOTAL: u64> PCM for FractionalCarrier<T, TOTAL> {
    closed spec fn unit() -> Self {
        FractionalCarrier::Empty
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

ghost enum FractionalCarrierOpt<T, const TOTAL: u64> {
    Value { v: Option<T>, n: int },
    Empty,
    Invalid,
}

impl<T, const TOTAL: u64> Protocol<(), T> for FractionalCarrierOpt<T, TOTAL> {
    closed spec fn op(self, other: Self) -> Self {
        match self {
            FractionalCarrierOpt::Invalid => FractionalCarrierOpt::Invalid,
            FractionalCarrierOpt::Empty => other,
            FractionalCarrierOpt::Value { v: sv, n: sn } => match other {
                FractionalCarrierOpt::Invalid => FractionalCarrierOpt::Invalid,
                FractionalCarrierOpt::Empty => self,
                FractionalCarrierOpt::Value { v: ov, n: on } => {
                    if sv != ov {
                        FractionalCarrierOpt::Invalid
                    } else if sn <= 0 || on <= 0 {
                        FractionalCarrierOpt::Invalid
                    } else {
                        FractionalCarrierOpt::Value { v: sv, n: sn + on }
                    }
                },
            },
        }
    }

    closed spec fn rel(self, s: IMap<(), T>) -> bool {
        match self {
            FractionalCarrierOpt::Value { v, n } => {
                (match v {
                    Some(v0) => s.dom().contains(()) && s[()] == v0,
                    None => s =~= imap![],
                }) && n == TOTAL && n != 0
            },
            FractionalCarrierOpt::Empty => false,
            FractionalCarrierOpt::Invalid => false,
        }
    }

    closed spec fn unit() -> Self {
        FractionalCarrierOpt::Empty
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }
}

pub tracked struct CountGhost<T, const TOTAL: u64 = 2> {
    r: vstd::resource::pcm::Resource<FractionalCarrier<T, TOTAL>>,
}

impl<T, const TOTAL: u64> CountGhost<T, TOTAL> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.r.value() is Value
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> T {
        self.r.value()->v
    }

    pub closed spec fn frac(self) -> int {
        self.r.value()->n
    }

    pub open spec fn valid(self, id: Loc, frac: int) -> bool {
        &&& self.id() == id
        &&& self.frac() == frac
    }

    #[verifier::external_body]
    pub proof fn new(v: T) -> (tracked result: Self)
        requires
            TOTAL > 0,
        ensures
            result.frac() == TOTAL as int,
            result@ == v,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn agree(tracked self: &Self, tracked other: &Self)
        requires
            self.id() == other.id(),
        ensures
            self@ == other@,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn take(tracked &mut self) -> (tracked result: Self)
        ensures
            result == *old(self),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split(tracked &mut self, n: int) -> (tracked result: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            result.id() == final(self).id(),
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            result@ == old(self)@,
            final(self).frac() + result.frac() == old(self).frac(),
            result.frac() == n,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn combine(tracked &mut self, tracked other: Self)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            final(self)@ == other@,
            final(self).frac() == old(self).frac() + other.frac(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn update(tracked &mut self, v: T)
        requires
            old(self).frac() == TOTAL,
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == v,
            final(self).frac() == old(self).frac(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn update_with(tracked &mut self, tracked other: &mut Self, v: T)
        requires
            old(self).id() == old(other).id(),
            old(self).frac() + old(other).frac() == TOTAL,
        ensures
            final(self).id() == old(self).id(),
            final(other).id() == old(other).id(),
            final(self).frac() == old(self).frac(),
            final(other).frac() == old(other).frac(),
            old(self)@ == old(other)@,
            final(self)@ == v,
            final(other)@ == v,
    {
        unimplemented!()
    }

    pub proof fn bounded(tracked &self)
        ensures
            0 < self.frac() <= TOTAL,
    {
        use_type_invariant(self);
        self.r.validate()
    }

    #[verifier::external_body]
    pub proof fn dummy() -> (tracked result: Self)
    {
        unimplemented!()
    }
}

pub tracked struct Count<T, const TOTAL: u64 = 2> {
    r: StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
}

pub tracked struct EmptyCount<T, const TOTAL: u64 = 2> {
    r: StorageResource<(), T, FractionalCarrierOpt<T, TOTAL>>,
}

impl<T, const TOTAL: u64> Count<T, TOTAL> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.r.value() matches FractionalCarrierOpt::Value { v: Some(_), .. }
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn resource(self) -> T {
        self.r.value()->v->0
    }

    pub closed spec fn frac(self) -> int {
        self.r.value()->n
    }

    pub open spec fn valid(self, id: Loc, frac: int) -> bool {
        &&& self.id() == id
        &&& self.frac() == frac
    }

    #[verifier::external_body]
    pub proof fn new(tracked v: T) -> (tracked result: Self)
        requires
            TOTAL > 0,
        ensures
            result.frac() == TOTAL as int,
            result.resource() == v,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn agree(tracked self: &Self, tracked other: &Self)
        requires
            self.id() == other.id(),
        ensures
            self.resource() == other.resource(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split(tracked &mut self, n: int) -> (tracked result: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            result.id() == final(self).id(),
            final(self).id() == old(self).id(),
            final(self).resource() == old(self).resource(),
            result.resource() == old(self).resource(),
            final(self).frac() + result.frac() == old(self).frac(),
            result.frac() == n,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn combine(tracked &mut self, tracked other: Self)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).resource() == old(self).resource(),
            final(self).resource() == other.resource(),
            final(self).frac() == old(self).frac() + other.frac(),
    {
        unimplemented!()
    }

    pub proof fn bounded(tracked &self)
        ensures
            0 < self.frac() <= TOTAL,
    {
        use_type_invariant(self);
        let (x, _) = self.r.validate();
    }

    #[verifier::external_body]
    pub proof fn borrow(tracked &self) -> (tracked ret: &T)
        ensures
            ret == self.resource(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn take_resource(tracked self) -> (tracked pair: (T, EmptyCount<T, TOTAL>))
        requires
            self.frac() == TOTAL,
        ensures
            pair.0 == self.resource(),
            pair.1.id() == self.id(),
    {
        unimplemented!()
    }
}

impl<T, const TOTAL: u64> EmptyCount<T, TOTAL> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.r.value() matches FractionalCarrierOpt::Value { v: None, n }
        &&& n == TOTAL
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    #[verifier::external_body]
    pub proof fn new(tracked v: T) -> (tracked result: Self)
        requires
            TOTAL > 0,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn put_resource(tracked self, tracked resource: T) -> (tracked frac: Count<T, TOTAL>)
        ensures
            frac.id() == self.id(),
            frac.resource() == resource,
            frac.frac() == TOTAL,
    {
        unimplemented!()
    }
}


pub tracked struct SumResource<A, B, const TOTAL: u64 = 2> {
    tracked r: StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
}

pub tracked struct Left<A, B, const TOTAL: u64 = 2> {
    tracked r: StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
}

pub tracked struct Right<A, B, const TOTAL: u64 = 2> {
    tracked r: StorageResource<(), Sum<A, B>, SumSP<A, B, TOTAL>>,
}

pub tracked struct OneLeftOwner<A, B, const TOTAL: u64 = 2> {
    tracked r: Left<A, B, TOTAL>,
}

pub tracked struct OneRightOwner<A, B, const TOTAL: u64 = 2> {
    tracked r: Right<A, B, TOTAL>,
}

pub tracked struct OneLeftKnowledge<A, B, const TOTAL: u64 = 2> {
    tracked r: Left<A, B, TOTAL>,
}

pub tracked struct OneRightKnowledge<A, B, const TOTAL: u64 = 2> {
    tracked r: Right<A, B, TOTAL>,
}

impl<A, B, const TOTAL: u64> SumResource<A, B, TOTAL> {
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn protocol_monoid(self) -> SumSP<A, B, TOTAL> {
        self.r.value()
    }

    pub open spec fn is_resource_owner(self) -> bool {
        self.protocol_monoid().is_resource_owner()
    }

    pub open spec fn resource(self) -> Sum<A, B> {
        self.protocol_monoid().resource()
    }

    pub open spec fn resource_left(self) -> A {
        self.resource()->Left_0
    }

    pub open spec fn resource_right(self) -> B {
        self.resource()->Right_0
    }

    pub open spec fn is_left(self) -> bool {
        self.protocol_monoid().is_left()
    }

    pub open spec fn is_right(self) -> bool {
        self.protocol_monoid().is_right()
    }

    pub open spec fn has_resource(self) -> bool {
        let p = self.protocol_monoid();
        p.is_resource_owner() && p.has_resource()
    }

    pub open spec fn has_no_resource(self) -> bool {
        let p = self.protocol_monoid();
        p.is_resource_owner() && p.has_no_resource()
    }

    pub open spec fn frac(self) -> int {
        self.protocol_monoid().frac()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    pub open spec fn wf(self) -> bool {
        &&& 1 <= self.frac() <= TOTAL
        &&& self.protocol_monoid().is_valid()
        &&& self.is_resource_owner() ==> (self.has_resource() <==> !self.has_no_resource())
        &&& (self.is_left() <==> !self.is_right())
    }

    #[verifier::external_body]
    pub proof fn alloc_left(tracked a: A) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.is_left(),
            res.is_resource_owner(),
            res.has_resource(),
            res.resource() == Sum::<A, B>::Left(a),
            res.frac() == TOTAL,
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn alloc_right(tracked b: B) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.is_right(),
            res.is_resource_owner(),
            res.has_resource(),
            res.resource() == Sum::<A, B>::Right(b),
            res.frac() == TOTAL,
            res.wf(),
    {
        unimplemented!()
    }

    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&*self);
    }

    #[verifier::external_body]
    pub proof fn validate_with_other(tracked &mut self, tracked other: &Self)
        requires
            old(self).is_left() && old(self).is_right() || other.is_left() && other.is_right()
                || old(self).is_left() && other.is_left() && old(self).is_resource_owner()
                && other.is_resource_owner() || old(self).is_right() && other.is_right() && old(
                self,
            ).is_resource_owner() && other.is_resource_owner(),
        ensures
            *old(self) == *final(self),
            final(self).id() != other.id(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn validate_with_left(tracked &mut self, tracked other: &Left<A, B, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            final(self).is_left(),
            !(final(self).is_resource_owner() && other.is_resource_owner()),
            final(self).frac() + other.frac() <= TOTAL,
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn validate_with_right(tracked &mut self, tracked other: &Right<A, B, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            final(self).is_right(),
            !(final(self).is_resource_owner() && other.is_resource_owner()),
            final(self).frac() + other.frac() <= TOTAL,
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn validate_with_one_left_owner(
        tracked &mut self,
        tracked other: &OneLeftOwner<A, B, TOTAL>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            final(self).is_left(),
            !final(self).is_resource_owner(),
            final(self).frac() + 1 <= TOTAL,
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn validate_with_one_right_owner(
        tracked &mut self,
        tracked other: &OneRightOwner<A, B, TOTAL>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            final(self).is_right(),
            !final(self).is_resource_owner(),
            final(self).frac() + 1 <= TOTAL,
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn validate_with_one_left_knowledge(
        tracked &mut self,
        tracked other: &OneLeftKnowledge<A, B, TOTAL>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            final(self).is_left(),
            final(self).frac() + 1 <= TOTAL,
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn validate_with_one_right_knowledge(
        tracked &mut self,
        tracked other: &OneRightKnowledge<A, B, TOTAL>,
    )
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            final(self).is_right(),
            final(self).frac() + 1 <= TOTAL,
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn tracked_borrow_left(tracked &self) -> (tracked res: &A)
        requires
            self.is_left(),
            self.is_resource_owner(),
            self.has_resource(),
        ensures
            *res == self.resource_left(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn tracked_borrow_right(tracked &self) -> (tracked res: &B)
        requires
            self.is_right(),
            self.is_resource_owner(),
            self.has_resource(),
        ensures
            *res == self.resource()->Right_0,
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split_left_with_resource(tracked &mut self, n: int) -> (tracked res: Left<A, B, TOTAL>)
        requires
            old(self).is_left(),
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.id() == old(self).id(),
            res.frac() == n,
            !final(self).is_resource_owner(),
            res.is_resource_owner() <==> old(self).is_resource_owner(),
            res.is_resource_owner() ==> (res.has_resource() <==> old(self).has_resource()),
            res.has_resource() ==> res.resource() == old(self).resource_left(),
            final(self).wf(),
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split_left_without_resource(tracked &mut self, n: int) -> (tracked res: Left<A, B, TOTAL>)
        requires
            old(self).is_left(),
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.id() == old(self).id(),
            res.frac() == n,
            !res.is_resource_owner(),
            final(self).is_resource_owner() <==> old(self).is_resource_owner(),
            final(self).is_resource_owner() ==> (final(self).has_resource() <==> old(self).has_resource()),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            final(self).wf(),
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split_right_with_resource(tracked &mut self, n: int) -> (tracked res: Right<A, B, TOTAL>)
        requires
            old(self).is_right(),
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.id() == old(self).id(),
            res.frac() == n,
            !final(self).is_resource_owner(),
            res.is_resource_owner() <==> old(self).is_resource_owner(),
            res.is_resource_owner() ==> (res.has_resource() <==> old(self).has_resource()),
            res.has_resource() ==> res.resource() == old(self).resource_right(),
            final(self).wf(),
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split_right_without_resource(tracked &mut self, n: int) -> (tracked res: Right<A, B, TOTAL>)
        requires
            old(self).is_right(),
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.id() == old(self).id(),
            res.frac() == n,
            !res.is_resource_owner(),
            final(self).is_resource_owner() <==> old(self).is_resource_owner(),
            final(self).is_resource_owner() ==> (final(self).has_resource() <==> old(self).has_resource()),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            final(self).wf(),
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split_one_left_owner(tracked &mut self) -> (tracked res: OneLeftOwner<A, B, TOTAL>)
        requires
            old(self).is_left(),
            old(self).is_resource_owner(),
            old(self).frac() > 1,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).is_left(),
            final(self).frac() + 1 == old(self).frac(),
            !final(self).is_resource_owner(),
            res.id() == old(self).id(),
            res.wf(),
            res.has_resource() == old(self).has_resource(),
            res.has_resource() ==> res.resource() == old(self).resource_left(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split_one_right_owner(tracked &mut self) -> (tracked res: OneRightOwner<A, B, TOTAL>)
        requires
            old(self).is_right(),
            old(self).is_resource_owner(),
            old(self).frac() > 1,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).is_right(),
            final(self).frac() + 1 == old(self).frac(),
            !final(self).is_resource_owner(),
            res.id() == old(self).id(),
            res.wf(),
            res.has_resource() == old(self).has_resource(),
            res.has_resource() ==> res.resource() == old(self).resource_right(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split_one_left_knowledge(tracked &mut self) -> (tracked res: OneLeftKnowledge<A, B, TOTAL>)
        requires
            old(self).is_left(),
            old(self).frac() > 1,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).is_left(),
            final(self).frac() + 1 == old(self).frac(),
            final(self).is_resource_owner() == old(self).is_resource_owner(),
            final(self).has_resource() == old(self).has_resource(),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            res.id() == old(self).id(),
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split_one_right_knowledge(tracked &mut self) -> (tracked res: OneRightKnowledge<A, B, TOTAL>)
        requires
            old(self).is_right(),
            old(self).frac() > 1,
        ensures
            final(self).wf(),
            final(self).id() == old(self).id(),
            final(self).is_right(),
            final(self).frac() + 1 == old(self).frac(),
            final(self).is_resource_owner() == old(self).is_resource_owner(),
            final(self).has_resource() == old(self).has_resource(),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            res.id() == old(self).id(),
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn take_resource_left(tracked &mut self) -> (tracked res: A)
        requires
            old(self).is_left(),
            old(self).is_resource_owner(),
            old(self).has_resource(),
        ensures
            final(self).is_left(),
            res == old(self).resource_left(),
            final(self).id() == old(self).id(),
            final(self).is_resource_owner(),
            final(self).has_no_resource(),
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn take_resource_right(tracked &mut self) -> (tracked res: B)
        requires
            old(self).is_right(),
            old(self).is_resource_owner(),
            old(self).has_resource(),
        ensures
            final(self).is_right(),
            res == old(self).resource_right(),
            final(self).id() == old(self).id(),
            final(self).is_resource_owner(),
            final(self).has_no_resource(),
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn put_resource_left(tracked &mut self, tracked a: A)
        requires
            old(self).is_left(),
            old(self).is_resource_owner(),
            old(self).has_no_resource(),
        ensures
            final(self).is_left(),
            final(self).has_resource(),
            final(self).is_resource_owner(),
            final(self).resource_left() == a,
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn put_resource_right(tracked &mut self, tracked b: B)
        requires
            old(self).is_right(),
            old(self).is_resource_owner(),
            old(self).has_no_resource(),
        ensures
            final(self).is_right(),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource_right() == b,
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn update_left(tracked &mut self, tracked a: A) -> (tracked res: Option<A>)
        requires
            old(self).is_left(),
            old(self).is_resource_owner(),
            old(self).has_resource(),
        ensures
            final(self).is_left(),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource_left() == a,
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac(),
            res == Some(old(self).resource_left()),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn update_right(tracked &mut self, tracked b: B) -> (tracked res: Option<B>)
        requires
            old(self).is_right(),
            old(self).is_resource_owner(),
            old(self).has_resource(),
        ensures
            final(self).is_right(),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource_right() == b,
            final(self).id() == old(self).id(),
            final(self).frac() == old(self).frac(),
            res == Some(old(self).resource_right()),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn change_to_left(tracked &mut self, tracked a: A) -> (tracked res: Option<Sum<A, B>>)
        requires
            old(self).is_resource_owner(),
            old(self).frac() == TOTAL,
        ensures
            final(self).id() == old(self).id(),
            final(self).protocol_monoid() == SumSP::<A, B, TOTAL>::Left(Some(a), old(self).frac(), true),
            final(self).frac() == old(self).frac(),
            final(self).is_left(),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource_left() == a,
            old(self).has_resource() ==> res == Some(old(self).resource()),
            old(self).has_no_resource() ==> res == None::<Sum<A, B>>,
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn change_to_right(tracked &mut self, tracked b: B) -> (tracked res: Option<Sum<A, B>>)
        requires
            old(self).is_resource_owner(),
            old(self).frac() == TOTAL,
        ensures
            final(self).id() == old(self).id(),
            final(self).protocol_monoid() == SumSP::<A, B, TOTAL>::Right(Some(b), old(self).frac(), true),
            final(self).frac() == old(self).frac(),
            final(self).is_right(),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource_right() == b,
            old(self).has_resource() ==> res == Some(old(self).resource()),
            old(self).has_no_resource() ==> res == None::<Sum<A, B>>,
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn join_left(tracked &mut self, tracked other: Left<A, B, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_left(),
            final(self).is_resource_owner() == (old(self).is_resource_owner() || other.is_resource_owner()),
            final(self).has_resource() == (old(self).has_resource() || other.has_resource()),
            final(self).has_resource() ==> final(self).resource() == if old(self).is_resource_owner() {
                old(self).resource()
            } else {
                Sum::Left(other.resource())
            },
            final(self).frac() == old(self).frac() + other.frac(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn join_right(tracked &mut self, tracked other: Right<A, B, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_right(),
            final(self).is_resource_owner() == (old(self).is_resource_owner() || other.is_resource_owner()),
            final(self).has_resource() == (old(self).has_resource() || other.has_resource()),
            final(self).has_resource() ==> final(self).resource() == if old(self).is_resource_owner() {
                old(self).resource()
            } else {
                Sum::Right(other.resource())
            },
            final(self).frac() == old(self).frac() + other.frac(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn join_one_left_owner(tracked &mut self, tracked other: OneLeftOwner<A, B, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_left(),
            final(self).is_resource_owner(),
            final(self).has_resource() == other.has_resource(),
            final(self).has_resource() ==> final(self).resource_left() == other.resource(),
            final(self).frac() == old(self).frac() + 1,
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn join_one_right_owner(tracked &mut self, tracked other: OneRightOwner<A, B, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_right(),
            final(self).is_resource_owner(),
            final(self).has_resource() == other.has_resource(),
            final(self).has_resource() ==> final(self).resource_right() == other.resource(),
            final(self).frac() == old(self).frac() + 1,
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn join_one_left_knowledge(tracked &mut self, tracked other: OneLeftKnowledge<A, B, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_left(),
            final(self).is_resource_owner() == old(self).is_resource_owner(),
            final(self).has_resource() == old(self).has_resource(),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            final(self).frac() == old(self).frac() + 1,
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn join_one_right_knowledge(tracked &mut self, tracked other: OneRightKnowledge<A, B, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_right(),
            final(self).is_resource_owner() == old(self).is_resource_owner(),
            final(self).has_resource() == old(self).has_resource(),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            final(self).frac() == old(self).frac() + 1,
            final(self).wf(),
    {
        unimplemented!()
    }
}

impl<A, B, const TOTAL: u64> Left<A, B, TOTAL> {
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn protocol_monoid(self) -> SumSP<A, B, TOTAL> {
        self.r.value()
    }

    pub open spec fn is_resource_owner(self) -> bool {
        self.protocol_monoid().is_resource_owner()
    }

    pub open spec fn resource(self) -> A {
        self.protocol_monoid().resource()->Left_0
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    pub open spec fn wf(self) -> bool {
        &&& self.protocol_monoid().is_left()
        &&& self.protocol_monoid().is_valid()
        &&& 1 <= self.frac() <= TOTAL
        &&& self.is_resource_owner() ==> (self.has_resource() <==> !self.has_no_resource())
    }

    pub open spec fn has_resource(self) -> bool {
        self.protocol_monoid().has_resource()
    }

    pub open spec fn has_no_resource(self) -> bool {
        self.protocol_monoid().has_no_resource()
    }

    pub open spec fn frac(self) -> int {
        self.protocol_monoid().frac()
    }

    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&*self);
    }

    #[verifier::external_body]
    pub proof fn validate_with_left(tracked &mut self, tracked other: &Self)
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            !(final(self).is_resource_owner() && other.is_resource_owner()),
            final(self).frac() + other.frac() <= TOTAL,
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn validate_with_right(tracked &self, tracked other: &Right<A, B, TOTAL>)
        ensures
            self.id() != other.id(),
            self.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &A)
        requires
            self.has_resource(),
        ensures
            *res == self.resource(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn take_resource(tracked &mut self) -> (tracked res: A)
        requires
            old(self).is_resource_owner(),
            old(self).has_resource(),
        ensures
            final(self).id() == old(self).id(),
            res == old(self).resource(),
            final(self).is_resource_owner(),
            final(self).has_no_resource(),
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn put_resource(tracked &mut self, tracked a: A)
        requires
            old(self).is_resource_owner(),
            old(self).has_no_resource(),
        ensures
            final(self).id() == old(self).id(),
            final(self).protocol_monoid() == SumSP::<A, B, TOTAL>::Left(Some(a), final(self).frac(), true),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource() == a,
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split_with_resource(tracked &mut self, n: int) -> (tracked res: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            res.id() == final(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.frac() == n,
            !final(self).is_resource_owner(),
            res.is_resource_owner() <==> old(self).is_resource_owner(),
            res.is_resource_owner() ==> (res.has_resource() <==> old(self).has_resource()),
            res.has_resource() ==> res.resource() == old(self).resource(),
            final(self).wf(),
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split_without_resource(tracked &mut self, n: int) -> (tracked res: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            res.id() == final(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.frac() == n,
            !res.is_resource_owner(),
            final(self).is_resource_owner() <==> old(self).is_resource_owner(),
            final(self).is_resource_owner() ==> (final(self).has_resource() <==> old(self).has_resource()),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            final(self).wf(),
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn update(tracked &mut self, tracked a: A) -> (tracked res: Option<A>)
        requires
            old(self).is_resource_owner(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource() == a,
            final(self).frac() == old(self).frac(),
            res == if old(self).has_resource() { Some(old(self).resource()) } else { None },
            final(self).wf(),
    {
        unimplemented!()
    }
}

impl<A, B, const TOTAL: u64> Right<A, B, TOTAL> {
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn protocol_monoid(self) -> SumSP<A, B, TOTAL> {
        self.r.value()
    }

    pub open spec fn is_resource_owner(self) -> bool {
        self.protocol_monoid().is_resource_owner()
    }

    pub open spec fn resource(self) -> B {
        self.protocol_monoid().resource()->Right_0
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    pub open spec fn wf(self) -> bool {
        &&& self.protocol_monoid().is_right()
        &&& self.protocol_monoid().is_valid()
        &&& 1 <= self.frac() <= TOTAL
        &&& self.is_resource_owner() ==> (self.has_resource() <==> !self.has_no_resource())
    }

    pub open spec fn has_resource(self) -> bool {
        self.protocol_monoid().has_resource()
    }

    pub open spec fn has_no_resource(self) -> bool {
        self.protocol_monoid().has_no_resource()
    }

    pub open spec fn frac(self) -> int {
        self.protocol_monoid().frac()
    }

    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&*self);
    }

    #[verifier::external_body]
    pub proof fn validate_with_left(tracked &self, tracked other: &Left<A, B, TOTAL>)
        ensures
            self.id() != other.id(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn validate_with_right(tracked &mut self, tracked other: &Self)
        requires
            old(self).id() == other.id(),
        ensures
            *old(self) == *final(self),
            !(final(self).is_resource_owner() && other.is_resource_owner()),
            final(self).frac() + other.frac() <= TOTAL,
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &B)
        requires
            self.has_resource(),
        ensures
            *res == self.resource(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn take_resource(tracked &mut self) -> (tracked res: B)
        requires
            old(self).is_resource_owner(),
            old(self).has_resource(),
        ensures
            final(self).id() == old(self).id(),
            res == old(self).resource(),
            final(self).is_resource_owner(),
            final(self).has_no_resource(),
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn put_resource(tracked &mut self, tracked b: B)
        requires
            old(self).is_resource_owner(),
            old(self).has_no_resource(),
        ensures
            final(self).id() == old(self).id(),
            final(self).protocol_monoid() == SumSP::<A, B, TOTAL>::Right(Some(b), final(self).frac(), true),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource() == b,
            final(self).frac() == old(self).frac(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split_with_resource(tracked &mut self, n: int) -> (tracked res: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            res.id() == final(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.frac() == n,
            !final(self).is_resource_owner(),
            res.is_resource_owner() <==> old(self).is_resource_owner(),
            res.is_resource_owner() ==> (res.has_resource() <==> old(self).has_resource()),
            res.has_resource() ==> res.resource() == old(self).resource(),
            final(self).wf(),
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split_without_resource(tracked &mut self, n: int) -> (tracked res: Self)
        requires
            0 < n < old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            res.id() == final(self).id(),
            final(self).frac() == old(self).frac() - n,
            res.frac() == n,
            !res.is_resource_owner(),
            final(self).is_resource_owner() <==> old(self).is_resource_owner(),
            final(self).is_resource_owner() ==> (final(self).has_resource() <==> old(self).has_resource()),
            final(self).has_resource() ==> final(self).resource() == old(self).resource(),
            final(self).wf(),
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn update(tracked &mut self, tracked b: B) -> (tracked res: Option<B>)
        requires
            old(self).is_resource_owner(),
        ensures
            final(self).id() == old(self).id(),
            final(self).is_resource_owner(),
            final(self).has_resource(),
            final(self).resource() == b,
            final(self).frac() == old(self).frac(),
            res == if old(self).has_resource() { Some(old(self).resource()) } else { None },
            final(self).wf(),
    {
        unimplemented!()
    }
}

impl<A, B, const TOTAL: u64> OneLeftOwner<A, B, TOTAL> {
    pub closed spec fn id(self) -> Loc {
        self.r.id()
    }

    pub closed spec fn protocol_monoid(self) -> SumSP<A, B, TOTAL> {
        self.r.protocol_monoid()
    }

    pub closed spec fn resource(self) -> A {
        self.r.resource()
    }

    pub closed spec fn frac(self) -> int {
        self.r.frac()
    }

    pub closed spec fn has_resource(self) -> bool {
        self.r.has_resource()
    }

    pub closed spec fn has_no_resource(self) -> bool {
        self.r.has_no_resource()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    pub open spec fn wf(self) -> bool {
        &&& self.protocol_monoid().is_left()
        &&& self.protocol_monoid().is_valid()
        &&& self.protocol_monoid().is_resource_owner()
        &&& self.frac() == 1
        &&& TOTAL >= 1
        &&& self.has_resource() <==> !self.has_no_resource()
    }

    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&*self);
    }

    #[verifier::external_body]
    pub proof fn validate_with_one_left_owner(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *final(self),
            final(self).id() != other.id(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &A)
        requires
            self.has_resource(),
        ensures
            *res == self.resource(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn take_resource(tracked &mut self) -> (tracked res: A)
        requires
            old(self).has_resource(),
        ensures
            res == old(self).resource(),
            final(self).has_no_resource(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn put_resource(tracked &mut self, tracked a: A)
        requires
            old(self).has_no_resource(),
        ensures
            final(self).resource() == a,
            final(self).has_resource(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn update(tracked &mut self, tracked a: A) -> (tracked res: Option<A>)
        ensures
            final(self).resource() == a,
            final(self).has_resource(),
            final(self).wf(),
            res == if old(self).has_resource() { Some(old(self).resource()) } else { None },
    {
        unimplemented!()
    }
}

impl<A, B, const TOTAL: u64> OneRightOwner<A, B, TOTAL> {
    pub closed spec fn id(self) -> Loc {
        self.r.id()
    }

    pub closed spec fn protocol_monoid(self) -> SumSP<A, B, TOTAL> {
        self.r.protocol_monoid()
    }

    pub closed spec fn resource(self) -> B {
        self.r.resource()
    }

    pub closed spec fn frac(self) -> int {
        self.r.frac()
    }

    pub closed spec fn has_resource(self) -> bool {
        self.r.has_resource()
    }

    pub closed spec fn has_no_resource(self) -> bool {
        self.r.has_no_resource()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    pub open spec fn wf(self) -> bool {
        &&& self.protocol_monoid().is_right()
        &&& self.protocol_monoid().is_valid()
        &&& self.protocol_monoid().is_resource_owner()
        &&& self.frac() == 1
        &&& TOTAL >= 1
        &&& self.has_resource() <==> !self.has_no_resource()
    }

    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&*self);
    }

    #[verifier::external_body]
    pub proof fn validate_with_one_right_owner(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *final(self),
            final(self).id() != other.id(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn tracked_borrow(tracked &self) -> (tracked res: &B)
        requires
            self.has_resource(),
        ensures
            *res == self.resource(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn take_resource(tracked &mut self) -> (tracked res: B)
        requires
            old(self).has_resource(),
        ensures
            res == old(self).resource(),
            final(self).has_no_resource(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn put_resource(tracked &mut self, tracked b: B)
        requires
            old(self).has_no_resource(),
        ensures
            final(self).resource() == b,
            final(self).has_resource(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn update(tracked &mut self, tracked b: B) -> (tracked res: Option<B>)
        ensures
            final(self).resource() == b,
            final(self).has_resource(),
            final(self).wf(),
            res == if old(self).has_resource() { Some(old(self).resource()) } else { None },
    {
        unimplemented!()
    }
}

impl<A, B, const TOTAL: u64> OneLeftKnowledge<A, B, TOTAL> {
    pub closed spec fn id(self) -> Loc {
        self.r.id()
    }

    pub closed spec fn protocol_monoid(self) -> SumSP<A, B, TOTAL> {
        self.r.protocol_monoid()
    }

    pub closed spec fn frac(self) -> int {
        self.r.frac()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    pub open spec fn wf(self) -> bool {
        &&& self.protocol_monoid().is_left()
        &&& self.protocol_monoid().is_valid()
        &&& !self.protocol_monoid().is_resource_owner()
        &&& self.frac() == 1
        &&& TOTAL >= 1
    }

    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&*self);
    }

    #[verifier::external_body]
    pub proof fn validate_with_one_right_knowledge(
        tracked &self,
        tracked other: &OneRightKnowledge<A, B, TOTAL>,
    )
        ensures
            self.id() != other.id(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn validate_with_one_right_owner(
        tracked &self,
        tracked other: &OneRightOwner<A, B, TOTAL>,
    )
        ensures
            self.id() != other.id(),
    {
        unimplemented!()
    }
}

impl<A, B, const TOTAL: u64> OneRightKnowledge<A, B, TOTAL> {
    pub closed spec fn id(self) -> Loc {
        self.r.id()
    }

    pub closed spec fn protocol_monoid(self) -> SumSP<A, B, TOTAL> {
        self.r.protocol_monoid()
    }

    pub closed spec fn frac(self) -> int {
        self.r.frac()
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    pub open spec fn wf(self) -> bool {
        &&& self.protocol_monoid().is_right()
        &&& self.protocol_monoid().is_valid()
        &&& !self.protocol_monoid().is_resource_owner()
        &&& self.frac() == 1
        &&& TOTAL >= 1
    }

    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(&*self);
    }

    #[verifier::external_body]
    pub proof fn validate_with_one_left_knowledge(
        tracked &self,
        tracked other: &OneLeftKnowledge<A, B, TOTAL>,
    )
        ensures
            self.id() != other.id(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn validate_with_one_left_owner(
        tracked &self,
        tracked other: &OneLeftOwner<A, B, TOTAL>,
    )
        ensures
            self.id() != other.id(),
    {
        unimplemented!()
    }
}


pub type UniqueToken = ExclusiveGhost<()>;

pub tracked struct ExclusiveGhost<T>(vstd::resource::algebra::Resource<ExclusiveRA<T>>);

impl<T> ExclusiveGhost<T> {
    pub closed spec fn id(self) -> Loc {
        self.0.loc()
    }

    pub closed spec fn pcm(self) -> ExclusiveRA<T> {
        self.0.value()
    }

    pub open spec fn value(self) -> T {
        self.pcm()->Exclusive_0
    }

    pub open spec fn view(self) -> T {
        self.value()
    }

    pub open spec fn wf(self) -> bool {
        self.pcm() is Exclusive
    }

    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        self.wf()
    }

    #[verifier::external_body]
    pub proof fn alloc(value: T) -> (tracked res: Self)
        ensures
            res.view() == value,
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn update(tracked &mut self, value: T) -> (res: T)
        ensures
            final(self).id() == old(self).id(),
            final(self).view() == value,
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn validate_with_other(tracked &mut self, tracked other: &Self)
        ensures
            *old(self) == *final(self),
            final(self).id() != other.id(),
            final(self).wf(),
    {
        unimplemented!()
    }

    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(self);
    }
}


pub tracked struct CountGhostResource<T, const TOTAL: u64> {
    tracked r: Option<CountGhost<T, TOTAL>>,
    ghost snapshot: T,
    ghost id: Loc,
}

impl<T, const TOTAL: u64> CountGhostResource<T, TOTAL> {
    #[verifier::type_invariant]
    closed spec fn type_inv(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& self.r is Some ==> {
            &&& self.id == self.r->0.id()
            &&& self.view() == self.r->0@
        }
    }

    pub open spec fn wf(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
    }

    pub open spec fn is_empty(self) -> bool {
        self.frac() == 0
    }

    pub open spec fn not_empty(self) -> bool {
        !self.is_empty()
    }

    pub open spec fn is_full(self) -> bool {
        self.frac() == TOTAL
    }

    pub closed spec fn storage(self) -> CountGhost<T, TOTAL> {
        self.r->0
    }

    pub closed spec fn view(self) -> T {
        self.snapshot
    }

    pub closed spec fn frac(self) -> int {
        if self.r is None {
            0int
        } else {
            self.storage().frac()
        }
    }

    pub closed spec fn id(self) -> Loc {
        self.id
    }

    pub proof fn arbitrary() -> (tracked res: Self)
        requires
            TOTAL > 0,
    {
        Self { r: None, snapshot: arbitrary(), id: arbitrary() }
    }

    #[verifier::external_body]
    pub proof fn alloc(value: T) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.not_empty(),
            res.is_full(),
            res@ == value,
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split_one(tracked &mut self) -> (tracked res: CountGhost<T, TOTAL>)
        requires
            old(self).not_empty(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() + 1 == old(self).frac(),
            final(self)@ == old(self)@,
            res.frac() == 1,
            res.id() == final(self).id(),
            res@ == final(self)@,
            old(self).frac() == 1 ==> final(self).is_empty(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split(tracked &mut self, n: int) -> (tracked res: CountGhost<T, TOTAL>)
        requires
            1 <= n <= old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() + n == old(self).frac(),
            final(self)@ == old(self)@,
            res.frac() == n,
            res.id() == final(self).id(),
            res@ == final(self)@,
            old(self).frac() == n ==> final(self).is_empty(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn combine(tracked &mut self, tracked other: CountGhost<T, TOTAL>)
        requires
            old(self).id() == other.id(),
            other@ == old(self)@,
        ensures
            old(self).frac() + other.frac() > TOTAL ==> false,
            old(self).frac() + other.frac() <= TOTAL ==> {
                &&& final(self).id() == old(self).id()
                &&& final(self)@ == old(self)@
                &&& final(self).frac() == old(self).frac() + other.frac()
                &&& final(self).wf()
            },
    {
        unimplemented!()
    }

    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(self);
    }

    pub proof fn validate_full(tracked &self)
        requires
            self.is_full(),
        ensures
            self.not_empty(),
            self.frac() == TOTAL,
            self.wf(),
    {
        use_type_invariant(self);
    }

    #[verifier::external_body]
    pub proof fn update(tracked &mut self, value: T)
        requires
            old(self).is_full(),
        ensures
            final(self).is_full(),
            final(self)@ == value,
            final(self).id() == old(self).id(),
            final(self).wf(),
    {
        unimplemented!()
    }
}

pub type TokenResource<const TOTAL: u64> = CountGhostResource<(), TOTAL>;

pub type Token<const TOTAL: u64> = CountGhost<(), TOTAL>;

pub tracked struct CountResource<T, const TOTAL: u64> {
    tracked r: Option<Count<T, TOTAL>>,
    ghost id: Loc,
}

impl<T, const TOTAL: u64> CountResource<T, TOTAL> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& match self.r {
            Some(frac) => self.id == frac.id(),
            None => true,
        }
    }

    pub closed spec fn storage(self) -> Count<T, TOTAL> {
        self.r->0
    }

    pub open spec fn wf(self) -> bool {
        &&& TOTAL > 0
        &&& 0 <= self.frac() <= TOTAL
        &&& self.type_inv()
    }

    pub open spec fn is_empty(self) -> bool {
        self.frac() == 0
    }

    pub open spec fn not_empty(self) -> bool {
        !self.is_empty()
    }

    pub open spec fn is_full(self) -> bool {
        self.frac() == TOTAL
    }

    pub closed spec fn resource(self) -> T {
        self.storage().resource()
    }

    #[verifier::inline]
    pub open spec fn view(self) -> T {
        self.resource()
    }

    pub closed spec fn frac(self) -> int {
        if self.r is None {
            0int
        } else {
            self.storage().frac()
        }
    }

    pub closed spec fn id(self) -> Loc {
        self.id
    }

    pub proof fn arbitrary() -> (tracked res: Self)
        requires
            TOTAL > 0,
    {
        Self { r: None, id: arbitrary() }
    }

    #[verifier::external_body]
    pub proof fn alloc(tracked value: T) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.not_empty(),
            res.is_full(),
            res@ == value,
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn alloc_from_empty(
        tracked empty: EmptyCount<T, TOTAL>,
        tracked value: T,
    ) -> (tracked res: Self)
        requires
            TOTAL > 0,
        ensures
            res.is_full(),
            res.id() == empty.id(),
            res.view() == value,
            res.wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split_one(tracked &mut self) -> (tracked res: Count<T, TOTAL>)
        requires
            old(self).not_empty(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() + 1 == old(self).frac(),
            old(self).frac() > 1 ==> final(self)@ == old(self)@,
            res.frac() == 1,
            res.id() == final(self).id(),
            res.resource() == old(self)@,
            old(self).frac() == 1 ==> final(self).is_empty(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn split(tracked &mut self, n: int) -> (tracked res: Count<T, TOTAL>)
        requires
            1 <= n <= old(self).frac(),
        ensures
            final(self).id() == old(self).id(),
            final(self).frac() + n == old(self).frac(),
            old(self).frac() > n ==> final(self)@ == old(self)@,
            res.frac() == n,
            res.id() == final(self).id(),
            res.resource() == old(self)@,
            old(self).frac() == n ==> final(self).is_empty(),
            final(self).wf(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn combine(tracked &mut self, tracked other: Count<T, TOTAL>)
        requires
            old(self).id() == other.id(),
        ensures
            old(self).frac() + other.frac() > TOTAL ==> false,
            old(self).frac() + other.frac() <= TOTAL ==> {
                &&& final(self).id() == old(self).id()
                &&& final(self).resource() == other.resource()
                &&& final(self).frac() == old(self).frac() + other.frac()
                &&& final(self).wf()
                &&& old(self).frac() > 0 ==> final(self)@ == old(self)@
            },
    {
        unimplemented!()
    }

    pub proof fn validate(tracked &self)
        ensures
            self.wf(),
    {
        use_type_invariant(self);
    }

    pub proof fn validate_full(tracked &self)
        requires
            self.is_full(),
        ensures
            self.not_empty(),
            self.frac() == TOTAL,
            self.wf(),
    {
        use_type_invariant(self);
    }

    #[verifier::external_body]
    pub proof fn validate_with_frac(tracked &self, tracked frac: &Count<T, TOTAL>)
        requires
            self.id() == frac.id(),
            self.frac() > 0,
        ensures
            self.resource() == frac.resource(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn take_resource(tracked self) -> (tracked (res, empty): (T, EmptyCount<T, TOTAL>))
        requires
            self.is_full(),
        ensures
            res == self@,
            empty.id() == self.id(),
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn update(tracked &mut self, tracked value: T) -> (tracked res: T)
        requires
            old(self).is_full(),
        ensures
            final(self).is_full(),
            res == old(self)@,
            final(self).id() == old(self).id(),
            final(self).wf(),
    {
        unimplemented!()
    }
}

}

verus! {

type NoPerm<T> = EmptyCount<PointsTo<T>>;

type HalfPerm<T> = Count<PointsTo<T>>;

type ReadPerm<T> = (HalfPerm<T>, OneLeftKnowledge<HalfPerm<T>, NoPerm<T>, 3>);

tracked struct RwPerms<T> {
    core_token: SumResource<HalfPerm<T>, NoPerm<T>, 3>,
    read_retract_token: TokenResource<V_MAX_READ_RETRACT_FRACS>,
    upread_retract_token: Option<UniqueToken>,
    upreader_guard_token: Option<OneLeftOwner<HalfPerm<T>, NoPerm<T>, 3>>,
    read_guard_token: Sum<
        CountResource<ReadPerm<T>, MAX_READER_U64>,
        EmptyCount<ReadPerm<T>, MAX_READER_U64>,
    >,
}

ghost struct RwId {
    core_token_id: Loc,
    frac_id: Loc,
    read_retract_token_id: Loc,
    upread_retract_token_id: Loc,
    read_guard_token_id: Loc,
}

pub closed spec fn no_max_reader_overflow(v: usize) -> bool {
    v & MAX_READER_MASK < MAX_READER_MASK
}

spec const READER_SPEC: usize = 1usize;
#[verifier::when_used_as_spec(READER_SPEC)]
#[verifier::external_body]
exec const READER: usize
    ensures READER == READER_SPEC,
{ 1usize }

spec const WRITER_SPEC: usize = 1usize << (usize::BITS - 1);
#[verifier::when_used_as_spec(WRITER_SPEC)]
#[verifier::external_body]
exec const WRITER: usize
    ensures WRITER == WRITER_SPEC,
{ 1 << (usize::BITS - 1) }

spec const UPGRADEABLE_READER_SPEC: usize = 1usize << (usize::BITS - 2);
#[verifier::when_used_as_spec(UPGRADEABLE_READER_SPEC)]
#[verifier::external_body]
exec const UPGRADEABLE_READER: usize
    ensures UPGRADEABLE_READER == UPGRADEABLE_READER_SPEC,
{ 1 << (usize::BITS - 2) }

spec const BEING_UPGRADED_SPEC: usize = 1usize << (usize::BITS - 3);
#[verifier::when_used_as_spec(BEING_UPGRADED_SPEC)]
#[verifier::external_body]
exec const BEING_UPGRADED: usize
    ensures BEING_UPGRADED == BEING_UPGRADED_SPEC,
{ 1 << (usize::BITS - 3) }

spec const MAX_READER_SPEC: usize = 1usize << (usize::BITS - 4);
#[verifier::when_used_as_spec(MAX_READER_SPEC)]
#[verifier::external_body]
exec const MAX_READER: usize
    ensures MAX_READER == MAX_READER_SPEC,
{ 1 << (usize::BITS - 4) }

spec const READER_MASK_SPEC: usize = (MAX_READER_SPEC - 1) as usize;
#[verifier::when_used_as_spec(READER_MASK_SPEC)]
#[verifier::external_body]
exec const READER_MASK: usize
    ensures READER_MASK == READER_MASK_SPEC,
{ MAX_READER - 1 }

spec const MAX_READER_MASK_SPEC: usize = (2 * (MAX_READER_SPEC as int) - 1) as usize;
#[verifier::when_used_as_spec(MAX_READER_MASK_SPEC)]
#[verifier::external_body]
exec const MAX_READER_MASK: usize
    ensures MAX_READER_MASK == MAX_READER_MASK_SPEC,
{ 2 * MAX_READER - 1 }

spec const MAX_READER_U64_SPEC: u64 = MAX_READER_SPEC as u64;
#[verifier::when_used_as_spec(MAX_READER_U64_SPEC)]
#[verifier::external_body]
exec const MAX_READER_U64: u64
    ensures MAX_READER_U64 == MAX_READER_U64_SPEC,
{ MAX_READER as u64 }

spec const V_MAX_READ_RETRACT_FRACS_SPEC: u64 = (2 * (MAX_READER_SPEC as int)) as u64;
#[verifier::when_used_as_spec(V_MAX_READ_RETRACT_FRACS_SPEC)]
#[verifier::external_body]
exec const V_MAX_READ_RETRACT_FRACS: u64
    ensures V_MAX_READ_RETRACT_FRACS == V_MAX_READ_RETRACT_FRACS_SPEC,
{ 2u64 * (MAX_READER as u64) }

struct_with_invariants! {
pub struct RwLock<T                , Guard                        > {
    guard: PhantomData<Guard>,
    lock: AtomicUsize<_, RwPerms<T>,_>,
    val: PCell<T>,
    ghost_id: Ghost<RwId>,
}

closed spec fn wf(self) -> bool {
    invariant on lock with (val, guard, ghost_id) is (v: usize, g: RwPerms<T>) {
        let has_writer_bit: bool = (v & WRITER) != 0;
        let has_upgrade_bit: bool = (v & UPGRADEABLE_READER) != 0;
        let has_max_reader_bit: bool = (v & MAX_READER) != 0;
        let total_reader_bits: int = (v & MAX_READER_MASK) as int;
        let reader_bits: int = if has_max_reader_bit { MAX_READER as int } else { (v & READER_MASK) as int };


        let active_writer: bool = g.core_token.is_right();
        let active_upgrade_guard: bool = !active_writer && g.upreader_guard_token is None;
        let active_read_guards: int = if g.read_guard_token is Left {
            MAX_READER_U64 - g.read_guard_token.left().frac()
        } else {
            0
        };
        let pending_failed_upread_attempt: bool = g.upread_retract_token is None;
        let failed_reader_attempts: int = V_MAX_READ_RETRACT_FRACS - g.read_retract_token.frac();

        &&& if g.core_token.is_left() {
            g.read_guard_token is Left
        } else {
            &&& g.upreader_guard_token is None
            &&& g.read_guard_token is Right
        }
        &&& has_upgrade_bit <==> (active_upgrade_guard || pending_failed_upread_attempt)
        &&& !(active_upgrade_guard && pending_failed_upread_attempt)
        &&& total_reader_bits == active_read_guards + failed_reader_attempts
        &&& active_writer <==> has_writer_bit
        &&& 0 <= active_read_guards <= reader_bits <= total_reader_bits
        &&& !(active_writer && (active_read_guards + if active_upgrade_guard { 1int } else { 0 }) > 0)
        &&& g.core_token.id() == ghost_id@.core_token_id
        &&& g.core_token.wf()
        &&& g.core_token.is_left() ==> {
            &&& !g.core_token.is_resource_owner()
            &&& g.core_token.frac() == 1
        }
        &&& g.core_token.is_right() ==> {
            let empty = g.core_token.resource_right();
            &&& empty.id() == ghost_id@.frac_id
            &&& g.core_token.frac() == 2
            &&& g.core_token.has_resource()
        }
        &&& g.read_retract_token.wf()
        &&& g.read_retract_token.id() == ghost_id@.read_retract_token_id
        &&& g.upread_retract_token is Some ==>
            {
                let token = g.upread_retract_token->0;
                &&& token.wf()
                &&& token.id() == ghost_id@.upread_retract_token_id
            }
        &&& g.upreader_guard_token is Some ==> {
            let token = g.upreader_guard_token->0;
            wf_upgradeable_guard_token(ghost_id@.core_token_id, ghost_id@.frac_id, val.id(), token)
        }
        &&& match g.read_guard_token {
            Sum::Left(token) => {
                &&& token.wf()
                &&& token.id() == ghost_id@.read_guard_token_id
                &&& token.not_empty() ==> {
                    let resource = token.resource();
                    let read_half_cell_perm = resource.0;
                    let mode_knowledge = resource.1;
                    &&& mode_knowledge.id() == ghost_id@.core_token_id
                    &&& read_half_cell_perm.id() == ghost_id@.frac_id
                    &&& read_half_cell_perm.resource().id() == val.id()
                    &&& read_half_cell_perm.frac() == 1
                }
            },
            Sum::Right(empty) => {
                &&& empty.id() == ghost_id@.read_guard_token_id
            },
        }

    }
}

}

impl<T, G> RwLock<T, G> {
    pub closed spec fn cell_id(self) -> cell::CellId {
        self.val.id()
    }

    pub closed spec fn core_token_id(self) -> Loc {
        self.ghost_id@.core_token_id
    }

    pub closed spec fn frac_id(self) -> Loc {
        self.ghost_id@.frac_id
    }

    pub closed spec fn upread_retract_token_id(self) -> Loc {
        self.ghost_id@.upread_retract_token_id
    }

    pub closed spec fn read_guard_token_id(self) -> Loc {
        self.ghost_id@.read_guard_token_id
    }

    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        self.wf()
    }
}

closed spec fn wf_upgradeable_guard_token<T>(
    core_token_id: Loc,
    frac_id: Loc,
    cell_id: CellId,
    token: OneLeftOwner<HalfPerm<T>, NoPerm<T>, 3>,
) -> bool {
    let half_cell_perm = token.resource();
    &&& token.id() == core_token_id
    &&& half_cell_perm.id() == frac_id
    &&& half_cell_perm.resource().id() == cell_id
    &&& token.has_resource()
    &&& half_cell_perm.frac() == 1
    &&& token.wf()
}

impl<T, G> RwLock<T, G> {
    pub const fn new(val: T) -> Self {
        let (val, Tracked(perm)) = PCell::new(val);

        proof {
            lemma_consts_properties();
        }
        let tracked mut frac_perm = Count::<PointsTo<T>>::new(perm);
        let tracked read_half_cell_perm = frac_perm.split(1int);
        let ghost frac_id = frac_perm.id();
        let tracked mut core_token = SumResource::alloc_left(frac_perm);
        let tracked read_retract_token = TokenResource::<V_MAX_READ_RETRACT_FRACS>::alloc(());
        let tracked upread_retract_token = UniqueToken::alloc(());
        let tracked upreader_guard_token = core_token.split_one_left_owner();
        let tracked left_token = core_token.split_one_left_knowledge();
        let tracked read_guard_token = CountResource::<ReadPerm<T>, MAX_READER_U64>::alloc(
            (read_half_cell_perm, left_token),
        );
        let ghost ghost_id = RwId {
            frac_id,
            core_token_id: core_token.id(),
            upread_retract_token_id: upread_retract_token.id(),
            read_retract_token_id: read_retract_token.id(),
            read_guard_token_id: read_guard_token.id(),
        };
        let tracked perms = RwPerms {
            core_token,
            read_retract_token,
            upread_retract_token: Some(upread_retract_token),
            upreader_guard_token: Some(upreader_guard_token),
            read_guard_token: Sum::Left(read_guard_token),
        };

        Self {
            guard: PhantomData,
            lock: AtomicUsize::new(Ghost((val, PhantomData, Ghost(ghost_id))), 0, Tracked(perms)),
            val: val,
            ghost_id: Ghost(ghost_id),
        }
    }
}

#[verus_verify]
impl<T               , G: SpinGuardian> RwLock<T, G> {
    #[verus_spec]
    pub fn try_read(&self) -> Option<RwLockReadGuard<'_, T, G>> {
        proof_decl!{
            let tracked mut read_token: Option<Count<ReadPerm<T>,MAX_READER_U64>> = None;
            let tracked mut retract_read_token: Option<Token<V_MAX_READ_RETRACT_FRACS>> = None;
        }
        proof!{
            use_type_invariant(self);
            lemma_consts_properties();
        }
        let guard = G::read_guard();

        let lock =
            atomic_with_ghost!(
            self.lock => fetch_add(READER);
            update prev -> next;
            ghost g => {
                let prev_usize = prev as usize;
                assume (no_max_reader_overflow(prev_usize));
                lemma_consts_properties_value(prev_usize);
                lemma_consts_properties_prev_next(prev_usize, next as usize);
                if prev_usize & (WRITER | MAX_READER | BEING_UPGRADED) == 0 {
                    assert(g.read_guard_token is Left);
                    assert(g.read_guard_token.left().not_empty());
                    let tracked mut token = g.read_guard_token.tracked_swap_left(
                        CountResource::arbitrary(),
                    );
                    read_token = Some(token.split_one());
                    g.read_guard_token.tracked_swap_left(token);
                } else {
                    assert(g.read_retract_token.not_empty());
                    retract_read_token = Some(g.read_retract_token.split_one());
                }
            }
        );
        if lock & (WRITER | MAX_READER | BEING_UPGRADED) == 0 {
            Some(
                RwLockReadGuard {
                    inner: self,
                    guard,
                    tracked_token: Tracked(read_token.tracked_unwrap()),
                },
            )
        } else {
            atomic_with_ghost!(
                self.lock => fetch_sub(READER);
                update prev -> next;
                ghost g => {
                    lemma_consts_properties_value(prev as usize);
                    lemma_consts_properties_prev_next(prev as usize, next as usize);
                    assert(retract_read_token is Some);
                    let tracked token = retract_read_token.tracked_unwrap();
                    g.read_retract_token.combine(token);
                }
            );
            None
        }
    }

}




#[verifier::external]
unsafe impl<T: Send, G> Send for RwLock<T, G> {

}

#[verifier::external]
unsafe impl<T: Send + Sync, G> Sync for RwLock<T, G> {

}

impl<T               , G: SpinGuardian> !Send for RwLockWriteGuard<'_, T, G> {

}

#[verifier::external]
unsafe impl<T: Sync, G: SpinGuardian> Sync for RwLockWriteGuard<'_, T, G> {

}

impl<T               , G: SpinGuardian> !Send for RwLockReadGuard<'_, T, G> {

}

#[verifier::external]
unsafe impl<T: Sync, G: SpinGuardian> Sync for RwLockReadGuard<'_, T, G> {

}

impl<T               , G: SpinGuardian> !Send for RwLockUpgradeableGuard<'_, T, G> {

}

#[verifier::external]
unsafe impl<T: Sync, G: SpinGuardian> Sync for RwLockUpgradeableGuard<'_, T, G> {

}

#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(G)]
#[clippy::has_significant_drop]
#[must_use]
#[verus_verify]
pub struct RwLockReadGuard<'a, T               , G: SpinGuardian> {
    guard: G::ReadGuard,
    inner: &'a RwLock<T, G>,
    tracked_token: Tracked<Count<ReadPerm<T>, MAX_READER_U64>>,
}


impl<'a, T, G: SpinGuardian> RwLockReadGuard<'a, T, G> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        let resource = self.tracked_token@.resource();
        let read_half_cell_perm = resource.0;
        let mode_knowledge = resource.1;
        &&& self.inner.core_token_id() == mode_knowledge.id()
        &&& self.inner.frac_id() == read_half_cell_perm.id()
        &&& self.inner.cell_id() == read_half_cell_perm.resource().id()
        &&& self.tracked_token@.id() == self.inner.read_guard_token_id()
        &&& read_half_cell_perm.frac() == 1
        &&& self.tracked_token@.frac() == 1
    }

    pub closed spec fn value(self) -> T {
        *self.tracked_token@.resource().0.resource().value()
    }

    pub open spec fn view(self) -> T {
        self.value()
    }

    #[verifier::external_body]
    pub proof fn tracked_borrow(tracked &self) -> (tracked r: &'a T)
        returns
            self.view(),
    {
        unimplemented!()
    }
}

impl<T               , G: SpinGuardian> Deref for RwLockReadGuard<'_, T, G> {
    type Target = T;

    #[verus_spec(returns self.view())]
    fn deref(&self) -> &T {
        proof!{
            use_type_invariant(self);
        }
        self.inner.val.borrow(Tracked(self.tracked_token.borrow().borrow().0.borrow()))
    }
}


#[verus_verify]
impl<T               , G: SpinGuardian> RwLockReadGuard<'_, T, G> {
}


#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(G)]
pub struct RwLockWriteGuard<'a, T               , G: SpinGuardian> {
    guard: G::Guard,
    inner: &'a RwLock<T, G>,
    tracked_perm: Tracked<PointsTo<T>>,
    tracked_token: Tracked<OneRightKnowledge<HalfPerm<T>, NoPerm<T>, 3>>,
}

impl<'a, T, G: SpinGuardian> RwLockWriteGuard<'a, T, G> {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        &&& self.inner.cell_id() == self.tracked_perm@.id()
        &&& self.inner.core_token_id() == self.tracked_token@.id()
    }

    pub closed spec fn value(self) -> T {
        *self.tracked_perm@.value()
    }

    pub open spec fn view(self) -> T {
        self.value()
    }

    #[verifier::external_body]
    pub proof fn tracked_borrow(tracked &self) -> (tracked r: &'a T)
        returns
            self.view(),
    {
        unimplemented!()
    }
}


impl<T               , G: SpinGuardian> Deref for RwLockWriteGuard<'_, T, G> {
    type Target = T;

    #[verus_spec(returns self.view())]
    fn deref(&self) -> &T {
        proof!{
            use_type_invariant(self);
        }
        self.inner.val.borrow(Tracked(self.tracked_perm.borrow()))
    }
}

#[verus_verify]
impl<T               , G: SpinGuardian> DerefMut for RwLockWriteGuard<'_, T, G> {
    #[verus_spec(ret =>
        ensures
            final(self).view() == *final(ret),
            old(self).view() == *ret,
    )]
    fn deref_mut(&mut self) -> &mut Self::Target {
        proof!{
            use_type_invariant(&*self);
        }
        self.inner.val.borrow_mut(Tracked(&mut *self.tracked_perm))
    }
}


impl<T               , G: SpinGuardian> RwLockWriteGuard<'_, T, G> {
}


#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(G)]
pub struct RwLockUpgradeableGuard<'a, T               , G: SpinGuardian> {
    guard: G::Guard,
    inner: &'a RwLock<T, G>,
    tracked_token: Tracked<OneLeftOwner<HalfPerm<T>, NoPerm<T>, 3>>,
}


impl<'a, T, G: SpinGuardian> RwLockUpgradeableGuard<'a, T, G> {
    #[verifier::type_invariant]
    pub closed spec fn type_inv(self) -> bool {
        wf_upgradeable_guard_token(
            self.inner.core_token_id(),
            self.inner.frac_id(),
            self.inner.cell_id(),
            self.tracked_token@,
        )
    }

    pub closed spec fn value(self) -> T {
        *self.tracked_token@.resource().resource().value()
    }

    pub open spec fn view(self) -> T {
        self.value()
    }
}

impl<'a, T               , G: SpinGuardian> RwLockUpgradeableGuard<'a, T, G> {
}

impl<T               , G: SpinGuardian> Deref for RwLockUpgradeableGuard<'_, T, G> {
    type Target = T;

    #[verus_spec(returns self.view())]
    fn deref(&self) -> &T {
        proof!{
            use_type_invariant(self);
        }
        self.inner.val.borrow(Tracked(self.tracked_token.borrow().tracked_borrow().borrow()))
    }
}


impl<T               , G: SpinGuardian> RwLockUpgradeableGuard<'_, T, G> {
}


#[verifier::external_body]
proof fn lemma_consts_properties()
    ensures
        0 & WRITER == 0,
        0 & UPGRADEABLE_READER == 0,
        0 & BEING_UPGRADED == 0,
        0 & READER_MASK == 0,
        0 & MAX_READER_MASK == 0,
        0 & MAX_READER == 0,
        0 & READER == 0,
        WRITER == 0x8000_0000_0000_0000,
        UPGRADEABLE_READER == 0x4000_0000_0000_0000,
        BEING_UPGRADED == 0x2000_0000_0000_0000,
        READER_MASK == 0x0FFF_FFFF_FFFF_FFFF,
        MAX_READER_MASK == 0x1FFF_FFFF_FFFF_FFFF,
        MAX_READER == 0x1000_0000_0000_0000,
        WRITER & WRITER == WRITER,
        WRITER & !WRITER == 0,
        WRITER & BEING_UPGRADED == 0,
        WRITER & READER_MASK == 0,
        WRITER & MAX_READER_MASK == 0,
        WRITER & MAX_READER == 0,
        WRITER & UPGRADEABLE_READER == 0,
        BEING_UPGRADED & WRITER == 0,
        BEING_UPGRADED & UPGRADEABLE_READER == 0,
        UPGRADEABLE_READER & BEING_UPGRADED == 0,
        UPGRADEABLE_READER & READER_MASK == 0,
        UPGRADEABLE_READER & MAX_READER_MASK == 0,
        UPGRADEABLE_READER & MAX_READER == 0,
        BEING_UPGRADED & READER_MASK == 0,
        BEING_UPGRADED & MAX_READER_MASK == 0,
        BEING_UPGRADED & MAX_READER == 0,
        (UPGRADEABLE_READER | BEING_UPGRADED) & WRITER == 0,
        (UPGRADEABLE_READER | BEING_UPGRADED) & UPGRADEABLE_READER == UPGRADEABLE_READER,
        (UPGRADEABLE_READER | BEING_UPGRADED) & BEING_UPGRADED == BEING_UPGRADED,
        (UPGRADEABLE_READER | BEING_UPGRADED) & READER_MASK == 0,
        (UPGRADEABLE_READER | BEING_UPGRADED) & MAX_READER_MASK == 0,
        (UPGRADEABLE_READER | BEING_UPGRADED) & MAX_READER == 0,
        (WRITER | UPGRADEABLE_READER) & WRITER == WRITER,
        (WRITER | UPGRADEABLE_READER) & UPGRADEABLE_READER == UPGRADEABLE_READER,
        (WRITER | UPGRADEABLE_READER) & BEING_UPGRADED == 0,
        (WRITER | UPGRADEABLE_READER) & READER_MASK == 0,
        (WRITER | UPGRADEABLE_READER) & MAX_READER_MASK == 0,
        (WRITER | UPGRADEABLE_READER) & MAX_READER == 0,
{
}

#[verifier::external_body]
proof fn lemma_consts_properties_value(prev: usize)
    ensures
        no_max_reader_overflow(prev) ==> prev + READER <= usize::MAX,
        prev & (WRITER | MAX_READER | BEING_UPGRADED) == 0 ==> {
            &&& prev & WRITER == 0
            &&& prev & BEING_UPGRADED == 0
            &&& prev & MAX_READER == 0
        },
        prev & (WRITER | UPGRADEABLE_READER) == 0 ==> {
            &&& prev & WRITER == 0
            &&& prev & UPGRADEABLE_READER == 0
        },
        prev & MAX_READER == 0 ==> prev & READER_MASK == prev & MAX_READER_MASK,
        prev & MAX_READER != 0 ==> prev & MAX_READER_MASK >= MAX_READER,
        prev & (WRITER | UPGRADEABLE_READER) == WRITER ==> {
            &&& prev & UPGRADEABLE_READER == 0
            &&& prev & WRITER == WRITER
        },
        prev & UPGRADEABLE_READER != 0 ==> prev >= UPGRADEABLE_READER,
        prev & UPGRADEABLE_READER == 0 ==> {
            ||| prev & (WRITER | UPGRADEABLE_READER) == 0
            ||| prev & (WRITER | UPGRADEABLE_READER) == WRITER
        },
{
}

#[verifier::external_body]
proof fn lemma_consts_properties_prev_next(prev: usize, next: usize)
    ensures
        prev & READER_MASK < MAX_READER,
        next == prev | UPGRADEABLE_READER ==> {
            &&& next & UPGRADEABLE_READER != 0
            &&& next & WRITER == prev & WRITER
            &&& next & READER_MASK == prev & READER_MASK
            &&& next & MAX_READER_MASK == prev & MAX_READER_MASK
            &&& next & MAX_READER == prev & MAX_READER
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
        next == prev | BEING_UPGRADED ==> {
            &&& next & BEING_UPGRADED != 0
            &&& next & WRITER == prev & WRITER
            &&& next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER
            &&& next & READER_MASK == prev & READER_MASK
            &&& next & MAX_READER_MASK == prev & MAX_READER_MASK
            &&& next & MAX_READER == prev & MAX_READER
        },
        next == prev - UPGRADEABLE_READER && prev & UPGRADEABLE_READER != 0 ==> {
            &&& next & UPGRADEABLE_READER == 0
            &&& next & WRITER == prev & WRITER
            &&& next & READER_MASK == prev & READER_MASK
            &&& next & MAX_READER_MASK == prev & MAX_READER_MASK
            &&& next & MAX_READER == prev & MAX_READER
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
        next == prev - READER && prev & READER_MASK != 0 ==> {
            &&& next & READER_MASK == (prev & READER_MASK) - READER
            &&& next & MAX_READER_MASK == (prev & MAX_READER_MASK) - READER
            &&& next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER
            &&& next & WRITER == prev & WRITER
            &&& next & MAX_READER == prev & MAX_READER
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
        next == prev - READER && prev & MAX_READER_MASK != 0 ==> {
            &&& next & MAX_READER_MASK == (prev & MAX_READER_MASK) - READER
            &&& next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER
            &&& next & WRITER == prev & WRITER
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
        next == prev + READER && no_max_reader_overflow(prev) ==> {
            &&& next & READER_MASK == if (prev & READER_MASK) + READER == MAX_READER {
                0
            } else {
                (prev & READER_MASK) + READER
            }
            &&& next & MAX_READER_MASK == (prev & MAX_READER_MASK) + READER
            &&& next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER
            &&& next & WRITER == prev & WRITER
            &&& next & MAX_READER == if (prev & READER_MASK) + READER == MAX_READER {
                MAX_READER
            } else {
                prev & MAX_READER
            }
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
        next == prev & !WRITER ==> {
            &&& next & WRITER == 0
            &&& next & UPGRADEABLE_READER == prev & UPGRADEABLE_READER
            &&& next & READER_MASK == prev & READER_MASK
            &&& next & MAX_READER_MASK == prev & MAX_READER_MASK
            &&& next & MAX_READER == prev & MAX_READER
            &&& next & BEING_UPGRADED == prev & BEING_UPGRADED
        },
{
}

}
