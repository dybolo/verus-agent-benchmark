use vstd::prelude::*;

fn main() {}

verus!{

// File: defs.rs
pub struct Execution<T> {
    pub nat_to_state: spec_fn(nat) -> T,
}

impl<T> Execution<T> {

    pub open spec fn suffix(self, pos: nat) -> Self {
        Execution {
            nat_to_state: |i: nat| (self.nat_to_state)(i + pos),
        }
    }

}


#[verifier(reject_recursive_types(T))]
pub struct TempPred<T> {
    pub pred: spec_fn(Execution<T>) -> bool,
}

impl<T> TempPred<T> {

    pub open spec fn new(pred: spec_fn(Execution<T>) -> bool) -> Self {
        TempPred {
            pred: pred,
        }
    }

    pub open spec fn satisfied_by(self, execution: Execution<T>) -> bool {
        (self.pred)(execution)
    }

}


pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}


// File: rules.rs

proof fn always_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires always(p).satisfied_by(ex),
    ensures forall |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
{
    // From `always(p).satisfied_by(ex)` we can extract `p` holding at every suffix.
    assert(always(p).satisfied_by(ex));
}

proof fn always_propagate_forwards<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires always(p).satisfied_by(ex),
    ensures always(p).satisfied_by(ex.suffix(i)),
{
    // `always(p).satisfied_by(ex.suffix(i))` is: forall j, p.satisfied_by((ex.suffix(i)).suffix(j))
    // which equals: forall j, p.satisfied_by(ex.suffix(i + j)).
    assert(
        forall |j: nat| #[trigger] p.satisfied_by(ex.suffix(i + j))
    ) by {
        assert(forall |k: nat| #[trigger] p.satisfied_by(ex.suffix(k)));
    };
}

proof fn always_double<T>(ex: Execution<T>, p: TempPred<T>)
    requires always(p).satisfied_by(ex),
    ensures always(always(p)).satisfied_by(ex),
{
    // Use the helper lemma that `always(p)` holds at every suffix.
    // Then the result is exactly the definition of `always(always(p))`.
    assert(forall |i: nat| #[trigger] always(p).satisfied_by(ex.suffix(i)));
}


}
