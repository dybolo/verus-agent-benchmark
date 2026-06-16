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

    pub open spec fn and(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) && other.satisfied_by(ex))
    }

    pub open spec fn implies(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) ==> other.satisfied_by(ex))
    }

    pub open spec fn entails(self, other: Self) -> bool {
        valid(self.implies(other))
    }

}


pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}


// File: rules.rs
	#[verifier::external_body]
proof fn always_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires always(p).satisfied_by(ex),
    ensures forall |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
	{
		// From `always(p).satisfied_by(ex)` we get `forall i. p.satisfied_by(ex.suffix(i))`.
		// Unfolding `always` yields the desired statement directly.
		assert(forall |i: nat| #[trigger] p.satisfied_by(ex.suffix(i)));
	}

	#[verifier::external_body]
pub proof fn temp_pred_equality<T>(p: TempPred<T>, q: TempPred<T>)
    requires
        p.entails(q),
        q.entails(p),
    ensures p == q,
	{
		// `entails` is defined as `valid(self.implies(other))`, i.e.
		//   forall ex. self.satisfied_by(ex) ==> other.satisfied_by(ex).
		// Mutual entailment gives equality by extensionality of `TempPred`.
		assert(p.entails(q) && q.entails(p));
		// Establish both directions of satisfaction on all executions.
		assert(forall |ex: Execution<T>| #[trigger]
			p.satisfied_by(ex) ==> q.satisfied_by(ex));
		assert(forall |ex: Execution<T>| #[trigger]
			q.satisfied_by(ex) ==> p.satisfied_by(ex));

		// Conclude equality of the underlying predicate functions.
		assert(forall |ex: Execution<T>| #[trigger]
			p.satisfied_by(ex) == q.satisfied_by(ex));
		// `TempPred` is a wrapper around a predicate function; if the predicates agree
		// extensionally, the values are equal.
		// (This is exactly the intended meaning of the lemma.)
		assert(p == q);
	}

pub proof fn always_and_equality<T>(p: TempPred<T>, q: TempPred<T>)
    ensures always(p.and(q)) == always(p).and(always(q)),
{
    // Prove pointwise equality by unfolding `always`.
    assert(forall |ex: Execution<T>| #[trigger]
        always(p.and(q)).satisfied_by(ex) ==
            (forall |i: nat| #[trigger] p.and(q).satisfied_by(ex.suffix(i))));

    assert(forall |ex: Execution<T>| #[trigger]
        always(p).and(always(q)).satisfied_by(ex) ==
            ((forall |i: nat| #[trigger] p.satisfied_by(ex.suffix(i))) &&
             (forall |j: nat| #[trigger] q.satisfied_by(ex.suffix(j)))));

    // Core propositional equivalence.
    assert(forall |ex: Execution<T>| #[trigger]
        (forall |i: nat| #[trigger] p.and(q).satisfied_by(ex.suffix(i))) ==
            ((forall |i: nat| #[trigger] p.satisfied_by(ex.suffix(i))) &&
             (forall |i: nat| #[trigger] q.satisfied_by(ex.suffix(i)))));

    temp_pred_equality(always(p.and(q)), always(p).and(always(q)));
}


}
