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

    pub open spec fn or(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) || other.satisfied_by(ex))
    }

    pub open spec fn implies(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) ==> other.satisfied_by(ex))
    }

}


pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn eventually<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| exists |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn later<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| temp_pred.satisfied_by(ex.suffix(1)))
}

pub open spec fn not<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| !temp_pred.satisfied_by(ex))
}


// File: rules.rs
	#[verifier::external_body]
proof fn later_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires later(p).satisfied_by(ex),
    ensures p.satisfied_by(ex.suffix(1)),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn always_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires always(p).satisfied_by(ex),
    ensures forall |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn not_eventually_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires not(eventually(p)).satisfied_by(ex),
    ensures forall |i| !p.satisfied_by(#[trigger] ex.suffix(i))
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn implies_apply<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        p.implies(q).satisfied_by(ex),
        p.satisfied_by(ex),
    ensures q.satisfied_by(ex),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn always_propagate_forwards<T>(ex: Execution<T>, p: TempPred<T>, i: nat)
    requires always(p).satisfied_by(ex),
    ensures always(p).satisfied_by(ex.suffix(i)),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn always_p_or_eventually_q_rec<T>(ex: Execution<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>, i: nat)
    requires
        forall |idx| p.satisfied_by(ex.suffix(idx)) && next.satisfied_by(ex.suffix(idx)) ==> p.satisfied_by(ex.suffix(idx + 1)) || q.satisfied_by(ex.suffix(idx + 1)),
        forall |idx| next.satisfied_by(#[trigger] ex.suffix(idx)),
        forall |idx| !q.satisfied_by(#[trigger] ex.suffix(idx)),
        p.satisfied_by(ex),
    ensures p.satisfied_by(ex.suffix(i)),
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn execution_equality<T>(ex1: Execution<T>, ex2: Execution<T>)
    requires forall |i: nat| #[trigger] (ex1.nat_to_state)(i) == (ex2.nat_to_state)(i),
    ensures ex1 == ex2,
	{
		unimplemented!()
	}

/// Helper: ex.suffix(a).suffix(b) == ex.suffix(a + b)
proof fn suffix_add<T>(ex: Execution<T>, a: nat, b: nat)
    ensures ex.suffix(a).suffix(b) == ex.suffix(a + b)
{
    execution_equality(ex.suffix(a).suffix(b), ex.suffix(a + b));
}

proof fn always_p_or_eventually_q<T>(ex: Execution<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        always(p.and(next).implies(later(p).or(later(q)))).satisfied_by(ex),
        always(next).satisfied_by(ex),
    ensures always(p.implies(always(p).or(eventually(q)))).satisfied_by(ex),
{
    // Unfold both always-predicates to obtain universally quantified statements
    always_unfold(ex, p.and(next).implies(later(p).or(later(q))));
    always_unfold(ex, next);

    // For every position i, show: p at ex.suffix(i) implies (always(p) or eventually(q)) at ex.suffix(i)
    assert forall |i: nat| (p.implies(always(p).or(eventually(q)))).satisfied_by(ex.suffix(i)) by {
        if p.satisfied_by(ex.suffix(i)) {
            if eventually(q).satisfied_by(ex.suffix(i)) {
                // eventually(q) already holds, so always(p).or(eventually(q)) holds trivially
            } else {
                // not eventually(q) — we will show always(p) holds at ex.suffix(i)
                // by applying always_p_or_eventually_q_rec on the sub-execution ex.suffix(i).

                // Condition 1: the step-wise implication holds for ex.suffix(i)
                assert forall |idx: nat|
                    p.satisfied_by(ex.suffix(i).suffix(idx)) && next.satisfied_by(ex.suffix(i).suffix(idx))
                    ==> p.satisfied_by(ex.suffix(i).suffix(idx + 1)) || q.satisfied_by(ex.suffix(i).suffix(idx + 1))
                by {
                    if p.satisfied_by(ex.suffix(i).suffix(idx)) && next.satisfied_by(ex.suffix(i).suffix(idx)) {
                        // Relate ex.suffix(i).suffix(idx) to ex.suffix(i + idx)
                        suffix_add(ex, i, idx);
                        // Now we can apply the precondition at position (i + idx)
                        // (p.and(next).implies(later(p).or(later(q)))).satisfied_by(ex.suffix(i + idx))
                        // => later(p).or(later(q)).satisfied_by(ex.suffix(i + idx))
                        // => p.satisfied_by(ex.suffix(i+idx).suffix(1)) || q.satisfied_by(ex.suffix(i+idx).suffix(1))
                        // Relate ex.suffix(i+idx).suffix(1) to ex.suffix(i+idx+1)
                        suffix_add(ex, i + idx, 1nat);
                        // Relate ex.suffix(i).suffix(idx+1) to ex.suffix(i+idx+1)
                        suffix_add(ex, i, idx + 1);
                    }
                };

                // Condition 2: next holds everywhere on ex.suffix(i)
                assert forall |idx: nat| next.satisfied_by(#[trigger] ex.suffix(i).suffix(idx)) by {
                    suffix_add(ex, i, idx);
                    // next.satisfied_by(ex.suffix(i + idx)) from always_unfold
                };

                // Condition 3: q never holds on ex.suffix(i)
                // This follows directly from !eventually(q).satisfied_by(ex.suffix(i))
                // = !(exists j, q.satisfied_by(ex.suffix(i).suffix(j)))
                // = forall j, !q.satisfied_by(ex.suffix(i).suffix(j))
                assert forall |idx: nat| !q.satisfied_by(#[trigger] ex.suffix(i).suffix(idx)) by {
                    // By contradiction: if q.satisfied_by(ex.suffix(i).suffix(idx)) then
                    // eventually(q).satisfied_by(ex.suffix(i)), contradicting our assumption.
                };

                // Apply the recursive lemma to get p at every suffix of ex.suffix(i)
                assert forall |k: nat| p.satisfied_by(#[trigger] ex.suffix(i).suffix(k)) by {
                    always_p_or_eventually_q_rec(ex.suffix(i), next, p, q, k);
                };
                // This establishes always(p).satisfied_by(ex.suffix(i))
            }
        }
    };
}

}
