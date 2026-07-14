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

proof fn suffix_suffix_eq<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix((i + j) as nat)
{
    execution_equality::<T>(
        ex.suffix(i).suffix(j),
        ex.suffix((i + j) as nat),
    );
}

proof fn always_p_or_eventually_q<T>(ex: Execution<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        always(p.and(next).implies(later(p).or(later(q)))).satisfied_by(ex),
        always(next).satisfied_by(ex),
    ensures always(p.implies(always(p).or(eventually(q)))).satisfied_by(ex),
{
    always_unfold(ex, next);
    always_unfold(ex, p.and(next).implies(later(p).or(later(q))));

    assert forall |i: nat| p.implies(always(p).or(eventually(q))).satisfied_by(#[trigger] ex.suffix(i)) by {
        if p.satisfied_by(ex.suffix(i)) {
            if !eventually(q).satisfied_by(ex.suffix(i)) {
                // q never holds from ex.suffix(i)
                assert(not(eventually(q)).satisfied_by(ex.suffix(i))) by {
                    assert(!(exists |k: nat| #[trigger] q.satisfied_by(ex.suffix(i).suffix(k))));
                };
                not_eventually_unfold(ex.suffix(i), q);
                // forall j, !q.satisfied_by(ex.suffix(i).suffix(j))

                // Build precondition 1 for always_p_or_eventually_q_rec:
                // forall idx, p(ex.suffix(i).suffix(idx)) && next(ex.suffix(i).suffix(idx)) ==>
                //              p(ex.suffix(i).suffix(idx+1)) || q(ex.suffix(i).suffix(idx+1))
                assert forall |idx: nat| p.satisfied_by(ex.suffix(i).suffix(idx)) && next.satisfied_by(ex.suffix(i).suffix(idx))
                    ==> p.satisfied_by(ex.suffix(i).suffix(idx + 1)) || q.satisfied_by(ex.suffix(i).suffix(idx + 1)) by {
                    // From the implies condition at ex.suffix(i + idx):
                    // (p.and(next).implies(later(p).or(later(q)))).satisfied_by(ex.suffix(i + idx))
                    // means: p(ex.suffix(i+idx)) && next(ex.suffix(i+idx)) ==> p(ex.suffix(i+idx).suffix(1)) || q(...)
                    // And ex.suffix(i+idx).suffix(1) == ex.suffix(i+idx+1)
                    // ex.suffix(i).suffix(idx) == ex.suffix(i+idx)
                    // ex.suffix(i).suffix(idx+1) == ex.suffix(i+idx+1)
                    if p.satisfied_by(ex.suffix(i).suffix(idx)) && next.satisfied_by(ex.suffix(i).suffix(idx)) {
                        suffix_suffix_eq(ex, i, idx);
                        // ex.suffix(i).suffix(idx) == ex.suffix(i + idx)
                        let combined = (i + idx) as nat;
                        // The implies condition at combined:
                        // p(ex.suffix(combined)) && next(ex.suffix(combined)) ==> p(ex.suffix(combined).suffix(1)) || q(ex.suffix(combined).suffix(1))
                        let comb_implies = p.and(next).implies(later(p).or(later(q)));
                        assert(comb_implies.satisfied_by(ex.suffix(combined)));
                        // So p(ex.suffix(combined)) && next(ex.suffix(combined)) => later(p).or(later(q)) at ex.suffix(combined)
                        // later(p).or(later(q)) at ex.suffix(combined) = p(ex.suffix(combined).suffix(1)) || q(ex.suffix(combined).suffix(1))
                        // ex.suffix(combined).suffix(1) == ex.suffix(combined + 1) == ex.suffix(i+idx+1)
                        suffix_suffix_eq(ex, combined, 1);
                        // ex.suffix(combined).suffix(1) == ex.suffix(combined + 1)
                        suffix_suffix_eq(ex, i, (idx + 1) as nat);
                        // ex.suffix(i).suffix(idx+1) == ex.suffix(i + idx + 1) == ex.suffix(combined + 1)
                    }
                };

                // Build precondition 2: forall idx, next(ex.suffix(i).suffix(idx))
                assert forall |idx: nat| next.satisfied_by(#[trigger] ex.suffix(i).suffix(idx)) by {
                    suffix_suffix_eq(ex, i, idx);
                    // ex.suffix(i).suffix(idx) == ex.suffix(i+idx)
                };

                // Build precondition 3: forall idx, !q(ex.suffix(i).suffix(idx)) -- already known from not_eventually_unfold

                // Now apply always_p_or_eventually_q_rec to show p holds at every suffix of ex.suffix(i)
                assert forall |j: nat| p.satisfied_by(#[trigger] ex.suffix(i).suffix(j)) by {
                    always_p_or_eventually_q_rec(ex.suffix(i), next, p, q, j);
                };

                // Now conclude always(p) holds at ex.suffix(i)
                assert(always(p).satisfied_by(ex.suffix(i)));
                assert((always(p).or(eventually(q))).satisfied_by(ex.suffix(i)));
            } else {
                assert((always(p).or(eventually(q))).satisfied_by(ex.suffix(i)));
            }
        }
        assert(p.implies(always(p).or(eventually(q))).satisfied_by(ex.suffix(i)));
    };
}

}
