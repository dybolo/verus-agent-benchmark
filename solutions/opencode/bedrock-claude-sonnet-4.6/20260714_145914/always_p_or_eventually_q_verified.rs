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

    proof fn always_p_or_eventually_q_rec_impl<T>(ex: Execution<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>, i: nat)
    requires
        forall |idx| p.satisfied_by(ex.suffix(idx)) && next.satisfied_by(ex.suffix(idx)) ==> p.satisfied_by(ex.suffix(idx + 1)) || q.satisfied_by(ex.suffix(idx + 1)),
        forall |idx| next.satisfied_by(#[trigger] ex.suffix(idx)),
        forall |idx| !q.satisfied_by(#[trigger] ex.suffix(idx)),
        p.satisfied_by(ex),
    ensures p.satisfied_by(ex.suffix(i)),
    decreases i,
    {
        // Induction on i
        if i == 0 {
            // need to show p.satisfied_by(ex.suffix(0))
            // We show ex.suffix(0) == ex
            assert(forall |k: nat| #[trigger] (ex.suffix(0).nat_to_state)(k) == (ex.nat_to_state)(k)) by {
                assert forall |k: nat| #[trigger] (ex.suffix(0).nat_to_state)(k) == (ex.nat_to_state)(k) by {
                    assert((ex.suffix(0).nat_to_state)(k) == (ex.nat_to_state)(k + 0nat));
                }
            };
            execution_equality(ex.suffix(0), ex);
        } else {
            // Inductive step: use i-1
            let i_prev: nat = (i - 1) as nat;
            always_p_or_eventually_q_rec_impl(ex, next, p, q, i_prev);
            assert(i_prev + 1 == i);
            assert(p.satisfied_by(ex.suffix(i_prev)) && next.satisfied_by(ex.suffix(i_prev)));
            assert(p.satisfied_by(ex.suffix(i_prev + 1)) || q.satisfied_by(ex.suffix(i_prev + 1)));
            assert(!q.satisfied_by(ex.suffix(i_prev + 1)));
            assert(p.satisfied_by(ex.suffix(i_prev + 1)));
        }
    }

	#[verifier::external_body]
pub proof fn execution_equality<T>(ex1: Execution<T>, ex2: Execution<T>)
    requires forall |i: nat| #[trigger] (ex1.nat_to_state)(i) == (ex2.nat_to_state)(i),
    ensures ex1 == ex2,
	{
		unimplemented!()
	}


proof fn always_p_or_eventually_q<T>(ex: Execution<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        always(p.and(next).implies(later(p).or(later(q)))).satisfied_by(ex),
        always(next).satisfied_by(ex),
    ensures always(p.implies(always(p).or(eventually(q)))).satisfied_by(ex),
{
    // We need to show: for all i, p.implies(always(p).or(eventually(q))).satisfied_by(ex.suffix(i))
    // i.e., for all i, p.satisfied_by(ex.suffix(i)) ==> always(p).or(eventually(q)).satisfied_by(ex.suffix(i))
    // i.e., for all i, p.satisfied_by(ex.suffix(i)) ==> always(p).satisfied_by(ex.suffix(i)) || eventually(q).satisfied_by(ex.suffix(i))

    assert forall |i: nat| p.implies(always(p).or(eventually(q))).satisfied_by(#[trigger] ex.suffix(i)) by {
        if p.satisfied_by(ex.suffix(i)) {
            // We need to show: always(p).or(eventually(q)) holds at ex.suffix(i)
            // i.e., always(p).satisfied_by(ex.suffix(i)) || eventually(q).satisfied_by(ex.suffix(i))

            // Unfold always(next) to get next holds everywhere
            always_unfold(ex, next);
            // Unfold always(p.and(next).implies(later(p).or(later(q)))) 
            always_unfold(ex, p.and(next).implies(later(p).or(later(q))));

            // The hypothesis says at every position j, (p && next) => (later(p) || later(q))
            // Which means: p(ex.suffix(j)) && next(ex.suffix(j)) => p(ex.suffix(j).suffix(1)) || q(ex.suffix(j).suffix(1))

            // We need to reason about ex.suffix(i):
            // At ex.suffix(i), we know:
            //   - p holds (by assumption)
            //   - For all j, (p.and(next).implies(later(p).or(later(q)))).satisfied_by(ex.suffix(i).suffix(j))
            //   - For all j, next.satisfied_by(ex.suffix(i).suffix(j))

            // Consider two cases:
            // Case 1: eventually(q) holds at ex.suffix(i): done
            // Case 2: not(eventually(q)) holds at ex.suffix(i): then we need to show always(p) holds at ex.suffix(i)

            if not(eventually(q)).satisfied_by(ex.suffix(i)) {
                // q never holds from i onwards
                not_eventually_unfold(ex.suffix(i), q);
                // So for all j, !q(ex.suffix(i).suffix(j))
                // We want to show always(p).satisfied_by(ex.suffix(i))
                // i.e., for all j, p.satisfied_by(ex.suffix(i).suffix(j))

                // We'll use always_p_or_eventually_q_rec on ex.suffix(i)
                // Need: for all idx, p(ex.suffix(i).suffix(idx)) && next(ex.suffix(i).suffix(idx)) => p(ex.suffix(i).suffix(idx+1)) || q(ex.suffix(i).suffix(idx+1))
                // This follows from the always hypothesis at ex.suffix(i)
                // Also need: next holds everywhere from ex.suffix(i) - yes, always(next) propagates
                // And p holds at ex.suffix(i)

                always_propagate_forwards(ex, next, i);
                // Now always(next).satisfied_by(ex.suffix(i))
                always_unfold(ex.suffix(i), next);
                // Now forall j, next.satisfied_by(ex.suffix(i).suffix(j))

                always_propagate_forwards(ex, p.and(next).implies(later(p).or(later(q))), i);
                // Now always(p.and(next).implies(later(p).or(later(q)))).satisfied_by(ex.suffix(i))
                always_unfold(ex.suffix(i), p.and(next).implies(later(p).or(later(q))));
                // Now forall j, (p.and(next).implies(later(p).or(later(q)))).satisfied_by(ex.suffix(i).suffix(j))

                // Build the condition for always_p_or_eventually_q_rec
                assert forall |idx: nat| p.satisfied_by(ex.suffix(i).suffix(idx)) && next.satisfied_by(ex.suffix(i).suffix(idx)) ==> p.satisfied_by(ex.suffix(i).suffix(idx + 1)) || q.satisfied_by(ex.suffix(i).suffix(idx + 1)) by {
                    if p.satisfied_by(ex.suffix(i).suffix(idx)) && next.satisfied_by(ex.suffix(i).suffix(idx)) {
                        // p.and(next).implies(later(p).or(later(q))).satisfied_by(ex.suffix(i).suffix(idx))
                        let ex_ij = ex.suffix(i).suffix(idx);
                        assert(p.and(next).satisfied_by(ex_ij));
                        implies_apply(ex_ij, p.and(next), later(p).or(later(q)));
                        // later(p).or(later(q)).satisfied_by(ex_ij)
                        // i.e., p.satisfied_by(ex_ij.suffix(1)) || q.satisfied_by(ex_ij.suffix(1))
                        // Need to show ex_ij.suffix(1) == ex.suffix(i).suffix(idx + 1)
                        assert(forall |k: nat| #[trigger] (ex_ij.suffix(1).nat_to_state)(k) == (ex.suffix(i).suffix(idx + 1).nat_to_state)(k)) by {
                            assert forall |k: nat| #[trigger] (ex_ij.suffix(1).nat_to_state)(k) == (ex.suffix(i).suffix(idx + 1).nat_to_state)(k) by {
                                assert((ex_ij.suffix(1).nat_to_state)(k) == (ex.nat_to_state)(k + 1 + idx + i));
                                assert((ex.suffix(i).suffix(idx + 1).nat_to_state)(k) == (ex.nat_to_state)(k + (idx + 1) + i));
                            }
                        };
                        execution_equality(ex_ij.suffix(1), ex.suffix(i).suffix(idx + 1));
                        // So p(ex.suffix(i).suffix(idx+1)) || q(ex.suffix(i).suffix(idx+1))
                    }
                };

                assert forall |j: nat| p.satisfied_by(#[trigger] ex.suffix(i).suffix(j)) by {
                    always_p_or_eventually_q_rec_impl(ex.suffix(i), next, p, q, j);
                };

                // So always(p).satisfied_by(ex.suffix(i))
                assert(always(p).satisfied_by(ex.suffix(i)));
                assert(always(p).or(eventually(q)).satisfied_by(ex.suffix(i)));
            } else {
                // eventually(q) holds at ex.suffix(i)
                assert(eventually(q).satisfied_by(ex.suffix(i)));
                assert(always(p).or(eventually(q)).satisfied_by(ex.suffix(i)));
            }
        }
    };
}

}
