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

    pub open spec fn leads_to(self, other: Self) -> Self {
        always(self.implies(eventually(other)))
    }

    pub open spec fn entails(self, other: Self) -> bool {
        valid(self.implies(other))
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

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}


// File: rules.rs
	#[verifier::external_body]
proof fn leads_to_unfold<T>(ex: Execution<T>, p: TempPred<T>, q: TempPred<T>)
    requires p.leads_to(q).satisfied_by(ex),
    ensures forall |i: nat| p.implies(eventually(q)).satisfied_by(#[trigger] ex.suffix(i)),
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
proof fn eventually_proved_by_witness<T>(ex: Execution<T>, p: TempPred<T>, witness_idx: nat)
    requires p.satisfied_by(ex.suffix(witness_idx)),
    ensures eventually(p).satisfied_by(ex)
	{
		unimplemented!()
	}

spec fn eventually_choose_witness<T>(ex: Execution<T>, p: TempPred<T>) -> nat
    recommends exists |i| p.satisfied_by(#[trigger] ex.suffix(i)),
{
    let witness = choose |i| p.satisfied_by(#[trigger] ex.suffix(i));
    witness
}

	#[verifier::external_body]
proof fn next_preserves_inv_rec<T>(ex: Execution<T>, next: TempPred<T>, inv: TempPred<T>, i: nat)
    requires
        inv.satisfied_by(ex),
        forall |idx| next.satisfied_by(#[trigger] ex.suffix(idx)),
        forall |idx| inv.satisfied_by(#[trigger] ex.suffix(idx)) && next.satisfied_by(ex.suffix(idx))
            ==> inv.satisfied_by(ex.suffix(idx + 1)),
    ensures inv.satisfied_by(ex.suffix(i)),
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

proof fn suffix_suffix<T>(ex: Execution<T>, a: nat, b: nat)
    ensures ex.suffix(a).suffix(b) == ex.suffix(a + b)
{
    assert forall |i: nat| #[trigger] (ex.suffix(a).suffix(b).nat_to_state)(i)
        == (ex.suffix(a + b).nat_to_state)(i) by {}
    execution_equality(ex.suffix(a).suffix(b), ex.suffix(a + b));
}

pub proof fn leads_to_stable<T>(spec: TempPred<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(q.and(next).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(p.leads_to(q)),
    ensures spec.entails(p.leads_to(always(q))),
{
    assert forall |ex: Execution<T>| spec.satisfied_by(ex)
        implies p.leads_to(always(q)).satisfied_by(ex) by
    {
        // Extract all three hypotheses for this execution
        implies_apply(ex, spec, always(q.and(next).implies(later(q))));
        implies_apply(ex, spec, always(next));
        implies_apply(ex, spec, p.leads_to(q));

        // p.leads_to(always(q)) = always(p.implies(eventually(always(q))))
        // so we need to show for every suffix, p implies eventually(always(q))
        assert forall |i: nat| p.implies(eventually(always(q))).satisfied_by(#[trigger] ex.suffix(i)) by {
            if p.satisfied_by(ex.suffix(i)) {
                // From p.leads_to(q), at every suffix, p implies eventually(q)
                leads_to_unfold(ex, p, q);
                // Apply at ex.suffix(i) to get eventually(q)
                implies_apply(ex.suffix(i), p, eventually(q));

                // Choose the witness j where q holds
                let j = eventually_choose_witness(ex.suffix(i), q);
                assert(q.satisfied_by(ex.suffix(i).suffix(j)));

                // ex.suffix(i).suffix(j) == ex.suffix(i + j)
                suffix_suffix(ex, i, j);
                let ex_ij: Execution<T> = ex.suffix(i + j);
                assert(ex.suffix(i).suffix(j) == ex_ij);
                assert(q.satisfied_by(ex_ij));

                // Propagate always(next) and the stability condition to ex_ij
                always_propagate_forwards(ex, next, i + j);
                always_propagate_forwards(ex, q.and(next).implies(later(q)), i + j);

                // always(next).satisfied_by(ex_ij)
                // => forall idx, next.satisfied_by(ex_ij.suffix(idx))
                assert(always(next).satisfied_by(ex_ij));

                // always(q.and(next).implies(later(q))).satisfied_by(ex_ij)
                // => forall idx, q.and(next).implies(later(q)).satisfied_by(ex_ij.suffix(idx))
                assert(always(q.and(next).implies(later(q))).satisfied_by(ex_ij));

                // Prove the transition: q && next at ex_ij.suffix(s) => q at ex_ij.suffix(s+1)
                assert forall |s: nat|
                    q.satisfied_by(#[trigger] ex_ij.suffix(s)) && next.satisfied_by(ex_ij.suffix(s))
                    ==> q.satisfied_by(ex_ij.suffix(s + 1)) by
                {
                    if q.satisfied_by(ex_ij.suffix(s)) && next.satisfied_by(ex_ij.suffix(s)) {
                        // Stability: q.and(next).implies(later(q)) at ex_ij.suffix(s)
                        assert(q.and(next).implies(later(q)).satisfied_by(ex_ij.suffix(s)));
                        // q.and(next) holds at ex_ij.suffix(s)
                        assert(q.and(next).satisfied_by(ex_ij.suffix(s)));
                        // So later(q) holds at ex_ij.suffix(s)
                        implies_apply(ex_ij.suffix(s), q.and(next), later(q));
                        // later(q) at ex_ij.suffix(s) means q at ex_ij.suffix(s).suffix(1)
                        assert(q.satisfied_by(ex_ij.suffix(s).suffix(1)));
                        // ex_ij.suffix(s).suffix(1) == ex_ij.suffix(s + 1)
                        suffix_suffix(ex_ij, s, 1);
                        assert(ex_ij.suffix(s).suffix(1) == ex_ij.suffix(s + 1));
                    }
                };

                // Use next_preserves_inv_rec to show q holds at all suffixes of ex_ij
                assert forall |k: nat| q.satisfied_by(#[trigger] ex_ij.suffix(k)) by {
                    next_preserves_inv_rec(ex_ij, next, q, k);
                };

                // Therefore always(q) holds at ex_ij
                assert(always(q).satisfied_by(ex_ij));

                // ex_ij = ex.suffix(i).suffix(j), so always(q) holds at ex.suffix(i).suffix(j)
                // Use j as witness to show eventually(always(q)) at ex.suffix(i)
                eventually_proved_by_witness(ex.suffix(i), always(q), j);
            }
        };
    };
}


}
