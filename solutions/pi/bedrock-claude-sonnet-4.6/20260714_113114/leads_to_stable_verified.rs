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

/// Helper lemma: suffix of suffix equals suffix at sum of offsets.
proof fn suffix_suffix<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix((i + j) as nat)
{
    assert forall |n: nat| #[trigger] (ex.suffix(i).suffix(j).nat_to_state)(n)
        == (ex.suffix((i + j) as nat).nat_to_state)(n) by {
        // ex.suffix(i).suffix(j).nat_to_state(n)
        //   = ex.suffix(i).nat_to_state(n + j)
        //   = ex.nat_to_state(n + j + i)
        // ex.suffix(i + j).nat_to_state(n)
        //   = ex.nat_to_state(n + (i + j))
        // n + j + i == n + (i + j) by arithmetic
        assert((ex.suffix(i).suffix(j).nat_to_state)(n) == (ex.nat_to_state)(n + j + i));
        assert((ex.suffix((i + j) as nat).nat_to_state)(n) == (ex.nat_to_state)(n + (i + j)));
        assert(n + j + i == n + (i + j)) by { vstd::arithmetic::mul::lemma_mul_is_commutative(1, 1); };
    };
    execution_equality(ex.suffix(i).suffix(j), ex.suffix((i + j) as nat));
}

pub proof fn leads_to_stable<T>(spec: TempPred<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        spec.entails(always(q.and(next).implies(later(q)))),
        spec.entails(always(next)),
        spec.entails(p.leads_to(q)),
    ensures spec.entails(p.leads_to(always(q))),
{
    assert forall |ex: Execution<T>| #[trigger] spec.satisfied_by(ex)
        implies p.leads_to(always(q)).satisfied_by(ex) by {

        // Extract spec consequences for this execution
        implies_apply(ex, spec, always(q.and(next).implies(later(q))));
        implies_apply(ex, spec, always(next));
        implies_apply(ex, spec, p.leads_to(q));

        // Unfold p.leads_to(q): gives us forall i, p.implies(eventually(q)).satisfied_by(ex.suffix(i))
        leads_to_unfold(ex, p, q);

        // We must show: always(p.implies(eventually(always(q)))).satisfied_by(ex)
        // i.e., forall i, if p holds at ex.suffix(i), then eventually(always(q)) holds there.
        assert forall |i: nat|
            p.implies(eventually(always(q))).satisfied_by(#[trigger] ex.suffix(i)) by {

            if p.satisfied_by(ex.suffix(i)) {
                // By leads_to unfolded: p.implies(eventually(q)) holds at ex.suffix(i)
                // Since p holds there, we get eventually(q).satisfied_by(ex.suffix(i))
                implies_apply(ex.suffix(i), p, eventually(q));

                // Choose a witness w such that q holds at ex.suffix(i).suffix(w)
                let w = eventually_choose_witness(ex.suffix(i), q);
                // q.satisfied_by(ex.suffix(i).suffix(w))

                let ex2 = ex.suffix(i).suffix(w);

                // Propagate always(next) and always(q.and(next).implies(later(q))) forward to ex2
                always_propagate_forwards(ex, next, i);
                always_propagate_forwards(ex.suffix(i), next, w);
                // now always(next).satisfied_by(ex2)

                always_propagate_forwards(ex, q.and(next).implies(later(q)), i);
                always_propagate_forwards(ex.suffix(i), q.and(next).implies(later(q)), w);
                // now always(q.and(next).implies(later(q))).satisfied_by(ex2)

                // Prove the one-step preservation property needed by next_preserves_inv_rec
                assert forall |j: nat|
                    q.satisfied_by(#[trigger] ex2.suffix(j)) && next.satisfied_by(ex2.suffix(j))
                    ==> q.satisfied_by(ex2.suffix(j + 1)) by {

                    if q.satisfied_by(ex2.suffix(j)) && next.satisfied_by(ex2.suffix(j)) {
                        // q.and(next) holds at ex2.suffix(j)
                        assert(q.and(next).satisfied_by(ex2.suffix(j)));
                        // q.and(next).implies(later(q)) holds at ex2.suffix(j) (from always(...))
                        // => later(q).satisfied_by(ex2.suffix(j))
                        implies_apply(ex2.suffix(j), q.and(next), later(q));
                        // later(q).satisfied_by(ex2.suffix(j)) = q.satisfied_by(ex2.suffix(j).suffix(1))
                        assert(q.satisfied_by(ex2.suffix(j).suffix(1)));
                        // ex2.suffix(j).suffix(1) == ex2.suffix(j + 1) by suffix_suffix
                        suffix_suffix(ex2, j, 1);
                        assert(q.satisfied_by(ex2.suffix((j + 1) as nat)));
                    }
                };

                // By induction, q holds at every position from ex2
                assert forall |j: nat| q.satisfied_by(#[trigger] ex2.suffix(j)) by {
                    next_preserves_inv_rec(ex2, next, q, j);
                };

                // Therefore always(q).satisfied_by(ex2)
                assert(always(q).satisfied_by(ex2));

                // Hence eventually(always(q)).satisfied_by(ex.suffix(i)) with witness w
                eventually_proved_by_witness(ex.suffix(i), always(q), w);
            }
        };
    };
}


}
