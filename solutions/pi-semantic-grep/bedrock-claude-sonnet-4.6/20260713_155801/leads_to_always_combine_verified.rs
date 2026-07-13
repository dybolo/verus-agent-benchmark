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

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}


// File: rules.rs
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
pub proof fn execution_equality<T>(ex1: Execution<T>, ex2: Execution<T>)
    requires forall |i: nat| #[trigger] (ex1.nat_to_state)(i) == (ex2.nat_to_state)(i),
    ensures ex1 == ex2,
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn always_and_equality<T>(p: TempPred<T>, q: TempPred<T>)
    ensures always(p.and(q)) == always(p).and(always(q)),
	{
		unimplemented!()
	}

// Helper: suffix composition law
proof fn suffix_add<T>(ex: Execution<T>, a: nat, b: nat)
    ensures ex.suffix(a).suffix(b) == ex.suffix(a + b),
{
    assert forall |m: nat|
        #[trigger] (ex.suffix(a).suffix(b).nat_to_state)(m) == (ex.suffix(a + b).nat_to_state)(m)
    by {};
    execution_equality(ex.suffix(a).suffix(b), ex.suffix(a + b));
}

pub proof fn leads_to_always_combine<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(always(q))),
        spec.entails(p.leads_to(always(r))),
    ensures
        spec.entails(p.leads_to(always(q.and(r)))),
        spec.entails(p.leads_to(always(q).and(always(r)))),
{
    // Establish always(q.and(r)) == always(q).and(always(r))
    always_and_equality(q, r);

    // Prove the first postcondition
    assert forall |ex: Execution<T>| spec.satisfied_by(ex)
        implies p.leads_to(always(q.and(r))).satisfied_by(ex)
    by {
        // Extract p.leads_to(always(q)).satisfied_by(ex) from precondition 1
        // Precondition 1: spec.entails(p.leads_to(always(q)))
        //   = valid(spec.implies(p.leads_to(always(q))))
        //   = forall ex', spec.implies(p.leads_to(always(q))).satisfied_by(ex')
        // Instantiate the forall with our ex:
        assert(spec.implies(p.leads_to(always(q))).satisfied_by(ex));
        // Now use implies_apply: spec.satisfied_by(ex) is the hypothesis
        implies_apply(ex, spec, p.leads_to(always(q)));
        // p.leads_to(always(q)).satisfied_by(ex) is now in scope

        // Same for precondition 2:
        assert(spec.implies(p.leads_to(always(r))).satisfied_by(ex));
        implies_apply(ex, spec, p.leads_to(always(r)));
        // p.leads_to(always(r)).satisfied_by(ex) is now in scope

        // Now prove: forall i, p.implies(eventually(always(q.and(r)))).satisfied_by(ex.suffix(i))
        assert forall |i: nat| #[trigger]
            p.implies(eventually(always(q.and(r)))).satisfied_by(ex.suffix(i))
        by {
            if p.satisfied_by(ex.suffix(i)) {
                // --- Get eventually(always(q)) at ex.suffix(i) ---
                // p.leads_to(always(q)).satisfied_by(ex)
                //   = always(p.implies(eventually(always(q)))).satisfied_by(ex)
                //   = forall i', p.implies(eventually(always(q))).satisfied_by(ex.suffix(i'))
                // Instantiate with i:
                assert(p.implies(eventually(always(q))).satisfied_by(ex.suffix(i)));
                implies_apply(ex.suffix(i), p, eventually(always(q)));
                assert(eventually(always(q)).satisfied_by(ex.suffix(i)));

                // --- Get eventually(always(r)) at ex.suffix(i) ---
                assert(p.implies(eventually(always(r))).satisfied_by(ex.suffix(i)));
                implies_apply(ex.suffix(i), p, eventually(always(r)));
                assert(eventually(always(r)).satisfied_by(ex.suffix(i)));

                // --- Extract witnesses ---
                // eventually(always(q)).satisfied_by(ex.suffix(i))
                //   = exists j, always(q).satisfied_by(ex.suffix(i).suffix(j))
                assert(exists |j: nat| always(q).satisfied_by(ex.suffix(i).suffix(j)));
                let j = eventually_choose_witness(ex.suffix(i), always(q));
                assert(always(q).satisfied_by(ex.suffix(i).suffix(j)));

                assert(exists |k: nat| always(r).satisfied_by(ex.suffix(i).suffix(k)));
                let k = eventually_choose_witness(ex.suffix(i), always(r));
                assert(always(r).satisfied_by(ex.suffix(i).suffix(k)));

                // --- Propagate always(q) from j to j+k via j.suffix(k) ---
                always_propagate_forwards(ex.suffix(i).suffix(j), q, k);
                assert(always(q).satisfied_by(ex.suffix(i).suffix(j).suffix(k)));
                // Suffix composition: ex.suffix(i).suffix(j).suffix(k) == ex.suffix(i).suffix(j+k)
                suffix_add(ex.suffix(i), j, k);
                assert(always(q).satisfied_by(ex.suffix(i).suffix(j + k)));

                // --- Propagate always(r) from k to k+j via k.suffix(j) ---
                always_propagate_forwards(ex.suffix(i).suffix(k), r, j);
                assert(always(r).satisfied_by(ex.suffix(i).suffix(k).suffix(j)));
                // Suffix composition: ex.suffix(i).suffix(k).suffix(j) == ex.suffix(i).suffix(k+j)
                suffix_add(ex.suffix(i), k, j);
                assert(always(r).satisfied_by(ex.suffix(i).suffix(k + j)));
                // k+j == j+k by commutativity of nat addition
                assert(k + j == j + k);
                assert(always(r).satisfied_by(ex.suffix(i).suffix(j + k)));

                // --- Both hold at j+k ---
                assert(always(q).and(always(r)).satisfied_by(ex.suffix(i).suffix(j + k)));
                // By always_and_equality: always(q.and(r)) == always(q).and(always(r))
                assert(always(q.and(r)).satisfied_by(ex.suffix(i).suffix(j + k)));

                // --- Use j+k as witness for eventually(always(q.and(r))) ---
                eventually_proved_by_witness(ex.suffix(i), always(q.and(r)), j + k);
            }
        };
    };

    // Second postcondition: spec.entails(p.leads_to(always(q).and(always(r))))
    // follows directly from the first postcondition plus always_and_equality(q, r)
    // which gave us always(q.and(r)) == always(q).and(always(r))
}


}
