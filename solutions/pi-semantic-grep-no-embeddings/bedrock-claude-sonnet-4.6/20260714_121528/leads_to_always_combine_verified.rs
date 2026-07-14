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

/// Helper: suffix composition is additive.
proof fn suffix_add<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix(i + j)
{
    assert forall |k: nat| #[trigger] (ex.suffix(i).suffix(j).nat_to_state)(k) == (ex.suffix(i + j).nat_to_state)(k) by {
        // LHS reduces to ex.nat_to_state(k + j + i)
        // RHS reduces to ex.nat_to_state(k + (i + j)) = ex.nat_to_state(k + i + j)
        // They are equal by arithmetic.
    };
    execution_equality(ex.suffix(i).suffix(j), ex.suffix(i + j));
}

/// Helper: always(q) propagates forward: if always(q) holds at ex.suffix(a),
/// and b >= a, then always(q) holds at ex.suffix(b).
proof fn always_forward_from<T>(ex: Execution<T>, q: TempPred<T>, a: nat, b: nat)
    requires
        always(q).satisfied_by(ex.suffix(a)),
        b >= a,
    ensures always(q).satisfied_by(ex.suffix(b))
{
    let d = (b - a) as nat;
    always_propagate_forwards(ex.suffix(a), q, d);
    // Now: always(q).satisfied_by(ex.suffix(a).suffix(d))
    // We need: ex.suffix(a).suffix(d) == ex.suffix(b)
    suffix_add(ex, a, d);
    // ex.suffix(a).suffix(d) == ex.suffix(a + d) == ex.suffix(b)
    assert(a + d == b);
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

    // Prove the second postcondition: spec.entails(p.leads_to(always(q).and(always(r))))
    assert forall |ex: Execution<T>|
        #[trigger] (spec.implies(p.leads_to(always(q).and(always(r))))).satisfied_by(ex)
    by {
        if spec.satisfied_by(ex) {
            // Show always(p.implies(eventually(always(q).and(always(r))))).satisfied_by(ex)
            assert forall |i: nat|
                #[trigger] (p.implies(eventually(always(q).and(always(r))))).satisfied_by(ex.suffix(i))
            by {
                if p.satisfied_by(ex.suffix(i)) {
                    // From hyp 1: get j1 such that always(q) holds at ex.suffix(i).suffix(j1)
                    implies_apply(ex, spec, p.leads_to(always(q)));
                    // p.leads_to(always(q)).satisfied_by(ex)
                    // = always(p.implies(eventually(always(q)))).satisfied_by(ex)
                    assert((p.implies(eventually(always(q)))).satisfied_by(ex.suffix(i)));
                    implies_apply(ex.suffix(i), p, eventually(always(q)));
                    let j1 = eventually_choose_witness(ex.suffix(i), always(q));
                    assert(always(q).satisfied_by(ex.suffix(i).suffix(j1)));

                    // From hyp 2: get j2 such that always(r) holds at ex.suffix(i).suffix(j2)
                    implies_apply(ex, spec, p.leads_to(always(r)));
                    assert((p.implies(eventually(always(r)))).satisfied_by(ex.suffix(i)));
                    implies_apply(ex.suffix(i), p, eventually(always(r)));
                    let j2 = eventually_choose_witness(ex.suffix(i), always(r));
                    assert(always(r).satisfied_by(ex.suffix(i).suffix(j2)));

                    // Take j = max(j1, j2)
                    let j: nat = if j1 >= j2 { j1 } else { j2 };

                    // Propagate always(q) to position j
                    always_forward_from(ex.suffix(i), q, j1, j);
                    assert(always(q).satisfied_by(ex.suffix(i).suffix(j)));

                    // Propagate always(r) to position j
                    always_forward_from(ex.suffix(i), r, j2, j);
                    assert(always(r).satisfied_by(ex.suffix(i).suffix(j)));

                    // Combine
                    assert((always(q).and(always(r))).satisfied_by(ex.suffix(i).suffix(j)));
                    eventually_proved_by_witness(ex.suffix(i), always(q).and(always(r)), j);
                }
            };
            assert(p.leads_to(always(q).and(always(r))).satisfied_by(ex));
        }
    };

    // Prove the first postcondition: spec.entails(p.leads_to(always(q.and(r))))
    // Since always(q.and(r)) == always(q).and(always(r)), these leads_to are equal.
    assert forall |ex: Execution<T>|
        #[trigger] (spec.implies(p.leads_to(always(q.and(r))))).satisfied_by(ex)
    by {
        if spec.satisfied_by(ex) {
            // We already proved p.leads_to(always(q).and(always(r))).satisfied_by(ex)
            assert((spec.implies(p.leads_to(always(q).and(always(r))))).satisfied_by(ex));
            implies_apply(ex, spec, p.leads_to(always(q).and(always(r))));
            // p.leads_to(always(q).and(always(r))).satisfied_by(ex)
            // = always(p.implies(eventually(always(q).and(always(r))))).satisfied_by(ex)
            // We need: always(p.implies(eventually(always(q.and(r))))).satisfied_by(ex)
            // Since always(q.and(r)) == always(q).and(always(r)):
            assert forall |i: nat|
                #[trigger] (p.implies(eventually(always(q.and(r))))).satisfied_by(ex.suffix(i))
            by {
                // From above: (p.implies(eventually(always(q).and(always(r))))).satisfied_by(ex.suffix(i))
                assert((p.implies(eventually(always(q).and(always(r))))).satisfied_by(ex.suffix(i)));
                if p.satisfied_by(ex.suffix(i)) {
                    implies_apply(ex.suffix(i), p, eventually(always(q).and(always(r))));
                    // eventually(always(q).and(always(r))).satisfied_by(ex.suffix(i))
                    let j = eventually_choose_witness(ex.suffix(i), always(q).and(always(r)));
                    // (always(q).and(always(r))).satisfied_by(ex.suffix(i).suffix(j))
                    assert((always(q).and(always(r))).satisfied_by(ex.suffix(i).suffix(j)));
                    // Since always(q.and(r)) == always(q).and(always(r)):
                    assert(always(q.and(r)).satisfied_by(ex.suffix(i).suffix(j)));
                    eventually_proved_by_witness(ex.suffix(i), always(q.and(r)), j);
                }
            };
            assert(p.leads_to(always(q.and(r))).satisfied_by(ex));
        }
    };
}


}
