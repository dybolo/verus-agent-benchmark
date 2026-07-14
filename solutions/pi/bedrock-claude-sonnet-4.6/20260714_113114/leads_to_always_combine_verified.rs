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

// Helper lemma: ex.suffix(a).suffix(b) == ex.suffix(a + b)
proof fn suffix_add<T>(ex: Execution<T>, a: nat, b: nat)
    ensures ex.suffix(a).suffix(b) == ex.suffix(a + b),
{
    assert forall |k: nat| #[trigger] (ex.suffix(a).suffix(b).nat_to_state)(k)
        == (ex.suffix(a + b).nat_to_state)(k) by {
        // Both sides reduce to ex.nat_to_state(k + b + a) == ex.nat_to_state(k + (a + b))
        // which holds by commutativity/associativity of nat addition
    };
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
    // First prove spec.entails(p.leads_to(always(q.and(r))))
    assert forall |ex: Execution<T>| spec.satisfied_by(ex)
        implies p.leads_to(always(q.and(r))).satisfied_by(ex) by {

        // Extract that p ~> always(q) and p ~> always(r) hold for this ex
        assert(p.leads_to(always(q)).satisfied_by(ex)) by {
            assert(spec.implies(p.leads_to(always(q))).satisfied_by(ex));
            implies_apply(ex, spec, p.leads_to(always(q)));
        };
        assert(p.leads_to(always(r)).satisfied_by(ex)) by {
            assert(spec.implies(p.leads_to(always(r))).satisfied_by(ex));
            implies_apply(ex, spec, p.leads_to(always(r)));
        };

        // p.leads_to(always(q)).satisfied_by(ex)
        //   = always(p.implies(eventually(always(q)))).satisfied_by(ex)
        //   = forall i, p.implies(eventually(always(q))).satisfied_by(ex.suffix(i))
        // Same for r.

        // Now prove the leads_to for q.and(r)
        assert forall |i: nat| #[trigger]
            p.implies(eventually(always(q.and(r)))).satisfied_by(ex.suffix(i)) by {
            if p.satisfied_by(ex.suffix(i)) {
                // Get eventually always(q) at ex.suffix(i)
                assert(eventually(always(q)).satisfied_by(ex.suffix(i))) by {
                    assert(p.implies(eventually(always(q))).satisfied_by(ex.suffix(i)));
                    implies_apply(ex.suffix(i), p, eventually(always(q)));
                };
                // Get eventually always(r) at ex.suffix(i)
                assert(eventually(always(r)).satisfied_by(ex.suffix(i))) by {
                    assert(p.implies(eventually(always(r))).satisfied_by(ex.suffix(i)));
                    implies_apply(ex.suffix(i), p, eventually(always(r)));
                };

                // Choose witnesses for the eventualities
                let j1 = eventually_choose_witness(ex.suffix(i), always(q));
                let j2 = eventually_choose_witness(ex.suffix(i), always(r));

                assert(always(q).satisfied_by(ex.suffix(i).suffix(j1)));
                assert(always(r).satisfied_by(ex.suffix(i).suffix(j2)));

                // Take j = max(j1, j2)
                let j: nat = if j1 >= j2 { j1 } else { j2 };

                // Show always(q.and(r)).satisfied_by(ex.suffix(i).suffix(j))
                assert(always(q.and(r)).satisfied_by(ex.suffix(i).suffix(j))) by {
                    assert forall |k: nat| #[trigger]
                        q.and(r).satisfied_by(ex.suffix(i).suffix(j).suffix(k)) by {

                        // Prove q holds: use always(q) at suffix(j1)
                        assert(q.satisfied_by(ex.suffix(i).suffix(j).suffix(k))) by {
                            // m = j - j1 + k; since j >= j1, this is a valid nat offset
                            let m: nat = (j - j1 + k) as nat;
                            // always(q) at ex.suffix(i).suffix(j1) gives q at offset m
                            assert(q.satisfied_by(ex.suffix(i).suffix(j1).suffix(m)));
                            // ex.suffix(i).suffix(j1).suffix(m) == ex.suffix(i).suffix(j1 + m)
                            suffix_add(ex.suffix(i), j1, m);
                            // ex.suffix(i).suffix(j).suffix(k) == ex.suffix(i).suffix(j + k)
                            suffix_add(ex.suffix(i), j, k);
                            // j1 + m == j + k (since m = j - j1 + k and j >= j1)
                            assert(j1 + m == j + k);
                        };

                        // Prove r holds: use always(r) at suffix(j2)
                        assert(r.satisfied_by(ex.suffix(i).suffix(j).suffix(k))) by {
                            // m2 = j - j2 + k; since j >= j2, valid nat offset
                            let m2: nat = (j - j2 + k) as nat;
                            // always(r) at ex.suffix(i).suffix(j2) gives r at offset m2
                            assert(r.satisfied_by(ex.suffix(i).suffix(j2).suffix(m2)));
                            // ex.suffix(i).suffix(j2).suffix(m2) == ex.suffix(i).suffix(j2 + m2)
                            suffix_add(ex.suffix(i), j2, m2);
                            // ex.suffix(i).suffix(j).suffix(k) == ex.suffix(i).suffix(j + k)
                            suffix_add(ex.suffix(i), j, k);
                            // j2 + m2 == j + k (since m2 = j - j2 + k and j >= j2)
                            assert(j2 + m2 == j + k);
                        };
                    };
                };

                // Use j as witness for eventually
                eventually_proved_by_witness(ex.suffix(i), always(q.and(r)), j);
            }
        };
    };

    // Second conclusion: spec.entails(p.leads_to(always(q).and(always(r))))
    // By always_and_equality, always(q.and(r)) == always(q).and(always(r))
    always_and_equality(q, r);
    // Now always(q.and(r)) == always(q).and(always(r))
    // So p.leads_to(always(q.and(r))) == p.leads_to(always(q).and(always(r)))
    assert(always(q.and(r)) == always(q).and(always(r)));
    // The two leads_to predicates are equal, so entailment transfers
    assert forall |ex: Execution<T>| spec.satisfied_by(ex)
        implies p.leads_to(always(q).and(always(r))).satisfied_by(ex) by {
        assert(p.leads_to(always(q.and(r))).satisfied_by(ex));
        // Since always(q.and(r)) == always(q).and(always(r)):
        assert(always(q.and(r)) == always(q).and(always(r)));
        // p.leads_to(always(q.and(r))) = always(p.implies(eventually(always(q.and(r)))))
        // p.leads_to(always(q).and(always(r))) = always(p.implies(eventually(always(q).and(always(r)))))
        // These are equal because always(q.and(r)) == always(q).and(always(r))
        assert(p.leads_to(always(q.and(r))) == p.leads_to(always(q).and(always(r))));
    };
}


}
