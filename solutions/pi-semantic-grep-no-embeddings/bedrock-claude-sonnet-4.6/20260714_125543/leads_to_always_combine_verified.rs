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

// Helper: suffix of suffix equals suffix of sum
proof fn suffix_add<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix((i + j) as nat),
{
    assert forall |n: nat| #[trigger] (ex.suffix(i).suffix(j).nat_to_state)(n)
        == (ex.suffix((i + j) as nat).nat_to_state)(n)
    by {
        assert((ex.suffix(i).suffix(j).nat_to_state)(n) == (ex.nat_to_state)(n + j + i));
        assert((ex.suffix((i + j) as nat).nat_to_state)(n) == (ex.nat_to_state)(n + (i + j)));
        assert(n + j + i == n + (i + j)) by { };
    };
    execution_equality(ex.suffix(i).suffix(j), ex.suffix((i + j) as nat));
}

// Helper: combine always(q) and always(r) into always(q.and(r))
proof fn always_and_combine<T>(ex: Execution<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        always(q).satisfied_by(ex),
        always(r).satisfied_by(ex),
    ensures
        always(q.and(r)).satisfied_by(ex),
{
    assert forall |n: nat| #[trigger] (q.and(r)).satisfied_by(ex.suffix(n)) by {
        assert(q.satisfied_by(ex.suffix(n)));
        assert(r.satisfied_by(ex.suffix(n)));
    };
}

// Helper: propagate always(p) from suffix(from) to suffix(to) when to >= from
proof fn always_propagate_to<T>(ex: Execution<T>, p: TempPred<T>, from: nat, to: nat)
    requires
        always(p).satisfied_by(ex.suffix(from)),
        to >= from,
    ensures
        always(p).satisfied_by(ex.suffix(to)),
{
    let diff = (to - from) as nat;
    always_propagate_forwards(ex.suffix(from), p, diff);
    // Now have: always(p).satisfied_by(ex.suffix(from).suffix(diff))
    // Show ex.suffix(from).suffix(diff) == ex.suffix(to)
    assert forall |n: nat| #[trigger] (ex.suffix(from).suffix(diff).nat_to_state)(n)
        == (ex.suffix(to).nat_to_state)(n)
    by {
        assert((ex.suffix(from).suffix(diff).nat_to_state)(n) == (ex.nat_to_state)(n + diff + from));
        assert((ex.suffix(to).nat_to_state)(n) == (ex.nat_to_state)(n + to));
        assert(n + diff + from == n + to) by {
            assert(diff == to - from);
        };
    };
    execution_equality(ex.suffix(from).suffix(diff), ex.suffix(to));
}

pub proof fn leads_to_always_combine<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(always(q))),
        spec.entails(p.leads_to(always(r))),
    ensures
        spec.entails(p.leads_to(always(q.and(r)))),
        spec.entails(p.leads_to(always(q).and(always(r)))),
{
    // First postcondition: spec.entails(p.leads_to(always(q.and(r))))
    assert forall |ex: Execution<T>| #[trigger] spec.satisfied_by(ex)
        implies p.leads_to(always(q.and(r))).satisfied_by(ex)
    by {
        // Obtain p.leads_to(always(q)).satisfied_by(ex) from entails + spec
        assert(spec.implies(p.leads_to(always(q))).satisfied_by(ex)) by {
            assert(forall |ex0: Execution<T>| #[trigger]
                spec.implies(p.leads_to(always(q))).satisfied_by(ex0));
        };
        implies_apply(ex, spec, p.leads_to(always(q)));
        assert(p.leads_to(always(q)).satisfied_by(ex));

        // Obtain p.leads_to(always(r)).satisfied_by(ex) from entails + spec
        assert(spec.implies(p.leads_to(always(r))).satisfied_by(ex)) by {
            assert(forall |ex0: Execution<T>| #[trigger]
                spec.implies(p.leads_to(always(r))).satisfied_by(ex0));
        };
        implies_apply(ex, spec, p.leads_to(always(r)));
        assert(p.leads_to(always(r)).satisfied_by(ex));

        assert forall |i: nat| #[trigger]
            p.implies(eventually(always(q.and(r)))).satisfied_by(ex.suffix(i))
        by {
            if p.satisfied_by(ex.suffix(i)) {
                // From p.leads_to(always(q)).satisfied_by(ex), get eventually(always(q)) at ex.suffix(i)
                assert(p.implies(eventually(always(q))).satisfied_by(ex.suffix(i)));
                implies_apply(ex.suffix(i), p, eventually(always(q)));
                let j = eventually_choose_witness(ex.suffix(i), always(q));
                assert(always(q).satisfied_by(ex.suffix(i).suffix(j)));

                // From p.leads_to(always(r)).satisfied_by(ex), get eventually(always(r)) at ex.suffix(i)
                assert(p.implies(eventually(always(r))).satisfied_by(ex.suffix(i)));
                implies_apply(ex.suffix(i), p, eventually(always(r)));
                let k = eventually_choose_witness(ex.suffix(i), always(r));
                assert(always(r).satisfied_by(ex.suffix(i).suffix(k)));

                // Pick m = max(j, k)
                let m: nat = if j >= k { j } else { k };

                if j >= k {
                    // m = j; always(q) already holds at suffix(j)
                    // Propagate always(r) from suffix(k) to suffix(j) = suffix(m)
                    always_propagate_to(ex.suffix(i), r, k, m);
                    assert(always(q).satisfied_by(ex.suffix(i).suffix(m)));
                    assert(always(r).satisfied_by(ex.suffix(i).suffix(m)));
                } else {
                    // m = k; always(r) already holds at suffix(k)
                    // Propagate always(q) from suffix(j) to suffix(k) = suffix(m)
                    always_propagate_to(ex.suffix(i), q, j, m);
                    assert(always(q).satisfied_by(ex.suffix(i).suffix(m)));
                    assert(always(r).satisfied_by(ex.suffix(i).suffix(m)));
                }

                // Combine: always(q.and(r)) at suffix(i).suffix(m)
                always_and_combine(ex.suffix(i).suffix(m), q, r);
                assert(always(q.and(r)).satisfied_by(ex.suffix(i).suffix(m)));

                // Witness for eventually(always(q.and(r))) at suffix(i)
                eventually_proved_by_witness(ex.suffix(i), always(q.and(r)), m);
            }
        };
    };

    // Second postcondition: use always_and_equality to convert
    always_and_equality(q, r);
    assert(always(q.and(r)) == always(q).and(always(r)));
    assert(p.leads_to(always(q.and(r))) == p.leads_to(always(q).and(always(r))));
}


}
