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

// Helper: suffix of suffix equals a single suffix with summed indices
proof fn suffix_add<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix((i + j) as nat)
{
    execution_equality(ex.suffix(i).suffix(j), ex.suffix((i + j) as nat));
}

// Helper: always(p) at ex.suffix(j) implies always(p) at ex.suffix(m) when m >= j
proof fn always_forward<T>(ex: Execution<T>, p: TempPred<T>, j: nat, m: nat)
    requires
        always(p).satisfied_by(ex.suffix(j)),
        m >= j,
    ensures
        always(p).satisfied_by(ex.suffix(m)),
{
    let diff: nat = (m - j) as nat;
    always_propagate_forwards(ex.suffix(j), p, diff);
    assert(ex.suffix(j).suffix(diff) == ex.suffix(m)) by {
        suffix_add(ex, j, diff);
        assert((j + diff) as nat == m);
    };
}

// Helper: always(q) and always(r) at same execution implies always(q.and(r))
proof fn always_and_combine<T>(ex: Execution<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        always(q).satisfied_by(ex),
        always(r).satisfied_by(ex),
    ensures
        always(q.and(r)).satisfied_by(ex),
{
    always_and_equality(q, r);
    assert(always(q.and(r)) == always(q).and(always(r)));
    assert(always(q).and(always(r)).satisfied_by(ex));
}

pub proof fn leads_to_always_combine<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(always(q))),
        spec.entails(p.leads_to(always(r))),
    ensures
        spec.entails(p.leads_to(always(q.and(r)))),
        spec.entails(p.leads_to(always(q).and(always(r)))),
{
    // spec.entails(X) = valid(spec.implies(X)) = forall ex, spec(ex) => X(ex)
    // First, prove spec.entails(p.leads_to(always(q.and(r))))
    assert forall |ex: Execution<T>| #[trigger] spec.implies(p.leads_to(always(q.and(r)))).satisfied_by(ex) by {
        if spec.satisfied_by(ex) {
            // From preconditions:
            // spec.entails(p.leads_to(always(q))) = valid(spec.implies(p.leads_to(always(q))))
            // So spec.implies(p.leads_to(always(q))).satisfied_by(ex) holds
            // Since spec.satisfied_by(ex), we get p.leads_to(always(q)).satisfied_by(ex)
            assert(spec.implies(p.leads_to(always(q))).satisfied_by(ex));
            implies_apply(ex, spec, p.leads_to(always(q)));
            assert(p.leads_to(always(q)).satisfied_by(ex));

            assert(spec.implies(p.leads_to(always(r))).satisfied_by(ex));
            implies_apply(ex, spec, p.leads_to(always(r)));
            assert(p.leads_to(always(r)).satisfied_by(ex));

            // p.leads_to(always(q)) = always(p.implies(eventually(always(q))))
            // So forall i, p.implies(eventually(always(q))).satisfied_by(ex.suffix(i))
            assert(always(p.implies(eventually(always(q)))).satisfied_by(ex));
            assert(always(p.implies(eventually(always(r)))).satisfied_by(ex));

            // Now show p.leads_to(always(q.and(r))).satisfied_by(ex)
            // = always(p.implies(eventually(always(q.and(r))))).satisfied_by(ex)
            // = forall i, p.implies(eventually(always(q.and(r)))).satisfied_by(ex.suffix(i))
            assert forall |i: nat| p.implies(eventually(always(q.and(r)))).satisfied_by(#[trigger] ex.suffix(i)) by {
                if p.satisfied_by(ex.suffix(i)) {
                    // Get eventually(always(q)) at ex.suffix(i)
                    assert(p.implies(eventually(always(q))).satisfied_by(ex.suffix(i)));
                    implies_apply(ex.suffix(i), p, eventually(always(q)));
                    assert(eventually(always(q)).satisfied_by(ex.suffix(i)));

                    // Get eventually(always(r)) at ex.suffix(i)
                    assert(p.implies(eventually(always(r))).satisfied_by(ex.suffix(i)));
                    implies_apply(ex.suffix(i), p, eventually(always(r)));
                    assert(eventually(always(r)).satisfied_by(ex.suffix(i)));

                    // Get witnesses j and k
                    let j = eventually_choose_witness(ex.suffix(i), always(q));
                    assert(always(q).satisfied_by(ex.suffix(i).suffix(j)));

                    let k = eventually_choose_witness(ex.suffix(i), always(r));
                    assert(always(r).satisfied_by(ex.suffix(i).suffix(k)));

                    // Let m = max(j, k)
                    let m: nat = if j >= k { j } else { k };
                    assert(m >= j);
                    assert(m >= k);

                    // always(q) holds at ex.suffix(i).suffix(m)
                    always_forward(ex.suffix(i), q, j, m);
                    assert(always(q).satisfied_by(ex.suffix(i).suffix(m)));

                    // always(r) holds at ex.suffix(i).suffix(m)
                    always_forward(ex.suffix(i), r, k, m);
                    assert(always(r).satisfied_by(ex.suffix(i).suffix(m)));

                    // Combine: always(q.and(r)) at ex.suffix(i).suffix(m)
                    always_and_combine(ex.suffix(i).suffix(m), q, r);
                    assert(always(q.and(r)).satisfied_by(ex.suffix(i).suffix(m)));

                    // Therefore eventually(always(q.and(r))) at ex.suffix(i)
                    eventually_proved_by_witness(ex.suffix(i), always(q.and(r)), m);
                    assert(eventually(always(q.and(r))).satisfied_by(ex.suffix(i)));
                }
            };
            assert(p.leads_to(always(q.and(r))).satisfied_by(ex));
        }
    };
    // Now valid(spec.implies(p.leads_to(always(q.and(r))))) holds
    assert(valid(spec.implies(p.leads_to(always(q.and(r))))));
    assert(spec.entails(p.leads_to(always(q.and(r)))));

    // Second postcondition: spec.entails(p.leads_to(always(q).and(always(r))))
    // By always_and_equality, always(q.and(r)) == always(q).and(always(r))
    // So p.leads_to(always(q.and(r))) == p.leads_to(always(q).and(always(r)))
    always_and_equality(q, r);
    assert(always(q.and(r)) == always(q).and(always(r)));
    assert(p.leads_to(always(q.and(r))) == p.leads_to(always(q).and(always(r))));
    assert(spec.entails(p.leads_to(always(q).and(always(r)))));
}


}
