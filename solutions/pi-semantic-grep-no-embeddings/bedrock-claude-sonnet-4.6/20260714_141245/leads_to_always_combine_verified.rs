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

/// Helper: ex.suffix(i).suffix(j) == ex.suffix(i + j)
proof fn suffix_addition<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix((i + j) as nat)
{
    assert forall |n: nat| #[trigger] (ex.suffix(i).suffix(j).nat_to_state)(n)
        == (ex.suffix((i + j) as nat).nat_to_state)(n) by {};
    execution_equality(ex.suffix(i).suffix(j), ex.suffix((i + j) as nat));
}

pub proof fn leads_to_always_combine<T>(spec: TempPred<T>, p: TempPred<T>, q: TempPred<T>, r: TempPred<T>)
    requires
        spec.entails(p.leads_to(always(q))),
        spec.entails(p.leads_to(always(r))),
    ensures
        spec.entails(p.leads_to(always(q.and(r)))),
        spec.entails(p.leads_to(always(q).and(always(r)))),
{
    // -----------------------------------------------------------------------
    // Part 1: Prove spec.entails(p.leads_to(always(q.and(r))))
    // -----------------------------------------------------------------------
    assert forall |ex: Execution<T>| spec.satisfied_by(ex)
        implies p.leads_to(always(q.and(r))).satisfied_by(ex) by
    {
        // Unfold entails for q and r
        implies_apply(ex, spec, p.leads_to(always(q)));
        implies_apply(ex, spec, p.leads_to(always(r)));

        // p.leads_to(always(q.and(r))) = always(p.implies(eventually(always(q.and(r)))))
        // Prove the inner forall over all positions i
        assert forall |i: nat|
            #[trigger] p.implies(eventually(always(q.and(r)))).satisfied_by(ex.suffix(i)) by
        {
            if p.satisfied_by(ex.suffix(i)) {
                // Get eventually(always(q)) and eventually(always(r)) at ex.suffix(i)
                implies_apply(ex.suffix(i), p, eventually(always(q)));
                implies_apply(ex.suffix(i), p, eventually(always(r)));

                // Choose witnesses j and k
                let j = eventually_choose_witness(ex.suffix(i), always(q));
                let k = eventually_choose_witness(ex.suffix(i), always(r));

                assert(always(q).satisfied_by(ex.suffix(i).suffix(j)));
                assert(always(r).satisfied_by(ex.suffix(i).suffix(k)));

                // m = max(j, k)
                let m: nat = if j >= k { j } else { k };

                // Show both always(q) and always(r) hold at ex.suffix(i).suffix(m)
                if j >= k {
                    // m == j, always(q) is already there
                    assert(always(q).satisfied_by(ex.suffix(i).suffix(m)));
                    // Propagate always(r) from k to j = m
                    always_propagate_forwards(ex.suffix(i).suffix(k), r, (j - k) as nat);
                    suffix_addition(ex.suffix(i), k, (j - k) as nat);
                    assert(always(r).satisfied_by(ex.suffix(i).suffix((k + (j - k)) as nat)));
                    assert(always(r).satisfied_by(ex.suffix(i).suffix(m)));
                } else {
                    // m == k, always(r) is already there
                    assert(always(r).satisfied_by(ex.suffix(i).suffix(m)));
                    // Propagate always(q) from j to k = m
                    always_propagate_forwards(ex.suffix(i).suffix(j), q, (k - j) as nat);
                    suffix_addition(ex.suffix(i), j, (k - j) as nat);
                    assert(always(q).satisfied_by(ex.suffix(i).suffix((j + (k - j)) as nat)));
                    assert(always(q).satisfied_by(ex.suffix(i).suffix(m)));
                };

                // Both always(q) and always(r) hold at ex.suffix(i).suffix(m),
                // so always(q.and(r)) holds there too.
                assert(always(q.and(r)).satisfied_by(ex.suffix(i).suffix(m))) by {
                    assert forall |l: nat|
                        #[trigger] q.and(r).satisfied_by(ex.suffix(i).suffix(m).suffix(l)) by
                    {
                        assert(q.satisfied_by(ex.suffix(i).suffix(m).suffix(l)));
                        assert(r.satisfied_by(ex.suffix(i).suffix(m).suffix(l)));
                    };
                };

                eventually_proved_by_witness(ex.suffix(i), always(q.and(r)), m);
            }
        };
    };

    // -----------------------------------------------------------------------
    // Part 2: Prove spec.entails(p.leads_to(always(q).and(always(r))))
    // -----------------------------------------------------------------------
    // By always_and_equality, always(q.and(r)) == always(q).and(always(r)).
    always_and_equality(q, r);
    assert(always(q.and(r)) == always(q).and(always(r)));

    assert forall |ex: Execution<T>| spec.satisfied_by(ex)
        implies p.leads_to(always(q).and(always(r))).satisfied_by(ex) by
    {
        // We just proved spec.entails(p.leads_to(always(q.and(r)))), use it
        implies_apply(ex, spec, p.leads_to(always(q.and(r))));
        assert(p.leads_to(always(q.and(r))).satisfied_by(ex));

        assert forall |i: nat|
            #[trigger] p.implies(eventually(always(q).and(always(r)))).satisfied_by(ex.suffix(i)) by
        {
            if p.satisfied_by(ex.suffix(i)) {
                implies_apply(ex.suffix(i), p, eventually(always(q.and(r))));
                assert(eventually(always(q.and(r))).satisfied_by(ex.suffix(i)));

                let j = eventually_choose_witness(ex.suffix(i), always(q.and(r)));
                assert(always(q.and(r)).satisfied_by(ex.suffix(i).suffix(j)));
                // Since always(q.and(r)) == always(q).and(always(r)):
                assert(always(q).and(always(r)).satisfied_by(ex.suffix(i).suffix(j)));
                eventually_proved_by_witness(ex.suffix(i), always(q).and(always(r)), j);
            }
        };
    };
}


}
