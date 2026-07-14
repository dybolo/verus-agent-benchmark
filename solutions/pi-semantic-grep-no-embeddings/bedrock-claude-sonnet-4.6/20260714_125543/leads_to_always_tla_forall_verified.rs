use vstd::prelude::*;
use vstd::map_lib::*;

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

pub open spec fn tla_forall<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |a: A| #[trigger] a_to_temp_pred(a).satisfied_by(ex))
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

// Helper: suffix(a).suffix(b) == suffix(a+b)
proof fn suffix_add<T>(ex: Execution<T>, a: nat, b: nat)
    ensures ex.suffix(a).suffix(b) == ex.suffix(a + b),
{
    execution_equality(
        ex.suffix(a).suffix(b),
        ex.suffix(a + b),
    );
}

// Helper: if always(p) holds at ex.suffix(j0) and j >= j0, then it holds at ex.suffix(j)
proof fn always_propagate_ge<T>(ex: Execution<T>, p: TempPred<T>, j0: nat, j: nat)
    requires
        always(p).satisfied_by(ex.suffix(j0)),
        j >= j0,
    ensures always(p).satisfied_by(ex.suffix(j)),
{
    let extra: nat = (j - j0) as nat;
    assert(j0 + extra == j);
    always_propagate_forwards(ex.suffix(j0), p, extra);
    // Now: always(p).satisfied_by(ex.suffix(j0).suffix(extra))
    suffix_add(ex, j0, extra);
    // Now: ex.suffix(j0).suffix(extra) == ex.suffix(j0 + extra) == ex.suffix(j)
    assert(ex.suffix(j0).suffix(extra) == ex.suffix(j));
}

// Core induction lemma: for any finite Set<A>, returns a witness j such that
// for all a in s, always(a_to_p(a)) holds at ex.suffix(i).suffix(j).
// Returning j directly avoids trigger issues with exists|j| forall|a|.
proof fn find_j_for_set<T, A>(
    spec: TempPred<T>,
    p: TempPred<T>,
    a_to_p: spec_fn(A) -> TempPred<T>,
    ex: Execution<T>,
    i: nat,
    s: Set<A>,
) -> (j: nat)
    requires
        spec.satisfied_by(ex),
        p.satisfied_by(ex.suffix(i)),
        forall |a: A| spec.entails(p.leads_to(always(#[trigger] a_to_p(a)))),
    ensures
        forall |a: A| #[trigger] s.contains(a) ==>
            always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)),
    decreases s.len(),
{
    if s.len() == 0 {
        // Empty set: j = 0 works trivially (vacuously true)
        assert(s =~= Set::empty());
        0nat
    } else {
        // Non-empty set: pick an element and recurse
        broadcast use vstd::set::lemma_set_choose_len;
        broadcast use vstd::set::lemma_set_remove_len;
        broadcast use vstd::set::lemma_set_remove_different;

        let a0 = s.choose();
        assert(s.contains(a0));

        // Prove the recursive call terminates: s.remove(a0).len() < s.len()
        assert(s.remove(a0).len() < s.len());

        // Apply induction hypothesis on s.remove(a0)
        let j_rest = find_j_for_set::<T, A>(spec, p, a_to_p, ex, i, s.remove(a0));
        // By ensures: forall a in s.remove(a0), always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j_rest))

        // Get witness time for a0:
        // From spec.entails(p.leads_to(always(a_to_p(a0)))) and spec.satisfied_by(ex)
        assert(spec.entails(p.leads_to(always(a_to_p(a0)))));
        assert(p.leads_to(always(a_to_p(a0))).satisfied_by(ex)) by {
            assert(spec.implies(p.leads_to(always(a_to_p(a0)))).satisfied_by(ex));
            implies_apply(ex, spec, p.leads_to(always(a_to_p(a0))));
        };

        // p.leads_to(always(a_to_p(a0))) = always(p.implies(eventually(always(a_to_p(a0)))))
        // Propagate always-leads_to to ex.suffix(i)
        always_propagate_forwards(ex, p.implies(eventually(always(a_to_p(a0)))), i);
        // Apply the implication with p.satisfied_by(ex.suffix(i))
        implies_apply(ex.suffix(i), p, eventually(always(a_to_p(a0))));
        // Now: eventually(always(a_to_p(a0))).satisfied_by(ex.suffix(i))
        // i.e., exists k, always(a_to_p(a0)).satisfied_by(ex.suffix(i).suffix(k))

        let j_a0 = choose |j: nat| always(a_to_p(a0)).satisfied_by(ex.suffix(i).suffix(j));
        assert(always(a_to_p(a0)).satisfied_by(ex.suffix(i).suffix(j_a0)));

        // Return max(j_rest, j_a0)
        if j_rest >= j_a0 {
            // j = j_rest works for all of s
            // For a0: propagate from j_a0 to j_rest
            always_propagate_ge(ex.suffix(i), a_to_p(a0), j_a0, j_rest);
            // For a != a0 in s: use IH (j_rest already works for s.remove(a0))
            assert forall |a: A| #[trigger] s.contains(a) implies
                always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j_rest)) by
            {
                if a == a0 {
                    // always_propagate_ge applied above
                } else {
                    // a is in s.remove(a0), so IH applies
                    assert(s.remove(a0).contains(a));
                }
            };
            j_rest
        } else {
            // j = j_a0 works for all of s (j_a0 > j_rest)
            // For a != a0 in s: propagate from j_rest to j_a0
            assert forall |a: A| #[trigger] s.contains(a) implies
                always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j_a0)) by
            {
                if a == a0 {
                    // already at j_a0
                } else {
                    assert(s.remove(a0).contains(a));
                    // j_a0 >= j_rest (j_rest < j_a0 implies j_a0 > j_rest >= j_rest)
                    always_propagate_ge(ex.suffix(i), a_to_p(a), j_rest, j_a0);
                }
            };
            j_a0
        }
    }
}

pub proof fn leads_to_always_tla_forall<T, A>(spec: TempPred<T>, p: TempPred<T>, a_to_p: spec_fn(A)->TempPred<T>, domain: Set<A>)
    requires
        forall |a: A| spec.entails(p.leads_to(always(#[trigger] a_to_p(a)))),
        domain.finite(),
        domain.len() > 0,
        forall |a: A| #[trigger] domain.contains(a),
    ensures spec.entails(p.leads_to(always(tla_forall(a_to_p)))),
{
    assert forall |ex: Execution<T>| #[trigger] spec.satisfied_by(ex) implies
        p.leads_to(always(tla_forall(a_to_p))).satisfied_by(ex) by
    {
        assert forall |i: nat|
            p.implies(eventually(always(tla_forall(a_to_p)))).satisfied_by(#[trigger] ex.suffix(i)) by
        {
            if p.satisfied_by(ex.suffix(i)) {
                // Apply find_j_for_set to domain to get a uniform witness j
                let j = find_j_for_set::<T, A>(spec, p, a_to_p, ex, i, domain);
                // By ensures: forall a in domain, always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j))
                // Since forall a: A, domain.contains(a), we have for all a: A:
                assert forall |a: A| #[trigger] always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)) by {
                    // domain.contains(a) holds from precondition
                    assert(domain.contains(a));
                    // find_j_for_set ensures: domain.contains(a) ==> always(a_to_p(a)).satisfied_by(...)
                };

                // Show always(tla_forall(a_to_p)).satisfied_by(ex.suffix(i).suffix(j))
                assert(always(tla_forall(a_to_p)).satisfied_by(ex.suffix(i).suffix(j))) by {
                    assert forall |k: nat|
                        tla_forall(a_to_p).satisfied_by(#[trigger] ex.suffix(i).suffix(j).suffix(k)) by
                    {
                        // Need: forall a: A, a_to_p(a).satisfied_by(ex.suffix(i).suffix(j).suffix(k))
                        assert forall |a: A|
                            #[trigger] a_to_p(a).satisfied_by(ex.suffix(i).suffix(j).suffix(k)) by
                        {
                            // From always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)):
                            // forall k', a_to_p(a).satisfied_by(ex.suffix(i).suffix(j).suffix(k'))
                            assert(always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)));
                            // Instantiate at k' = k:
                            assert(a_to_p(a).satisfied_by(ex.suffix(i).suffix(j).suffix(k)));
                        };
                    };
                };

                // Show eventually(always(tla_forall(a_to_p))).satisfied_by(ex.suffix(i))
                eventually_proved_by_witness(ex.suffix(i), always(tla_forall(a_to_p)), j);
            }
        };
    };
}


}
