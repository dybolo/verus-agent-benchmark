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

// Helper: suffix composition
proof fn suffix_suffix_eq<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix((i + j) as nat),
{
    execution_equality(
        ex.suffix(i).suffix(j),
        ex.suffix((i + j) as nat),
    );
}

// Helper: always on a suffix
proof fn always_on_suffix<T>(ex: Execution<T>, p: TempPred<T>, i: nat, j: nat)
    requires always(p).satisfied_by(ex.suffix(i)),
    ensures p.satisfied_by(ex.suffix(i).suffix(j)),
{
    // always(p).satisfied_by(ex.suffix(i)) means forall k, p.satisfied_by(ex.suffix(i).suffix(k))
    assert(always(p).satisfied_by(ex.suffix(i)));
    // so p.satisfied_by(ex.suffix(i).suffix(j))
}

// The key helper: for a finite set S of elements, if for each a in S we have a witness j_a
// such that always(a_to_p(a)) holds at ex.suffix(i + j_a), then there exists j such that
// for all a in S, always(a_to_p(a)) holds at ex.suffix(i + j).
// We prove this by induction on the finite set.
proof fn finite_set_leads_to_always_forall_witness<T, A>(
    ex: Execution<T>,
    i: nat,
    a_to_p: spec_fn(A) -> TempPred<T>,
    s: Set<A>,
    witness_fn: spec_fn(A) -> nat,
) -> (j: nat)
    requires
        s.len() > 0,
        forall |a: A| s.contains(a) ==> always(#[trigger] a_to_p(a)).satisfied_by(ex.suffix(i).suffix(witness_fn(a))),
    ensures
        forall |a: A| s.contains(a) ==> always(#[trigger] a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)),
    decreases s.len(),
{
    if s.len() == 1 {
        // Single element: just use its witness
        let a = s.choose();
        assert(s.contains(a));
        let j = witness_fn(a);
        assert(always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)));
        assert forall |a2: A| s.contains(a2) implies always(#[trigger] a_to_p(a2)).satisfied_by(ex.suffix(i).suffix(j)) by {
            // a2 must equal a since s has exactly one element
            assert(s.contains(a2));
            assert(s.contains(a));
            // Use the fact that s has len 1 to show a == a2
            lemma_set_is_singleton_means_all_eq(s, a, a2);
            assert(a == a2);
        };
        j
    } else {
        // Pick one element, get its witness
        let a0 = s.choose();
        assert(s.contains(a0));
        let j0 = witness_fn(a0);

        // Recurse on s.remove(a0)
        let s_rest = s.remove(a0);
        assert(s_rest.len() == s.len() - 1);
        assert(s_rest.len() > 0);

        // The witness_fn still works on s_rest
        assert forall |a: A| s_rest.contains(a) implies always(#[trigger] a_to_p(a)).satisfied_by(ex.suffix(i).suffix(witness_fn(a))) by {
            assert(s.contains(a));
        };

        let j_rest = finite_set_leads_to_always_forall_witness(ex, i, a_to_p, s_rest, witness_fn);

        // Now combine j0 and j_rest: take max
        let j = if j0 >= j_rest { j0 } else { j_rest };

        // Show that for all a in s, always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j))
        assert forall |a: A| s.contains(a) implies always(#[trigger] a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)) by {
            if a == a0 {
                // We have always(a_to_p(a0)) at ex.suffix(i).suffix(j0)
                // Need to propagate to ex.suffix(i).suffix(j)
                if j == j0 {
                    assert(always(a_to_p(a0)).satisfied_by(ex.suffix(i).suffix(j)));
                } else {
                    // j == j_rest > j0, propagate forwards
                    let diff = (j - j0) as nat;
                    always_propagate_forwards(ex.suffix(i).suffix(j0), a_to_p(a0), diff);
                    suffix_suffix_eq(ex.suffix(i), j0, diff);
                    assert((j0 + diff) as nat == j);
                    assert(always(a_to_p(a0)).satisfied_by(ex.suffix(i).suffix(j)));
                }
            } else {
                // a is in s_rest
                assert(s_rest.contains(a));
                // We have always(a_to_p(a)) at ex.suffix(i).suffix(j_rest)
                if j == j_rest {
                    assert(always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)));
                } else {
                    // j == j0 > j_rest, propagate forwards
                    let diff = (j - j_rest) as nat;
                    always_propagate_forwards(ex.suffix(i).suffix(j_rest), a_to_p(a), diff);
                    suffix_suffix_eq(ex.suffix(i), j_rest, diff);
                    assert((j_rest + diff) as nat == j);
                    assert(always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)));
                }
            }
        };
        j
    }
}

// Helper lemma: in a singleton set, all elements are equal
proof fn lemma_set_is_singleton_means_all_eq<A>(s: Set<A>, a1: A, a2: A)
    requires
        s.len() == 1,
        s.contains(a1),
        s.contains(a2),
    ensures a1 == a2,
{
    broadcast use vstd::set::group_set_lemmas;
    // s.len() == 1 means s = {a1}
    // if a2 != a1, then s.remove(a1) would still contain a2, but remove(a1) has len 0
    if a1 != a2 {
        assert(s.remove(a1).contains(a2));
        assert(s.remove(a1).len() == 0);
        // contradiction: s.remove(a1) has len 0 but contains a2
        assert(s.remove(a1).len() != 0);
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
    // We need to show: for all ex satisfying spec, always(p.implies(eventually(always(tla_forall(a_to_p))))).satisfied_by(ex)
    assert forall |ex: Execution<T>| spec.implies(p.leads_to(always(tla_forall(a_to_p)))).satisfied_by(ex) by {
        if spec.satisfied_by(ex) {
            // Show p.leads_to(always(tla_forall(a_to_p))).satisfied_by(ex)
            // = always(p.implies(eventually(always(tla_forall(a_to_p))))).satisfied_by(ex)
            assert forall |i: nat| #[trigger] p.implies(eventually(always(tla_forall(a_to_p)))).satisfied_by(ex.suffix(i)) by {
                if p.satisfied_by(ex.suffix(i)) {
                    // For each a, spec.entails(p.leads_to(always(a_to_p(a))))
                    // so always(p.implies(eventually(always(a_to_p(a))))).satisfied_by(ex)
                    // so p.implies(eventually(always(a_to_p(a)))).satisfied_by(ex.suffix(i))
                    // since p.satisfied_by(ex.suffix(i)):
                    // eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i))
                    // so exists j_a: always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j_a))

                    // Build a witness function: for each a, give the j_a
                    let witness_fn: spec_fn(A) -> nat = |a: A| {
                        let j = eventually_choose_witness(ex.suffix(i), always(a_to_p(a)));
                        j
                    };

                    // Verify witness_fn works for all a in domain
                    assert forall |a: A| domain.contains(a) implies always(#[trigger] a_to_p(a)).satisfied_by(ex.suffix(i).suffix(witness_fn(a))) by {
                        // From the hypothesis:
                        assert(spec.entails(p.leads_to(always(a_to_p(a)))));
                        // spec.entails(...) means valid(spec.implies(...))
                        // valid means for all ex, spec.satisfied_by(ex) ==> p.leads_to(...).satisfied_by(ex)
                        // since spec.satisfied_by(ex):
                        assert(spec.implies(p.leads_to(always(a_to_p(a)))).satisfied_by(ex));
                        implies_apply(ex, spec, p.leads_to(always(a_to_p(a))));
                        assert(p.leads_to(always(a_to_p(a))).satisfied_by(ex));
                        // p.leads_to(always(a_to_p(a))) = always(p.implies(eventually(always(a_to_p(a)))))
                        assert(always(p.implies(eventually(always(a_to_p(a))))).satisfied_by(ex));
                        // Propagate always to suffix i
                        assert(p.implies(eventually(always(a_to_p(a)))).satisfied_by(ex.suffix(i)));
                        // since p.satisfied_by(ex.suffix(i)):
                        implies_apply(ex.suffix(i), p, eventually(always(a_to_p(a))));
                        assert(eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i)));
                        // so exists j_a: always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j_a))
                        let j_a = eventually_choose_witness(ex.suffix(i), always(a_to_p(a)));
                        assert(always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j_a)));
                        assert(witness_fn(a) == j_a);
                    };

                    // Now use finite_set_leads_to_always_forall_witness
                    let j = finite_set_leads_to_always_forall_witness(ex, i, a_to_p, domain, witness_fn);

                    // j is the index where for all a in domain (= all a in A),
                    // always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j))
                    assert forall |a: A| #[trigger] always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)) by {
                        assert(domain.contains(a));
                    };

                    // Therefore always(tla_forall(a_to_p)).satisfied_by(ex.suffix(i).suffix(j))
                    assert(always(tla_forall(a_to_p)).satisfied_by(ex.suffix(i).suffix(j))) by {
                        assert forall |k: nat| #[trigger] tla_forall(a_to_p).satisfied_by(ex.suffix(i).suffix(j).suffix(k)) by {
                            assert forall |a: A| #[trigger] a_to_p(a).satisfied_by(ex.suffix(i).suffix(j).suffix(k)) by {
                                // always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j))
                                // means forall k, a_to_p(a).satisfied_by(ex.suffix(i).suffix(j).suffix(k))
                                assert(always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)));
                            };
                        };
                    };

                    // So eventually(always(tla_forall(a_to_p))).satisfied_by(ex.suffix(i))
                    eventually_proved_by_witness(ex.suffix(i), always(tla_forall(a_to_p)), j);
                }
            };
        }
    };
}


}
