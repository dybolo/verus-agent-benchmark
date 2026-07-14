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

// Helper: suffix(a).suffix(b) == suffix(a + b)
proof fn suffix_suffix_eq<T>(ex: Execution<T>, a: nat, b: nat)
    ensures ex.suffix(a).suffix(b) == ex.suffix(a + b)
{
    execution_equality(ex.suffix(a).suffix(b), ex.suffix(a + b));
}

// Helper: propagate always forward from ex.suffix(j_from) to ex.suffix(j_to)
// Uses ex as the base execution: always(p).satisfied_by(ex.suffix(j_from)) =>
//                                 always(p).satisfied_by(ex.suffix(j_to))
proof fn always_propagate_to<T>(ex: Execution<T>, p: TempPred<T>, j_from: nat, j_to: nat)
    requires
        j_from <= j_to,
        always(p).satisfied_by(ex.suffix(j_from)),
    ensures
        always(p).satisfied_by(ex.suffix(j_to))
{
    let delta: nat = (j_to - j_from) as nat;
    always_propagate_forwards(ex.suffix(j_from), p, delta);
    // Now: always(p).satisfied_by(ex.suffix(j_from).suffix(delta))
    suffix_suffix_eq(ex, j_from, delta);
    // Now: ex.suffix(j_from).suffix(delta) == ex.suffix(j_from + delta) == ex.suffix(j_to)
    assert(j_from + delta == j_to);
}

// Helper: find a uniform delta such that for all a in domain,
// always(a_to_p(a)) holds starting from ex.suffix(i).suffix(delta)
proof fn exists_uniform_always_witness<T, A>(
    ex: Execution<T>,
    i: nat,
    a_to_p: spec_fn(A) -> TempPred<T>,
    domain: Set<A>,
)
    requires
        forall |a: A| domain.contains(a) ==> #[trigger] eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i)),
    ensures
        exists |delta: nat| forall |a: A| domain.contains(a) ==>
            #[trigger] always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(delta)),
    decreases domain.len(),
{
    if domain.len() == 0 {
        // Empty domain: delta = 0 works trivially
        assert(forall |a: A| domain.contains(a) ==>
            #[trigger] always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(0nat)));
    } else {
        let a0 = domain.choose();
        // domain.contains(a0) from lemma_set_choose_len (broadcast)

        // Inductive hypothesis on domain.remove(a0)
        assert forall |a: A| domain.remove(a0).contains(a) implies
            eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i))
        by {
            // domain.remove(a0).contains(a) implies domain.contains(a)
            // (by broadcast set lemmas: either a == a0 giving contradiction, or lemma_set_remove_different)
            assert(domain.contains(a));
        };
        exists_uniform_always_witness(ex, i, a_to_p, domain.remove(a0));
        let d_rest: nat = choose |delta: nat| forall |a: A|
            domain.remove(a0).contains(a) ==>
            #[trigger] always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(delta));

        // Get witness d0 for a0:
        // eventually(always(a_to_p(a0))).satisfied_by(ex.suffix(i))
        // = exists k, always(a_to_p(a0)).satisfied_by(ex.suffix(i).suffix(k))
        assert(eventually(always(a_to_p(a0))).satisfied_by(ex.suffix(i)));
        let d0: nat = choose |k: nat| #[trigger] always(a_to_p(a0)).satisfied_by(ex.suffix(i).suffix(k));
        // By choose axiom:
        assert(always(a_to_p(a0)).satisfied_by(ex.suffix(i).suffix(d0)));

        // Take max of d0 and d_rest
        let d_max: nat = if d0 >= d_rest { d0 } else { d_rest };

        // Show d_max works for all elements of domain
        assert forall |a: A| domain.contains(a) implies
            always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(d_max))
        by {
            if a == a0 {
                // have: always(a_to_p(a0)).satisfied_by(ex.suffix(i).suffix(d0))
                // d0 <= d_max, propagate forward
                assert(d0 <= d_max);
                always_propagate_to(ex.suffix(i), a_to_p(a0), d0, d_max);
            } else {
                // a is in domain.remove(a0) (since a != a0 and domain.contains(a))
                assert(domain.remove(a0).contains(a));
                // from d_rest: always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(d_rest))
                assert(always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(d_rest)));
                // d_rest <= d_max, propagate forward
                assert(d_rest <= d_max);
                always_propagate_to(ex.suffix(i), a_to_p(a), d_rest, d_max);
            }
        };
        // d_max is our witness
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
    // Unfold entails: for all ex satisfying spec, show p.leads_to(always(tla_forall(a_to_p))).satisfied_by(ex)
    assert forall |ex: Execution<T>| spec.satisfied_by(ex) implies
        p.leads_to(always(tla_forall(a_to_p))).satisfied_by(ex)
    by {
        // p.leads_to(q) = always(p.implies(eventually(q)))
        // We need: forall i, p.implies(eventually(always(tla_forall(a_to_p)))).satisfied_by(ex.suffix(i))
        assert forall |i: nat| #[trigger]
            p.implies(eventually(always(tla_forall(a_to_p)))).satisfied_by(ex.suffix(i))
        by {
            if p.satisfied_by(ex.suffix(i)) {
                // For each a: A, derive eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i))
                assert forall |a: A| eventually(always(#[trigger] a_to_p(a))).satisfied_by(ex.suffix(i)) by {
                    // Trigger the precondition for this specific a (trigger: a_to_p(a))
                    assert(spec.entails(p.leads_to(always(a_to_p(a)))));
                    // With spec.satisfied_by(ex):
                    assert(p.leads_to(always(a_to_p(a))).satisfied_by(ex));
                    // p.leads_to(q) = always(p.implies(eventually(q)))
                    // always(...).sat(ex) => p.implies(eventually(q)).sat(ex.suffix(i))
                    assert(p.implies(eventually(always(a_to_p(a)))).satisfied_by(ex.suffix(i)));
                    // p.implies(q).sat(ex) and p.sat(ex) => q.sat(ex)
                    implies_apply(ex.suffix(i), p, eventually(always(a_to_p(a))));
                };

                // exists_uniform_always_witness needs:
                // forall a, domain.contains(a) ==> eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i))
                // We have the stronger: forall a, eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i))
                // Build the weaker form:
                assert forall |a: A| domain.contains(a) implies
                    eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i))
                by {
                    // The stronger fact above implies this
                };

                // Find uniform witness delta: forall a in domain, always(a_to_p(a)).sat(ex.suffix(i).suffix(delta))
                exists_uniform_always_witness(ex, i, a_to_p, domain);
                let j: nat = choose |delta: nat| forall |a: A|
                    domain.contains(a) ==>
                    #[trigger] always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(delta));

                // Show always(tla_forall(a_to_p)).satisfied_by(ex.suffix(i).suffix(j))
                assert(always(tla_forall(a_to_p)).satisfied_by(ex.suffix(i).suffix(j))) by {
                    assert forall |k: nat| #[trigger]
                        tla_forall(a_to_p).satisfied_by(ex.suffix(i).suffix(j).suffix(k))
                    by {
                        // tla_forall(a_to_p).sat(ex') = forall a, a_to_p(a).sat(ex')
                        assert forall |a: A| #[trigger]
                            a_to_p(a).satisfied_by(ex.suffix(i).suffix(j).suffix(k))
                        by {
                            assert(domain.contains(a));
                            // always(a_to_p(a)).sat(ex.suffix(i).suffix(j))
                            // = forall k', a_to_p(a).sat(ex.suffix(i).suffix(j).suffix(k'))
                            // with k' = k:
                            assert(always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j)));
                        };
                    };
                };

                // Use witness j for eventually(always(tla_forall(a_to_p)))
                eventually_proved_by_witness(ex.suffix(i), always(tla_forall(a_to_p)), j);
                // Result: eventually(always(tla_forall(a_to_p))).satisfied_by(ex.suffix(i))
            }
        };
    };
}


}
