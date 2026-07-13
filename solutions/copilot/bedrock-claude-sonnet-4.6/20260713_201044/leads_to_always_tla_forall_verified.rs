use vstd::prelude::*;
use vstd::map_lib::*;
use vstd::set::*;

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
proof fn suffix_add<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix((i + j) as nat),
{
    execution_equality(
        ex.suffix(i).suffix(j),
        ex.suffix((i + j) as nat),
    );
}

// Helper: always holds at any later suffix
proof fn always_weaken<T>(ex: Execution<T>, p: TempPred<T>, j_a: nat, j: nat)
    requires
        always(p).satisfied_by(ex.suffix(j_a)),
        j >= j_a,
    ensures
        always(p).satisfied_by(ex.suffix(j)),
{
    let diff = (j - j_a) as nat;
    always_propagate_forwards(ex.suffix(j_a), p, diff);
    suffix_add(ex, j_a, diff);
    assert(j_a + diff == j) by { };
    assert(ex.suffix(j_a).suffix(diff) == ex.suffix(j)) by {
        suffix_add(ex, j_a, diff);
    };
}

// Spec function: compute max witness time for all elements of a finite domain.
// Given: for each a in domain, witness_fn(a) is the time at which always(a_to_p(a)) starts.
// Returns the maximum such witness.
spec fn max_witness_for_domain<A>(domain: Set<A>, witness_fn: spec_fn(A) -> nat) -> nat
    decreases domain.len()
{
    if domain.len() == 0 {
        0
    } else {
        let a = domain.choose();
        let rest = domain.remove(a);
        let w = witness_fn(a);
        let rest_max = max_witness_for_domain(rest, witness_fn);
        if w >= rest_max { w } else { rest_max }
    }
}

// Lemma: for all a in domain, witness_fn(a) <= max_witness_for_domain(domain, witness_fn)
proof fn max_witness_upper_bound<A>(domain: Set<A>, witness_fn: spec_fn(A) -> nat, a: A)
    requires domain.contains(a),
    ensures witness_fn(a) <= max_witness_for_domain(domain, witness_fn),
    decreases domain.len(),
{
    broadcast use lemma_set_choose_len, lemma_set_remove_len;
    let a0 = domain.choose();
    let rest = domain.remove(a0);
    // domain.len() > 0 since it contains a
    assert(domain.len() > 0);
    if a == a0 {
        // witness_fn(a) = witness_fn(a0)
        // max_witness_for_domain(domain, ...) = max(witness_fn(a0), max_witness_for_domain(rest, ...))
        // so witness_fn(a0) <= result
    } else {
        // a is in rest
        assert(rest.contains(a)) by {
            broadcast use lemma_set_remove_different;
        };
        max_witness_upper_bound(rest, witness_fn, a);
        // witness_fn(a) <= max_witness_for_domain(rest, ...) <= result
    }
}

// Helper: always(tla_forall_restricted(a_to_p, domain)) means
// forall a in domain, always(a_to_p(a))
// We need: given witnesses for each a in domain, at the max witness time
// all always(a_to_p(a)) hold simultaneously.

// Key lemma: if for each a in domain, always(a_to_p(a)).satisfied_by(ex.suffix(witness_fn(a)))
// then always(tla_forall(a_to_p)).satisfied_by(ex.suffix(max_witness_for_domain(domain, witness_fn)))
// provided domain covers all of A (i.e., forall a: A, domain.contains(a))
proof fn always_tla_forall_at_max_witness<T, A>(
    ex: Execution<T>,
    a_to_p: spec_fn(A) -> TempPred<T>,
    domain: Set<A>,
    witness_fn: spec_fn(A) -> nat,
)
    requires
        forall |a: A| #[trigger] domain.contains(a),
        forall |a: A| always(a_to_p(a)).satisfied_by(ex.suffix(#[trigger] witness_fn(a))),
    ensures
        always(tla_forall(a_to_p)).satisfied_by(
            ex.suffix(max_witness_for_domain(domain, witness_fn))
        ),
{
    let j = max_witness_for_domain(domain, witness_fn);
    assert forall |k: nat| #[trigger] tla_forall(a_to_p).satisfied_by(ex.suffix(j).suffix(k)) by {
        assert forall |a: A| #[trigger] a_to_p(a).satisfied_by(ex.suffix(j).suffix(k)) by {
            // a is in domain
            assert(domain.contains(a));
            // witness_fn(a) <= j
            max_witness_upper_bound(domain, witness_fn, a);
            let w_a = witness_fn(a);
            // always(a_to_p(a)) holds at ex.suffix(w_a)
            // j >= w_a, so always(a_to_p(a)) holds at ex.suffix(j)
            always_weaken(ex, a_to_p(a), w_a, j);
            // always(a_to_p(a)).satisfied_by(ex.suffix(j))
            // means forall k, a_to_p(a).satisfied_by(ex.suffix(j).suffix(k))
            assert(always(a_to_p(a)).satisfied_by(ex.suffix(j)));
        };
    };
}

// Helper: convert "eventually always" witness from ex.suffix(i) using always_propagate_forwards
// Given: eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i))
// Then: there exists j such that always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j))
// and ex.suffix(i).suffix(j) = ex.suffix(i+j)
proof fn get_always_witness_from_eventually<T>(
    ex: Execution<T>,
    p: TempPred<T>,
    i: nat,
) -> (j: nat)
    requires eventually(always(p)).satisfied_by(ex.suffix(i)),
    ensures always(p).satisfied_by(ex.suffix(i).suffix(j)),
{
    // eventually(always(p)).satisfied_by(ex.suffix(i))
    // means exists j, always(p).satisfied_by(ex.suffix(i).suffix(j))
    let j = choose |j: nat| #[trigger] always(p).satisfied_by(ex.suffix(i).suffix(j));
    j
}

pub proof fn leads_to_always_tla_forall<T, A>(spec: TempPred<T>, p: TempPred<T>, a_to_p: spec_fn(A)->TempPred<T>, domain: Set<A>)
    requires
        forall |a: A| spec.entails(p.leads_to(always(#[trigger] a_to_p(a)))),
        domain.finite(),
        domain.len() > 0,
        forall |a: A| #[trigger] domain.contains(a),
    ensures spec.entails(p.leads_to(always(tla_forall(a_to_p)))),
{
    // We need to show: for all ex satisfying spec,
    // p.leads_to(always(tla_forall(a_to_p))).satisfied_by(ex)
    // i.e., always(p.implies(eventually(always(tla_forall(a_to_p))))).satisfied_by(ex)
    // i.e., forall i, p.satisfied_by(ex.suffix(i)) => eventually(always(tla_forall(a_to_p))).satisfied_by(ex.suffix(i))
    assert forall |ex: Execution<T>| spec.satisfied_by(ex) implies
        p.leads_to(always(tla_forall(a_to_p))).satisfied_by(ex) by {
        // Show: always(p.implies(eventually(always(tla_forall(a_to_p))))).satisfied_by(ex)
        assert forall |i: nat| #[trigger]
            p.implies(eventually(always(tla_forall(a_to_p)))).satisfied_by(ex.suffix(i)) by {
            // Show: if p.satisfied_by(ex.suffix(i)) then eventually(always(tla_forall(a_to_p))).satisfied_by(ex.suffix(i))
            if p.satisfied_by(ex.suffix(i)) {
                // For each a, spec entails p.leads_to(always(a_to_p(a)))
                // so eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i))
                assert forall |a: A| #[trigger] eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i)) by {
                    // spec.entails(p.leads_to(always(a_to_p(a)))) means
                    // forall ex', spec.satisfied_by(ex') => p.leads_to(always(a_to_p(a))).satisfied_by(ex')
                    assert(spec.entails(p.leads_to(always(a_to_p(a)))));
                    // spec.entails(X) = valid(spec.implies(X))
                    // = forall ex', spec.satisfied_by(ex') => X.satisfied_by(ex')
                    // Unfolding entails manually:
                    assert(valid(spec.implies(p.leads_to(always(a_to_p(a))))));
                    assert(spec.implies(p.leads_to(always(a_to_p(a)))).satisfied_by(ex));
                    implies_apply(ex, spec, p.leads_to(always(a_to_p(a))));
                    // Now p.leads_to(always(a_to_p(a))).satisfied_by(ex)
                    // = always(p.implies(eventually(always(a_to_p(a))))).satisfied_by(ex)
                    // so p.implies(eventually(always(a_to_p(a)))).satisfied_by(ex.suffix(i))
                    assert(p.implies(eventually(always(a_to_p(a)))).satisfied_by(ex.suffix(i)));
                    implies_apply(ex.suffix(i), p, eventually(always(a_to_p(a))));
                };
                // For each a, choose witness j_a such that always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j_a))
                // Define witness_fn: A -> nat
                let witness_fn = |a: A| eventually_choose_witness(ex.suffix(i), always(a_to_p(a)));
                // For each a, always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(witness_fn(a)))
                assert forall |a: A| always(a_to_p(a)).satisfied_by(
                    ex.suffix(i).suffix(#[trigger] witness_fn(a))
                ) by {
                    assert(eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i)));
                };
                // Now we need: eventually(always(tla_forall(a_to_p))).satisfied_by(ex.suffix(i))
                // = exists j, always(tla_forall(a_to_p)).satisfied_by(ex.suffix(i).suffix(j))
                // We use j = max_witness_for_domain(domain, witness_fn)
                // But witness_fn is defined in terms of ex.suffix(i) which uses ex and i.
                // We need to "flatten" ex.suffix(i).suffix(j) = ex.suffix(i+j)
                // Let's work with ex_i = ex.suffix(i)
                let ex_i = ex.suffix(i);
                // For each a, always(a_to_p(a)).satisfied_by(ex_i.suffix(witness_fn(a)))
                // Apply always_tla_forall_at_max_witness to ex_i
                let j = max_witness_for_domain(domain, witness_fn);
                always_tla_forall_at_max_witness(ex_i, a_to_p, domain, witness_fn);
                // always(tla_forall(a_to_p)).satisfied_by(ex_i.suffix(j))
                // = always(tla_forall(a_to_p)).satisfied_by(ex.suffix(i).suffix(j))
                eventually_proved_by_witness(ex_i, always(tla_forall(a_to_p)), j);
            }
        };
    };
}


}
