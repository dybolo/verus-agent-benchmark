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

// Helper: instantiate `valid(pred)` at a specific execution
proof fn valid_apply<T>(pred: TempPred<T>, ex: Execution<T>)
    requires valid(pred),
    ensures pred.satisfied_by(ex),
{
    // valid(pred) = forall |ex': Execution<T>| pred.satisfied_by(ex')
    // Trigger: pred.satisfied_by(ex') matches goal pred.satisfied_by(ex) with ex' := ex
}

// Helper: suffix of suffix equals suffix of sum
proof fn suffix_composition<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix(i + j),
{
    assert forall |k: nat| #[trigger] (ex.suffix(i).suffix(j).nat_to_state)(k) == (ex.suffix(i + j).nat_to_state)(k) by {
        // ex.suffix(i).suffix(j).nat_to_state(k) = ex.nat_to_state((k+j)+i)
        // ex.suffix(i+j).nat_to_state(k) = ex.nat_to_state(k+(i+j))
        // (k+j)+i == k+(i+j) by arithmetic
    };
    execution_equality(ex.suffix(i).suffix(j), ex.suffix(i + j));
}

// Helper: spec function computing the max of f over a finite non-empty set
spec fn set_nat_max<A>(s: Set<A>, f: spec_fn(A) -> nat) -> nat
    recommends s.len() > 0,
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        let a = s.choose();
        let rest = s.remove(a);
        if rest.len() == 0 {
            f(a)
        } else {
            let rest_max = set_nat_max(rest, f);
            if f(a) >= rest_max { f(a) } else { rest_max }
        }
    }
}

// Helper: for every element a in a non-empty finite set, f(a) <= set_nat_max
proof fn set_nat_max_ge<A>(s: Set<A>, f: spec_fn(A) -> nat, a: A)
    requires
        s.len() > 0,
        s.contains(a),
    ensures
        f(a) <= set_nat_max(s, f),
    decreases s.len(),
{
    broadcast use lemma_set_choose_len, lemma_set_remove_len, lemma_set_contains_len,
                  lemma_set_remove_different, lemma_set_remove_same;
    let chosen = s.choose();
    let rest = s.remove(chosen);
    if chosen == a {
        // set_nat_max(s, f) is either f(chosen) or max(f(chosen), set_nat_max(rest, f))
        // Either way, set_nat_max(s, f) >= f(chosen) = f(a)
        if rest.len() == 0 {
            assert(set_nat_max(s, f) == f(chosen));
        } else {
            assert(set_nat_max(s, f) >= f(chosen));
        }
    } else {
        // a is in rest = s.remove(chosen)
        assert(rest.contains(a));
        assert(rest.len() > 0);
        // By induction, f(a) <= set_nat_max(rest, f)
        set_nat_max_ge(rest, f, a);
        // set_nat_max(s, f) >= set_nat_max(rest, f) >= f(a)
        assert(set_nat_max(s, f) >= set_nat_max(rest, f));
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
    // Prove: for all ex satisfying spec, p leads_to always(tla_forall(a_to_p)) holds at ex
    assert forall |ex: Execution<T>| spec.satisfied_by(ex) implies
        p.leads_to(always(tla_forall(a_to_p))).satisfied_by(ex) by
    {
        // p.leads_to(always(tla_forall(a_to_p))) = always(p.implies(eventually(always(tla_forall(a_to_p)))))
        // Prove: for all i, p.implies(eventually(always(tla_forall(a_to_p)))).satisfied_by(ex.suffix(i))
        assert forall |i: nat| #[trigger]
            p.implies(eventually(always(tla_forall(a_to_p)))).satisfied_by(ex.suffix(i)) by
        {
            if p.satisfied_by(ex.suffix(i)) {
                // Build the function mapping each a to its eventually-always-witness
                let get_j = |a: A| eventually_choose_witness(ex.suffix(i), always(a_to_p(a)));
                // Compute the max witness index across all a in domain
                let j_star = set_nat_max(domain, get_j);

                // We'll show always(tla_forall(a_to_p)).satisfied_by(ex.suffix(i).suffix(j_star))
                assert forall |k: nat| #[trigger]
                    tla_forall(a_to_p).satisfied_by(ex.suffix(i).suffix(j_star).suffix(k)) by
                {
                    // tla_forall(a_to_p).satisfied_by(e) = forall a, a_to_p(a).satisfied_by(e)
                    assert forall |a: A| #[trigger]
                        a_to_p(a).satisfied_by(ex.suffix(i).suffix(j_star).suffix(k)) by
                    {
                        // --- Step 1: get the entailment hypothesis for this a ---
                        assert(spec.entails(p.leads_to(always(a_to_p(a)))));

                        // --- Step 2: instantiate entailment at ex ---
                        // spec.entails(q) = valid(spec.implies(q))
                        //   => spec.implies(p.leads_to(always(a_to_p(a)))).satisfied_by(ex)
                        //   => (spec.satisfied_by(ex) ==> p.leads_to(always(a_to_p(a))).satisfied_by(ex))
                        //   => p.leads_to(always(a_to_p(a))).satisfied_by(ex)
                        valid_apply(spec.implies(p.leads_to(always(a_to_p(a)))), ex);
                        assert(p.leads_to(always(a_to_p(a))).satisfied_by(ex));

                        // --- Step 3: instantiate leads_to at suffix i ---
                        // p.leads_to(q) = always(p.implies(eventually(q)))
                        //   => p.implies(eventually(always(a_to_p(a)))).satisfied_by(ex.suffix(i))
                        assert(p.implies(eventually(always(a_to_p(a)))).satisfied_by(ex.suffix(i)));

                        // --- Step 4: apply implies with p.satisfied_by(ex.suffix(i)) ---
                        assert(eventually(always(a_to_p(a))).satisfied_by(ex.suffix(i)));

                        // --- Step 5: extract witness j_a ---
                        let j_a = get_j(a);
                        // eventually(q).satisfied_by(ex') = exists j, q.satisfied_by(ex'.suffix(j))
                        assert(exists |j: nat| always(a_to_p(a)).satisfied_by(#[trigger] ex.suffix(i).suffix(j)));
                        // j_a = choose |j| always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j))
                        assert(always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j_a)));

                        // --- Step 6: j_star >= j_a ---
                        set_nat_max_ge(domain, get_j, a);
                        assert(j_a <= j_star);

                        // --- Step 7: propagate always forward from j_a to j_star ---
                        let d: nat = (j_star - j_a) as nat;
                        assert(j_a + d == j_star);
                        always_propagate_forwards(ex.suffix(i).suffix(j_a), a_to_p(a), d);
                        // => always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j_a).suffix(d))

                        // --- Step 8: suffix composition ---
                        suffix_composition(ex.suffix(i), j_a, d);
                        assert(ex.suffix(i).suffix(j_a).suffix(d) == ex.suffix(i).suffix(j_a + d));
                        assert(ex.suffix(i).suffix(j_a + d) == ex.suffix(i).suffix(j_star));

                        // --- Step 9: always at j_star ---
                        assert(always(a_to_p(a)).satisfied_by(ex.suffix(i).suffix(j_star)));

                        // --- Step 10: from always, get value at suffix k ---
                        // always(q).satisfied_by(e) = forall m, q.satisfied_by(e.suffix(m))
                        // => a_to_p(a).satisfied_by(ex.suffix(i).suffix(j_star).suffix(k))
                        assert(a_to_p(a).satisfied_by(ex.suffix(i).suffix(j_star).suffix(k)));
                    };
                    // forall a, a_to_p(a).satisfied_by(...) => tla_forall satisfied
                };
                // always(tla_forall(a_to_p)).satisfied_by(ex.suffix(i).suffix(j_star))
                assert(always(tla_forall(a_to_p)).satisfied_by(ex.suffix(i).suffix(j_star)));
                // => eventually(always(tla_forall(a_to_p))).satisfied_by(ex.suffix(i))
                eventually_proved_by_witness(ex.suffix(i), always(tla_forall(a_to_p)), j_star);
            }
        };
    };
}


}
