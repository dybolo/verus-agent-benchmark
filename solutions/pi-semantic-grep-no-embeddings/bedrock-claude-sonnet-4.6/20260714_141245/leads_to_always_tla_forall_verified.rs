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

// Helper: ex.suffix(a).suffix(b) == ex.suffix(a + b)
proof fn suffix_add<T>(ex: Execution<T>, a: nat, b: nat)
    ensures ex.suffix(a).suffix(b) == ex.suffix(a + b),
{
    assert forall |i: nat|
        #[trigger] (ex.suffix(a).suffix(b).nat_to_state)(i) == (ex.suffix(a + b).nat_to_state)(i)
    by {
        // LHS: ex.nat_to_state(i + b + a)
        // RHS: ex.nat_to_state(i + (a + b))
        // These are equal by nat arithmetic
    };
    execution_equality(ex.suffix(a).suffix(b), ex.suffix(a + b));
}

// Helper: if always(p) holds at ex.suffix(j1), and j1 <= j2, then always(p) holds at ex.suffix(j2)
proof fn always_weaken<T>(ex: Execution<T>, p: TempPred<T>, j1: nat, j2: nat)
    requires
        always(p).satisfied_by(ex.suffix(j1)),
        j1 <= j2,
    ensures always(p).satisfied_by(ex.suffix(j2)),
    decreases j2 - j1,
{
    if j1 == j2 {
        // trivial: ex.suffix(j1) == ex.suffix(j2)
    } else {
        // j2 > j1 >= 0, so j2 >= 1
        let j2m1: nat = (j2 - 1) as nat;
        // j1 <= j2m1 since j2 > j1 implies j2 >= j1 + 1, so j2 - 1 >= j1
        assert(j1 <= j2m1);
        // Inductive step: first get to j2 - 1
        always_weaken(ex, p, j1, j2m1);
        // have: always(p).satisfied_by(ex.suffix(j2m1))
        // Now propagate one more step
        always_propagate_forwards(ex.suffix(j2m1), p, 1);
        // have: always(p).satisfied_by(ex.suffix(j2m1).suffix(1))
        suffix_add(ex, j2m1, 1);
        // have: ex.suffix(j2m1).suffix(1) == ex.suffix(j2m1 + 1)
        assert(j2m1 + 1 == j2);
        assert(ex.suffix(j2m1).suffix(1) == ex.suffix(j2));
    }
}

// Spec fn: compute max witness index for all elements in domain
spec fn witnesses_max<T, A>(
    ex: Execution<T>,
    a_to_p: spec_fn(A) -> TempPred<T>,
    domain: Set<A>,
) -> nat
    decreases domain.len(),
{
    if domain.len() == 0 {
        0
    } else {
        let a = domain.choose();
        let j = eventually_choose_witness(ex, always(a_to_p(a)));
        let j_rest = witnesses_max(ex, a_to_p, domain.remove(a));
        if j >= j_rest { j } else { j_rest }
    }
}

// Key inductive lemma: witnesses_max gives a valid common witness index
proof fn witnesses_max_spec<T, A>(
    ex: Execution<T>,
    a_to_p: spec_fn(A) -> TempPred<T>,
    domain: Set<A>,
)
    requires
        domain.len() > 0,
        forall |a: A| #[trigger] domain.contains(a) ==>
            eventually(always(a_to_p(a))).satisfied_by(ex),
    ensures
        forall |a: A| #[trigger] domain.contains(a) ==>
            always(a_to_p(a)).satisfied_by(ex.suffix(witnesses_max(ex, a_to_p, domain))),
    decreases domain.len(),
{
    broadcast use vstd::set::group_set_lemmas;

    let j_max = witnesses_max(ex, a_to_p, domain);
    let a0 = domain.choose();
    // domain.len() > 0 implies a0 is in domain
    assert(domain.contains(a0));

    let j0 = eventually_choose_witness(ex, always(a_to_p(a0)));
    // Since eventually(always(a_to_p(a0))).satisfied_by(ex) and j0 is the witness:
    assert(always(a_to_p(a0)).satisfied_by(ex.suffix(j0)));

    let rest = domain.remove(a0);

    if domain.len() == 1 {
        assert(rest.len() == 0);
        // witnesses_max(ex, a_to_p, rest) = 0 because rest.len() == 0
        // j_max = if j0 >= 0 { j0 } else { 0 } = j0 (since j0: nat >= 0)
        assert(witnesses_max(ex, a_to_p, rest) == 0);
        assert(j_max == j0);

        assert forall |a: A| #[trigger] domain.contains(a) implies
            always(a_to_p(a)).satisfied_by(ex.suffix(j_max)) by {
            // domain has exactly one element: a0
            // any a in domain must equal a0
            if a != a0 {
                // If a != a0 and domain.contains(a), then rest.contains(a)
                assert(rest.contains(a));
                // But rest has length 0, so it's empty
                rest.lemma_len0_is_empty();
                // Contradiction: rest is empty but rest.contains(a)
                assert(false);
            }
            // a == a0, and we know always(a_to_p(a0)).satisfied_by(ex.suffix(j_max))
        };
    } else {
        // domain.len() >= 2
        assert(rest.len() > 0);
        assert(rest.len() < domain.len());

        // The precondition for rest: for a in rest, domain.contains(a) (since rest subset domain)
        assert forall |a: A| #[trigger] rest.contains(a) implies
            eventually(always(a_to_p(a))).satisfied_by(ex) by {
            // rest.contains(a) implies domain.contains(a)
            assert(domain.contains(a));
        };

        // Apply induction hypothesis on rest
        witnesses_max_spec(ex, a_to_p, rest);
        let j_rest = witnesses_max(ex, a_to_p, rest);

        // j_max = max(j0, j_rest)
        assert(j_max == (if j0 >= j_rest { j0 } else { j_rest }));
        assert(j_max >= j0);
        assert(j_max >= j_rest);

        // always(a_to_p(a0)) holds from j0, and j_max >= j0, so it holds from j_max
        always_weaken(ex, a_to_p(a0), j0, j_max);

        assert forall |a: A| #[trigger] domain.contains(a) implies
            always(a_to_p(a)).satisfied_by(ex.suffix(j_max)) by {
            if a == a0 {
                // handled by always_weaken above
            } else {
                // a is in rest
                assert(rest.contains(a));
                // By IH: always(a_to_p(a)).satisfied_by(ex.suffix(j_rest))
                assert(always(a_to_p(a)).satisfied_by(ex.suffix(j_rest)));
                // j_max >= j_rest, so propagate forward
                always_weaken(ex, a_to_p(a), j_rest, j_max);
            }
        };
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
    // We prove: for all ex satisfying spec, p.leads_to(always(tla_forall(a_to_p))).satisfied_by(ex)
    assert forall |ex: Execution<T>| spec.satisfied_by(ex) implies
        p.leads_to(always(tla_forall(a_to_p))).satisfied_by(ex) by {

        // p.leads_to(always(tla_forall(a_to_p))) = always(p.implies(eventually(always(tla_forall(a_to_p)))))
        // We need: for all i, p.implies(eventually(always(tla_forall(a_to_p)))).satisfied_by(ex.suffix(i))
        assert forall |i: nat|
            #[trigger] p.implies(eventually(always(tla_forall(a_to_p)))).satisfied_by(ex.suffix(i)) by {

            if p.satisfied_by(ex.suffix(i)) {
                let ex_i = ex.suffix(i);

                // Step 1: For each a in domain, get eventually(always(a_to_p(a))).satisfied_by(ex_i)
                assert forall |a: A| #[trigger] domain.contains(a) implies
                    eventually(always(a_to_p(a))).satisfied_by(ex_i) by {
                    // From hypothesis: spec.entails(p.leads_to(always(a_to_p(a))))
                    // = valid(spec.implies(always(p.implies(eventually(always(a_to_p(a)))))))
                    let hyp_a = p.leads_to(always(a_to_p(a)));
                    assert(spec.entails(hyp_a));
                    // spec.satisfied_by(ex) and entails means hyp_a.satisfied_by(ex)
                    assert(spec.implies(hyp_a).satisfied_by(ex));
                    implies_apply(ex, spec, hyp_a);
                    assert(hyp_a.satisfied_by(ex));
                    // hyp_a = always(p.implies(eventually(always(a_to_p(a)))))
                    // at suffix i:
                    assert(p.implies(eventually(always(a_to_p(a)))).satisfied_by(ex_i));
                    // p holds at ex_i, so:
                    implies_apply(ex_i, p, eventually(always(a_to_p(a))));
                };

                // Step 2: Use witnesses_max to get a common witness j_max
                let j_max = witnesses_max(ex_i, a_to_p, domain);
                witnesses_max_spec(ex_i, a_to_p, domain);
                // Now: for all a in domain, always(a_to_p(a)).satisfied_by(ex_i.suffix(j_max))

                // Step 3: Show always(tla_forall(a_to_p)).satisfied_by(ex_i.suffix(j_max))
                assert(always(tla_forall(a_to_p)).satisfied_by(ex_i.suffix(j_max))) by {
                    assert forall |k: nat|
                        #[trigger] tla_forall(a_to_p).satisfied_by(ex_i.suffix(j_max).suffix(k)) by {
                        assert forall |a: A| #[trigger] a_to_p(a).satisfied_by(ex_i.suffix(j_max).suffix(k)) by {
                            // a is in domain (precondition: forall a, domain.contains(a))
                            assert(domain.contains(a));
                            // always(a_to_p(a)).satisfied_by(ex_i.suffix(j_max))
                            assert(always(a_to_p(a)).satisfied_by(ex_i.suffix(j_max)));
                            // so a_to_p(a).satisfied_by(ex_i.suffix(j_max).suffix(k))
                        };
                    };
                };

                // Step 4: Use eventually_proved_by_witness with witness j_max
                eventually_proved_by_witness(ex_i, always(tla_forall(a_to_p)), j_max);
            }
        };
    };
}


}
