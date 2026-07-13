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

    pub open spec fn or(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) || other.satisfied_by(ex))
    }

    pub open spec fn implies(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) ==> other.satisfied_by(ex))
    }

}


pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn eventually<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| exists |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn later<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| temp_pred.satisfied_by(ex.suffix(1)))
}

pub open spec fn not<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| !temp_pred.satisfied_by(ex))
}


// File: rules.rs
	#[verifier::external_body]
proof fn later_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires later(p).satisfied_by(ex),
    ensures p.satisfied_by(ex.suffix(1)),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn always_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires always(p).satisfied_by(ex),
    ensures forall |i: nat| p.satisfied_by(#[trigger] ex.suffix(i)),
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn not_eventually_unfold<T>(ex: Execution<T>, p: TempPred<T>)
    requires not(eventually(p)).satisfied_by(ex),
    ensures forall |i| !p.satisfied_by(#[trigger] ex.suffix(i))
	{
		unimplemented!()
	}

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
proof fn always_p_or_eventually_q_rec<T>(ex: Execution<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>, i: nat)
    requires
        forall |idx| p.satisfied_by(ex.suffix(idx)) && next.satisfied_by(ex.suffix(idx)) ==> p.satisfied_by(ex.suffix(idx + 1)) || q.satisfied_by(ex.suffix(idx + 1)),
        forall |idx| next.satisfied_by(#[trigger] ex.suffix(idx)),
        forall |idx| !q.satisfied_by(#[trigger] ex.suffix(idx)),
        p.satisfied_by(ex),
    ensures p.satisfied_by(ex.suffix(i)),
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn execution_equality<T>(ex1: Execution<T>, ex2: Execution<T>)
    requires forall |i: nat| #[trigger] (ex1.nat_to_state)(i) == (ex2.nat_to_state)(i),
    ensures ex1 == ex2,
	{
		unimplemented!()
	}

proof fn suffix_add<T>(ex: Execution<T>, i: nat, j: nat)
    ensures ex.suffix(i).suffix(j) == ex.suffix((i + j) as nat)
{
    execution_equality(ex.suffix(i).suffix(j), ex.suffix((i + j) as nat));
}

// Core helper: if p holds at ex.suffix(i) and q never holds anywhere from ex.suffix(i),
// then p always holds from ex.suffix(i)
proof fn p_implies_always_p<T>(ex: Execution<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>, i: nat)
    requires
        always(p.and(next).implies(later(p).or(later(q)))).satisfied_by(ex),
        always(next).satisfied_by(ex),
        not(eventually(q)).satisfied_by(ex.suffix(i)),
        p.satisfied_by(ex.suffix(i)),
    ensures always(p).satisfied_by(ex.suffix(i)),
{
    not_eventually_unfold(ex.suffix(i), q);

    always_unfold(ex, p.and(next).implies(later(p).or(later(q))));

    always_unfold(ex, next);

    assert forall |j: nat| next.satisfied_by(#[trigger] ex.suffix(i).suffix(j)) by {
        suffix_add(ex, i, j);
    };

    assert forall |idx: nat| p.satisfied_by(ex.suffix(i).suffix(idx)) && next.satisfied_by(ex.suffix(i).suffix(idx)) implies p.satisfied_by(ex.suffix(i).suffix(idx + 1)) || q.satisfied_by(ex.suffix(i).suffix(idx + 1)) by {
        suffix_add(ex, i, idx);
        suffix_add(ex, i, (idx + 1) as nat);
        let k: nat = (i + idx) as nat;
        let implied = later(p).or(later(q));
        assert(p.satisfied_by(ex.suffix(k)));
        assert(next.satisfied_by(ex.suffix(k)));
        assert(p.and(next).satisfied_by(ex.suffix(k)));
        implies_apply(ex.suffix(k), p.and(next), implied);
        suffix_add(ex, k, 1);
        assert(ex.suffix(k).suffix(1) == ex.suffix((k + 1) as nat));
        assert(ex.suffix(i).suffix((idx + 1) as nat) == ex.suffix((i + idx + 1) as nat));
        assert((k + 1) as nat == (i + idx + 1) as nat);
        assert(later(p).satisfied_by(ex.suffix(k)) || later(q).satisfied_by(ex.suffix(k)));
        if later(p).satisfied_by(ex.suffix(k)) {
            later_unfold(ex.suffix(k), p);
            assert(p.satisfied_by(ex.suffix(k).suffix(1)));
            assert(ex.suffix(k).suffix(1) == ex.suffix(i).suffix((idx + 1) as nat));
        } else {
            assert(later(q).satisfied_by(ex.suffix(k)));
            later_unfold(ex.suffix(k), q);
            assert(q.satisfied_by(ex.suffix(k).suffix(1)));
            assert(ex.suffix(k).suffix(1) == ex.suffix(i).suffix((idx + 1) as nat));
        }
    };

    assert forall |j: nat| p.satisfied_by(#[trigger] ex.suffix(i).suffix(j)) by {
        always_p_or_eventually_q_rec(ex.suffix(i), next, p, q, j);
    };

    assert(always(p).satisfied_by(ex.suffix(i)));
}

proof fn always_p_or_eventually_q<T>(ex: Execution<T>, next: TempPred<T>, p: TempPred<T>, q: TempPred<T>)
    requires
        always(p.and(next).implies(later(p).or(later(q)))).satisfied_by(ex),
        always(next).satisfied_by(ex),
    ensures always(p.implies(always(p).or(eventually(q)))).satisfied_by(ex),
{
    assert forall |i: nat| p.implies(always(p).or(eventually(q))).satisfied_by(#[trigger] ex.suffix(i)) by {
        always_propagate_forwards(ex, p.and(next).implies(later(p).or(later(q))), i);
        always_propagate_forwards(ex, next, i);

        if p.satisfied_by(ex.suffix(i)) {
            if not(eventually(q)).satisfied_by(ex.suffix(i)) {
                p_implies_always_p(ex, next, p, q, i);
                assert(always(p).satisfied_by(ex.suffix(i)));
                assert(always(p).or(eventually(q)).satisfied_by(ex.suffix(i)));
            } else {
                assert(eventually(q).satisfied_by(ex.suffix(i)));
                assert(always(p).or(eventually(q)).satisfied_by(ex.suffix(i)));
            }
        }
    };
}

}
