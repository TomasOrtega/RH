import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CasimirPowerCommute

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `hM : ∀ i j, Mm E i j = E i j` using `fun _ _ => rfl`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `a b`.

Simplify using `only [pow_zero, Matrix.one_apply]`. Establish `h0 : (if d = a then (if c = b then (1 : Module.End ℂ V) else 0) else 0) = (if b = c then (if a = d then 1 else 0) else 0)`. Distinguish the cases in `h2 : d = a`. Substitute `h2` using the available equality. Distinguish the cases in `h3 : b = c`.

Substitute `h3` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h3, Ne.symm h3]`. Simplify using `[h2, Ne.symm h2]`. Rewrite using `[h0, sub_self]`.

Apply the tactic sequence `split_ifs <;> simp`. Consider the case `succ k ih`. Introduce `a b`. Establish `key : ∀ j, E c d * ((Mm E ^ k) a j * E j b) - ((Mm E ^ k) a j * E j b) * E c d = (E c d * (Mm E ^ k) a j - (Mm E ^ k) a j * E c d) * E j b + (Mm E ^ k) a j * (E c d * E j b - E j b * E c d)`. Introduce `j`.

Use `noncomm_ring`. Simplify using `only [pow_succ, Matrix.mul_apply, hM]`. Rewrite using `[Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Simplify using `only [key, ih, hE c d]`. Simplify using `only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Apply the tactic sequence `by_cases h1 : d = a <;> by_cases h2 : b = c <;> simp [h1, h2] <;> abel`.
-/
theorem comm_pow (E : Fin n → Fin n → Module.End ℂ V) (hE : IsGlRep E) (c d : Fin n) :
    ∀ (k : ℕ) (a b : Fin n), E c d * (Mm E ^ k) a b - (Mm E ^ k) a b * E c d =
      (if d = a then (Mm E ^ k) c b else 0) - (if b = c then (Mm E ^ k) a d else 0) := by
  have hM : ∀ i j, Mm E i j = E i j := fun _ _ => rfl
  intro k
  induction k with
  | zero =>
    intro a b
    simp only [pow_zero, Matrix.one_apply]
    have h0 : (if d = a then (if c = b then (1 : Module.End ℂ V) else 0) else 0) =
        (if b = c then (if a = d then 1 else 0) else 0) := by
      by_cases h2 : d = a
      · subst h2
        by_cases h3 : b = c
        · subst h3; simp
        · simp [h3, Ne.symm h3]
      · simp [h2, Ne.symm h2]
    rw [h0, sub_self]
    split_ifs <;> simp
  | succ k ih =>
    intro a b
    have key : ∀ j, E c d * ((Mm E ^ k) a j * E j b) - ((Mm E ^ k) a j * E j b) * E c d
        = (E c d * (Mm E ^ k) a j - (Mm E ^ k) a j * E c d) * E j b
          + (Mm E ^ k) a j * (E c d * E j b - E j b * E c d) := by
      intro j; noncomm_ring
    simp only [pow_succ, Matrix.mul_apply, hM]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [key, ih, hE c d]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h1 : d = a <;> by_cases h2 : b = c <;> simp [h1, h2] <;> abel

end CasimirPowerCommute

/- English proof (translation)
Introduce `n ε V _ _ E h k c d`. Establish `hc` using `CasimirPowerCommute.comm_pow E h.gl c d k`. Rewrite using `[← sub_eq_zero, Matrix.trace, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Simplify using `only [Matrix.diag_apply, hc, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]`.
-/
theorem gelfand_central_holds : A2 := by
  intro n ε V _ _ E h k c d
  have hc := CasimirPowerCommute.comm_pow E h.gl c d k
  rw [← sub_eq_zero, Matrix.trace, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [Matrix.diag_apply, hc, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self]

end PositivityTheory.CW

end
