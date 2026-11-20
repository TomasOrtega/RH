import Mathlib
import Formalism.PeriodIntegrals.RowLetter
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.Development

open MvPolynomial

noncomputable section

namespace PI.RL.W

open PI.RL

section

variable {K : Type} [Field K] {k : ℕ}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem RE_add (a b : Fin k) (f g : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b (f + g) = RE K k a b f + RE K k a b g := by
  simp only [PI.RL.RE, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem RE_C (a b : Fin k) (r : K) : RE K k a b (C r) = 0 := by
  simp [PI.RL.RE]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem pderiv_mul_eq {σ : Type*} {R : Type*} [CommRing R] (i : σ) (f g : MvPolynomial σ R) :
    pderiv i (f * g) = pderiv i f * g + f * pderiv i g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem RE_mul (a b : Fin k) (f g : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b (f * g) = RE K k a b f * g + f * RE K k a b g := by
  simp only [PI.RL.RE, pderiv_mul_eq, mul_add, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum]
  congr 1 <;> (refine Finset.sum_congr rfl (fun t _ => ?_); ring)

end

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private theorem pderiv_X_eq_ite {σ : Type*} {R : Type*} [CommRing R] [DecidableEq σ] (c i : σ) :
    pderiv c (X i : MvPolynomial σ R) = if c = i then 1 else 0 := by
  rw [pderiv_X]
  by_cases h : c = i
  · subst h; simp
  · rw [if_neg h, Pi.single_apply, if_neg (Ne.symm h)]

/- English proof (translation)
Proceed by induction. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
private theorem derivation_aeval_eq_sum_pderiv {K : Type*} [CommRing K] {σ τ : Type*} [Fintype σ] [DecidableEq σ]
    (D : MvPolynomial τ K → MvPolynomial τ K)
    (hadd : ∀ f g, D (f + g) = D f + D g) (hC : ∀ r, D (C r) = 0)
    (hmul : ∀ f g, D (f * g) = D f * g + f * D g)
    (g : σ → MvPolynomial τ K) (P : MvPolynomial σ K) :
    D (aeval g P) = ∑ c, aeval g (pderiv c P) * D (g c) := by
  induction P using MvPolynomial.induction_on
  next r =>
    rw [aeval_C, MvPolynomial.algebraMap_eq, hC]
    simp
  next p q hp hq =>
    rw [map_add, hadd, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [map_add, map_add, add_mul]
  next p i ih =>
    have e : ∀ c, aeval g (pderiv c (p * X i)) * D (g c) =
        g i * (aeval g (pderiv c p) * D (g c)) + (if c = i then aeval g p * D (g i) else 0) := by
      intro c
      rw [pderiv_mul_eq, pderiv_X_eq_ite, map_add, map_mul, map_mul, aeval_X]
      by_cases h : c = i
      · subst h; rw [if_pos rfl, if_pos rfl, map_one]; ring
      · rw [if_neg h, if_neg h, map_zero]; ring
    rw [Finset.sum_congr rfl (fun c _ => e c), Finset.sum_add_distrib, ← Finset.mul_sum, ← ih,
      map_mul, aeval_X, hmul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem chainRule : ChainRule := by
  intro K _ m vec a b P
  simp only [PI.RL.theta]
  exact derivation_aeval_eq_sum_pderiv (PI.RL.RE K (m + 1) a b) (RE_add a b) (RE_C a b)
    (RE_mul a b) _ P

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem vecX : VecX := by
  intro K _ m a b c
  have hp : ∀ t : Fin (m + 1),
      pderiv (b, t) (X (c, 0) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) =
        if c = b ∧ t = 0 then 1 else 0 := by
    intro t
    rw [pderiv_X]
    by_cases h : c = b ∧ t = 0
    · obtain ⟨rfl, rfl⟩ := h; simp
    · rw [if_neg h, Pi.single_apply, if_neg]
      intro he
      simp only [Prod.mk.injEq] at he
      exact h ⟨he.1, he.2.symm⟩
  simp only [PI.RL.Nv, if_true, PI.RL.RE, hp, mul_ite, mul_one, mul_zero]
  by_cases h : c = b
  · subst h; simp [Finset.sum_ite_eq']
  · simp [h]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem hdHom : HdHom := by
  intro K _ k d P hP
  unfold PI.RL.Hd at hP
  rw [mem_restrictSupport_iff] at hP
  intro μ hμ
  have h2 := hP (mem_support_iff.mpr hμ)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simpa using h2

end PI.RL.W
