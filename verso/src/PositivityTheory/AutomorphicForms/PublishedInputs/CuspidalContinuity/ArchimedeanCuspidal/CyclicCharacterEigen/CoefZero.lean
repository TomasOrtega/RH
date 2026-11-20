import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.PropEG

noncomputable section

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

namespace Ad3P.EigenformCoefficientExpansion

/- English proof (translation)
Establish `hp : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods` using `by simp`. Establish `h` using `hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hp) f.holo' (ModularFormClass.bdd_at_infty f) τ`. Use `cast (congrArg (HasSum · (f τ)) (funext fun n => ?_)) h` and prove the remaining obligations. Rewrite using `[smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul, coef]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_of {k N : ℕ} [NeZero N] (f : CuspForm (Gamma1 N) (k : ℤ)) (τ : ℍ) :
    HasSum (fun n : ℕ => coef f n * Complex.exp (2 * Real.pi * Complex.I * n * τ)) (f τ) := by
  have hp : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have h := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hp)
    f.holo' (ModularFormClass.bdd_at_infty f) τ
  refine cast (congrArg (HasSum · (f τ)) (funext fun n => ?_)) h
  rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul, coef]
  congr 2
  push_cast
  ring

/- English proof (translation)
Establish `hp : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods` using `by simp`. Conclude with `CuspFormClass.qExpansion_coeff_zero f one_pos hp`.
-/
theorem coef_zero {k N : ℕ} [NeZero N] (f : CuspForm (Gamma1 N) (k : ℤ)) : coef f 0 = 0 := by
  have hp : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  exact CuspFormClass.qExpansion_coeff_zero f one_pos hp

end Ad3P.EigenformCoefficientExpansion

open Ad3P.EigenformCoefficientExpansion in
/- English proof (translation)
Introduce `k N _ _ χ g`. Use `⟨⟨fun γ hγ => g.char γ hγ, fun τ => exp_of g.f τ⟩, coef_zero g.f, g.one, fun p n hp => ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `only [Eigenform.a, mul_zero, dvd_zero, if_true, Nat.zero_div, coef_zero, add_zero]`. Establish `h` using `g.eig p hp n hn`.

Simplify using `only [Eigenform.a]`. Rewrite using `[← h]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem Ad3P.sEig : Ad3P.SEig := by
  intro k N _ _ χ g
  refine ⟨⟨fun γ hγ => g.char γ hγ, fun τ => exp_of g.f τ⟩, coef_zero g.f, g.one, fun p n hp => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Eigenform.a, mul_zero, dvd_zero, if_true, Nat.zero_div, coef_zero, add_zero]
  · have h := g.eig p hp n hn
    simp only [Eigenform.a]
    rw [← h]
    split_ifs <;> ring
