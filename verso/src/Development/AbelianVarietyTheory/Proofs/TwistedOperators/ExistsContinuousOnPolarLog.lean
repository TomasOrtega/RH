import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarLogCont

section
open scoped Matrix.Norms.L2Operator ComplexOrder
variable {n : Type} [Fintype n] [DecidableEq n]

def halfLog (g : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℝ) • CFC.log (gᴴ * g)

/- English proof (translation)
Establish `h : ContinuousOn (fun g : Matrix n n ℂ => CFC.log (gᴴ * g)) {g | IsUnit g}`. Use `CFC.continuousOn_log.comp (by fun_prop) ?_` and prove the remaining obligations. Introduce `g hg`. Establish `hu : IsUnit g` using `hg`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `show star (gᴴ * g) = gᴴ * g`. Rewrite using `[star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]`. Conclude with `(show IsUnit gᴴ from hu.star).mul hu`. Conclude with `h.const_smul (1 / 2 : ℝ)`.
-/
theorem continuousOn_halfLog : ContinuousOn (halfLog (n := n)) {g | IsUnit g} := by
  have h : ContinuousOn (fun g : Matrix n n ℂ => CFC.log (gᴴ * g)) {g | IsUnit g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    have hu : IsUnit g := hg
    refine ⟨?_, ?_⟩
    · show star (gᴴ * g) = gᴴ * g
      rw [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
    · exact (show IsUnit gᴴ from hu.star).mul hu
  exact h.const_smul (1 / 2 : ℝ)

/- English proof (translation)
Establish `he : (NormedSpace.exp Y)ᴴ = NormedSpace.exp Y`. Rewrite using `[← Matrix.exp_conjTranspose, hY]`. Establish `h2 : NormedSpace.exp (Y + Y) = NormedSpace.exp Y * NormedSpace.exp Y` using `Matrix.exp_add_of_commute _ _ (Commute.refl Y)`. Establish `sq : (c * NormedSpace.exp Y)ᴴ * (c * NormedSpace.exp Y) = NormedSpace.exp (Y + Y)`. Rewrite using `[conjTranspose_mul, he, h2]`.

Combine the equalities or inequalities in the displayed calculation. Use `_ = _ := by rw [hc, Matrix.mul_one]`. Establish `hsa : IsSelfAdjoint (Y + Y)`. Rewrite using `[IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_add, hY]`. Unfold `halfLog`.

Rewrite using `[sq, CFC.log_exp _ hsa, ← two_smul ℝ Y, smul_smul]`. Evaluate the numerical expressions.
-/
theorem halfLog_mul_exp (c Y : Matrix n n ℂ) (hc : cᴴ * c = 1) (hY : Yᴴ = Y) :
    halfLog (c * NormedSpace.exp Y) = Y := by
  have he : (NormedSpace.exp Y)ᴴ = NormedSpace.exp Y := by
    rw [← Matrix.exp_conjTranspose, hY]
  have h2 : NormedSpace.exp (Y + Y) = NormedSpace.exp Y * NormedSpace.exp Y :=
    Matrix.exp_add_of_commute _ _ (Commute.refl Y)
  have sq : (c * NormedSpace.exp Y)ᴴ * (c * NormedSpace.exp Y) = NormedSpace.exp (Y + Y) := by
    rw [conjTranspose_mul, he, h2]
    calc NormedSpace.exp Y * cᴴ * (c * NormedSpace.exp Y)
        = NormedSpace.exp Y * (cᴴ * c) * NormedSpace.exp Y := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hc, Matrix.mul_one]
  have hsa : IsSelfAdjoint (Y + Y) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_add, hY]
  unfold halfLog
  rw [sq, CFC.log_exp _ hsa, ← two_smul ℝ Y, smul_smul]
  norm_num

end

/- English proof (translation)
Introduce `p q`. Use `⟨fun g i j => halfLog g (Sum.inl i) (Sum.inr j), ?_, ?_⟩` and prove the remaining obligations. Establish `hc : Continuous fun (M : Mat p q) (i : Fin p) (j : Fin q) => M (Sum.inl i) (Sum.inr j)` using `by fun_prop`. Conclude with `hc.comp_continuousOn continuousOn_halfLog`. Introduce `k B hk`.

Use function extensionality and compare the values at `i j`. Use `show halfLog (k * NormedSpace.exp (pY B)) (Sum.inl i) (Sum.inr j) = B i j`. Rewrite using `[halfLog_mul_exp k _ hk (pY_conjTranspose B)]`. Simplify using `[pY, pOf]`.
-/
theorem exists_continuousOn_polar_log : ∀ (p q : ℕ), ∃ L : Mat p q → (Fin p → Fin q → ℂ), ContinuousOn L {g | IsUnit g} ∧ ∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B := by
  intro p q
  refine ⟨fun g i j => halfLog g (Sum.inl i) (Sum.inr j), ?_, ?_⟩
  · have hc : Continuous fun (M : Mat p q) (i : Fin p) (j : Fin q) => M (Sum.inl i) (Sum.inr j) := by
      fun_prop
    exact hc.comp_continuousOn continuousOn_halfLog
  · intro k B hk
    funext i j
    show halfLog (k * NormedSpace.exp (pY B)) (Sum.inl i) (Sum.inr j) = B i j
    rw [halfLog_mul_exp k _ hk (pY_conjTranspose B)]
    simp [pY, pOf]

end GlobalTheory.PolarLogCont
