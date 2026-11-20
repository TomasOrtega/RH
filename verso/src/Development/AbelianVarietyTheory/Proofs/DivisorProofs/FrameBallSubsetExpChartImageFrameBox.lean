import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.BallCover

section Exp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `h` using `(hasFDerivAt_iff_isLittleO_nhds_zero.1 (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt).def (by norm_num : (0 : ℝ) < 1 / 2)`. Take `⟨δ, hδ, hh⟩` from `Metric.eventually_nhds_iff.1 h`. Use `⟨δ, hδ, fun Y hY => ?_⟩` and prove the remaining obligations. Use `hh (y := Y) (by rwa [dist_zero_right])` as an intermediate fact. Simplify using `only [zero_add, NormedSpace.exp_zero] at this`.

Establish `h1 : ‖NormedSpace.exp Y - 1 - Y‖ ≤ 1 / 2 * ‖Y‖` using `this`. Establish `h2 : ‖Y‖ ≤ ‖NormedSpace.exp Y - 1‖ + ‖NormedSpace.exp Y - 1 - Y‖`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_exp_lower (n : Type) [Fintype n] [DecidableEq n] :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < ρ → ‖Y‖ ≤ 2 * ‖NormedSpace.exp Y - 1‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1
    (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt).def (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun Y hY => ?_⟩
  have := hh (y := Y) (by rwa [dist_zero_right])
  simp only [zero_add, NormedSpace.exp_zero] at this
  have h1 : ‖NormedSpace.exp Y - 1 - Y‖ ≤ 1 / 2 * ‖Y‖ := this
  have h2 : ‖Y‖ ≤ ‖NormedSpace.exp Y - 1‖ + ‖NormedSpace.exp Y - 1 - Y‖ := by
    calc ‖Y‖ = ‖(NormedSpace.exp Y - 1) - (NormedSpace.exp Y - 1 - Y)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith

end Exp

section Main

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `E _ _ _ r Ψ G x hG hx δ hδ`. Take `⟨ρ, hρ, hexp⟩` from `exists_exp_lower (Fin r)`. Set `cj : (Ψ → Fin r → Fin r → ℂ) → (Ψ → Matrix (Fin r) (Fin r) ℂ)` to `fun X τ => (mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ`. Establish `hcj : Continuous cj` using `continuous_pi fun τ => (continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const`. Set `U : Set (realLie Ψ G)` to `{X | ‖X‖ < δ ∧ ∀ τ, ‖cj X.1 τ‖ < ρ}`.

Establish `hU : U ∈ nhds 0`. Use `IsOpen.mem_nhds ?_ ?_` and prove the remaining obligations. Use `(isOpen_lt continuous_norm continuous_const).inter ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsOpen {X : realLie Ψ G | ∀ τ, ‖cj X.1 τ‖ < ρ}`. Rewrite using `[Set.setOf_forall]`.

Conclude with `isOpen_iInter_of_finite fun τ => isOpen_lt ((continuous_apply τ).comp (hcj.comp continuous_subtype_val)).norm continuous_const`. Use `⟨by simpa using hδ, fun τ => ?_⟩` and prove the remaining obligations. Establish `e : cj (0 : realLie Ψ G).1 τ = 0`. Express the relevant statement in the definitionally equal form `(mat x τ)⁻¹ * (0 : Matrix (Fin r) (Fin r) ℂ) * mat x τ = 0`. Simplify using the standard rewrite rules.

Rewrite using `[e, norm_zero]`. Conclude with `hρ`. Establish `hev` using `GlobalTheory.SUVol.DensOne.eventually_mem_image Ψ G hG hU`. Rewrite `hev` using `[Filter.eventually_comap]`. Take `⟨η, hη, hh⟩` from `Metric.eventually_nhds_iff.1 hev`.

Set `bk : (Ψ → Matrix (Fin r) (Fin r) ℂ) → (Ψ → Matrix (Fin r) (Fin r) ℂ)` to `fun A τ => mat x τ * A τ * (mat x τ)⁻¹`. Establish `hbk : Continuous bk` using `continuous_pi fun τ => (continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const`. Establish `hbk0 : bk 0 = 0` using `by funext τ; simp [bk]`. Take `⟨ε₁, hε₁, hbkε⟩` from `Metric.continuous_iff.1 hbk 0 η hη`. Use `⟨ε₁, hε₁, fun ε hε hεε₁ g hg => ?_⟩` and prove the remaining obligations.

Set `A : Ψ → Matrix (Fin r) (Fin r) ℂ` to `fun τ => (mat x τ)⁻¹ * GlobalTheory.SUVol.DensOne.matR Ψ G g τ * mat x τ - 1`. Establish `hA : ‖A‖ < ε` using `(pi_norm_lt_iff hε).2 fun τ => (Matrix.norm_lt_iff hε).2 fun a b => hg τ a b`. Establish `hbkA : bk A = GlobalTheory.SUVol.DensOne.matR Ψ G g - 1`. Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `mat x τ * ((mat x τ)⁻¹ * GlobalTheory.SUVol.DensOne.matR Ψ G g τ * mat x τ - 1) * (mat x τ)⁻¹ = GlobalTheory.SUVol.DensOne.matR Ψ G g τ - 1`.

Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ (hx τ).isUnit, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit, Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]`. Establish `hdist : dist (GlobalTheory.SUVol.DensOne.matR Ψ G g) 1 < η`. Use `hbkε A (by rw [dist_zero_right]; linarith)` as an intermediate fact. Rewrite `this` using `[hbk0, dist_zero_right, hbkA]`. Rewrite using `[dist_eq_norm]` and apply the resulting hypothesis.

Take `⟨X, ⟨hXδ, hXρ⟩, rfl⟩` from `hh hdist g rfl`. Use `⟨X, ⟨hXδ, fun τ a b => ?_⟩, rfl⟩` and prove the remaining obligations. Establish `hY` using `hexp (cj X.1 τ) (hXρ τ)`. Establish `he : NormedSpace.exp (cj X.1 τ) - 1 = A τ`. Express the relevant statement in the definitionally equal form `NormedSpace.exp ((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) - 1 = (mat x τ)⁻¹ * NormedSpace.exp (Matrix.of (X.1 τ)) * mat x τ - 1`.

Rewrite using `[Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (hx τ).isUnit)]`. Establish `hAτ : ‖A τ‖ < ε` using `lt_of_le_of_lt (norm_le_pi_norm A τ) hA`. Rewrite `hY` using `[he]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem frBall_subset_chartExp_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (hG : G.det ≠ 0), (∀ τ, (mat x τ).det ≠ 0) → ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → frBall Ψ G x ε ⊆ GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' {X : realLie Ψ G | ‖X‖ < δ ∧ ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) a b‖ < 2 * ε} := by
  intro E _ _ _ r Ψ G x hG hx δ hδ
  obtain ⟨ρ, hρ, hexp⟩ := exists_exp_lower (Fin r)
  let cj : (Ψ → Fin r → Fin r → ℂ) → (Ψ → Matrix (Fin r) (Fin r) ℂ) :=
    fun X τ => (mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ
  have hcj : Continuous cj :=
    continuous_pi fun τ => (continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const
  let U : Set (realLie Ψ G) := {X | ‖X‖ < δ ∧ ∀ τ, ‖cj X.1 τ‖ < ρ}
  have hU : U ∈ nhds 0 := by
    refine IsOpen.mem_nhds ?_ ?_
    · refine (isOpen_lt continuous_norm continuous_const).inter ?_
      change IsOpen {X : realLie Ψ G | ∀ τ, ‖cj X.1 τ‖ < ρ}
      rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun τ =>
        isOpen_lt ((continuous_apply τ).comp (hcj.comp continuous_subtype_val)).norm continuous_const
    · refine ⟨by simpa using hδ, fun τ => ?_⟩
      have e : cj (0 : realLie Ψ G).1 τ = 0 := by
        change (mat x τ)⁻¹ * (0 : Matrix (Fin r) (Fin r) ℂ) * mat x τ = 0
        simp
      rw [e, norm_zero]; exact hρ
  have hev := GlobalTheory.SUVol.DensOne.eventually_mem_image Ψ G hG hU
  rw [Filter.eventually_comap] at hev
  obtain ⟨η, hη, hh⟩ := Metric.eventually_nhds_iff.1 hev
  let bk : (Ψ → Matrix (Fin r) (Fin r) ℂ) → (Ψ → Matrix (Fin r) (Fin r) ℂ) :=
    fun A τ => mat x τ * A τ * (mat x τ)⁻¹
  have hbk : Continuous bk :=
    continuous_pi fun τ => (continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const
  have hbk0 : bk 0 = 0 := by funext τ; simp [bk]
  obtain ⟨ε₁, hε₁, hbkε⟩ := Metric.continuous_iff.1 hbk 0 η hη
  refine ⟨ε₁, hε₁, fun ε hε hεε₁ g hg => ?_⟩
  let A : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (mat x τ)⁻¹ * GlobalTheory.SUVol.DensOne.matR Ψ G g τ * mat x τ - 1
  have hA : ‖A‖ < ε := (pi_norm_lt_iff hε).2 fun τ => (Matrix.norm_lt_iff hε).2 fun a b => hg τ a b
  have hbkA : bk A = GlobalTheory.SUVol.DensOne.matR Ψ G g - 1 := by
    funext τ
    change mat x τ * ((mat x τ)⁻¹ * GlobalTheory.SUVol.DensOne.matR Ψ G g τ * mat x τ - 1) * (mat x τ)⁻¹ =
      GlobalTheory.SUVol.DensOne.matR Ψ G g τ - 1
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ (hx τ).isUnit,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hdist : dist (GlobalTheory.SUVol.DensOne.matR Ψ G g) 1 < η := by
    have := hbkε A (by rw [dist_zero_right]; linarith)
    rw [hbk0, dist_zero_right, hbkA] at this
    rwa [dist_eq_norm]
  obtain ⟨X, ⟨hXδ, hXρ⟩, rfl⟩ := hh hdist g rfl
  refine ⟨X, ⟨hXδ, fun τ a b => ?_⟩, rfl⟩
  have hY := hexp (cj X.1 τ) (hXρ τ)
  have he : NormedSpace.exp (cj X.1 τ) - 1 = A τ := by
    change NormedSpace.exp ((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) - 1 =
      (mat x τ)⁻¹ * NormedSpace.exp (Matrix.of (X.1 τ)) * mat x τ - 1
    rw [Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (hx τ).isUnit)]
  have hAτ : ‖A τ‖ < ε := lt_of_le_of_lt (norm_le_pi_norm A τ) hA
  rw [he] at hY
  calc ‖((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) a b‖ = ‖cj X.1 τ a b‖ := rfl
    _ ≤ ‖cj X.1 τ‖ := Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ 2 * ‖A τ‖ := hY
    _ < 2 * ε := by linarith

end Main

end GlobalTheory.CovTop.VolUp.BallCover
