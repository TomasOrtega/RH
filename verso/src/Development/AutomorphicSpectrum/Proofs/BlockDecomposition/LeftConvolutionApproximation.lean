import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularRepresentationContinuous
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

/- English proof (translation)
Introduce `n _ _ μ _ V _ _ _ hU φ hφ hpos h1 x ε hε`. Establish `hemb` using `GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG n`. Establish `hφc : Continuous fun y : G n => φ y.val` using `hφ.1.continuous.comp hemb.continuous`. Establish `hK : IsCompact ((Units.val : G n → Mat n) ⁻¹' tsupport φ)`. Use `(hemb.isInducing.isCompact_preimage_iff ?_).2 hφ.2.1` and prove the remaining obligations.

Introduce `z hz`. Establish `hdet : z.det ≠ 0` using `hφ.2.2 hz`. Take `⟨u, rfl⟩` from `(Matrix.isUnit_iff_isUnit_det z).2 (isUnit_iff_ne_zero.2 hdet)`. Conclude with `⟨u, rfl⟩`. Establish `hcs : HasCompactSupport (fun y : G n => φ y.val)` using `HasCompactSupport.of_support_subset_isCompact hK (fun y hy => subset_tsupport φ hy)`.

Establish `hL` using `(translations_strongly_continuous n μ V hU x).2`. Establish `hint1 : Integrable (fun y : G n => φ y.val) μ` using `hφc.integrable_of_hasCompactSupport hcs`. Establish `hf : Integrable (fun y : G n => φ y.val • lT μ V y x) μ` using `(hφc.smul hL).integrable_of_hasCompactSupport hcs.smul_right`. Establish `hg : Integrable (fun y : G n => φ y.val • x) μ` using `hint1.smul_const x`. Establish `e : lConv μ V φ x - x = ∫ y : G n, φ y.val • (lT μ V y x - x) ∂μ`.

Repeatedly rewrite using `[smul_sub]`. Rewrite using `[integral_sub hf hg, integral_smul_const, h1, one_smul]`. Both sides reduce to the same expression. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Use `norm_integral_le_of_norm_le (hint1.mul_const ε) (ae_of_all _ fun y => ?_)` and prove the remaining obligations. Distinguish the cases in `h0 : φ y.val = 0`. Simplify using `[h0]`. Rewrite using `[norm_smul, Real.norm_of_nonneg (hpos _)]`. Conclude with `mul_le_mul_of_nonneg_left (hε y h0) (hpos _)`.

Use `_ = ε := by rw [integral_mul_const, h1, one_mul]`.
-/
theorem norm_lConv_sub_le : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → (∀ y, 0 ≤ φ y) → (∫ y : G n, φ y.val ∂μ = 1) → ∀ (x : Lp V 2 μ) (ε : ℝ), (∀ y : G n, φ y.val ≠ 0 → ‖lT μ V y x - x‖ ≤ ε) → ‖lConv μ V φ x - x‖ ≤ ε := by
  intro n _ _ μ _ V _ _ _ hU φ hφ hpos h1 x ε hε
  have hemb := GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG n
  have hφc : Continuous fun y : G n => φ y.val := hφ.1.continuous.comp hemb.continuous
  have hK : IsCompact ((Units.val : G n → Mat n) ⁻¹' tsupport φ) := by
    refine (hemb.isInducing.isCompact_preimage_iff ?_).2 hφ.2.1
    intro z hz
    have hdet : z.det ≠ 0 := hφ.2.2 hz
    obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det z).2 (isUnit_iff_ne_zero.2 hdet)
    exact ⟨u, rfl⟩
  have hcs : HasCompactSupport (fun y : G n => φ y.val) :=
    HasCompactSupport.of_support_subset_isCompact hK (fun y hy => subset_tsupport φ hy)
  have hL := (translations_strongly_continuous n μ V hU x).2
  have hint1 : Integrable (fun y : G n => φ y.val) μ := hφc.integrable_of_hasCompactSupport hcs
  have hf : Integrable (fun y : G n => φ y.val • lT μ V y x) μ :=
    (hφc.smul hL).integrable_of_hasCompactSupport hcs.smul_right
  have hg : Integrable (fun y : G n => φ y.val • x) μ := hint1.smul_const x
  have e : lConv μ V φ x - x = ∫ y : G n, φ y.val • (lT μ V y x - x) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub hf hg, integral_smul_const, h1, one_smul]
    rfl
  rw [e]
  calc ‖∫ y : G n, φ y.val • (lT μ V y x - x) ∂μ‖ ≤ ∫ y : G n, φ y.val * ε ∂μ := by
        refine norm_integral_le_of_norm_le (hint1.mul_const ε) (ae_of_all _ fun y => ?_)
        by_cases h0 : φ y.val = 0
        · simp [h0]
        · rw [norm_smul, Real.norm_of_nonneg (hpos _)]
          exact mul_le_mul_of_nonneg_left (hε y h0) (hpos _)
    _ = ε := by rw [integral_mul_const, h1, one_mul]

end GlobalTheory.CompanionTheory.PresSobA
