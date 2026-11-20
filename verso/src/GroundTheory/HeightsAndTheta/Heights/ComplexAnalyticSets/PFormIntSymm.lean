import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutOffLimit
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

/- English proof (translation)
Introduce and unpack `rfl`. Establish `h1` using `hx (linForm ℓ - 1) (Ideal.mem_sup_right (Ideal.subset_span rfl))`. Simplify using `[linForm] at h1`.
-/
theorem ne_zero_of_mem_zeroSet_slice {n : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    {x : Fin n → ℂ} (hx : x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) : x ≠ 0 := by
  rintro rfl
  have h1 := hx (linForm ℓ - 1) (Ideal.mem_sup_right (Ideal.subset_span rfl))
  simp [linForm] at h1

/- English proof (translation)
Introduce `n e h W u u' ε δ hW ⟨g, hg⟩ hε hδ`. Unfold `formInt`. Use `split_ifs with hℓ`. Establish `hℓW : linForm hℓ.choose ∉ W` using `hℓ.choose_spec`. Generalize the expression as in `hℓ.choose = ℓ at hℓW ⊢`.

Take `⟨hJ, hdim, -⟩` from `hI n (e + 1) W g ℓ hW hg hℓW`. Establish `hnear : ∀ F : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ F {x | x ≠ 0} → SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) F` using `fun F hF => ⟨{x | x ≠ 0}, isOpen_ne, fun x hx => ne_zero_of_mem_zeroSet_slice hx, hF⟩`. Take `⟨χ, hχs, hχc, hlim⟩` from `hC n e h W g ℓ hW hg hℓW`. Take `⟨h1, h2⟩` from `hlim (fsLogReg h u δ) (fsLogReg h u' ε) (fsLogReg_smul h u δ) (fsLogReg_smul h u' ε) (contDiffOn_fsLogReg h u hδ) (contDiffOn_fsLogReg h u' hε)`. Use `tendsto_nhds_unique h1 (h2.congr fun k => ?_)` and prove the remaining obligations.

Conclude with `(hS n e _ (fun x => χ k x * fsLogReg h u δ x) (fsLogReg h u' ε) (fun _ x => Real.log (h.dualNorm x)) hJ hdim (hnear _ ((hχs k).contDiffOn.mul (contDiffOn_fsLogReg h u hδ))) (hnear _ (contDiffOn_fsLogReg h u' hε)) (fun _ => hnear _ h.contDiffOn_log_dualNorm) (Or.inl (hχc k).mul_ri …`. Both sides reduce to the same expression.
-/
theorem FormIntSymm.proof (hI : SliceIdeal.Statement) (hS : StokesOnVariety.Statement)
    (hC : SliceCutOffLimit.Statement) : FormIntSymm.Statement := by
  intro n e h W u u' ε δ hW ⟨g, hg⟩ hε hδ
  unfold formInt
  split_ifs with hℓ
  · have hℓW : linForm hℓ.choose ∉ W := hℓ.choose_spec
    generalize hℓ.choose = ℓ at hℓW ⊢
    obtain ⟨hJ, hdim, -⟩ := hI n (e + 1) W g ℓ hW hg hℓW
    have hnear : ∀ F : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ F {x | x ≠ 0} →
        SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) F := fun F hF =>
      ⟨{x | x ≠ 0}, isOpen_ne, fun x hx => ne_zero_of_mem_zeroSet_slice hx, hF⟩
    obtain ⟨χ, hχs, hχc, hlim⟩ := hC n e h W g ℓ hW hg hℓW
    obtain ⟨h1, h2⟩ := hlim (fsLogReg h u δ) (fsLogReg h u' ε) (fsLogReg_smul h u δ)
      (fsLogReg_smul h u' ε) (contDiffOn_fsLogReg h u hδ) (contDiffOn_fsLogReg h u' hε)
    refine tendsto_nhds_unique h1 (h2.congr fun k => ?_)
    exact (hS n e _ (fun x => χ k x * fsLogReg h u δ x) (fsLogReg h u' ε)
      (fun _ x => Real.log (h.dualNorm x)) hJ hdim
      (hnear _ ((hχs k).contDiffOn.mul (contDiffOn_fsLogReg h u hδ)))
      (hnear _ (contDiffOn_fsLogReg h u' hε)) (fun _ => hnear _ h.contDiffOn_log_dualNorm)
      (Or.inl (hχc k).mul_right)).symm
  · rfl

end GroundTheory.Heights₂.Heights
