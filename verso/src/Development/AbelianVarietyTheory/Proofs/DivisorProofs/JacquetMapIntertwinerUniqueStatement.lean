import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetMapIntertwinerUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsJacMapZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JacLineGL.jacMap_line` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FJacquetMapIntertwinerUnique.lean&line=154#L154)
-/
theorem _root_.GlobalTheory.T.jacquet_map_intertwiner_unique : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a b : ℕ) (α β : kˣ →* ℂˣ), GlobalTheory.KSplit.IsSmU α → GlobalTheory.KSplit.IsSmU β → b + 2 < a →
    ∀ φ φ' : GlobalTheory.KSplit.indSp a (b + 2) α β →ₗ[ℂ] GlobalTheory.KSplit.indSp a b α β,
      GlobalTheory.JacLine.IsJacMap a b α β (fun x => (β x : ℂ) * GlobalTheory.SplitFlip.apow x ((a : ℂ) / 2))
        (fun y => (β y : ℂ) * GlobalTheory.SplitFlip.apow y (-(a : ℂ) / 2)) φ →
      GlobalTheory.JacLine.IsJacMap a b α β (fun x => (β x : ℂ) * GlobalTheory.SplitFlip.apow x ((a : ℂ) / 2))
        (fun y => (β y : ℂ) * GlobalTheory.SplitFlip.apow y (-(a : ℂ) / 2)) φ' →
      φ = 0 ∨ ∃ c : ℂ, φ' = c • φ := by
  first | exact @GlobalTheory.JacLineGL.jacMap_line | exact GlobalTheory.JacLineGL.jacMap_line | (intros; apply GlobalTheory.JacLineGL.jacMap_line <;> assumption)
