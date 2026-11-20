import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormalizedPointHeightLatticeSmul.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.normalizedPointHeightLattice_smul : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (y : Fin N → K) (c : K), y ≠ 0 → c ≠ 0 → pointHeight w A (c • y) = pointHeight w A y := by
  first | exact @GlobalTheory.Adelic.HeightScaling.pointHeight_smul | exact GlobalTheory.Adelic.HeightScaling.pointHeight_smul | (intros; apply GlobalTheory.Adelic.HeightScaling.pointHeight_smul <;> assumption)
