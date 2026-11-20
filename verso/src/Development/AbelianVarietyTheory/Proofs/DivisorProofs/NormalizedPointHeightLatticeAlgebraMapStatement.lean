import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormalizedPointHeightLatticeAlgebraMap.lean&line=135#L135)
-/
theorem _root_.GlobalTheory.T.normalizedPointHeightLattice_algebraMap : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] (y : Fin N → K), y ≠ 0 → pointHeight w A (fun j => algebraMap K K' (y j)) = pointHeight w A y := by
  first | exact @GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap | exact GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap | (intros; apply GlobalTheory.Adelic.HeightExt.pointHeight_algebraMap <;> assumption)
