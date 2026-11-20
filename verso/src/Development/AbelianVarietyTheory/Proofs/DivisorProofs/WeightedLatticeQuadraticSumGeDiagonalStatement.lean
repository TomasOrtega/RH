import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLatticeQuadraticSumGeDiagonal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Poinc.QWDom.qW_ge` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeightedLatticeQuadraticSumGeDiagonal.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.weightedLatticeQuadraticSum_ge_diagonal : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∃ c : ℝ, 0 < c ∧ ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ y, 0 ≤ β y y) → ∀ y : Fin s → X, c * (∑ u, β (y u) (y u) : ℤ) ≤ (qW W β y : ℤ) := by
  first | exact @GlobalTheory.Poinc.QWDom.qW_ge | exact GlobalTheory.Poinc.QWDom.qW_ge | (intros; apply GlobalTheory.Poinc.QWDom.qW_ge <;> assumption)
