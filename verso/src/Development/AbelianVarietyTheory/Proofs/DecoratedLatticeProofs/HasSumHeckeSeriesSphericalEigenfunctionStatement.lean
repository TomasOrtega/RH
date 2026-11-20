import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesSphericalEigenfunction
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeShift.hasSum_hecke_shift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FHasSumHeckeSeriesSphericalEigenfunction.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.hasSum_hecke_series_spherical_eigenfunction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1) → ∀ g : GL (Fin n) k, HasSum (fun c : {c : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ (g * c.1.out)) ((∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) * φ g) := by
  first | exact @GlobalTheory.HeckeShift.hasSum_hecke_shift | exact GlobalTheory.HeckeShift.hasSum_hecke_shift | (intros; apply GlobalTheory.HeckeShift.hasSum_hecke_shift <;> assumption)
