import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspIntegralBasisCovolumeConstant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGeo.covolume_const` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FCuspIntegralBasisCovolumeConstant.lean&line=194#L194)
-/
theorem _root_.GlobalTheory.T.cusp_integralBasis_covolume_constant : ∀ I : AutInst, ∃ (N : ℕ) (e : Fin N → Fin I.n → I.E) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (d : ℝ), 0 < d ∧ IsZBasis I e ∧ IsRealCoord I ρ ∧ ∀ y : I.Ginf, |(gm I ρ y e).det| = d := by
  first | exact @GlobalTheory.CuspGeo.covolume_const | exact GlobalTheory.CuspGeo.covolume_const | (intros; apply GlobalTheory.CuspGeo.covolume_const <;> assumption)
