import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantIndexIdealMapInjectiveEqColon
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeDeterminantIndexIdealMapInjectiveEqColon.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.latticeDeterminantIndexIdeal_map_injective_eq_colon : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (p : ℕ) (φ : (Fin p → F) →ₗ[F] V), Function.Injective φ →
    ∀ (L N : Submodule (𝓞 F) (Fin p → F)),
    GlobalTheory.FlatCM.idx F p (L.map (φ.restrictScalars (𝓞 F))) (N.map (φ.restrictScalars (𝓞 F))) =
      (GlobalTheory.IdxTensor.dets F p N).colon (GlobalTheory.IdxTensor.dets F p L : Set F) := by
  first | exact @GlobalTheory.IdxMap.idx_map_eq_colon_dets | exact GlobalTheory.IdxMap.idx_map_eq_colon_dets | (intros; apply GlobalTheory.IdxMap.idx_map_eq_colon_dets <;> assumption)
