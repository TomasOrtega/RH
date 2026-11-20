import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneModulesFreeFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
open CategoryTheory TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDieudonneModulesFreeFinite.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.dieudonne_modules_free_finite : GlobalTheory.Published.BarsottiTateDieudonne.WittModule → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (h : (p : R) = 0) (G : PDivGroup p R), Module.Free R G.omega ∧ Module.Finite R G.omega ∧ Module.Free R G.dual.omega ∧ Module.Finite R G.dual.omega ∧ Module.Free R G.VecExt ∧ Module.Finite R G.VecExt ∧ Module.Free R G.RigExt ∧ Module.Finite R G.RigExt := by
  first | exact @GlobalTheory.PDivGroup.free_finite_omega_ext_of_isDiscreteValuationRing | exact GlobalTheory.PDivGroup.free_finite_omega_ext_of_isDiscreteValuationRing | (intros; apply GlobalTheory.PDivGroup.free_finite_omega_ext_of_isDiscreteValuationRing <;> assumption)
