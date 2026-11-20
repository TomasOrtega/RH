import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockLiftActionOnPrincipalCongruenceFixedVectors
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FBlockLiftActionOnPrincipalCongruenceFixedVectors.lean&line=148#L148)
-/
theorem _root_.GlobalTheory.T.blockLift_action_on_principalCongruenceFixedVectors : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V), u ∈ fixK1 (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) → ∀ (h : GL (Fin r) (ZMod g)) (h' : GL (Fin (r + t)) F), GlobalTheory.PendOf.IsLiftN h h' → ρ h' u = ρ (Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1))) u := by
  first | exact @GlobalTheory.SerSys.BlockLift.blockLift_act | exact GlobalTheory.SerSys.BlockLift.blockLift_act | (intros; apply GlobalTheory.SerSys.BlockLift.blockLift_act <;> assumption)
