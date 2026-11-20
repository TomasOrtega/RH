import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentMatrixPiIffForallEval
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BesselChar.unip_pi_iff` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FIsFlagUnipotentMatrixPiIffForallEval.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.isFlagUnipotentMatrix_pi_iff_forall_eval : ∀ {ι S : Type} [Fintype ι] [DecidableEq ι] [CommRing S] {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) (ι → S)) (K : Matrix (Fin ρ) (Fin n) (ι → S)) (M : Matrix (Fin n) (Fin n) (ι → S)), GlobalTheory.BesselChar.Unip E K M ↔ ∀ i, GlobalTheory.BesselChar.Unip (E.map (Pi.evalRingHom (fun _ => S) i)) (K.map (Pi.evalRingHom (fun _ => S) i)) (M.map (Pi.evalRingHom (fun _ => S) i)) := by
  first | exact @GlobalTheory.BesselChar.unip_pi_iff | exact GlobalTheory.BesselChar.unip_pi_iff | (intros; apply GlobalTheory.BesselChar.unip_pi_iff <;> assumption)
