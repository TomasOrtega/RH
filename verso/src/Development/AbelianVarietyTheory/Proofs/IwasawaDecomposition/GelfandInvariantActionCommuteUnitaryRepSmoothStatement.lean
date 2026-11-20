import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantActionCommuteUnitaryRepSmooth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FGelfandInvariantActionCommuteUnitaryRepSmooth.lean&line=175#L175)
-/
theorem _root_.GlobalTheory.T.gelfandInvariantAction_commute_unitaryRep_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (k : ℕ), ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P), gelfH G (trRep σ P) k ((trRep σ P) g w) = (trRep σ P) g (gelfH G (trRep σ P) k w) := by
  first | exact @GlobalTheory.SmVecGelfComm.gelfH_rep | exact GlobalTheory.SmVecGelfComm.gelfH_rep | (intros; apply GlobalTheory.SmVecGelfComm.gelfH_rep <;> assumption)
