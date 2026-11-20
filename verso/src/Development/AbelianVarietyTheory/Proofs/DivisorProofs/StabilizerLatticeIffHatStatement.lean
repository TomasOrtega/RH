import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerLatticeIffHat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStabilizerLatticeIffHat.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.stabilizer_lattice_iff_hat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (L : Set (Fin r → E)) (k : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), IsSA G k →
    (IsKM (IsCMField.complexConj E) G L 1 k ↔ GlobalTheory.Mem.Vol.StabHat (maximalRealSubfield E) L k) := by
  first | exact @GlobalTheory.KMStab.isKM_one_iff_stabHat_of_isSA | exact GlobalTheory.KMStab.isKM_one_iff_stabHat_of_isSA | (intros; apply GlobalTheory.KMStab.isKM_one_iff_stabHat_of_isSA <;> assumption)
