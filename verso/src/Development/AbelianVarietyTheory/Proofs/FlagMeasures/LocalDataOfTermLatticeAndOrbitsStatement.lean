import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataOfTermLatticeAndOrbits
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Unfold.TermLocal.local_data_of_term` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLocalDataOfTermLatticeAndOrbits.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.localData_of_term_lattice_and_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → ∃ y : Dat Z FP, LocOver Λ y ∧ ∀ p d, GlobalTheory.LocOver.Over (FP p) d (GlobalTheory.LocOver.locU Z p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')) ↔ LocNG.Datum.Rel d (y p) := by
  first | exact @GlobalTheory.Unfold.TermLocal.local_data_of_term | exact GlobalTheory.Unfold.TermLocal.local_data_of_term | (intros; apply GlobalTheory.Unfold.TermLocal.local_data_of_term <;> assumption)
