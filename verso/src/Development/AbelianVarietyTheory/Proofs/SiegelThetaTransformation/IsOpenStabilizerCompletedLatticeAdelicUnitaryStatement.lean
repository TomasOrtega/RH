import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsOpenStabilizerCompletedLatticeAdelicUnitary
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StabOpen.isOpen_stab_latHat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FIsOpenStabilizerCompletedLatticeAdelicUnitary.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.isOpen_stabilizer_completedLattice_adelicUnitary : ∀ (D : D7) (V : HSp D), IsOpen {h : GA D V | ∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)} := by
  first | exact @GlobalTheory.StabOpen.isOpen_stab_latHat | exact GlobalTheory.StabOpen.isOpen_stab_latHat | (intros; apply GlobalTheory.StabOpen.isOpen_stab_latHat <;> assumption)
