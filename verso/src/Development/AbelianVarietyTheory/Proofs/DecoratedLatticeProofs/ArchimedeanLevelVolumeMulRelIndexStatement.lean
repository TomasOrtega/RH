import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndex
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LevVol.volLev_mul_relIndex` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FArchimedeanLevelVolumeMulRelIndex.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.archimedeanLevelVolume_mul_relIndex : ∀ (D : D7) (V : HSp D) (v : GlobalTheory.Unf.Vol V) (U U' : Subgroup (GA D V)), U ≤ U' → U' ≤ GfC V → IsCompact (U' : Set (GA D V)) → IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) → volLev v U * (U.relIndex U' : ℝ) = volLev v U' := by
  first | exact @GlobalTheory.LevVol.volLev_mul_relIndex | exact GlobalTheory.LevVol.volLev_mul_relIndex | (intros; apply GlobalTheory.LevVol.volLev_mul_relIndex <;> assumption)
