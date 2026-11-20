import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalHeckeAtLevelsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RationalHeckeAllSt
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeFamRead.rationalHecke_allSt_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FRationalHeckeAllSt.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.rationalHecke_of_levelA : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ i : Fin (Dof x).R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke x.m.z.R.toRealDat i := by
  first | exact @_root_.GlobalTheory.HeckeFamRead.rationalHecke_allSt_alt | exact _root_.GlobalTheory.HeckeFamRead.rationalHecke_allSt_alt | (intros; apply _root_.GlobalTheory.HeckeFamRead.rationalHecke_allSt_alt <;> assumption)
end
