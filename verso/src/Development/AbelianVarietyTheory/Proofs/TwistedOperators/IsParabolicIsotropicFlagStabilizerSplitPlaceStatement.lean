import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsParabolicIsotropicFlagStabilizerSplitPlace
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SplitFlag.isParabRad_parAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIsParabolicIsotropicFlagStabilizerSplitPlace.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.isParabolic_isotropicFlag_stabilizer_split_place : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (𝔉 : IsoFlag V), GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.IsParabRad (parAt 𝔉 s)
      ((NLoc 𝔉 v).map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) := by
  first | exact @GlobalTheory.SplitFlag.isParabRad_parAt | exact GlobalTheory.SplitFlag.isParabRad_parAt | (intros; apply GlobalTheory.SplitFlag.isParabRad_parAt <;> assumption)
