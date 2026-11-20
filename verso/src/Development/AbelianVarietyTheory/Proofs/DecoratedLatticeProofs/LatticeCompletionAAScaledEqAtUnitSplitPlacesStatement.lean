import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAAScaledEqAtUnitSplitPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.UnitPlaces.latA_eq_latV` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FLatticeCompletionAAScaledEqAtUnitSplitPlaces.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.latticeCompletionAAScaled_eq_at_unitSplitPlaces : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (S : HSp D) (L : Lat S), latA S L P = latV S L P := by
  first | exact @GlobalTheory.FinPl.UnitPlaces.latA_eq_latV | exact GlobalTheory.FinPl.UnitPlaces.latA_eq_latV | (intros; apply GlobalTheory.FinPl.UnitPlaces.latA_eq_latV <;> assumption)
