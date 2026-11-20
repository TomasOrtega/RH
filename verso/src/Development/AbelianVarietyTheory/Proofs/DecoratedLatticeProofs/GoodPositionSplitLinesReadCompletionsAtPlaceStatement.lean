import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodPositionSplitLinesReadCompletionsAtPlace
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocCongr.goodAt_splitAt_congr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FGoodPositionSplitLinesReadCompletionsAtPlace.lean&line=132#L132)
-/
theorem _root_.GlobalTheory.T.goodPosition_splitLines_read_completions_at_place : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀) (x : Pl D), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) ∧ IsSelfDualC (c.V j) (N j) ∧ latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) → (∀ j ρ h, IsSelfDualC _ (o.M j ρ h) ∧ IsSelfDualC _ (M j ρ h) ∧ latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) → (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧ (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x) := by
  first | exact @GlobalTheory.LocCongr.goodAt_splitAt_congr | exact GlobalTheory.LocCongr.goodAt_splitAt_congr | (intros; apply GlobalTheory.LocCongr.goodAt_splitAt_congr <;> assumption)
