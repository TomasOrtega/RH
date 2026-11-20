import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineConditionsDual
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.ScalarDual.cond_dual` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSplitPlaceLineConditionsDual.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.splitPlace_lineConditions_dual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (h h' : D.host.E), h ≠ 0 → h' ≠ 0 → star h' = h' → h = D.host.xi0 * star D.host.xi0 * h' → ∀ d : AE D, d ∈ idAt D P → ((∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D h') ∈ 𝒪[k]) ↔ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D h) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D h ∈ intAt D P) := by
  first | exact @GlobalTheory.FinPl.ScalarDual.cond_dual | exact GlobalTheory.FinPl.ScalarDual.cond_dual | (intros; apply GlobalTheory.FinPl.ScalarDual.cond_dual <;> assumption)
