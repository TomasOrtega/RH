import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLastStageCharsUnramifiedAtLevelPrime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSeesawLastStageCharsUnramifiedAtLevelPrime.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.seesawLastStage_chars_unramified_at_levelPrime : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (t : Tup c), t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ (χz χS' χT : (AE D)ˣ →* Circle), IsWeilDatumO c.ψ _ _ χS' (χT * χz⁻¹) (t.kom (j + 1)) → IsWeilDatumO c.ψ _ _ χS' χT (t.omT j h) → ∀ x, x ∈ v.tP → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' x ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT x := by
  first | exact @GlobalTheory.LastStep.chars_unram | exact GlobalTheory.LastStep.chars_unram | (intros; apply GlobalTheory.LastStep.chars_unram <;> assumption)
