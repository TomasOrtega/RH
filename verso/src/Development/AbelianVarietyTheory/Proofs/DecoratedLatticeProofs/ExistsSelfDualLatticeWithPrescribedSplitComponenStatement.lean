import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrameGlob.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsSelfDualLatticeWithPrescribedSplitComponen.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S)
    (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → Λ.IsLattice k →
    ∃ M : Lat S, IsSelfDualC S M ∧ β.IsLat M Λ ∧ latV S M (· ≠ p.v) = latV S L (· ≠ p.v) := by
  first | exact @GlobalTheory.FrameGlob.main | exact GlobalTheory.FrameGlob.main | (intros; apply GlobalTheory.FrameGlob.main <;> assumption)
