import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFrameGramPositive
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHodgeFrameGramPositive.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.hodge_frame_gram_positive : ∀ (ι : Type) [Fintype ι] (p q : ℕ) (U : Set (ι → ℂ))
    (ψ : (ι → ℂ) → Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) (a b : ℝ),
    IsHodgeFrame U ψ → 0 < a → 0 < b →
      IsPosFrame U (fun x => (a : ℂ) • quotGram (ψ x)) ∧ IsPosFrame U (fun x => (b : ℂ) • -subGram (ψ x)) := by
  first | exact @GlobalTheory.isPosFrame_hodge_quot_and_sub | exact GlobalTheory.isPosFrame_hodge_quot_and_sub | (intros; apply GlobalTheory.isPosFrame_hodge_quot_and_sub <;> assumption)
