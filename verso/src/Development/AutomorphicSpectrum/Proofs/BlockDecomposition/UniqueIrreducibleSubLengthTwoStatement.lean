import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueIrreducibleSubLengthTwo
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUniqueIrreducibleSubLengthTwo.lean&line=416#L416)
-/
theorem _root_.GlobalTheory.T.unique_irreducible_sub_length_two : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
        S.toRepresentation.IsIrreducible ∧
        (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
          S'.toRepresentation.IsIrreducible → S' = S) ∧
        Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor (segTerm σ.ρ 2)))) →
  GlobalTheory.Published.SegmentRepresentation := by
  first | exact @GlobalTheory.CompanionTheory.SegZRep.segmentRepresentation_of_two | exact GlobalTheory.CompanionTheory.SegZRep.segmentRepresentation_of_two | (intros; apply GlobalTheory.CompanionTheory.SegZRep.segmentRepresentation_of_two <;> assumption)
