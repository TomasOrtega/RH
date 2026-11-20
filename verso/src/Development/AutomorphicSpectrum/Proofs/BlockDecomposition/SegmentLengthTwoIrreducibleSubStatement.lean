import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentLengthTwoIrreducibleSub
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SegTwo.segment_two` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSegmentLengthTwoIrreducibleSub.lean&line=120#L120)
-/
theorem _root_.GlobalTheory.T.segment_length_two_irreducible_sub : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible) →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
        S.toRepresentation.IsIrreducible ∧
        (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
          S'.toRepresentation.IsIrreducible → S' = S) ∧
        Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor (segTerm σ.ρ 2))) := by
  first | exact @GlobalTheory.CompanionTheory.SegTwo.segment_two | exact GlobalTheory.CompanionTheory.SegTwo.segment_two | (intros; apply GlobalTheory.CompanionTheory.SegTwo.segment_two <;> assumption)
