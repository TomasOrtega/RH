import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedEmbeddingMemCongruenceIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulMemBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FShiftedEmbeddingMemCongruenceIff.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.shifted_embedding_mem_congruence_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (x : Mir k n),
  sEmb k n x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs (n + 1) ↔ x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.sEmb_mem_congM_iff | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.sEmb_mem_congM_iff | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.sEmb_mem_congM_iff <;> assumption)
