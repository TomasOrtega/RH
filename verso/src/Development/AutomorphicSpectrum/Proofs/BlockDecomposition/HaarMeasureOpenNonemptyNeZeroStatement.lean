import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureOpenNonemptyNeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZPhiPG.OntoO.muD_toReal_ne_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHaarMeasureOpenNonemptyNeZero.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.haar_measure_open_nonempty_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (E C : Set (Fin t → k)) (hE : IsOpen E) (hn : E.Nonempty) (hC : IsCompact C) (hEC : E ⊆ C),
    ((muD k t) E).toReal ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.muD_toReal_ne_zero | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.muD_toReal_ne_zero | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.muD_toReal_ne_zero <;> assumption)
