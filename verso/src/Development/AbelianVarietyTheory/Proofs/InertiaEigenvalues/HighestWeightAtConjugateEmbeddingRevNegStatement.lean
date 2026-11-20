import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HighestWeightAtConjugateEmbeddingRevNeg
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.hwAt_conj_swap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHighestWeightAtConjugateEmbeddingRevNeg.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.highestWeightAt_conjugate_embedding_rev_neg : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (τ : L →+* ℂ) (lam' : Fin n → ℤ), a.HWAt (ComplexEmbedding.conjugate τ) lam' → a.HWAt τ (fun i => -lam' (Fin.rev i)) := by
  first | exact @GlobalTheory.hwAt_conj_swap | exact GlobalTheory.hwAt_conj_swap | (intros; apply GlobalTheory.hwAt_conj_swap <;> assumption)
