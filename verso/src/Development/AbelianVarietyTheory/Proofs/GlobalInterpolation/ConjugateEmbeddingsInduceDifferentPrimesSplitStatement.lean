import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugateEmbeddingsInduceDifferentPrimesSplit
import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConjPlace.conj_place_ne` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FConjugateEmbeddingsInduceDifferentPrimesSplit.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.conjugate_embeddings_induce_different_primes_split : ∀ (D : D7) (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → ∀ ι : ℂ ≃+* ℂ_[q], ∃ y : 𝓞 D.host.K, ‖ι (D.host.φ₀ ((y : D.host.K) : D.host.E))‖ < 1 ∧ 1 ≤ ‖ι (D.host.φ₀ (D.host.conj ((y : D.host.K) : D.host.E)))‖ := by
  first | exact @GlobalTheory.ConjPlace.conj_place_ne | exact GlobalTheory.ConjPlace.conj_place_ne | (intros; apply GlobalTheory.ConjPlace.conj_place_ne <;> assumption)
