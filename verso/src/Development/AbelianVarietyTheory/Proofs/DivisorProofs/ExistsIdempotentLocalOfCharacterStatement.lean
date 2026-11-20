import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLocalOfCharacter
import Mathlib
open scoped TensorProduct
universe u
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.exists_idempotent_local_of_character : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (φ : A →ₐ[k] k), ∃ e : A, IsIdempotentElem e ∧ φ e = 1 ∧ ∀ a, φ a = 0 → IsNilpotent (e * a) := by
  first | (exact @GlobalTheory.exists_idem_local_of_character) | (exact GlobalTheory.exists_idem_local_of_character) | (intros; apply GlobalTheory.exists_idem_local_of_character <;> assumption)
