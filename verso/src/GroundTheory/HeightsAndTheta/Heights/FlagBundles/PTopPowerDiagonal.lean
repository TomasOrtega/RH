import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Finset

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem add_pow_succ_of_sq_eq_zero {S : Type*} [CommRing S] {x y : S} (hx : x ^ 2 = 0)
    (m : ℕ) : (x + y) ^ (m + 1) = y ^ (m + 1) + ((m : S) + 1) * x * y ^ m := by
  induction m with
  | zero => simp [add_comm]
  | succ m ih =>
    push_cast
    linear_combination (x + y) * ih + ((m : S) + 1) * y ^ m * hx

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_pow_card_of_sq_eq_zero {S ι : Type*} [CommRing S] [DecidableEq ι] (x : ι → S)
    (hx : ∀ j, x j ^ 2 = 0) (s : Finset ι) :
    (∑ j ∈ s, x j) ^ (s.card + 1) = 0 ∧
      (∑ j ∈ s, x j) ^ s.card = (s.card.factorial : S) * ∏ j ∈ s, x j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [sum_insert ha, prod_insert ha, card_insert_of_notMem ha]
    constructor
    · rw [add_pow_succ_of_sq_eq_zero (hx a) (s.card + 1), pow_succ, h1]
      simp
    · rw [add_pow_succ_of_sq_eq_zero (hx a) s.card, h1, h2, Nat.factorial_succ]
      push_cast
      ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem TopPowerDiagonal.proof : TopPowerDiagonal.Statement := by
  intro S _ D ω lam hω
  have h := (sum_pow_card_of_sq_eq_zero (fun j => lam j * ω j)
    (fun j => by rw [mul_pow, hω j, mul_zero]) (univ : Finset (Fin D))).2
  rw [card_univ, Fintype.card_fin, prod_mul_distrib] at h
  rw [h, mul_assoc]

end GroundTheory.Heights₂.Heights.FlagBundles
