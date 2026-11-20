import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Finset

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [add_comm]`. Consider the case `succ m ih`. Use `push_cast`. Take the linear combination `(x + y) * ih + ((m : S) + 1) * y ^ m * hx`.
-/
theorem add_pow_succ_of_sq_eq_zero {S : Type*} [CommRing S] {x y : S} (hx : x ^ 2 = 0)
    (m : ℕ) : (x + y) ^ (m + 1) = y ^ (m + 1) + ((m : S) + 1) * x * y ^ m := by
  induction m with
  | zero => simp [add_comm]
  | succ m ih =>
    push_cast
    linear_combination (x + y) * ih + ((m : S) + 1) * y ^ m * hx

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `@insert a s ha ih`. Take `⟨h1, h2⟩` from `ih`. Rewrite using `[sum_insert ha, prod_insert ha, card_insert_of_notMem ha]`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[add_pow_succ_of_sq_eq_zero (hx a) (s.card + 1), pow_succ, h1]`. Simplify using the standard rewrite rules. Rewrite using `[add_pow_succ_of_sq_eq_zero (hx a) s.card, h1, h2, Nat.factorial_succ]`. Use `push_cast`.

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
Introduce `S _ D ω lam hω`. Establish `h` using `(sum_pow_card_of_sq_eq_zero (fun j => lam j * ω j) (fun j => by rw [mul_pow, hω j, mul_zero]) (univ : Finset (Fin D))).2`. Rewrite `h` using `[card_univ, Fintype.card_fin, prod_mul_distrib]`. Rewrite using `[h, mul_assoc]`.
-/
theorem TopPowerDiagonal.proof : TopPowerDiagonal.Statement := by
  intro S _ D ω lam hω
  have h := (sum_pow_card_of_sq_eq_zero (fun j => lam j * ω j)
    (fun j => by rw [mul_pow, hω j, mul_zero]) (univ : Finset (Fin D))).2
  rw [card_univ, Fintype.card_fin, prod_mul_distrib] at h
  rw [h, mul_assoc]

end GroundTheory.Heights₂.Heights.FlagBundles
