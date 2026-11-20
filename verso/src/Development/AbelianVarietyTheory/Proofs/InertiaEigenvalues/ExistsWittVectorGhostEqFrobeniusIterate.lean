import Mathlib

open scoped NNReal
open Finset

namespace GlobalTheory.DworkGhost

open Classical in

noncomputable def coeff {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A) (a : A) : ℕ → A
  | n => if h : ((l : A) ^ n ∣ φ^[n] a - ∑ i : Fin n, (l : A) ^ (i : ℕ) * coeff l φ a i ^ l ^ (n - i))
      then h.choose else 0
decreasing_by all_goals exact i.isLt

/- English proof (translation)
Establish `h' : (l : A) ^ n ∣ φ^[n] a - ∑ i : Fin n, (l : A) ^ (i : ℕ) * coeff l φ a i ^ l ^ (n - i)`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) n]` and apply the resulting hypothesis. Establish `e : coeff l φ a n = h'.choose`. Rewrite using `[coeff, dif_pos h']`. Establish `hc` using `h'.choose_spec`.

Rewrite `hc` using `[← e, Fin.sum_univ_eq_sum_range (fun i => (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) n]`. Rewrite using `[sum_range_succ, Nat.sub_self, pow_zero, pow_one, ← hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_spec {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A) (a : A) (n : ℕ)
    (h : (l : A) ^ n ∣ φ^[n] a - ∑ i ∈ range n, (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) :
    φ^[n] a = ∑ i ∈ range (n + 1), (l : A) ^ i * coeff l φ a i ^ l ^ (n - i) := by
  have h' : (l : A) ^ n ∣ φ^[n] a - ∑ i : Fin n, (l : A) ^ (i : ℕ) * coeff l φ a i ^ l ^ (n - i) := by
    rwa [Fin.sum_univ_eq_sum_range (fun i => (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) n]
  have e : coeff l φ a n = h'.choose := by
    rw [coeff, dif_pos h']
  have hc := h'.choose_spec
  rw [← e, Fin.sum_univ_eq_sum_range (fun i => (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) n] at hc
  rw [sum_range_succ, Nat.sub_self, pow_zero, pow_one, ← hc]
  ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact coeff_spec l φ a 0 (by simp)`. Consider the case `succ n ih`. Apply `coeff_spec` to reduce the goal to its premises. Rewrite using `[Function.iterate_succ_apply', ih, map_sum, ← sum_sub_distrib]`.

Apply `dvd_sum` to reduce the goal to its premises. Introduce `i hi`. Establish `hin : i ≤ n` using `Nat.lt_succ_iff.mp (mem_range.mp hi)`. Rewrite using `[map_mul, map_pow, map_pow, map_natCast, ← mul_sub]`. Establish `e1 : n + 1 = i + (n - i + 1)` using `by omega`.

Establish `e2 : n + 1 - i = n - i + 1` using `by omega`. Establish `e3 : coeff l φ a i ^ l ^ (n - i + 1) = (coeff l φ a i ^ l) ^ l ^ (n - i)`. Rewrite using `[pow_succ', pow_mul]`. Rewrite using `[e2, e3, e1, pow_add]`. Conclude with `mul_dvd_mul_left _ (dvd_sub_pow_of_dvd_sub (hφ (coeff l φ a i)) (n - i))`.
-/
theorem ghost_eq {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A)
    (hφ : ∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) (a : A) (n : ℕ) :
    φ^[n] a = ∑ i ∈ range (n + 1), (l : A) ^ i * coeff l φ a i ^ l ^ (n - i) := by
  induction n with
  | zero => exact coeff_spec l φ a 0 (by simp)
  | succ n ih =>
    apply coeff_spec
    rw [Function.iterate_succ_apply', ih, map_sum, ← sum_sub_distrib]
    apply dvd_sum
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [map_mul, map_pow, map_pow, map_natCast, ← mul_sub]
    have e1 : n + 1 = i + (n - i + 1) := by omega
    have e2 : n + 1 - i = n - i + 1 := by omega
    have e3 : coeff l φ a i ^ l ^ (n - i + 1) = (coeff l φ a i ^ l) ^ l ^ (n - i) := by
      rw [pow_succ', pow_mul]
    rw [e2, e3, e1, pow_add]
    exact mul_dvd_mul_left _ (dvd_sub_pow_of_dvd_sub (hφ (coeff l φ a i)) (n - i))

/- English proof (translation)
Introduce `l _ A _ φ hφ a`. Use `⟨WittVector.mk l (coeff l φ a), fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[WittVector.ghostComponent_apply, aeval_wittPolynomial, ghost_eq l φ hφ a n]`. Both sides reduce to the same expression.
-/
theorem exists_witt_ghost_iterate : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A),
    (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → ∀ a : A, ∃ w : WittVector l A,
      ∀ n, WittVector.ghostComponent n w = φ^[n] a := by
  intro l _ A _ φ hφ a
  refine ⟨WittVector.mk l (coeff l φ a), fun n => ?_⟩
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial, ghost_eq l φ hφ a n]
  rfl

end GlobalTheory.DworkGhost
