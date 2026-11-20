import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliLeftComatrixStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorCommOfCommColumnsStatement

open Formalism.REAL Finset

namespace GlobalTheory

/- English proof (translation)
Establish `h1` using `GlobalTheory.T.capelli_left_comatrix_qminor_eq A m E hE u j j`. Rewrite `h1` using `[if_pos rfl]`. Establish `h2 : ∀ a : Fin (m + 1), qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1) * x j = x j * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)`. Introduce `a`. Use `GlobalTheory.T.qminor_commute_of_commute_columns A (m + 1) m E (x j) _ _ _ ?_` and prove the remaining obligations.

Introduce `c i`. Rewrite using `[hx, if_neg (Fin.succAbove_ne j i), add_zero]`. Establish `h3 : ∀ a : Fin (m + 1), Tm E u a j * x j = x j * Tm E u a j + x a`. Introduce `a`. Establish `h` using `hx a j j`.

Rewrite `h` using `[if_pos rfl]`. Unfold `Tm`. Distinguish the cases in `haj : a = j`. Simplify using `only [if_pos haj, add_mul, mul_add, h, Algebra.commutes]`. Normalize the expressions using the abelian group laws.

Simplify using `only [if_neg haj, zero_add, h]`. Rewrite using `[← h1, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, mul_smul_comm, ← smul_add, mul_assoc, h2, ← mul_assoc, h3, add_mul, mul_assoc]`.
-/
theorem qdet_mul_vector (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ)
    (E : Fin (m + 1) → Fin (m + 1) → A) (x : Fin (m + 1) → A) (hE : GlRel E)
    (hx : ∀ a b j, E a b * x j = x j * E a b + if b = j then x a else 0)
    (u : ℂ) (j : Fin (m + 1)) :
    qdet E u * x j = x j * qdet E u + ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) •
      (x a * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) := by
  have h1 := GlobalTheory.T.capelli_left_comatrix_qminor_eq A m E hE u j j
  rw [if_pos rfl] at h1
  have h2 : ∀ a : Fin (m + 1), qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1) * x j
      = x j * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1) := by
    intro a
    refine GlobalTheory.T.qminor_commute_of_commute_columns A (m + 1) m E (x j) _ _ _ ?_
    intro c i
    rw [hx, if_neg (Fin.succAbove_ne j i), add_zero]
  have h3 : ∀ a : Fin (m + 1), Tm E u a j * x j = x j * Tm E u a j + x a := by
    intro a
    have h := hx a j j
    rw [if_pos rfl] at h
    unfold Tm
    by_cases haj : a = j
    · simp only [if_pos haj, add_mul, mul_add, h, Algebra.commutes]
      abel
    · simp only [if_neg haj, zero_add, h]
  rw [← h1, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add, mul_assoc, h2, ← mul_assoc, h3, add_mul,
    mul_assoc]

end GlobalTheory
