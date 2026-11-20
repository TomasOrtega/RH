import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeGtDvdEval
open scoped TensorProduct Polynomial

namespace GlobalTheory

open Polynomial in

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval`. Consider the case `exact _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval`. Consider the case `(apply _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval ..)`.
-/
theorem exists_prime_gt_dvd_eval :
    ∀ f : ℤ[X], 0 < f.natDegree → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
  first
  | exact @_root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval
  | exact _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval
  | (apply _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval ..)

end GlobalTheory
