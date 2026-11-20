import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

/- English proof (translation)
Establish `h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2)` using `Real.summable_one_div_nat_pow.mpr (by norm_num)`. Use `((summable_nat_add_iff 1).mpr h).congr fun n => ?_` and prove the remaining obligations. Simplify using `only [Nat.cast_add, Nat.cast_one, one_div, add_comm (n : ℝ) 1]`.
-/
theorem summable_inv_one_add_sq :
    Summable (fun n : ℕ => ((1 + (n : ℝ)) ^ 2)⁻¹) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine ((summable_nat_add_iff 1).mpr h).congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one, one_div, add_comm (n : ℝ) 1]

/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero => exact Summable.of_finite`. Consider the case `succ r ih`. Establish `h` using `GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_inv_one_add_sq.mul_of_nonneg ih (fun n => inv_nonneg.mpr (sq_nonneg _)) (fun m => Finset.prod_nonneg fun i _ => inv_nonneg.mpr (sq_nonneg _))`.

Rewrite using `[← (Fin.consEquiv fun _ : Fin (r + 1) => ℕ).summable_iff]`. Use `h.congr fun p => ?_` and prove the remaining obligations. Simplify using `[Fin.consEquiv, Fin.prod_univ_succ, mul_comm]`.
-/
theorem summable_prod_inv_one_add_sq :
    ∀ r : ℕ, Summable (fun m : Fin r → ℕ => ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹) := by
  intro r
  induction r with
  | zero => exact Summable.of_finite
  | succ r ih =>
    have h := GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_inv_one_add_sq.mul_of_nonneg ih
      (fun n => inv_nonneg.mpr (sq_nonneg _))
      (fun m => Finset.prod_nonneg fun i _ => inv_nonneg.mpr (sq_nonneg _))
    rw [← (Fin.consEquiv fun _ : Fin (r + 1) => ℕ).summable_iff]
    refine h.congr fun p => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ, mul_comm]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
