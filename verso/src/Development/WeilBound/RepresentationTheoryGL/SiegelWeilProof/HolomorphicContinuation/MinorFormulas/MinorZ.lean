import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDivOf

noncomputable section

namespace PositivityTheory.Rg.Sw.SP

open Polynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem divZ_C_mul {n : ℕ} (i : ℕ) (p : Polynomial ℂ) (R : Fm n) (h : (X : Polynomial ℂ) ^ i ∣ p) :
    DivZ i (MvPolynomial.C p * R) := by
  intro e
  rw [MvPolynomial.coeff_C_mul]
  exact Dvd.dvd.mul_right h _

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem pow_dvd_prod (N ρ i : ℕ) (f : ℕ → ℕ → Polynomial ℂ) (hi : i ≤ N)
    (hf : ∀ l < i, ∃ i' < ρ, f l i' = -X) :
    (X : Polynomial ℂ) ^ i ∣ ∏ l ∈ Finset.range N, ∏ i' ∈ Finset.range ρ, f l i' := by
  have h1 : (X : Polynomial ℂ) ^ i = ∏ _l ∈ Finset.range i, (X : Polynomial ℂ) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [h1]
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun l hl => ?_)
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono hi))
  obtain ⟨i', hi', he⟩ := hf l (Finset.mem_range.1 hl)
  have h2 : f l i' ∣ ∏ i' ∈ Finset.range ρ, f l i' := Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hi')
  rw [he] at h2
  exact dvd_trans (dvd_neg.2 dvd_rfl) h2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem minorZ_of (hF : MinorFormula) : MinorZ := by
  intro n s hs m i N hiN I J
  rw [hF n s hs m false (m + i) N I J]
  apply divZ_C_mul
  apply Dvd.dvd.mul_left
  apply pow_dvd_prod N (m + i) i _ hiN
  intro l hl
  refine ⟨m + l, by omega, ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_add, map_sub, map_add]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem minorZ'_of (hF : MinorFormula) : MinorZ' := by
  intro n s hs m j N hjN I J
  rw [hF n s hs m true j N I J]
  apply divZ_C_mul
  apply Dvd.dvd.mul_left
  apply pow_dvd_prod N j j _ hjN
  intro l hl
  refine ⟨l, hl, ?_⟩
  simp only [↓reduceIte, sub_self, map_zero, sub_zero]

end PositivityTheory.Rg.Sw.SP
