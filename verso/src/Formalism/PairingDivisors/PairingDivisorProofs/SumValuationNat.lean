import Mathlib
import Formalism.PairingDivisors.StatementA
import Formalism.PairingDivisors.StatementX
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ProdFormula

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)

namespace Formalism.PairingDivisionLocalBalance

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ratio_valuation : RatioVal := by
  intro K _ _ _ w a a' g ha ha'
  rw [div_eq_mul_inv, Formalism.DivisionValues.ValuationRepresentative.vw_mul w a a'⁻¹ ha (inv_ne_zero ha'), Formalism.DivisionValues.ValuationRepresentative.vw_inv]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem gaussValUnit : GaussUnit := by
  intro K _ _ _ w G G' q hq h hv
  have hq0 : (q : K) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hG : (G : K) ≠ 0 := by intro h0; rw [h0, zero_mul] at h; exact hq0 h.symm
  have hG' : (G' : K) ≠ 0 := by intro h0; rw [h0, mul_zero] at h; exact hq0 h.symm
  have h1 := Formalism.DivisionValues.ValuationRepresentative.vw_mul w (G : K) (G' : K) hG hG'
  rw [h, hv] at h1
  have h2 := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w G
  have h3 := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w G'
  omega

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem vw_prod {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) {P : Type} (R : Finset P)
    (e : P → K) (he : ∀ q ∈ R, e q ≠ 0) : vw w (∏ q ∈ R, e q) = ∑ q ∈ R, vw w (e q) := by
  classical
  induction R using Finset.induction_on with
  | empty => simp [Formalism.DivisionValues.ValuationRepresentative.vw_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (he a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun q hq => he q (Finset.mem_insert_of_mem hq)),
      ih fun q hq => he q (Finset.mem_insert_of_mem hq)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem upper_part_stays : UpperStays := by
  intro K _ _ _ w P R y y' e B hy hyy he hB
  have hy' : y' ≠ 0 := by intro h0; rw [h0, zero_mul] at hyy; exact hy hyy
  have hp : ∏ q ∈ R, e q ≠ 0 := by intro h0; rw [h0, mul_zero] at hyy; exact hy hyy
  have h1 := Formalism.DivisionValues.ValuationRepresentative.vw_mul w y' _ hy' hp
  rw [← hyy, vw_prod w R e (fun q hq => (Finset.prod_ne_zero_iff.mp hp) q hq)] at h1
  have h2 : 0 ≤ ∑ q ∈ R, vw w (e q) := Finset.sum_nonneg he
  have h3 : vw w y' ≤ vw w y := by omega
  exact le_trans (by exact_mod_cast h3) hB

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion. Clear the denominators using the available nonvanishing facts.
-/
theorem sum_valuation_nat : SumValNat := by
  intro K _ _ _ _ n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Formalism.DivisionValues.ValuationRepresentative.vw_zero]
  · have hn0 : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
    obtain ⟨h1, h2⟩ := Formalism.DivisionValues.prod_formula' K (n : K) hn0
    refine ⟨h1, ?_⟩
    rw [← h2]
    have hc : (Fintype.card (InfinitePlace K) : ℝ) * 2 = (finrank ℚ K : ℝ) := by
      have h3 := IsTotallyComplex.finrank K
      have h4 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
      have h5 := IsTotallyComplex.nrRealPlaces_eq_zero K
      rw [h3, h4, h5]; push_cast; ring
    have hpos : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
    simp only [map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hc]
    have : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hc; linarith
    field_simp

end Formalism.PairingDivisionLocalBalance
