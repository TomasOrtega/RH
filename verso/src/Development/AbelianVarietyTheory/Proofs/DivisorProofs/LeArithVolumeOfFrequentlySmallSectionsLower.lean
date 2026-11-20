import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem le_arVol_of_frequently_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (a : ℝ), (∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop, (L.pow N).smallSec.Finite ∧ (a / (D + 1).factorial - ε) * (N : ℝ) ^ (D + 1) ≤ Real.log ((L.pow N).smallSec.ncard : ℝ)) → (a : EReal) ≤ arVol L D := by
  intro k _ X _ p D L a h
  have hc : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  have key : ∀ δ : ℝ, 0 < δ → ((a - δ : ℝ) : EReal) ≤ arVol L D := by
    intro δ hδ
    refine Filter.le_limsup_of_frequently_le ?_
    have hε : 0 < δ / ((D + 1).factorial : ℝ) := div_pos hδ hc
    refine ((h _ hε).and_eventually (eventually_gt_atTop 0)).mono ?_
    rintro N ⟨⟨hfin, hle⟩, hN⟩
    have h0 : 0 < (L.pow N).smallSec.ncard := (Set.ncard_pos hfin).2 ⟨_, (L.pow N).zero_mem_smallSec⟩
    rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
      ENNReal.log_ofReal_of_pos (by exact_mod_cast h0), ← EReal.coe_mul, EReal.coe_le_coe_iff]
    have hNp : (0 : ℝ) < (N : ℝ) ^ (D + 1) := by positivity
    rw [mul_div_assoc', le_div_iff₀ hNp]
    have e : (a / ((D + 1).factorial : ℝ) - δ / ((D + 1).factorial : ℝ)) * ((D + 1).factorial : ℝ) = a - δ := by
      field_simp
    calc (a - δ) * (N : ℝ) ^ (D + 1)
        = ((a / ((D + 1).factorial : ℝ) - δ / ((D + 1).factorial : ℝ)) * (N : ℝ) ^ (D + 1)) * ((D + 1).factorial : ℝ) := by
          rw [← e]; ring
      _ ≤ Real.log ((L.pow N).smallSec.ncard : ℝ) * ((D + 1).factorial : ℝ) :=
          mul_le_mul_of_nonneg_right hle hc.le
  refine le_of_forall_lt_imp_le_of_dense fun z hz => ?_
  induction z using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hz (not_lt.2 le_top)
  | coe r =>
    have hr : r < a := EReal.coe_lt_coe_iff.1 hz
    have := key (a - r) (by linarith)
    rwa [sub_sub_cancel] at this

end GlobalTheory.VolBr
