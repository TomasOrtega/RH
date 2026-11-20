import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.DataTies
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `Ω _ ν r q ρ Ph Rr s hρm hρ0 hPm hP0 hP1 hR hbd`. Establish `hR0 : (0:ℝ) ≤ Rr` using `le_trans zero_le_one hR`. Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Substitute `hr` using the available equality. Establish `hs : s = ∅` using `Finset.eq_empty_of_isEmpty s`.

Substitute `hs` using the available equality. Simplify using `using hP1`. Use `set N : ℕ := 2 * (r * q) with hN`. Set `u : Fin r → Ω → ℝ` to `fun a x => if a ∈ s then ρ a x else Rr`. Establish `hrR : (0:ℝ) < r` using `by exact_mod_cast hr`.

Establish `hr0 : r ≠ 0` using `Nat.pos_iff_ne_zero.mp hr`. Establish `hpt : ∀ᵐ x ∂ν, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ≤ ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x)`. Establish `hall : ∀ᵐ x ∂ν, ∀ a, 0 ≤ ρ a x` using `ae_all_iff.mpr hρ0`. Use `filter_upwards [hall] with x hx`. Establish `hu0 : ∀ a, 0 ≤ u a x` using `fun a => by`.

Apply the tactic sequence `by_cases ha : a ∈ s <;> simp [u, ha, hx a, hR0]`. Establish `h1 : (∏ a ∈ s, ρ a x) ^ (2 * q) ≤ ∏ a : Fin r, u a x ^ (2 * q)`. Establish `: (∏ a ∈ s, ρ a x) ^ (2 * q) = ∏ a : Fin r, (if a ∈ s then ρ a x ^ (2 * q) else 1)`. Rewrite using `[Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_pow]`. Rewrite using `[this]`.

Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `a _`. Distinguish the cases in `ha : a ∈ s`. Simplify using `[ha, pow_nonneg (hx a)]`. Simplify using `[ha]`.

Introduce `a _`. Distinguish the cases in `ha : a ∈ s`. Simplify using `[u, ha]`. Simplify using `[u, ha, one_le_pow₀ hR]`. Establish `h2 : ∏ a : Fin r, u a x ^ (2 * q) ≤ ∑ a : Fin r, (r:ℝ)⁻¹ * u a x ^ N`.

Establish `hw : ∑ _a : Fin r, (r:ℝ)⁻¹ = 1`. Simplify using `[Finset.card_univ, Fintype.card_fin, hrR.ne']`. Establish `key` using `Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin r)) (fun _ => (r:ℝ)⁻¹) (fun a => (u a x ^ (2 * q)) ^ r) (fun _ _ => inv_nonneg.mpr hrR.le) hw (fun a _ => pow_nonneg (pow_nonneg (hu0 a) _) _)`. Establish `e1 : ∀ a, ((u a x ^ (2 * q)) ^ r) ^ ((r:ℝ)⁻¹) = u a x ^ (2 * q)` using `fun a => Real.pow_rpow_inv_natCast (pow_nonneg (hu0 a) _) hr0`. Establish `e2 : ∀ a, (u a x ^ (2 * q)) ^ r = u a x ^ N` using `fun a => by`.

Rewrite using `[← pow_mul, hN]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e1] at key`. Simplify using `only [e2] at key`.

Conclude with `key`. Establish `hP : 0 ≤ Ph x` using `hP0 x`. Establish `h3 : (∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x ≤ ∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul]`.

Use `congr 1`. Use extensionality with `a`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.ofReal_sum_of_nonneg]`.

Use `congr 1`. Use extensionality with `a`. Rewrite using `[ENNReal.ofReal_mul (inv_nonneg.mpr hrR.le)]`. Introduce `a _`. Conclude with `mul_nonneg (inv_nonneg.mpr hrR.le) (mul_nonneg (pow_nonneg (hu0 a) _) hP)`.

Establish `hum : ∀ a, AEMeasurable (u a) ν` using `fun a => by`. Distinguish the cases in `ha : a ∈ s`. Simplify `hρm a` using `[u, ha]`. Simplify using `only [u, ha, if_false]`. Conclude with `aemeasurable_const`.

Establish `hint : ∀ a, ∫⁻ x, ENNReal.ofReal (u a x ^ N * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ N)`. Introduce `a`. Distinguish the cases in `ha : a ∈ s`. Simplify `hbd a` using `[u, ha]`. Simplify using `only [u, ha, if_false]`.

Establish `hRN : (0:ℝ) ≤ Rr ^ N` using `pow_nonneg hR0 _`. Repeatedly rewrite using `[ENNReal.ofReal_mul hRN]`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[lintegral_finset_sum']`. Use `congr 1`. Use extensionality with `a`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Introduce `a _`.

Conclude with `(((hum a).pow_const N).mul hPm).ennreal_ofReal.const_mul _`. Use `_ ≤ ∑ _a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (Rr ^ N) := by gcongr with a`. Conclude with `hint a`. Use `_ = ENNReal.ofReal (Rr ^ N) := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]`.

Establish `: (r : ℝ≥0∞) * ENNReal.ofReal ((r:ℝ)⁻¹) = 1`. Rewrite using `[← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg r), mul_inv_cancel₀ hrR.ne', ENNReal.ofReal_one]`. Rewrite using `[this, one_mul]`.
-/
theorem lintegral_prod_pow_le_of_moments : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r q : ℕ) (ρ : Fin r → Ω → ℝ) (Ph : Ω → ℝ) (Rr : ℝ) (s : Finset (Fin r)), (∀ a, AEMeasurable (ρ a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 ≤ ρ a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν ≤ 1 → 1 ≤ Rr → (∀ a, ∫⁻ x, ENNReal.ofReal (ρ a x ^ (2 * (r * q)) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q)))) → ∫⁻ x, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q))) := by
  classical
  intro Ω _ ν r q ρ Ph Rr s hρm hρ0 hPm hP0 hP1 hR hbd
  have hR0 : (0:ℝ) ≤ Rr := le_trans zero_le_one hR
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hs : s = ∅ := Finset.eq_empty_of_isEmpty s
    subst hs
    simpa using hP1
  · set N : ℕ := 2 * (r * q) with hN
    let u : Fin r → Ω → ℝ := fun a x => if a ∈ s then ρ a x else Rr
    have hrR : (0:ℝ) < r := by exact_mod_cast hr
    have hr0 : r ≠ 0 := Nat.pos_iff_ne_zero.mp hr
    have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x)
        ≤ ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) := by
      have hall : ∀ᵐ x ∂ν, ∀ a, 0 ≤ ρ a x := ae_all_iff.mpr hρ0
      filter_upwards [hall] with x hx
      have hu0 : ∀ a, 0 ≤ u a x := fun a => by
        by_cases ha : a ∈ s <;> simp [u, ha, hx a, hR0]
      have h1 : (∏ a ∈ s, ρ a x) ^ (2 * q) ≤ ∏ a : Fin r, u a x ^ (2 * q) := by
        have : (∏ a ∈ s, ρ a x) ^ (2 * q)
            = ∏ a : Fin r, (if a ∈ s then ρ a x ^ (2 * q) else 1) := by
          rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_pow]
        rw [this]
        apply Finset.prod_le_prod
        · intro a _
          by_cases ha : a ∈ s
          · simp [ha, pow_nonneg (hx a)]
          · simp [ha]
        · intro a _
          by_cases ha : a ∈ s
          · simp [u, ha]
          · simp [u, ha, one_le_pow₀ hR]
      have h2 : ∏ a : Fin r, u a x ^ (2 * q) ≤ ∑ a : Fin r, (r:ℝ)⁻¹ * u a x ^ N := by
        have hw : ∑ _a : Fin r, (r:ℝ)⁻¹ = 1 := by
          simp [Finset.card_univ, Fintype.card_fin, hrR.ne']
        have key := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin r))
          (fun _ => (r:ℝ)⁻¹) (fun a => (u a x ^ (2 * q)) ^ r)
          (fun _ _ => inv_nonneg.mpr hrR.le) hw (fun a _ => pow_nonneg (pow_nonneg (hu0 a) _) _)
        have e1 : ∀ a, ((u a x ^ (2 * q)) ^ r) ^ ((r:ℝ)⁻¹) = u a x ^ (2 * q) := fun a =>
          Real.pow_rpow_inv_natCast (pow_nonneg (hu0 a) _) hr0
        have e2 : ∀ a, (u a x ^ (2 * q)) ^ r = u a x ^ N := fun a => by
          rw [← pow_mul, hN]; congr 1; ring
        simp only [e1] at key
        simp only [e2] at key
        exact key
      have hP : 0 ≤ Ph x := hP0 x
      have h3 : (∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x
          ≤ ∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x) := by
        calc (∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x
            ≤ (∑ a : Fin r, (r:ℝ)⁻¹ * u a x ^ N) * Ph x :=
              mul_le_mul_of_nonneg_right (h1.trans h2) hP
          _ = ∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x) := by
              rw [Finset.sum_mul]; congr 1; ext a; ring
      calc ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x)
          ≤ ENNReal.ofReal (∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x)) :=
            ENNReal.ofReal_le_ofReal h3
        _ = ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            · congr 1; ext a
              rw [ENNReal.ofReal_mul (inv_nonneg.mpr hrR.le)]
            · intro a _
              exact mul_nonneg (inv_nonneg.mpr hrR.le) (mul_nonneg (pow_nonneg (hu0 a) _) hP)
    have hum : ∀ a, AEMeasurable (u a) ν := fun a => by
      by_cases ha : a ∈ s
      · simpa [u, ha] using hρm a
      · simp only [u, ha, if_false]; exact aemeasurable_const
    have hint : ∀ a, ∫⁻ x, ENNReal.ofReal (u a x ^ N * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ N) := by
      intro a
      by_cases ha : a ∈ s
      · simpa [u, ha] using hbd a
      · simp only [u, ha, if_false]
        have hRN : (0:ℝ) ≤ Rr ^ N := pow_nonneg hR0 _
        simp_rw [ENNReal.ofReal_mul hRN]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        calc ENNReal.ofReal (Rr ^ N) * ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν
            ≤ ENNReal.ofReal (Rr ^ N) * 1 := by gcongr
          _ = ENNReal.ofReal (Rr ^ N) := mul_one _
    calc ∫⁻ x, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ∂ν
        ≤ ∫⁻ x, ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) ∂ν :=
          lintegral_mono_ae hpt
      _ = ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ∫⁻ x, ENNReal.ofReal (u a x ^ N * Ph x) ∂ν := by
          rw [lintegral_finset_sum']
          · congr 1; ext a
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          · intro a _
            exact (((hum a).pow_const N).mul hPm).ennreal_ofReal.const_mul _
      _ ≤ ∑ _a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (Rr ^ N) := by
          gcongr with a
          exact hint a
      _ = ENNReal.ofReal (Rr ^ N) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
          have : (r : ℝ≥0∞) * ENNReal.ofReal ((r:ℝ)⁻¹) = 1 := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg r),
              mul_inv_cancel₀ hrR.ne', ENNReal.ofReal_one]
          rw [this, one_mul]

end GlobalTheory
