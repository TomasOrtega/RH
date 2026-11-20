import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

/- English proof (translation)
Establish `hrR : (0 : ℝ) < r` using `by exact_mod_cast hr`. Establish `heR : (0 : ℝ) < e` using `by exact_mod_cast Nat.pos_of_ne_zero he`. Establish `hapos : 0 < ((r : ℝ) * c) ^ e` using `by positivity`. Take `⟨T, hT⟩ : ∃ T : ℤ, T = ⌊((r : ℝ) * c) ^ e⌋ + 1` from `⟨_, rfl⟩`. Establish `hTa : ((r : ℝ) * c) ^ e < (T : ℝ)`.

Rewrite using `[hT]`. Use `push_cast`. Conclude with `Int.lt_floor_add_one _`. Establish `hTpos : (0 : ℝ) < T` using `hapos.trans hTa`. Establish `hupos : 0 < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c)` using `by positivity`.

Establish `hue : ((2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c)) ^ e = 2 * (e : ℝ) ^ e / ((r : ℝ) * c) ^ e`. Rewrite using `[div_pow, mul_pow, one_div, Real.rpow_inv_natCast_pow (by norm_num) he]`. Establish `hv0 : 0 ≤ (2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹)` using `by positivity`. Establish `hve : ((2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹)) ^ e = 2 * (e : ℝ) ^ e / T` using `Real.rpow_inv_natCast_pow (by positivity) he`. Establish `hvu : (2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c)`.

Rewrite using `[← pow_lt_pow_iff_left₀ hv0 hupos.le he, hve, hue]`. Conclude with `div_lt_div_of_pos_left (by positivity) hapos hTa`. Take `⟨q, hvq, hqu⟩` from `exists_rat_btwn hvu`. Establish `hq0 : (0 : ℝ) < q` using `lt_of_le_of_lt hv0 hvq`. Use `⟨q, by exact_mod_cast hq0, hqu, ?_⟩` and prove the remaining obligations.

Introduce `t ht`. Establish `hct : c ^ e * (r : ℝ) ^ e < t` using `(lt_div_iff₀ (by positivity)).1 ht`. Establish `hat : ((r : ℝ) * c) ^ e < t`. Combine the equalities or inequalities in the displayed calculation. Establish `hTt : (T : ℝ) ≤ t`.

Establish `h1` using `Int.floor_lt.2 hat`. Establish `: T ≤ t` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `key : 2 * (e : ℝ) ^ e < (q : ℝ) ^ e * t`. Establish `h1` using `pow_lt_pow_left₀ hvq hv0 he`.

Rewrite `h1` using `[hve, div_lt_iff₀ hTpos]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `key` after adjusting the coercions.
-/
theorem exists_rat_budget_term (r : ℕ) (hr : 0 < r) (e : ℕ) (he : e ≠ 0) (c : ℝ) (hc : 0 < c) :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) ∧
      ∀ t : ℤ, c ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < q ^ e * t := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heR : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he
  have hapos : 0 < ((r : ℝ) * c) ^ e := by positivity
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = ⌊((r : ℝ) * c) ^ e⌋ + 1 := ⟨_, rfl⟩
  have hTa : ((r : ℝ) * c) ^ e < (T : ℝ) := by
    rw [hT]; push_cast; exact Int.lt_floor_add_one _
  have hTpos : (0 : ℝ) < T := hapos.trans hTa
  have hupos : 0 < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) := by positivity
  have hue : ((2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c)) ^ e = 2 * (e : ℝ) ^ e / ((r : ℝ) * c) ^ e := by
    rw [div_pow, mul_pow, one_div, Real.rpow_inv_natCast_pow (by norm_num) he]
  have hv0 : 0 ≤ (2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹) := by positivity
  have hve : ((2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹)) ^ e = 2 * (e : ℝ) ^ e / T :=
    Real.rpow_inv_natCast_pow (by positivity) he
  have hvu : (2 * (e : ℝ) ^ e / T) ^ ((e : ℝ)⁻¹) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c) := by
    rw [← pow_lt_pow_iff_left₀ hv0 hupos.le he, hve, hue]
    exact div_lt_div_of_pos_left (by positivity) hapos hTa
  obtain ⟨q, hvq, hqu⟩ := exists_rat_btwn hvu
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt hv0 hvq
  refine ⟨q, by exact_mod_cast hq0, hqu, ?_⟩
  intro t ht
  have hct : c ^ e * (r : ℝ) ^ e < t := (lt_div_iff₀ (by positivity)).1 ht
  have hat : ((r : ℝ) * c) ^ e < t := by
    calc ((r : ℝ) * c) ^ e = c ^ e * (r : ℝ) ^ e := by rw [mul_pow, mul_comm]
      _ < t := hct
  have hTt : (T : ℝ) ≤ t := by
    have h1 := Int.floor_lt.2 hat
    have : T ≤ t := by omega
    exact_mod_cast this
  have key : 2 * (e : ℝ) ^ e < (q : ℝ) ^ e * t := by
    have h1 := pow_lt_pow_left₀ hvq hv0 he
    rw [hve, div_lt_iff₀ hTpos] at h1
    calc 2 * (e : ℝ) ^ e < (q : ℝ) ^ e * T := h1
      _ ≤ (q : ℝ) ^ e * t := mul_le_mul_of_nonneg_left hTt (by positivity)
  exact_mod_cast key

/- English proof (translation)
Introduce `n r c hr hc hsum`. Establish `hex : ∀ e, ∃ q : ℚ, 0 < q ∧ (e ∈ Finset.Icc 1 n → (q : ℝ) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c e) ∧ ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < q ^ e * t)`. Introduce `e`. Distinguish the cases in `he : e ∈ Finset.Icc 1 n`. Establish `he0 : e ≠ 0`.

Use `(Finset.mem_Icc.1 he).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨q, hq0, hqu, hqt⟩` from `exists_rat_budget_term r hr e he0 (c e) (hc e he)`. Conclude with `⟨q, hq0, fun _ => ⟨hqu, hqt⟩⟩`. Conclude with `⟨1, one_pos, fun h => absurd h he⟩`.

Use `choose h hpos hprop using hex`. Use `⟨h, hpos, ?_, fun e he => (hprop e he).2⟩` and prove the remaining obligations. Establish `hrR : (0 : ℝ) < r` using `by exact_mod_cast hr`. Establish `hR : ∑ e ∈ Finset.Icc 1 n, (h e : ℝ) < 1 / (r : ℝ)`. Break down `(Finset.Icc 1 n).eq_empty_or_nonempty with hE | hE` into its components or cases.

Rewrite using `[hE, Finset.sum_empty]`. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun e _ => by ring`.

Use `_ ≤ 1 / (r : ℝ) * 1 := mul_le_mul_of_nonneg_left hsum (by positivity)`. Use `_ = 1 / (r : ℝ) := mul_one _`. Establish `hR' : ((∑ e ∈ Finset.Icc 1 n, h e : ℚ) : ℝ) < ((1 / (r : ℚ) : ℚ) : ℝ)` using `by push_cast; exact hR`. Conclude with `Rat.cast_lt.mp hR'`.
-/
theorem exists_rat_budgets : ∀ (n r : ℕ) (c : ℕ → ℝ), 0 < r → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
    ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e ≤ 1 →
    ∃ (h : ℕ → ℚ), (∀ e, 0 < h e) ∧ ∑ e ∈ Finset.Icc 1 n, h e < 1 / (r : ℚ) ∧
      ∀ e ∈ Finset.Icc 1 n, ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e →
        2 * (e : ℚ) ^ e < h e ^ e * t := by
  intro n r c hr hc hsum
  have hex : ∀ e, ∃ q : ℚ, 0 < q ∧ (e ∈ Finset.Icc 1 n →
      (q : ℝ) < (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c e) ∧
      ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < q ^ e * t) := by
    intro e
    by_cases he : e ∈ Finset.Icc 1 n
    · have he0 : e ≠ 0 := by
        have := (Finset.mem_Icc.1 he).1
        omega
      obtain ⟨q, hq0, hqu, hqt⟩ := exists_rat_budget_term r hr e he0 (c e) (hc e he)
      exact ⟨q, hq0, fun _ => ⟨hqu, hqt⟩⟩
    · exact ⟨1, one_pos, fun h => absurd h he⟩
  choose h hpos hprop using hex
  refine ⟨h, hpos, ?_, fun e he => (hprop e he).2⟩
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hR : ∑ e ∈ Finset.Icc 1 n, (h e : ℝ) < 1 / (r : ℝ) := by
    rcases (Finset.Icc 1 n).eq_empty_or_nonempty with hE | hE
    · rw [hE, Finset.sum_empty]; positivity
    · calc ∑ e ∈ Finset.Icc 1 n, (h e : ℝ)
          < ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / (r * c e) :=
            Finset.sum_lt_sum_of_nonempty hE (fun e he => (hprop e he).1)
        _ = 1 / (r : ℝ) * ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun e _ => by ring
        _ ≤ 1 / (r : ℝ) * 1 := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 1 / (r : ℝ) := mul_one _
  have hR' : ((∑ e ∈ Finset.Icc 1 n, h e : ℚ) : ℝ) < ((1 / (r : ℚ) : ℚ) : ℝ) := by
    push_cast; exact hR
  exact Rat.cast_lt.mp hR'

end GlobalTheory.PairStep
