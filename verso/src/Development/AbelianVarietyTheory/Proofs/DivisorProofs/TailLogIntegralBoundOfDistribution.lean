import Mathlib
open scoped ComplexOrder Matrix
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `h` using `summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (D + 1) (r := (1 / 2 : ℝ)) (by norm_num)`. Establish `h2` using `(summable_nat_add_iff 2).mpr h`. Establish `h3` using `h2.mul_left 4`. Use `h3.congr ?_` and prove the remaining obligations. Introduce `k`.

Use `push_cast`. Simplify using `only [one_div, inv_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem summable_shell_weights (D : ℕ) :
    Summable (fun k : ℕ => ((k : ℝ) + 2) ^ (D + 1) / 2 ^ k) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (D + 1) (r := (1 / 2 : ℝ))
    (by norm_num)
  have h2 := (summable_nat_add_iff 2).mpr h
  have h3 := h2.mul_left 4
  refine h3.congr ?_
  intro k
  push_cast
  simp only [one_div, inv_pow]
  field_simp
  ring

/- English proof (translation)
Introduce `X _ μ r D C R _hr hC hR htail`. Establish `hRpos : 0 < R` using `lt_of_lt_of_le (Real.exp_pos 1) hR`. Establish `hL1 : 1 ≤ Real.log R`. Use `Real.log_le_log (Real.exp_pos 1) hR` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis.

Establish `hLnn : 0 ≤ Real.log R` using `by linarith`. Establish `hlog2 : Real.log 2 ≤ 1`. Use `Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith` as an intermediate fact. Establish `hlog2nn : 0 ≤ Real.log 2` using `Real.log_nonneg (by norm_num)`. Set `S : ℕ → Set X` to `fun k => {x | 2 ^ k * R ≤ r x ∧ r x < 2 ^ (k + 1) * R}`.

Establish `hcover : {x | R ≤ r x} ⊆ ⋃ k, S k`. Introduce `x hx`. Simplify using `only [Set.mem_setOf_eq] at hx`. Establish `hex : ∃ n : ℕ, r x < 2 ^ (n + 1) * R`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (r x / R) (by norm_num : (1:ℝ) < 2)`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `: r x / R < 2 ^ (n + 1)` using `lt_of_lt_of_le hn (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))`. Rewrite `this` using `[div_lt_iff₀ hRpos]`. Then use the resulting hypothesis. Establish `h1 : 2 ^ (Nat.find hex) * R ≤ r x`. Distinguish the cases in `h0 : Nat.find hex = 0`.

Rewrite using `[h0]`. Simplify using `using hx`. Establish `hpos : 0 < Nat.find hex` using `Nat.pos_of_ne_zero h0`. Establish `hmin` using `Nat.find_min hex (Nat.sub_lt hpos one_pos)`. Use `push_neg at hmin`.

Establish `he : Nat.find hex - 1 + 1 = Nat.find hex` using `by omega`. Rewrite `hmin` using `[he]`. Then use the resulting hypothesis. Conclude with `Set.mem_iUnion.mpr ⟨Nat.find hex, show _ ∧ _ from ⟨h1, Nat.find_spec hex⟩⟩`. Establish `hshell : ∀ k : ℕ, ∫⁻ x in S k, ENNReal.ofReal (Real.log (r x)) ∂μ ≤ ENNReal.ofReal (C * Real.log R ^ (D + 1) / R * (((k : ℝ) + 2) ^ (D + 1) / 2 ^ k))`. Introduce `k`.

Establish `hρ : R ≤ 2 ^ k * R` using `le_mul_of_one_le_left hRpos.le (one_le_pow₀ (by norm_num))`. Establish `hlogρ : Real.log (2 ^ k * R) = k * Real.log 2 + Real.log R`. Rewrite using `[Real.log_mul (by positivity) hRpos.ne', Real.log_pow]`. Establish `hkL : 0 ≤ ((k : ℝ) + 2) * Real.log R` using `mul_nonneg (by positivity) hLnn`. Establish `hfb : ∀ x ∈ S k, ENNReal.ofReal (Real.log (r x)) ≤ ENNReal.ofReal (((k : ℝ) + 2) * Real.log R)`.

Introduce `x hx`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `hxpos : 0 < r x` using `lt_of_lt_of_le (by positivity) hx.1`. Use `Real.log_le_log hxpos hx.2.le` as an intermediate fact. Rewrite `this` using `[Real.log_mul (by positivity) hRpos.ne', Real.log_pow]`.

Move the coercions through the operations in `at this`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Apply `lintegral_mono_ae` to reduce the goal to its premises. Rewrite using `[ae_restrict_iff' ?_]`.

Conclude with `Filter.Eventually.of_forall hfb`. Conclude with `(measurableSet_le measurable_const _hr).inter (measurableSet_lt _hr measurable_const)`. Use `_ = ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) * μ (S k) := setLIntegral_const _ _`. Use `_ ≤ ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) * μ {x | 2 ^ k * R ≤ r x} := by gcongr; intro x hx; exact hx.1`. Use `_ ≤ ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) * ENNReal.ofReal (C * Real.log (2 ^ k * R) ^ D / (2 ^ k * R)) := by gcongr; exact htail _ hρ`.

Use `_ = ENNReal.ofReal (((k : ℝ) + 2) * Real.log R * (C * Real.log (2 ^ k * R) ^ D / (2 ^ k * R))) := (ENNReal.ofReal_mul hkL).symm`. Use `_ ≤ _ := by`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[hlogρ]`. Establish `h1 : (k : ℝ) * Real.log 2 + Real.log R ≤ ((k : ℝ) + 2) * Real.log R` using `by nlinarith`.

Establish `h0 : 0 ≤ (k : ℝ) * Real.log 2 + Real.log R` using `add_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog2nn) hLnn`. Establish `hp` using `pow_le_pow_left₀ h0 h1 D`. Combine the equalities or inequalities in the displayed calculation. Establish `hsum` using `summable_shell_weights D`. Establish `hnn : ∀ k : ℕ, 0 ≤ C * Real.log R ^ (D + 1) / R * (((k : ℝ) + 2) ^ (D + 1) / 2 ^ k)` using `fun k => mul_nonneg (div_nonneg (mul_nonneg hC (pow_nonneg hLnn _)) hRpos.le) (by positivity)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem lintegral_log_le_of_tail_bound : ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X) (r : X → ℝ) (D : ℕ) (C R : ℝ), Measurable r → 0 ≤ C → Real.exp 1 ≤ R → (∀ ρ, R ≤ ρ → μ {x | ρ ≤ r x} ≤ ENNReal.ofReal (C * Real.log ρ ^ D / ρ)) → ∫⁻ x in {x | R ≤ r x}, ENNReal.ofReal (Real.log (r x)) ∂μ ≤ ENNReal.ofReal (C * (∑' k : ℕ, ((k : ℝ) + 2) ^ (D + 1) / 2 ^ k) * Real.log R ^ (D + 1) / R) := by
  intro X _ μ r D C R _hr hC hR htail
  have hRpos : 0 < R := lt_of_lt_of_le (Real.exp_pos 1) hR
  have hL1 : 1 ≤ Real.log R := by
    have := Real.log_le_log (Real.exp_pos 1) hR
    rwa [Real.log_exp] at this
  have hLnn : 0 ≤ Real.log R := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  let S : ℕ → Set X := fun k => {x | 2 ^ k * R ≤ r x ∧ r x < 2 ^ (k + 1) * R}
  have hcover : {x | R ≤ r x} ⊆ ⋃ k, S k := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    have hex : ∃ n : ℕ, r x < 2 ^ (n + 1) * R := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (r x / R) (by norm_num : (1:ℝ) < 2)
      refine ⟨n, ?_⟩
      have : r x / R < 2 ^ (n + 1) :=
        lt_of_lt_of_le hn (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))
      rwa [div_lt_iff₀ hRpos] at this
    classical
    have h1 : 2 ^ (Nat.find hex) * R ≤ r x := by
      by_cases h0 : Nat.find hex = 0
      · rw [h0]; simpa using hx
      · have hpos : 0 < Nat.find hex := Nat.pos_of_ne_zero h0
        have hmin := Nat.find_min hex (Nat.sub_lt hpos one_pos)
        push_neg at hmin
        have he : Nat.find hex - 1 + 1 = Nat.find hex := by omega
        rwa [he] at hmin
    exact Set.mem_iUnion.mpr ⟨Nat.find hex, show _ ∧ _ from ⟨h1, Nat.find_spec hex⟩⟩
  have hshell : ∀ k : ℕ, ∫⁻ x in S k, ENNReal.ofReal (Real.log (r x)) ∂μ ≤
      ENNReal.ofReal (C * Real.log R ^ (D + 1) / R * (((k : ℝ) + 2) ^ (D + 1) / 2 ^ k)) := by
    intro k
    have hρ : R ≤ 2 ^ k * R := le_mul_of_one_le_left hRpos.le (one_le_pow₀ (by norm_num))
    have hlogρ : Real.log (2 ^ k * R) = k * Real.log 2 + Real.log R := by
      rw [Real.log_mul (by positivity) hRpos.ne', Real.log_pow]
    have hkL : 0 ≤ ((k : ℝ) + 2) * Real.log R := mul_nonneg (by positivity) hLnn
    have hfb : ∀ x ∈ S k, ENNReal.ofReal (Real.log (r x)) ≤ ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) := by
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      have hxpos : 0 < r x := lt_of_lt_of_le (by positivity) hx.1
      have := Real.log_le_log hxpos hx.2.le
      rw [Real.log_mul (by positivity) hRpos.ne', Real.log_pow] at this
      push_cast at this
      nlinarith
    calc ∫⁻ x in S k, ENNReal.ofReal (Real.log (r x)) ∂μ
        ≤ ∫⁻ x in S k, ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) ∂μ := by
          apply lintegral_mono_ae
          rw [ae_restrict_iff' ?_]
          · exact Filter.Eventually.of_forall hfb
          · exact (measurableSet_le measurable_const _hr).inter (measurableSet_lt _hr measurable_const)
      _ = ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) * μ (S k) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) * μ {x | 2 ^ k * R ≤ r x} := by
          gcongr; intro x hx; exact hx.1
      _ ≤ ENNReal.ofReal (((k : ℝ) + 2) * Real.log R) *
            ENNReal.ofReal (C * Real.log (2 ^ k * R) ^ D / (2 ^ k * R)) := by
          gcongr; exact htail _ hρ
      _ = ENNReal.ofReal (((k : ℝ) + 2) * Real.log R * (C * Real.log (2 ^ k * R) ^ D / (2 ^ k * R))) :=
          (ENNReal.ofReal_mul hkL).symm
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          rw [hlogρ]
          have h1 : (k : ℝ) * Real.log 2 + Real.log R ≤ ((k : ℝ) + 2) * Real.log R := by nlinarith
          have h0 : 0 ≤ (k : ℝ) * Real.log 2 + Real.log R :=
            add_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog2nn) hLnn
          have hp := pow_le_pow_left₀ h0 h1 D
          calc ((k : ℝ) + 2) * Real.log R * (C * ((k : ℝ) * Real.log 2 + Real.log R) ^ D / (2 ^ k * R))
              ≤ ((k : ℝ) + 2) * Real.log R * (C * (((k : ℝ) + 2) * Real.log R) ^ D / (2 ^ k * R)) := by
                gcongr
            _ = _ := by rw [mul_pow]; field_simp; ring
  have hsum := summable_shell_weights D
  have hnn : ∀ k : ℕ, 0 ≤ C * Real.log R ^ (D + 1) / R * (((k : ℝ) + 2) ^ (D + 1) / 2 ^ k) :=
    fun k => mul_nonneg (div_nonneg (mul_nonneg hC (pow_nonneg hLnn _)) hRpos.le) (by positivity)
  calc ∫⁻ x in {x | R ≤ r x}, ENNReal.ofReal (Real.log (r x)) ∂μ
      ≤ ∫⁻ x in ⋃ k, S k, ENNReal.ofReal (Real.log (r x)) ∂μ := lintegral_mono_set hcover
    _ ≤ ∑' k, ∫⁻ x in S k, ENNReal.ofReal (Real.log (r x)) ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (C * Real.log R ^ (D + 1) / R * (((k : ℝ) + 2) ^ (D + 1) / 2 ^ k)) :=
        ENNReal.tsum_le_tsum hshell
    _ = ENNReal.ofReal (∑' k : ℕ, C * Real.log R ^ (D + 1) / R * (((k : ℝ) + 2) ^ (D + 1) / 2 ^ k)) :=
        (ENNReal.ofReal_tsum_of_nonneg hnn (hsum.mul_left _)).symm
    _ = _ := by rw [tsum_mul_left]; congr 1; ring

end GlobalTheory
