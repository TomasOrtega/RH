import Mathlib
import Formalism.DirichletDensity.Statement

open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt Complex LSeries

noncomputable section

namespace Formalism.HF.P

variable {q : ℕ} [NeZero q] {a : ZMod q}

/- English proof (translation)
Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Rewrite using `[LSeries.term_zero, residueClass_apply_zero, zero_div, Complex.ofReal_zero]`. Rewrite using `[LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]`.
-/
private lemma apld_term_lemma (a : ZMod q) (x : ℝ) (n : ℕ) :
    LSeries.term (fun n ↦ (residueClass a n : ℂ)) (x : ℂ) n =
      ((residueClass a n / (n : ℝ) ^ x : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, residueClass_apply_zero, zero_div, Complex.ofReal_zero]
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_natCast]

/- English proof (translation)
Establish `hx' : (x : ℂ) ∈ {s : ℂ | 1 < s.re}` using `by simpa using hx`. Establish `hLS : LSeries (fun n ↦ (residueClass a n : ℂ)) x = ((∑' n, residueClass a n / (n : ℝ) ^ x : ℝ) : ℂ)`. Unfold `LSeries`. Rewrite using `[Complex.ofReal_tsum]`. Conclude with `tsum_congr fun n => apld_term_lemma a x n`.

Establish `hE` using `eqOn_LFunctionResidueClassAux ha hx'`. Establish `hA : LFunctionResidueClassAux a x = (((∑' n, residueClass a n / (n : ℝ) ^ x) - (q.totient : ℝ)⁻¹ / (x - 1) : ℝ) : ℂ)`. Rewrite using `[hE]`. Simplify using `only [hLS]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[hA, Complex.ofReal_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma apld_tsum_residueClass_eq (ha : IsUnit a) {x : ℝ} (hx : 1 < x) :
    ∑' n, residueClass a n / (n : ℝ) ^ x =
      (LFunctionResidueClassAux a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
  have hx' : (x : ℂ) ∈ {s : ℂ | 1 < s.re} := by simpa using hx
  have hLS : LSeries (fun n ↦ (residueClass a n : ℂ)) x =
      ((∑' n, residueClass a n / (n : ℝ) ^ x : ℝ) : ℂ) := by
    unfold LSeries
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun n => apld_term_lemma a x n
  have hE := eqOn_LFunctionResidueClassAux ha hx'
  have hA : LFunctionResidueClassAux a x =
      (((∑' n, residueClass a n / (n : ℝ) ^ x) - (q.totient : ℝ)⁻¹ / (x - 1) : ℝ) : ℂ) := by
    rw [hE]
    simp only [hLS]
    push_cast
    rfl
  rw [hA, Complex.ofReal_re]
  ring

/- English proof (translation)
Establish `hL : LSeriesSummable (fun n ↦ (residueClass a n : ℂ)) x` using `LSeriesSummable_of_abscissaOfAbsConv_lt_re ((abscissaOfAbsConv_residueClass_le_one a).trans_lt (by simp only [Complex.ofReal_re]; exact_mod_cast hx))`. Establish `h2 : Summable (LSeries.term (fun n ↦ (residueClass a n : ℂ)) x)` using `hL`. Establish `h3 : Summable fun n : ℕ ↦ ((residueClass a n / (n : ℝ) ^ x : ℝ) : ℂ)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`.

Conclude with `(apld_term_lemma a x n).symm`. Conclude with `Complex.summable_ofReal.1 h3`.
-/
lemma apld_summable (a : ZMod q) {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ ↦ residueClass a n / (n : ℝ) ^ x := by
  have hL : LSeriesSummable (fun n ↦ (residueClass a n : ℂ)) x :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re ((abscissaOfAbsConv_residueClass_le_one a).trans_lt
      (by simp only [Complex.ofReal_re]; exact_mod_cast hx))
  have h2 : Summable (LSeries.term (fun n ↦ (residueClass a n : ℂ)) x) := hL
  have h3 : Summable fun n : ℕ ↦ ((residueClass a n / (n : ℝ) ^ x : ℝ) : ℂ) := by
    convert h2 using 1
    funext n
    exact (apld_term_lemma a x n).symm
  exact Complex.summable_ofReal.1 h3

/- English proof (translation)
Establish `hc : ContinuousWithinAt (fun x : ℝ ↦ LFunctionResidueClassAux a x) (Set.Ioi 1) 1`. Establish `h1 : ContinuousWithinAt (LFunctionResidueClassAux a) {s : ℂ | 1 ≤ s.re} ((1 : ℝ) : ℂ)` using `continuousOn_LFunctionResidueClassAux a _ (by simp)`. Conclude with `h1.comp Complex.continuous_ofReal.continuousWithinAt (fun x hx => by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; exact le_of_lt hx)`. Establish `hre : Tendsto (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) (𝓝[>] 1) (𝓝 (LFunctionResidueClassAux a ((1 : ℝ) : ℂ)).re)` using `(Complex.continuous_re.tendsto _).comp hc.tendsto`. Establish `hlin : Tendsto (fun x : ℝ ↦ x - 1) (𝓝[>] 1) (𝓝 0)`.

Establish `: Tendsto (fun x : ℝ ↦ x - 1) (𝓝 1) (𝓝 (1 - 1))` using `(continuous_id.sub continuous_const).tendsto 1`. Rewrite `this` using `[sub_self]`. Conclude with `this.mono_left nhdsWithin_le_nhds`. Simplify using `using hlin.mul hre`.
-/
lemma residue_class_l_function_tendsto (a : ZMod q) :
    Tendsto (fun x : ℝ ↦ (x - 1) * (LFunctionResidueClassAux a x).re) (𝓝[>] 1) (𝓝 0) := by
  have hc : ContinuousWithinAt (fun x : ℝ ↦ LFunctionResidueClassAux a x) (Set.Ioi 1) 1 := by
    have h1 : ContinuousWithinAt (LFunctionResidueClassAux a) {s : ℂ | 1 ≤ s.re} ((1 : ℝ) : ℂ) :=
      continuousOn_LFunctionResidueClassAux a _ (by simp)
    exact h1.comp Complex.continuous_ofReal.continuousWithinAt
      (fun x hx => by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; exact le_of_lt hx)
  have hre : Tendsto (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) (𝓝[>] 1)
      (𝓝 (LFunctionResidueClassAux a ((1 : ℝ) : ℂ)).re) :=
    (Complex.continuous_re.tendsto _).comp hc.tendsto
  have hlin : Tendsto (fun x : ℝ ↦ x - 1) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ ↦ x - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub continuous_const).tendsto 1
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  simpa using hlin.mul hre

/- English proof (translation)
Use `split_ifs`. Simplify using the standard rewrite rules. Conclude with `div_nonneg (residueClass_nonneg a n) (Real.rpow_nonneg (Nat.cast_nonneg n) x)`.
-/
lemma apld_nonprime_nonneg (a : ZMod q) (x : ℝ) (n : ℕ) :
    0 ≤ (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x := by
  split_ifs
  · simp
  · exact div_nonneg (residueClass_nonneg a n) (Real.rpow_nonneg (Nat.cast_nonneg n) x)

/- English proof (translation)
Use `split_ifs`. Simplify using the standard rewrite rules. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Rewrite using `[residueClass_apply_zero, zero_div, zero_div]`. Apply `div_le_div_of_nonneg_left (residueClass_nonneg a n) (by exact_mod_cast hn)` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma apld_nonprime_le (a : ZMod q) {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x ≤
      (if n.Prime then 0 else residueClass a n) / n := by
  split_ifs
  · simp
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [residueClass_apply_zero, zero_div, zero_div]
    · apply div_le_div_of_nonneg_left (residueClass_nonneg a n) (by exact_mod_cast hn)
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hx

/- English proof (translation)
Distinguish the cases in `hp : n.Prime`. Distinguish the cases in `hn : (n : ZMod q) = a`. Establish `hmem : n ∈ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}}` using `⟨hp, hn⟩`. Rewrite using `[if_pos hp, Set.indicator_of_mem hmem]`. Simplify using `[residueClass, Set.indicator, hn, vonMangoldt_apply_prime hp]`.

Establish `hmem : n ∉ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}}` using `fun h => hn h.2`. Rewrite using `[if_pos hp, Set.indicator_of_notMem hmem]`. Simplify using `[residueClass, Set.indicator, hn]`. Establish `hmem : n ∉ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}}` using `fun h => hp h.1`. Rewrite using `[if_neg hp, Set.indicator_of_notMem hmem, zero_div]`.
-/
lemma apld_prime_part_eq (a : ZMod q) (x : ℝ) (n : ℕ) :
    (if n.Prime then residueClass a n else 0) / (n : ℝ) ^ x =
      {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n := by
  by_cases hp : n.Prime
  · by_cases hn : (n : ZMod q) = a
    · have hmem : n ∈ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}} := ⟨hp, hn⟩
      rw [if_pos hp, Set.indicator_of_mem hmem]
      simp [residueClass, Set.indicator, hn, vonMangoldt_apply_prime hp]
    · have hmem : n ∉ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}} := fun h => hn h.2
      rw [if_pos hp, Set.indicator_of_notMem hmem]
      simp [residueClass, Set.indicator, hn]
  · have hmem : n ∉ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}} := fun h => hp h.1
    rw [if_neg hp, Set.indicator_of_notMem hmem, zero_div]

end Formalism.HF.P

open Formalism.HF.P in

/- English proof (translation)
Introduce `N _ a ha`. Unfold `Formalism.HF.LogDensity`. Use `set P : ℝ → ℕ → ℝ := fun x n => (if n.Prime then residueClass a n else 0) / (n : ℝ) ^ x with hP`. Use `set Q : ℝ → ℕ → ℝ := fun x n => (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x with hQ`. Establish `hPQ : ∀ x n, residueClass a n / (n : ℝ) ^ x = P x n + Q x n`.

Introduce `x n`. Simplify using `only [hP, hQ, ← add_div]`. Use `congr 1`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hPnn : ∀ x n, 0 ≤ P x n`.

Introduce `x n`. Simplify using `only [hP]`. Use `div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) x)` and prove the remaining obligations. Use `split_ifs`. Conclude with `residueClass_nonneg a n`.

Conclude with `le_rfl`. Establish `hQnn : ∀ x n, 0 ≤ Q x n` using `fun x n => apld_nonprime_nonneg a x n`. Establish `hPs : ∀ x : ℝ, 1 < x → Summable (P x)` using `fun x hx => (apld_summable a hx).of_nonneg_of_le (hPnn x) (fun n => by rw [hPQ]; linarith [hQnn x n])`. Establish `hQs : ∀ x : ℝ, 1 < x → Summable (Q x)` using `fun x hx => (apld_summable a hx).of_nonneg_of_le (hQnn x) (fun n => by rw [hPQ]; linarith [hPnn x n])`. Establish `hB : Summable fun n : ℕ => (if n.Prime then 0 else residueClass a n) / n` using `summable_residueClass_non_primes_div a`.

Use `set B := ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / n with hBdef`. Establish `hQle : ∀ x : ℝ, 1 < x → ∑' n, Q x n ≤ B` using `fun x hx => (hQs x hx).tsum_le_tsum (fun n => apld_nonprime_le a hx.le n) hB`. Establish `hsplit : ∀ x : ℝ, 1 < x → (x - 1) * (LFunctionResidueClassAux a x).re + (N.totient : ℝ)⁻¹ - (x - 1) * ∑' n, Q x n = (x - 1) * (∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n)`. Introduce `x hx`. Establish `hsum : ∑' n, residueClass a n / (n : ℝ) ^ x = ∑' n, P x n + ∑' n, Q x n`.

Rewrite using `[← (hPs x hx).tsum_add (hQs x hx)]`. Conclude with `tsum_congr (hPQ x)`. Establish `hPind : ∑' n, P x n = ∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n` using `tsum_congr (fun n => apld_prime_part_eq a x n)`. Establish `hT` using `apld_tsum_residueClass_eq ha hx`. Establish `hx1 : x - 1 ≠ 0` using `sub_ne_zero.2 hx.ne'`.

Rewrite using `[← hPind]`. Establish `: ∑' n, P x n = (LFunctionResidueClassAux a x).re + (N.totient : ℝ)⁻¹ / (x - 1) - ∑' n, Q x n`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.

Establish `h1 : Tendsto (fun x : ℝ => (x - 1) * (LFunctionResidueClassAux a x).re) (𝓝[>] 1) (𝓝 0)` using `residue_class_l_function_tendsto a`. Establish `hlin : Tendsto (fun x : ℝ ↦ x - 1) (𝓝[>] 1) (𝓝 0)`. Establish `: Tendsto (fun x : ℝ ↦ x - 1) (𝓝 1) (𝓝 (1 - 1))` using `(continuous_id.sub continuous_const).tendsto 1`. Rewrite `this` using `[sub_self]`. Conclude with `this.mono_left nhdsWithin_le_nhds`.

Establish `h3 : Tendsto (fun x : ℝ => (x - 1) * ∑' n, Q x n) (𝓝[>] 1) (𝓝 0)`. Establish `hup : Tendsto (fun x : ℝ => (x - 1) * B) (𝓝[>] 1) (𝓝 0)`. Simplify using `using hlin.mul_const B`. Use `squeeze_zero' ?_ ?_ hup` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with x hx`.

Conclude with `mul_nonneg (sub_nonneg.2 (le_of_lt hx)) (tsum_nonneg (hQnn x))`. Use `filter_upwards [self_mem_nhdsWithin] with x hx`. Conclude with `mul_le_mul_of_nonneg_left (hQle x hx) (sub_nonneg.2 (le_of_lt hx))`. Establish `hlim` using `(h1.add (tendsto_const_nhds (x := (N.totient : ℝ)⁻¹))).sub h3`. Establish `e : (0 : ℝ) + (N.totient : ℝ)⁻¹ - 0 = 1 / (N.totient : ℝ)` using `by simp`.

Rewrite `hlim` using `[e]`. Use `hlim.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with x hx`. Conclude with `hsplit x hx`.
-/
theorem Formalism.HF.apLogDensity : Formalism.HF.APLogDensity := by
  intro N _ a ha
  unfold Formalism.HF.LogDensity
  set P : ℝ → ℕ → ℝ := fun x n => (if n.Prime then residueClass a n else 0) / (n : ℝ) ^ x with hP
  set Q : ℝ → ℕ → ℝ := fun x n => (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x with hQ
  have hPQ : ∀ x n, residueClass a n / (n : ℝ) ^ x = P x n + Q x n := by
    intro x n
    simp only [hP, hQ, ← add_div]
    congr 1
    split_ifs <;> simp
  have hPnn : ∀ x n, 0 ≤ P x n := by
    intro x n
    simp only [hP]
    refine div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) x)
    split_ifs
    · exact residueClass_nonneg a n
    · exact le_rfl
  have hQnn : ∀ x n, 0 ≤ Q x n := fun x n => apld_nonprime_nonneg a x n
  have hPs : ∀ x : ℝ, 1 < x → Summable (P x) := fun x hx =>
    (apld_summable a hx).of_nonneg_of_le (hPnn x) (fun n => by rw [hPQ]; linarith [hQnn x n])
  have hQs : ∀ x : ℝ, 1 < x → Summable (Q x) := fun x hx =>
    (apld_summable a hx).of_nonneg_of_le (hQnn x) (fun n => by rw [hPQ]; linarith [hPnn x n])
  have hB : Summable fun n : ℕ => (if n.Prime then 0 else residueClass a n) / n :=
    summable_residueClass_non_primes_div a
  set B := ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / n with hBdef
  have hQle : ∀ x : ℝ, 1 < x → ∑' n, Q x n ≤ B := fun x hx =>
    (hQs x hx).tsum_le_tsum (fun n => apld_nonprime_le a hx.le n) hB
  have hsplit : ∀ x : ℝ, 1 < x →
      (x - 1) * (LFunctionResidueClassAux a x).re + (N.totient : ℝ)⁻¹ - (x - 1) * ∑' n, Q x n =
      (x - 1) * (∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) := by
    intro x hx
    have hsum : ∑' n, residueClass a n / (n : ℝ) ^ x = ∑' n, P x n + ∑' n, Q x n := by
      rw [← (hPs x hx).tsum_add (hQs x hx)]
      exact tsum_congr (hPQ x)
    have hPind : ∑' n, P x n = ∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n :=
      tsum_congr (fun n => apld_prime_part_eq a x n)
    have hT := apld_tsum_residueClass_eq ha hx
    have hx1 : x - 1 ≠ 0 := sub_ne_zero.2 hx.ne'
    rw [← hPind]
    have : ∑' n, P x n = (LFunctionResidueClassAux a x).re + (N.totient : ℝ)⁻¹ / (x - 1) - ∑' n, Q x n := by
      linarith
    rw [this]
    field_simp
  have h1 : Tendsto (fun x : ℝ => (x - 1) * (LFunctionResidueClassAux a x).re) (𝓝[>] 1) (𝓝 0) :=
    residue_class_l_function_tendsto a
  have hlin : Tendsto (fun x : ℝ ↦ x - 1) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ ↦ x - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub continuous_const).tendsto 1
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun x : ℝ => (x - 1) * ∑' n, Q x n) (𝓝[>] 1) (𝓝 0) := by
    have hup : Tendsto (fun x : ℝ => (x - 1) * B) (𝓝[>] 1) (𝓝 0) := by
      simpa using hlin.mul_const B
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_nonneg (sub_nonneg.2 (le_of_lt hx)) (tsum_nonneg (hQnn x))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_le_mul_of_nonneg_left (hQle x hx) (sub_nonneg.2 (le_of_lt hx))
  have hlim := (h1.add (tendsto_const_nhds (x := (N.totient : ℝ)⁻¹))).sub h3
  have e : (0 : ℝ) + (N.totient : ℝ)⁻¹ - 0 = 1 / (N.totient : ℝ) := by simp
  rw [e] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hsplit x hx
