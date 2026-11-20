import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzRamified

/- English proof (translation)
Rewrite using `[← map_intCast (algebraMap ℚ_[l] ℂ_[l]) z, norm_algebraMap']`. Conclude with `le_antisymm (Padic.norm_int_le_one z) (not_lt.mp fun h' => h (Padic.norm_intCast_lt_one_iff.mp h'))`.
-/
theorem norm_int_eq_one {l : ℕ} [Fact l.Prime] {z : ℤ} (h : ¬ (l : ℤ) ∣ z) : ‖(z : ℂ_[l])‖ = 1 := by
  rw [← map_intCast (algebraMap ℚ_[l] ℂ_[l]) z, norm_algebraMap']
  exact le_antisymm (Padic.norm_int_le_one z) (not_lt.mp fun h' => h (Padic.norm_intCast_lt_one_iff.mp h'))

/- English proof (translation)
Establish `hpr : l.Prime` using `Fact.out`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hpr.one_lt`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Establish `hn : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]`.

Establish `h12 : ‖(12 : ℂ_[l])‖ = 1`. Establish `hd : ¬ (l : ℤ) ∣ 12`. Introduce `h`. Establish `h' : l ∣ 12` using `by exact_mod_cast h`. Establish `h4 : l ∣ 2 ^ 2 * 3` using `h'`.

Break down `(Nat.Prime.dvd_mul hpr).1 h4 with h5 | h5` into its components or cases. Use `Nat.le_of_dvd (by norm_num) (hpr.dvd_of_dvd_pow h5); omega` as an intermediate fact. Use `Nat.le_of_dvd (by norm_num) h5; omega` as an intermediate fact. Simplify using `using norm_int_eq_one (l := l) hd`. Establish `h2 : ‖(2 : ℂ_[l])‖ = 1`.

Establish `hd : ¬ (l : ℤ) ∣ 2`. Introduce `h`. Use `Int.le_of_dvd (by norm_num) h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `using norm_int_eq_one (l := l) hd`.

Establish `hW2 : ‖W‖ ^ 2 = (l : ℝ)⁻¹` using `by rw [← norm_pow, hW, norm_neg, hn]`. Establish `hW1 : ‖W‖ < 1`. Establish `: ‖W‖ ^ 2 < 1` using `by rw [hW2]; exact inv_lt_one_of_one_lt₀ hl1`. Use polynomial arithmetic with `[norm_nonneg W]`. Establish `h1W : ‖1 + W‖ = 1`.

Rewrite using `[IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hW1.ne'), norm_one, max_eq_left hW1.le]`. Establish `hP1 : ‖P‖ ≤ 1` using `by rwa [norm_mul, h12, one_mul] at hP`. Establish `hB : ‖((1 + W) ^ 2 - 1) * P‖ ≤ 1`. Establish `e : ((1 + W) ^ 2 - 1) * P = W * (2 + W) * P` using `by ring`. Establish `h2W : ‖2 + W‖ ≤ 1` using `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2.le hW1.le)`.

Rewrite using `[e, norm_mul, norm_mul]`. Conclude with `mul_le_one₀ (mul_le_one₀ hW1.le (norm_nonneg _) h2W) (norm_nonneg _) hP1`. Establish `hA : ‖W‖ * ‖S‖ ≤ 1`. Establish `e : 2 * W * (1 + W) * S = (((1 + W) ^ 2 - (1 + (l : ℂ_[l]))) * S - ((1 + W) ^ 2 - 1) * P) + ((1 + W) ^ 2 - 1) * P`. Take the linear combination `S * hW`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hS hB)` as an intermediate fact. Rewrite `this` using `[← e, norm_mul, norm_mul, norm_mul, h2, h1W, one_mul, mul_one]`. Then use the resulting hypothesis. Establish `hsq : ‖S‖ ^ 2 ≤ l`. Establish `h3 : (‖W‖ * ‖S‖) ^ 2 ≤ 1` using `pow_le_one₀ (by positivity) hA`. Rewrite `h3` using `[mul_pow, hW2, inv_mul_le_iff₀ hl0, mul_one]`.

Conclude with `h3`. Rewrite using `[← Real.sqrt_eq_rpow]`. Conclude with `Real.le_sqrt_of_sq_le hsq`.
-/
theorem norm_bound {l : ℕ} [Fact l.Prime] (W S P : ℂ_[l]) (hl : 4 < l) (hW : W ^ 2 = -(l : ℂ_[l]))
    (hP : ‖12 * P‖ ≤ 1) (hS : ‖((1 + W) ^ 2 - (1 + (l : ℂ_[l]))) * S - ((1 + W) ^ 2 - 1) * P‖ ≤ 1) :
    ‖S‖ ≤ (l : ℝ) ^ (1 / 2 : ℝ) := by
  have hpr : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hpr.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hn : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]
  have h12 : ‖(12 : ℂ_[l])‖ = 1 := by
    have hd : ¬ (l : ℤ) ∣ 12 := by
      intro h
      have h' : l ∣ 12 := by exact_mod_cast h
      have h4 : l ∣ 2 ^ 2 * 3 := h'
      rcases (Nat.Prime.dvd_mul hpr).1 h4 with h5 | h5
      · have := Nat.le_of_dvd (by norm_num) (hpr.dvd_of_dvd_pow h5); omega
      · have := Nat.le_of_dvd (by norm_num) h5; omega
    simpa using norm_int_eq_one (l := l) hd
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have hd : ¬ (l : ℤ) ∣ 2 := by
      intro h
      have := Int.le_of_dvd (by norm_num) h
      omega
    simpa using norm_int_eq_one (l := l) hd
  have hW2 : ‖W‖ ^ 2 = (l : ℝ)⁻¹ := by rw [← norm_pow, hW, norm_neg, hn]
  have hW1 : ‖W‖ < 1 := by
    have : ‖W‖ ^ 2 < 1 := by rw [hW2]; exact inv_lt_one_of_one_lt₀ hl1
    nlinarith [norm_nonneg W]
  have h1W : ‖1 + W‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hW1.ne'), norm_one,
      max_eq_left hW1.le]
  have hP1 : ‖P‖ ≤ 1 := by rwa [norm_mul, h12, one_mul] at hP
  have hB : ‖((1 + W) ^ 2 - 1) * P‖ ≤ 1 := by
    have e : ((1 + W) ^ 2 - 1) * P = W * (2 + W) * P := by ring
    have h2W : ‖2 + W‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2.le hW1.le)
    rw [e, norm_mul, norm_mul]
    exact mul_le_one₀ (mul_le_one₀ hW1.le (norm_nonneg _) h2W) (norm_nonneg _) hP1
  have hA : ‖W‖ * ‖S‖ ≤ 1 := by
    have e : 2 * W * (1 + W) * S =
        (((1 + W) ^ 2 - (1 + (l : ℂ_[l]))) * S - ((1 + W) ^ 2 - 1) * P) + ((1 + W) ^ 2 - 1) * P := by
      linear_combination S * hW
    have := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hS hB)
    rwa [← e, norm_mul, norm_mul, norm_mul, h2, h1W, one_mul, mul_one] at this
  have hsq : ‖S‖ ^ 2 ≤ l := by
    have h3 : (‖W‖ * ‖S‖) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hA
    rw [mul_pow, hW2, inv_mul_le_iff₀ hl0, mul_one] at h3
    exact h3
  rw [← Real.sqrt_eq_rpow]
  exact Real.le_sqrt_of_sq_le hsq

/- English proof (translation)
Introduce `l _ lam w σ p hl hw hp hs`. Take `⟨hp, hp'⟩` from `hp`. Take `⟨hs, hs'⟩` from `hs`. Rewrite `hp'`, `hs'` using `[Real.rpow_zero]`. Establish `hlK : (l : ℂ) ∈ algebraicClosure ℚ ℂ` using `natCast_mem _ l`.

Establish `hwK : w ∈ algebraicClosure ℚ ℂ`. Rewrite using `[mem_algebraicClosure_iff]`. Use `IsAlgebraic.of_pow (n := 2) two_pos ?_` and prove the remaining obligations. Rewrite using `[← mem_algebraicClosure_iff, hw]`. Conclude with `neg_mem hlK`.

Establish `hpK : p ∈ algebraicClosure ℚ ℂ`. Establish `e : p = (12 * p) / ((12 : ℕ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `div_mem hp (natCast_mem _ 12)`. Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast (by omega : 0 < l)`.

Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`. Establish `: (l : ℂ) = 0` using `by linear_combination hw`. Establish `h' : l = 0` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers.

Establish `hw1 : 1 + w ≠ 0`. Introduce `h`. Establish `: ((l + 1 : ℕ) : ℂ) = 0` using `by push_cast; linear_combination hw + (1 - w) * h`. Conclude with `Nat.succ_ne_zero l (by exact_mod_cast this)`. Establish `hσK : σ ∈ algebraicClosure ℚ ℂ`.

Establish `e : σ = ((((1 + w) ^ 2 - (1 + (l : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) + ((1 + w) ^ 2 - 1) * p) / (((2 : ℕ) : ℂ) * w * (1 + w))`. Rewrite using `[eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) hw0) hw1)]`. Use `push_cast`. Take the linear combination `σ * hw`. Establish `h1 : 1 + w ∈ algebraicClosure ℚ ℂ` using `add_mem (one_mem _) hwK`.

Rewrite using `[e]`. Conclude with `div_mem (add_mem hs (mul_mem (sub_mem (pow_mem h1 2) (one_mem _)) hpK)) (mul_mem (mul_mem (natCast_mem _ 2) hwK) h1)`. Use `⟨hσK, norm_bound (lam ⟨w, hwK⟩) _ (lam ⟨p, hpK⟩) hl ?_ ?_ ?_⟩` and prove the remaining obligations. Establish `e : (⟨w, hwK⟩ : algebraicClosure ℚ ℂ) ^ 2 = -(l : algebraicClosure ℚ ℂ)` using `Subtype.ext (by simpa using hw)`. Rewrite using `[← map_pow, e, map_neg, map_natCast]`.

Establish `e : (⟨12 * p, hp⟩ : algebraicClosure ℚ ℂ) = ((12 : ℕ) : algebraicClosure ℚ ℂ) * ⟨p, hpK⟩` using `Subtype.ext (by show 12 * p = ((12 : ℕ) : ℂ) * p norm_num)`. Rewrite `hp'` using `[e, map_mul, map_natCast]`. Conclude with `hp'` after adjusting the coercions. Establish `e : (⟨_, hs⟩ : algebraicClosure ℚ ℂ) = ((1 + ⟨w, hwK⟩) ^ 2 - (1 + (l : algebraicClosure ℚ ℂ))) * ⟨σ, hσK⟩ - ((1 + ⟨w, hwK⟩) ^ 2 - 1) * ⟨p, hpK⟩` using `Subtype.ext (by simp)`. Rewrite `hs'` using `[e]`.

Simplify `hs'` using `only [map_sub, map_mul, map_pow, map_add, map_one, map_natCast]`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (w σ p : ℂ), 4 < l → w ^ 2 = -(l : ℂ) → Sz l lam 0 (12 * p) → Sz l lam 0 (((1 + w) ^ 2 - (1 + (l : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz l lam (1 / 2) σ := by
  intro l _ lam w σ p hl hw hp hs
  obtain ⟨hp, hp'⟩ := hp
  obtain ⟨hs, hs'⟩ := hs
  rw [Real.rpow_zero] at hp' hs'
  have hlK : (l : ℂ) ∈ algebraicClosure ℚ ℂ := natCast_mem _ l
  have hwK : w ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff]
    refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    rw [← mem_algebraicClosure_iff, hw]
    exact neg_mem hlK
  have hpK : p ∈ algebraicClosure ℚ ℂ := by
    have e : p = (12 * p) / ((12 : ℕ) : ℂ) := by push_cast; ring
    rw [e]
    exact div_mem hp (natCast_mem _ 12)
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hw0 : w ≠ 0 := by
    rintro rfl
    have : (l : ℂ) = 0 := by linear_combination hw
    have h' : l = 0 := by exact_mod_cast this
    omega
  have hw1 : 1 + w ≠ 0 := by
    intro h
    have : ((l + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination hw + (1 - w) * h
    exact Nat.succ_ne_zero l (by exact_mod_cast this)
  have hσK : σ ∈ algebraicClosure ℚ ℂ := by
    have e : σ = ((((1 + w) ^ 2 - (1 + (l : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) + ((1 + w) ^ 2 - 1) * p) /
        (((2 : ℕ) : ℂ) * w * (1 + w)) := by
      rw [eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) hw0) hw1)]
      push_cast
      linear_combination σ * hw
    have h1 : 1 + w ∈ algebraicClosure ℚ ℂ := add_mem (one_mem _) hwK
    rw [e]
    exact div_mem (add_mem hs (mul_mem (sub_mem (pow_mem h1 2) (one_mem _)) hpK))
      (mul_mem (mul_mem (natCast_mem _ 2) hwK) h1)
  refine ⟨hσK, norm_bound (lam ⟨w, hwK⟩) _ (lam ⟨p, hpK⟩) hl ?_ ?_ ?_⟩
  · have e : (⟨w, hwK⟩ : algebraicClosure ℚ ℂ) ^ 2 = -(l : algebraicClosure ℚ ℂ) := Subtype.ext (by simpa using hw)
    rw [← map_pow, e, map_neg, map_natCast]
  · have e : (⟨12 * p, hp⟩ : algebraicClosure ℚ ℂ) = ((12 : ℕ) : algebraicClosure ℚ ℂ) * ⟨p, hpK⟩ :=
      Subtype.ext (by
        show 12 * p = ((12 : ℕ) : ℂ) * p
        norm_num)
    rw [e, map_mul, map_natCast] at hp'
    exact_mod_cast hp'
  · have e : (⟨_, hs⟩ : algebraicClosure ℚ ℂ) =
        ((1 + ⟨w, hwK⟩) ^ 2 - (1 + (l : algebraicClosure ℚ ℂ))) * ⟨σ, hσK⟩ - ((1 + ⟨w, hwK⟩) ^ 2 - 1) * ⟨p, hpK⟩ :=
      Subtype.ext (by simp)
    rw [e] at hs'
    simpa only [map_sub, map_mul, map_pow, map_add, map_one, map_natCast] using hs'

end GlobalTheory.SzRamified
