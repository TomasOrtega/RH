import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

namespace GlobalTheory.RootsOfUnityClose

/- English proof (translation)
Establish `hz1 : ‖z‖ ≤ 1`. Establish `h` using `IsUltrametricDist.norm_add_le_max (z - 1) 1`. Rewrite `h` using `[sub_add_cancel, norm_one]`. Conclude with `h.trans (max_le hz.le le_rfl)`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Take `⟨h1, h2⟩` from `ih`. Prove the components needed by the constructor for the conclusion. Establish `e : z ^ (n + 1) - 1 = z * (z ^ n - 1) + (z - 1)` using `by ring`.

Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hz)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt h1`. Establish `e : (∑ i ∈ Finset.range (n + 1), z ^ i) - ((n + 1 : ℕ) : K) = ((∑ i ∈ Finset.range n, z ^ i) - (n : K)) + (z ^ n - 1)`.

Rewrite using `[Finset.sum_range_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h2 h1)`.
-/
theorem geom_sum_close {K : Type*} [NormedField K] [IsUltrametricDist K] {z : K}
    (hz : ‖z - 1‖ < 1) (n : ℕ) :
    ‖z ^ n - 1‖ < 1 ∧ ‖(∑ i ∈ Finset.range n, z ^ i) - (n : K)‖ < 1 := by
  have hz1 : ‖z‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (z - 1) 1
    rw [sub_add_cancel, norm_one] at h
    exact h.trans (max_le hz.le le_rfl)
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · have e : z ^ (n + 1) - 1 = z * (z ^ n - 1) + (z - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hz)
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt h1
    · have e : (∑ i ∈ Finset.range (n + 1), z ^ i) - ((n + 1 : ℕ) : K)
          = ((∑ i ∈ Finset.range n, z ^ i) - (n : K)) + (z ^ n - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h2 h1)

/- English proof (translation)
Establish `e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l])` using `by simp`. Rewrite using `[e, norm_algebraMap']`. Conclude with `Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h)`.
-/
theorem norm_natCast_eq_one {l : ℕ} [Fact l.Prime] {m : ℕ} (h : ¬ l ∣ m) :
    ‖(m : PadicAlgCl l)‖ = 1 := by
  have e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := by simp
  rw [e, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h)

/- English proof (translation)
Establish `hb1 : ‖b‖ = 1`. Establish `h : ‖b‖ ^ m = 1` using `by rw [← norm_pow, hb, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp h`. Establish `hb0 : b ≠ 0`. Introduce `h`.

Rewrite `hb1` using `[h, norm_zero]`. Conclude with `zero_ne_one hb1`. Establish `hz : ‖a / b - 1‖ < 1`. Rewrite using `[div_sub_one hb0, norm_div, hb1, div_one]`. Conclude with `hab`.

Establish `hzm : (a / b) ^ m = 1` using `by rw [div_pow, ha, hb, div_one]`. Assume the negation of the conclusion as `hne`. Establish `hne1 : a / b - 1 ≠ 0`. Rewrite using `[sub_ne_zero]`. Introduce `h`.

Conclude with `hne ((div_eq_one_iff_eq hb0).mp h)`. Establish `hs : (∑ i ∈ Finset.range m, (a / b) ^ i) = 0`. Establish `h` using `geom_sum_mul (a / b) m`. Rewrite `h` using `[hzm, sub_self]`. Conclude with `(mul_eq_zero.mp h).resolve_right hne1`.

Establish `h` using `(geom_sum_close hz m).2`. Rewrite `h` using `[hs, zero_sub, norm_neg, norm_natCast_eq_one hl]`. Conclude with `lt_irrefl _ h`.
-/
theorem eq_of_pow_eq_one_of_norm_sub_lt_one {l : ℕ} [Fact l.Prime] {m : ℕ} (hm : 0 < m)
    (hl : ¬ l ∣ m) {a b : Formalism.BasicNotions.Loc.Om l} (ha : a ^ m = 1) (hb : b ^ m = 1)
    (hab : ‖a - b‖ < 1) : a = b := by
  have hb1 : ‖b‖ = 1 := by
    have h : ‖b‖ ^ m = 1 := by rw [← norm_pow, hb, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp h
  have hb0 : b ≠ 0 := by
    intro h; rw [h, norm_zero] at hb1; exact zero_ne_one hb1
  have hz : ‖a / b - 1‖ < 1 := by
    rw [div_sub_one hb0, norm_div, hb1, div_one]; exact hab
  have hzm : (a / b) ^ m = 1 := by rw [div_pow, ha, hb, div_one]
  by_contra hne
  have hne1 : a / b - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hne ((div_eq_one_iff_eq hb0).mp h)
  have hs : (∑ i ∈ Finset.range m, (a / b) ^ i) = 0 := by
    have h := geom_sum_mul (a / b) m
    rw [hzm, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right hne1
  have h := (geom_sum_close hz m).2
  rw [hs, zero_sub, norm_neg, norm_natCast_eq_one hl] at h
  exact lt_irrefl _ h

end GlobalTheory.RootsOfUnityClose
