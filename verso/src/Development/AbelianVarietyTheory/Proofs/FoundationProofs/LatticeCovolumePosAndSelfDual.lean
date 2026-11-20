import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PlaneLattice

/- English proof (translation)
Introduce `h0`. Establish `hind` using `LinearIndependent.pair_iff.mp L.indep`. Simplify using `only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0`. Establish `hy` using `hind L.ω₂.im (-L.ω₁.im) (by`. Apply the tactic sequence `refine Complex.ext ?_ ?_ <;>`.

Simplify using `only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.zero_re, Complex.zero_im]`. Take the linear combination `h0`. Use the proof step `ring)`. Establish `hy₁ : L.ω₁.im = 0` using `neg_eq_zero.mp hy.2`. Establish `hx` using `hind L.ω₂.re (-L.ω₁.re) (by`.

Apply the tactic sequence `refine Complex.ext ?_ ?_ <;>`. Simplify using `only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.zero_re, Complex.zero_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hy₁, hy.1]`. Use the proof step `ring)`.

Establish `hω : L.ω₁ = 0` using `Complex.ext (by simpa using neg_eq_zero.mp hx.2) (by simpa using hy₁)`. Conclude with `one_ne_zero (hind 1 0 (by simp [hω])).1`.
-/
theorem signedArea_ne_zero (L : PeriodPair) : ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ≠ 0 := by
  intro h0
  have hind := LinearIndependent.pair_iff.mp L.indep
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
  have hy := hind L.ω₂.im (-L.ω₁.im) (by
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
        Complex.zero_re, Complex.zero_im]
    · linear_combination h0
    · ring)
  have hy₁ : L.ω₁.im = 0 := neg_eq_zero.mp hy.2
  have hx := hind L.ω₂.re (-L.ω₁.re) (by
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
        Complex.zero_re, Complex.zero_im]
    · ring
    · rw [hy₁, hy.1]; ring)
  have hω : L.ω₁ = 0 := Complex.ext (by simpa using neg_eq_zero.mp hx.2) (by simpa using hy₁)
  exact one_ne_zero (hind 1 0 (by simp [hω])).1

/- English proof (translation)
Take `⟨a, b, rfl⟩` from `PeriodPair.mem_lattice.mp h₁`. Take `⟨c, d, rfl⟩` from `PeriodPair.mem_lattice.mp h₂`. Use `⟨a * d - b * c, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_intCast, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_int_mul (L : PeriodPair) {w₁ w₂ : ℂ} (h₁ : w₁ ∈ L.lattice) (h₂ : w₂ ∈ L.lattice) :
    ∃ k : ℤ, ((starRingEnd ℂ) w₁ * w₂).im = k * ((starRingEnd ℂ) L.ω₁ * L.ω₂).im := by
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.mp h₁
  obtain ⟨c, d, rfl⟩ := PeriodPair.mem_lattice.mp h₂
  refine ⟨a * d - b * c, ?_⟩
  simp only [map_add, map_mul, map_intCast, Complex.mul_im, Complex.mul_re, Complex.add_im,
    Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

/- English proof (translation)
Establish `hA` using `signedArea_ne_zero L`. Unfold `Formalism.MainNotions.TaylorLogMetric.area`. Use `IsLeast.csInf_eq ⟨⟨abs_pos.mpr hA, L.ω₁, (h _).mpr L.ω₁_mem_lattice, L.ω₂, (h _).mpr L.ω₂_mem_lattice, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `a ⟨ha, w₁, hw₁, w₂, hw₂, rfl⟩`. Take `⟨k, hk⟩` from `exists_int_mul L ((h _).mp hw₁) ((h _).mp hw₂)`.

Rewrite `ha`, the goal using `[hk, abs_mul]`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Simplify using `at ha`. Establish `hk1 : (1 : ℝ) ≤ |(k : ℝ)|` using `by exact_mod_cast Int.one_le_abs hk0`.

Conclude with `le_mul_of_one_le_left (abs_nonneg _) hk1`.
-/
theorem area_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) :
    area Λ = |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| := by
  have hA := signedArea_ne_zero L
  unfold Formalism.MainNotions.TaylorLogMetric.area
  refine IsLeast.csInf_eq ⟨⟨abs_pos.mpr hA, L.ω₁, (h _).mpr L.ω₁_mem_lattice, L.ω₂,
    (h _).mpr L.ω₂_mem_lattice, rfl⟩, ?_⟩
  rintro a ⟨ha, w₁, hw₁, w₂, hw₂, rfl⟩
  obtain ⟨k, hk⟩ := exists_int_mul L ((h _).mp hw₁) ((h _).mp hw₂)
  rw [hk, abs_mul] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  exact le_mul_of_one_le_left (abs_nonneg _) hk1

/- English proof (translation)
Apply the tactic sequence `refine Complex.ext ?_ ?_ <;>`. Apply the tactic sequence `simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring`.
-/
private theorem mul_signedArea_eq_periodPair_combination (L : PeriodPair) (z : ℂ) :
    z * (((starRingEnd ℂ) L.ω₁ * L.ω₂).im : ℂ) =
      (((starRingEnd ℂ) z * L.ω₂).im : ℂ) * L.ω₁ + (((starRingEnd ℂ) L.ω₁ * z).im : ℂ) * L.ω₂ := by
  refine Complex.ext ?_ ?_ <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

/- English proof (translation)
Introduce `L Λ h`. Establish `hA` using `signedArea_ne_zero L`. Rewrite using `[area_eq L Λ h]`. Use `⟨abs_pos.mpr hA, fun z => ⟨fun hz w hw => ?_, fun hz => ?_⟩⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `exists_int_mul L ((h _).mp hw) ((h _).mp hz)`.

Rewrite using `[mul_comm, hk]`. Break down `abs_cases ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with ⟨hab, _⟩ | ⟨hab, _⟩` into its components or cases. Conclude with `⟨k, by rw [hab, mul_div_cancel_right₀ _ hA]⟩`. Conclude with `⟨-k, by rw [hab, Int.cast_neg, div_neg, mul_div_cancel_right₀ _ hA]⟩`. Take `⟨m, hm⟩` from `hz L.ω₂ ((h _).mpr L.ω₂_mem_lattice)`.

Take `⟨n, hn⟩` from `hz L.ω₁ ((h _).mpr L.ω₁_mem_lattice)`. Establish `habs : |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| ≠ 0` using `abs_ne_zero.mpr hA`. Rewrite `hm`, `hn` using `[div_eq_iff habs]`. Establish `key` using `mul_signedArea_eq_periodPair_combination L z`. Establish `e1 : ((starRingEnd ℂ) z * L.ω₂).im = -(z * (starRingEnd ℂ) L.ω₂).im`.

Simplify using `only [Complex.mul_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ((starRingEnd ℂ) L.ω₁ * z).im = (z * (starRingEnd ℂ) L.ω₁).im`. Rewrite using `[mul_comm]`. Rewrite `key` using `[e1, e2, hm, hn]`.

Establish `hA' : ((((starRingEnd ℂ) L.ω₁ * L.ω₂).im : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hA`. Rewrite using `[h, PeriodPair.mem_lattice]`. Break down `abs_cases ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with ⟨hab, _⟩ | ⟨hab, _⟩` into its components or cases. Use `⟨-m, n, mul_right_cancel₀ hA' ?_⟩` and prove the remaining obligations. Rewrite using `[key, hab]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨m, -n, mul_right_cancel₀ hA' ?_⟩` and prove the remaining obligations. Rewrite using `[key, hab]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem area_pos_and_selfDual : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) → 0 < area Λ ∧ ∀ z : ℂ, z ∈ Λ ↔ ∀ w ∈ Λ, ∃ m : ℤ, (z * (starRingEnd ℂ) w).im / area Λ = m := by
  intro L Λ h
  have hA := signedArea_ne_zero L
  rw [area_eq L Λ h]
  refine ⟨abs_pos.mpr hA, fun z => ⟨fun hz w hw => ?_, fun hz => ?_⟩⟩
  · obtain ⟨k, hk⟩ := exists_int_mul L ((h _).mp hw) ((h _).mp hz)
    rw [mul_comm, hk]
    rcases abs_cases ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with ⟨hab, _⟩ | ⟨hab, _⟩
    · exact ⟨k, by rw [hab, mul_div_cancel_right₀ _ hA]⟩
    · exact ⟨-k, by rw [hab, Int.cast_neg, div_neg, mul_div_cancel_right₀ _ hA]⟩
  · obtain ⟨m, hm⟩ := hz L.ω₂ ((h _).mpr L.ω₂_mem_lattice)
    obtain ⟨n, hn⟩ := hz L.ω₁ ((h _).mpr L.ω₁_mem_lattice)
    have habs : |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| ≠ 0 := abs_ne_zero.mpr hA
    rw [div_eq_iff habs] at hm hn
    have key := mul_signedArea_eq_periodPair_combination L z
    have e1 : ((starRingEnd ℂ) z * L.ω₂).im = -(z * (starRingEnd ℂ) L.ω₂).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    have e2 : ((starRingEnd ℂ) L.ω₁ * z).im = (z * (starRingEnd ℂ) L.ω₁).im := by
      rw [mul_comm]
    rw [e1, e2, hm, hn] at key
    have hA' : ((((starRingEnd ℂ) L.ω₁ * L.ω₂).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA
    rw [h, PeriodPair.mem_lattice]
    rcases abs_cases ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with ⟨hab, _⟩ | ⟨hab, _⟩
    · refine ⟨-m, n, mul_right_cancel₀ hA' ?_⟩
      rw [key, hab]
      push_cast
      ring
    · refine ⟨m, -n, mul_right_cancel₀ hA' ?_⟩
      rw [key, hab]
      push_cast
      ring

end GlobalTheory.PlaneLattice
