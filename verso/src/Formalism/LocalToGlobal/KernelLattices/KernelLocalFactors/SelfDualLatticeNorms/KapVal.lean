import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime

noncomputable section
open NumberField IsDedekindDomain

namespace Formalism.L2.Ker.KS

section Val

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (f : K →+* ℂ_[p])

/- English proof (translation)
Take `⟨P, hm, hP⟩` from `RingOfIntegers.isIntegral_coe a`. Set `v : Valuation ℂ_[p] NNReal` to `NormedField.valuation`. Establish `hv` using `Valuation.integer.integers v`. Establish `h2 : IsIntegral v.integer (f (a : K))`. Use `⟨P.map (Int.castRingHom v.integer), hm.map _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.eval₂_map]`. Establish `e1 : (algebraMap v.integer ℂ_[p]).comp (Int.castRingHom v.integer) = f.comp (algebraMap ℤ K)` using `RingHom.ext_int _ _`. Rewrite using `[e1, ← Polynomial.hom_eval₂]`. Establish `: Polynomial.eval₂ (algebraMap ℤ K) (a : K) P = 0` using `hP`. Rewrite using `[this, map_zero]`.

Use `(hv.isIntegral_iff_v_le_one).mp h2` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem normO_le (a : 𝓞 K) : ‖f (a : K)‖ ≤ 1 := by
  obtain ⟨P, hm, hP⟩ := RingOfIntegers.isIntegral_coe a
  let v : Valuation ℂ_[p] NNReal := NormedField.valuation
  have hv := Valuation.integer.integers v
  have h2 : IsIntegral v.integer (f (a : K)) := by
    refine ⟨P.map (Int.castRingHom v.integer), hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e1 : (algebraMap v.integer ℂ_[p]).comp (Int.castRingHom v.integer) = f.comp (algebraMap ℤ K) :=
      RingHom.ext_int _ _
    rw [e1, ← Polynomial.hom_eval₂]
    have : Polynomial.eval₂ (algebraMap ℤ K) (a : K) P = 0 := hP
    rw [this, map_zero]
  have := (hv.isIntegral_iff_v_le_one).mp h2
  exact_mod_cast this

variable (𝔭 : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (h : ℕ) (hgen : 𝔭.asIdeal ^ h = Ideal.span {ϖ}) (hlt : ‖f (ϖ : K)‖ < 1)

include hgen hlt in

/- English proof (translation)
Establish `hmem : t ^ h ∈ Ideal.span {ϖ}` using `hgen ▸ Ideal.pow_mem_pow ht h`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hmem`. Establish `key : ‖f (t : K)‖ ^ h < 1`. Establish `e : ‖f (t : K)‖ ^ h = ‖f (c : K)‖ * ‖f (ϖ : K)‖`. Rewrite using `[← norm_pow, ← map_pow, ← norm_mul, ← map_mul]`.

Use `congr 2`. Conclude with `hc.symm` after adjusting the coercions. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Establish `hh : h ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at key`. Conclude with `(pow_lt_one_iff_of_nonneg (norm_nonneg _) hh).mp key`.
-/
theorem norm_lt_of_mem {t : 𝓞 K} (ht : t ∈ 𝔭.asIdeal) : ‖f (t : K)‖ < 1 := by
  have hmem : t ^ h ∈ Ideal.span {ϖ} := hgen ▸ Ideal.pow_mem_pow ht h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have key : ‖f (t : K)‖ ^ h < 1 := by
    have e : ‖f (t : K)‖ ^ h = ‖f (c : K)‖ * ‖f (ϖ : K)‖ := by
      rw [← norm_pow, ← map_pow, ← norm_mul, ← map_mul]
      congr 2
      exact_mod_cast hc.symm
    rw [e]
    calc ‖f (c : K)‖ * ‖f (ϖ : K)‖ ≤ 1 * ‖f (ϖ : K)‖ :=
          mul_le_mul_of_nonneg_right (normO_le f c) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hlt
  have hh : h ≠ 0 := by
    rintro rfl
    simp at key
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hh).mp key

include hgen hlt in

/- English proof (translation)
Take `⟨b, i, hi, hbi⟩` from `𝔭.isMaximal.exists_inv ha`. Establish `hsmall : ‖f (i : K)‖ < 1` using `norm_lt_of_mem f 𝔭 ϖ h hgen hlt hi`. Establish `hba : ‖f (b : K)‖ * ‖f (a : K)‖ = 1`. Rewrite using `[← norm_mul, ← map_mul]`. Establish `e : ((b : K) * (a : K)) = 1 + -(i : K)`.

Establish `: ((b * a + i : 𝓞 K) : K) = 1` using `by rw [hbi]; rfl`. Move the coercions through the operations in `at this`. Take the linear combination `this`. Rewrite using `[e, map_add, map_neg, map_one]`. Apply the tactic sequence `rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm] <;> simp [norm_neg] <;> linarith [hsmall]`.

Use `le_antisymm (normO_le f a) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_eq_one_of_not_mem {a : 𝓞 K} (ha : a ∉ 𝔭.asIdeal) : ‖f (a : K)‖ = 1 := by
  obtain ⟨b, i, hi, hbi⟩ := 𝔭.isMaximal.exists_inv ha
  have hsmall : ‖f (i : K)‖ < 1 := norm_lt_of_mem f 𝔭 ϖ h hgen hlt hi
  have hba : ‖f (b : K)‖ * ‖f (a : K)‖ = 1 := by
    rw [← norm_mul, ← map_mul]
    have e : ((b : K) * (a : K)) = 1 + -(i : K) := by
      have : ((b * a + i : 𝓞 K) : K) = 1 := by rw [hbi]; rfl
      push_cast at this
      linear_combination this
    rw [e, map_add, map_neg, map_one]
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm] <;> simp [norm_neg] <;> linarith [hsmall]
  refine le_antisymm (normO_le f a) ?_
  calc (1 : ℝ) = ‖f (b : K)‖ * ‖f (a : K)‖ := hba.symm
    _ ≤ 1 * ‖f (a : K)‖ := mul_le_mul_of_nonneg_right (normO_le f b) (norm_nonneg _)
    _ = ‖f (a : K)‖ := one_mul _

include hgen hlt in

/- English proof (translation)
Take `⟨n, hva⟩ : ∃ n : ℕ, 𝔭.intValuation a = WithZero.exp (-(n : ℤ))` from `⟨_, 𝔭.intValuation_if_neg ha⟩`. Use `⟨n, hva, ?_⟩` and prove the remaining obligations. Establish `hvah : 𝔭.intValuation (a ^ h) = WithZero.exp (-((n * h : ℕ) : ℤ))`. Rewrite using `[map_pow, hva, ← WithZero.exp_nsmul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : a ^ h ∈ Ideal.span {ϖ ^ n}`. Use `(𝔭.intValuation_le_pow_iff_mem (a ^ h) (n * h)).mp hvah.le` as an intermediate fact. Rewrite `this` using `[mul_comm, pow_mul, hgen, Ideal.span_singleton_pow]`. Then use the resulting hypothesis.

Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hmem`. Establish `hcn : c ∉ 𝔭.asIdeal`. Introduce `hcm`. Establish `h1 : a ^ h ∈ 𝔭.asIdeal ^ (n * h + 1)`. Rewrite using `[← hc, pow_succ', mul_comm n h, pow_mul, hgen, Ideal.span_singleton_pow]`.

Conclude with `Ideal.mul_mem_mul hcm (Ideal.mem_span_singleton_self _)`. Establish `h2` using `(𝔭.intValuation_le_pow_iff_mem _ _).mpr h1`. Rewrite `h2` using `[hvah, WithZero.exp_le_exp]`. Move the coercions through the operations in `at h2`. Use linear arithmetic over natural numbers and integers.

Establish `hc1` using `norm_eq_one_of_not_mem f 𝔭 ϖ h hgen hlt hcn`. Establish `e : (a : K) ^ h = (c : K) * (ϖ : K) ^ n` using `by exact_mod_cast hc.symm`. Rewrite using `[← norm_pow, ← map_pow f, e, map_mul, norm_mul, hc1, one_mul, map_pow, norm_pow]`.
-/
theorem norm_pow_int {a : 𝓞 K} (ha : a ≠ 0) :
    ∃ n : ℕ, 𝔭.intValuation a = WithZero.exp (-(n : ℤ)) ∧ ‖f (a : K)‖ ^ h = ‖f (ϖ : K)‖ ^ n := by
  classical
  obtain ⟨n, hva⟩ : ∃ n : ℕ, 𝔭.intValuation a = WithZero.exp (-(n : ℤ)) := ⟨_, 𝔭.intValuation_if_neg ha⟩
  refine ⟨n, hva, ?_⟩
  have hvah : 𝔭.intValuation (a ^ h) = WithZero.exp (-((n * h : ℕ) : ℤ)) := by
    rw [map_pow, hva, ← WithZero.exp_nsmul]
    congr 1
    push_cast
    ring
  have hmem : a ^ h ∈ Ideal.span {ϖ ^ n} := by
    have := (𝔭.intValuation_le_pow_iff_mem (a ^ h) (n * h)).mp hvah.le
    rwa [mul_comm, pow_mul, hgen, Ideal.span_singleton_pow] at this
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hcn : c ∉ 𝔭.asIdeal := by
    intro hcm
    have h1 : a ^ h ∈ 𝔭.asIdeal ^ (n * h + 1) := by
      rw [← hc, pow_succ', mul_comm n h, pow_mul, hgen, Ideal.span_singleton_pow]
      exact Ideal.mul_mem_mul hcm (Ideal.mem_span_singleton_self _)
    have h2 := (𝔭.intValuation_le_pow_iff_mem _ _).mpr h1
    rw [hvah, WithZero.exp_le_exp] at h2
    push_cast at h2
    omega
  have hc1 := norm_eq_one_of_not_mem f 𝔭 ϖ h hgen hlt hcn
  have e : (a : K) ^ h = (c : K) * (ϖ : K) ^ n := by exact_mod_cast hc.symm
  rw [← norm_pow, ← map_pow f, e, map_mul, norm_mul, hc1, one_mul, map_pow, norm_pow]

include hgen hlt in

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) x`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hx`.

Take `⟨n, hva, hna⟩` from `norm_pow_int f 𝔭 ϖ h hgen hlt ha0`. Take `⟨m, hvb, hnb⟩` from `norm_pow_int f 𝔭 ϖ h hgen hlt hb0`. Establish `hϖ : ϖ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hgen` using `[Ideal.span_singleton_eq_bot.mpr rfl]`.

Conclude with `(pow_ne_zero h 𝔭.ne_bot) hgen`. Establish `hfϖ : ‖f (ϖ : K)‖ ≠ 0` using `by simpa using hϖ`. Establish `hva' : 𝔭.valuation K (algebraMap (𝓞 K) K a) = WithZero.exp (-(n : ℤ))`. Rewrite using `[← hva]`. Conclude with `HeightOneSpectrum.valuation_of_algebraMap 𝔭 a`.

Establish `hvb' : 𝔭.valuation K (algebraMap (𝓞 K) K b) = WithZero.exp (-(m : ℤ))`. Rewrite using `[← hvb]`. Conclude with `HeightOneSpectrum.valuation_of_algebraMap 𝔭 b`. Rewrite using `[(𝔭.valuation K).map_div, hva', hvb', ← WithZero.exp_sub, WithZero.log_exp, map_div₀, norm_div, div_pow]`. Express the relevant statement in the definitionally equal form `‖f (a : K)‖ ^ h / ‖f (b : K)‖ ^ h = _`.

Rewrite using `[hna, hnb, show -(-(n : ℤ) - -(m : ℤ)) = (n : ℤ) - m by ring, zpow_sub₀ hfϖ, zpow_natCast, zpow_natCast]`.
-/
theorem norm_pow_eq {x : K} (hx : x ≠ 0) :
    ‖f x‖ ^ h = ‖f (ϖ : K)‖ ^ (-WithZero.log (𝔭.valuation K x)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨n, hva, hna⟩ := norm_pow_int f 𝔭 ϖ h hgen hlt ha0
  obtain ⟨m, hvb, hnb⟩ := norm_pow_int f 𝔭 ϖ h hgen hlt hb0
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hgen
    exact (pow_ne_zero h 𝔭.ne_bot) hgen
  have hfϖ : ‖f (ϖ : K)‖ ≠ 0 := by simpa using hϖ
  have hva' : 𝔭.valuation K (algebraMap (𝓞 K) K a) = WithZero.exp (-(n : ℤ)) := by
    rw [← hva]
    exact HeightOneSpectrum.valuation_of_algebraMap 𝔭 a
  have hvb' : 𝔭.valuation K (algebraMap (𝓞 K) K b) = WithZero.exp (-(m : ℤ)) := by
    rw [← hvb]
    exact HeightOneSpectrum.valuation_of_algebraMap 𝔭 b
  rw [(𝔭.valuation K).map_div, hva', hvb', ← WithZero.exp_sub, WithZero.log_exp, map_div₀, norm_div,
    div_pow]
  change ‖f (a : K)‖ ^ h / ‖f (b : K)‖ ^ h = _
  rw [hna, hnb, show -(-(n : ℤ) - -(m : ℤ)) = (n : ℤ) - m by ring, zpow_sub₀ hfϖ, zpow_natCast,
    zpow_natCast]

end Val

end Formalism.L2.Ker.KS
