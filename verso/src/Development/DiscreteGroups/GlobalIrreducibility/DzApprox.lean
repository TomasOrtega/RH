import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne

open IsDedekindDomain NumberField

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (𝓞 E) e`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hbE : algebraMap (𝓞 E) E b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`. Establish `hν0 : w.intValuation b ≠ 0` using `w.intValuation_ne_zero b hb0`. Use `set m : ℕ := (-(w.intValuation b).log).toNat with hm`.

Establish `hνm : w.intValuation b = WithZero.exp (-(m : ℤ))`. Establish `hlog : (w.intValuation b).log ≤ 0`. Establish `h1 : WithZero.exp (w.intValuation b).log ≤ WithZero.exp 0`. Rewrite using `[WithZero.exp_log hν0, WithZero.exp_zero]`. Conclude with `w.intValuation_le_one b`.

Conclude with `WithZero.exp_le_exp.mp h1`. Rewrite using `[hm, Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hν0]`. Establish `hbm : b ∈ w.asIdeal ^ m` using `(w.intValuation_le_pow_iff_mem b m).mp hνm.le`. Establish `hbm1 : b ∉ w.asIdeal ^ (m + 1)`. Introduce `h`.

Establish `h2` using `(w.intValuation_le_pow_iff_mem b (m + 1)).mpr h`. Rewrite `h2` using `[hνm, WithZero.exp_le_exp]`. Move the coercions through the operations in `at h2`. Use linear arithmetic over natural numbers and integers. Establish `hva : w.intValuation a ≤ w.intValuation b`.

Establish `h1 : w.valuation E (algebraMap (𝓞 E) E a) = w.valuation E (algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b) * w.valuation E (algebraMap (𝓞 E) E b)`. Rewrite using `[← map_mul, div_mul_cancel₀ _ hbE]`. Rewrite `h1` using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]`. Rewrite using `[h1]`. Conclude with `mul_le_of_le_one_left' he`.

Establish `ham : a ∈ w.asIdeal ^ m` using `(w.intValuation_le_pow_iff_mem a m).mp (hva.trans hνm.le)`. Take `⟨B, hB⟩ : w.asIdeal ^ m ∣ Ideal.span {b}` from `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hbm)`. Establish `hBw : ¬ B ≤ w.asIdeal`. Introduce `hle`. Apply `hbm1` to reduce the goal to its premises.

Establish `: Ideal.span {b} ≤ w.asIdeal ^ (m + 1)`. Rewrite using `[hB, pow_succ]`. Conclude with `Ideal.mul_mono_right hle`. Conclude with `(Ideal.span_singleton_le_iff_mem _).mp this`. Take `⟨s, hsB, hsw⟩` from `SetLike.not_le_iff_exists.mp hBw`.

Establish `hsa : s * a ∈ Ideal.span {b}`. Rewrite using `[hB, mul_comm s a]`. Conclude with `Ideal.mul_mem_mul ham hsB`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hsa`. Use `haveI := w.isMaximal`.

Establish `hs0 : Ideal.Quotient.mk w.asIdeal s ≠ 0` using `by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]`. Take `⟨s'', hs''⟩` from `Ideal.Quotient.exists_inv hs0`. Take `⟨s', rfl⟩` from `Ideal.Quotient.mk_surjective s''`. Establish `hss : s * s' - 1 ∈ w.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hs'', map_one, sub_self]`.

Establish `hsne : s ≠ 0` using `fun h => hsw (h ▸ w.asIdeal.zero_mem)`. Establish `hsE : algebraMap (𝓞 E) E s ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]`. Conclude with `hsne`. Use `⟨c * s', ?_⟩` and prove the remaining obligations.

Establish `hcE : algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E a`. Rewrite using `[← map_mul, ← map_mul, hc]`. Establish `hab : algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E c / algebraMap (𝓞 E) E s`. Rewrite using `[div_eq_div_iff hbE hsE]`. Take the linear combination `(-1 : E) * hcE`.

Establish `e1 : algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b - algebraMap (𝓞 E) E (c * s') = algebraMap (𝓞 E) E c * (-algebraMap (𝓞 E) E (s * s' - 1)) / algebraMap (𝓞 E) E s`. Rewrite using `[hab]`. Simplify using `only [map_mul, map_sub, map_one]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hs1 : w.intValuation s = 1` using `le_antisymm (w.intValuation_le_one s) (not_lt.mp fun h => hsw ((w.intValuation_lt_one_iff_mem s).mp h))`. Establish `hss1 : w.intValuation (s * s' - 1) < 1` using `(w.intValuation_lt_one_iff_mem _).mpr hss`. Rewrite using `[e1, map_div₀, map_mul, Valuation.map_neg, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hs1, div_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_int_approx (e : E) (he : w.valuation E e ≤ 1) :
    ∃ x : 𝓞 E, w.valuation E (e - algebraMap (𝓞 E) E x) < 1 := by
  classical
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) e
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbE : algebraMap (𝓞 E) E b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hν0 : w.intValuation b ≠ 0 := w.intValuation_ne_zero b hb0
  set m : ℕ := (-(w.intValuation b).log).toNat with hm
  have hνm : w.intValuation b = WithZero.exp (-(m : ℤ)) := by
    have hlog : (w.intValuation b).log ≤ 0 := by
      have h1 : WithZero.exp (w.intValuation b).log ≤ WithZero.exp 0 := by
        rw [WithZero.exp_log hν0, WithZero.exp_zero]; exact w.intValuation_le_one b
      exact WithZero.exp_le_exp.mp h1
    rw [hm, Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hν0]
  have hbm : b ∈ w.asIdeal ^ m := (w.intValuation_le_pow_iff_mem b m).mp hνm.le
  have hbm1 : b ∉ w.asIdeal ^ (m + 1) := by
    intro h
    have h2 := (w.intValuation_le_pow_iff_mem b (m + 1)).mpr h
    rw [hνm, WithZero.exp_le_exp] at h2
    push_cast at h2
    omega
  have hva : w.intValuation a ≤ w.intValuation b := by
    have h1 : w.valuation E (algebraMap (𝓞 E) E a) =
        w.valuation E (algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b) * w.valuation E (algebraMap (𝓞 E) E b) := by
      rw [← map_mul, div_mul_cancel₀ _ hbE]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap] at h1
    rw [h1]
    exact mul_le_of_le_one_left' he
  have ham : a ∈ w.asIdeal ^ m := (w.intValuation_le_pow_iff_mem a m).mp (hva.trans hνm.le)
  obtain ⟨B, hB⟩ : w.asIdeal ^ m ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hbm)
  have hBw : ¬ B ≤ w.asIdeal := by
    intro hle
    apply hbm1
    have : Ideal.span {b} ≤ w.asIdeal ^ (m + 1) := by
      rw [hB, pow_succ]; exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).mp this
  obtain ⟨s, hsB, hsw⟩ := SetLike.not_le_iff_exists.mp hBw
  have hsa : s * a ∈ Ideal.span {b} := by
    rw [hB, mul_comm s a]; exact Ideal.mul_mem_mul ham hsB
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hsa
  haveI := w.isMaximal
  have hs0 : Ideal.Quotient.mk w.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨s'', hs''⟩ := Ideal.Quotient.exists_inv hs0
  obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective s''
  have hss : s * s' - 1 ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hs'', map_one, sub_self]
  have hsne : s ≠ 0 := fun h => hsw (h ▸ w.asIdeal.zero_mem)
  have hsE : algebraMap (𝓞 E) E s ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]; exact hsne
  refine ⟨c * s', ?_⟩
  have hcE : algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E a := by
    rw [← map_mul, ← map_mul, hc]
  have hab : algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E c / algebraMap (𝓞 E) E s := by
    rw [div_eq_div_iff hbE hsE]; linear_combination (-1 : E) * hcE
  have e1 : algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b - algebraMap (𝓞 E) E (c * s') =
      algebraMap (𝓞 E) E c * (-algebraMap (𝓞 E) E (s * s' - 1)) / algebraMap (𝓞 E) E s := by
    rw [hab]
    simp only [map_mul, map_sub, map_one]
    field_simp
    ring
  have hs1 : w.intValuation s = 1 :=
    le_antisymm (w.intValuation_le_one s) (not_lt.mp fun h => hsw ((w.intValuation_lt_one_iff_mem s).mp h))
  have hss1 : w.intValuation (s * s' - 1) < 1 := (w.intValuation_lt_one_iff_mem _).mpr hss
  rw [e1, map_div₀, map_mul, Valuation.map_neg, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hs1, div_one]
  calc w.intValuation c * w.intValuation (s * s' - 1) ≤ 1 * w.intValuation (s * s' - 1) :=
        mul_le_mul_left (w.intValuation_le_one c) _
    _ = w.intValuation (s * s' - 1) := one_mul _
    _ < 1 := hss1

/- English proof (translation)
Establish `hvF : ∀ e : E, Valued.v (algebraMap E (w.adicCompletion E) e) = w.valuation E e` using `fun e => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w e`. Take `⟨e, he⟩` from `(HeightOneSpectrum.denseRange_algebraMap E w).exists_dist_lt u one_pos`. Rewrite `he` using `[dist_eq_norm, Valued.toNormedField.norm_lt_one_iff]`. Establish `hve : w.valuation E e ≤ 1`. Rewrite using `[← hvF]`.

Establish `e2 : algebraMap E (w.adicCompletion E) e = u - (u - algebraMap E (w.adicCompletion E) e)` using `by ring`. Rewrite using `[e2]`. Conclude with `(Valuation.map_sub _ _ _).trans (max_le hu he.le)`. Take `⟨x, hx⟩` from `exists_int_approx w e hve`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Establish `e3 : u - algebraMap E (w.adicCompletion E) (x : E) = (u - algebraMap E (w.adicCompletion E) e) + algebraMap E (w.adicCompletion E) (e - algebraMap (𝓞 E) E x)`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3]`. Conclude with `Valuation.map_add_lt _ he (by rw [hvF]; exact hx)`.
-/
theorem exists_int_approx_compl (u : w.adicCompletion E) (hu : Valued.v u ≤ 1) :
    ∃ x : 𝓞 E, Valued.v (u - algebraMap E (w.adicCompletion E) (x : E)) < 1 := by
  have hvF : ∀ e : E, Valued.v (algebraMap E (w.adicCompletion E) e) = w.valuation E e :=
    fun e => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w e
  obtain ⟨e, he⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_dist_lt u one_pos
  rw [dist_eq_norm, Valued.toNormedField.norm_lt_one_iff] at he
  have hve : w.valuation E e ≤ 1 := by
    rw [← hvF]
    have e2 : algebraMap E (w.adicCompletion E) e = u - (u - algebraMap E (w.adicCompletion E) e) := by ring
    rw [e2]
    exact (Valuation.map_sub _ _ _).trans (max_le hu he.le)
  obtain ⟨x, hx⟩ := exists_int_approx w e hve
  refine ⟨x, ?_⟩
  have e3 : u - algebraMap E (w.adicCompletion E) (x : E) =
      (u - algebraMap E (w.adicCompletion E) e) + algebraMap E (w.adicCompletion E) (e - algebraMap (𝓞 E) E x) := by
    rw [map_sub]; ring
  rw [e3]
  exact Valuation.map_add_lt _ he (by rw [hvF]; exact hx)

end DiscreteGroups.sglob.DzType

end
