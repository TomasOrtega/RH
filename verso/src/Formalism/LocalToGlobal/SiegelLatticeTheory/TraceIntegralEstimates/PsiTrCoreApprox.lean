import Mathlib

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Formalism.L2.S.Pv.PsiTrCore

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
The claim follows from `valuedAdicCompletion_eq_valuation' v k`.
-/
theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
  valuedAdicCompletion_eq_valuation' v k

/- English proof (translation)
Rewrite using `[valued_algebraMap]`. Conclude with `valuation_of_algebraMap v r`.
-/
theorem valued_algebraMap_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (r : F)) = v.intValuation r := by
  rw [valued_algebraMap]
  exact valuation_of_algebraMap v r

/- English proof (translation)
Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (𝓞 F) k`. Establish `hy0 : y ≠ 0` using `nonZeroDivisors.ne_zero hy`. Establish `hY : algebraMap (𝓞 F) F y ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy`. Use `set m := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {y})).factors with hm`. Establish `hvy : v.intValuation y = WithZero.exp (-(m : ℤ))` using `v.intValuation_if_neg hy0`.

Establish `hX : v.intValuation x = v.valuation F (algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y) * v.intValuation y`. Rewrite using `[← valuation_of_algebraMap (K := F) v x, ← valuation_of_algebraMap (K := F) v y, ← map_mul, div_mul_cancel₀ _ hY]`. Establish `hxm : x ∈ v.asIdeal ^ m`. Rewrite using `[← intValuation_le_pow_iff_mem, hX, ← hvy]`. Conclude with `mul_le_of_le_one_left' hk`.

Establish `hdvd : v.asIdeal ^ m ∣ Ideal.span {y}` using `(intValuation_le_pow_iff_dvd v y m).mp hvy.le`. Take `⟨J, hJ⟩` from `hdvd`. Establish `hJv : ¬ J ≤ v.asIdeal`. Introduce `hJv`. Establish `hy1 : y ∈ v.asIdeal ^ m * J` using `hJ ▸ Ideal.mem_span_singleton_self y`.

Establish `hy2 : y ∈ v.asIdeal ^ (m + 1)`. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mono_right hJv hy1`. Use `(intValuation_le_pow_iff_mem v y (m + 1)).mpr hy2` as an intermediate fact. Rewrite `this` using `[hvy, WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers. Take `⟨t, htJ, htv⟩` from `SetLike.not_le_iff_exists.mp hJv`. Establish `hxt : x * t ∈ Ideal.span {y}` using `hJ ▸ Ideal.mul_mem_mul hxm htJ`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.mp hxt`. Take `⟨s, i, hi, hsi⟩` from `v.isMaximal.exists_inv htv`.

Establish `htt : t * (s * ∑ j ∈ Finset.range N, i ^ j) = 1 - i ^ N`. Establish `h1 : s * t = 1 - i` using `by linear_combination hsi`. Combine the equalities or inequalities in the displayed calculation. Use `⟨z * (s * ∑ j ∈ Finset.range N, i ^ j), ?_⟩` and prove the remaining obligations. Use `set X := algebraMap (𝓞 F) F x`.

Use `set Y := algebraMap (𝓞 F) F y`. Establish `hzF : algebraMap (𝓞 F) F z * Y = X * algebraMap (𝓞 F) F t`. Simplify using `only [X, Y, ← map_mul, hz]`. Establish `httF : algebraMap (𝓞 F) F t * algebraMap (𝓞 F) F (s * ∑ j ∈ Finset.range N, i ^ j) = 1 - algebraMap (𝓞 F) F (i ^ N)`. Rewrite using `[← map_mul, htt, map_sub, map_one]`.

Establish `hZ : algebraMap (𝓞 F) F z = X * algebraMap (𝓞 F) F t / Y` using `eq_div_of_mul_eq hY hzF`. Establish `key : X / Y - algebraMap (𝓞 F) F (z * (s * ∑ j ∈ Finset.range N, i ^ j)) = X / Y * algebraMap (𝓞 F) F (i ^ N)`. Rewrite using `[map_mul, hZ]`. Take the linear combination `(-(X / Y)) * httF`. Rewrite using `[key, map_mul, valuation_of_algebraMap]`.

Establish `hIN : v.intValuation (i ^ N) ≤ WithZero.exp (-(N : ℤ))` using `(intValuation_le_pow_iff_mem v _ N).mpr (Ideal.pow_mem_pow hi N)`. Conclude with `(mul_le_of_le_one_left' hk).trans hIN`.
-/
private theorem exists_integer_approx_valuation (v : HeightOneSpectrum (𝓞 F)) (k : F) (hk : v.valuation F k ≤ 1)
    (N : ℕ) : ∃ r : 𝓞 F, v.valuation F (k - algebraMap (𝓞 F) F r) ≤ WithZero.exp (-(N : ℤ)) := by
  classical
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (𝓞 F) k
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hY : algebraMap (𝓞 F) F y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  set m := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {y})).factors with hm
  have hvy : v.intValuation y = WithZero.exp (-(m : ℤ)) := v.intValuation_if_neg hy0
  have hX : v.intValuation x =
      v.valuation F (algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y) * v.intValuation y := by
    rw [← valuation_of_algebraMap (K := F) v x, ← valuation_of_algebraMap (K := F) v y, ← map_mul,
      div_mul_cancel₀ _ hY]
  have hxm : x ∈ v.asIdeal ^ m := by
    rw [← intValuation_le_pow_iff_mem, hX, ← hvy]
    exact mul_le_of_le_one_left' hk
  have hdvd : v.asIdeal ^ m ∣ Ideal.span {y} := (intValuation_le_pow_iff_dvd v y m).mp hvy.le
  obtain ⟨J, hJ⟩ := hdvd
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hJv
    have hy1 : y ∈ v.asIdeal ^ m * J := hJ ▸ Ideal.mem_span_singleton_self y
    have hy2 : y ∈ v.asIdeal ^ (m + 1) := by
      rw [pow_succ]; exact Ideal.mul_mono_right hJv hy1
    have := (intValuation_le_pow_iff_mem v y (m + 1)).mpr hy2
    rw [hvy, WithZero.exp_le_exp] at this
    omega
  obtain ⟨t, htJ, htv⟩ := SetLike.not_le_iff_exists.mp hJv
  have hxt : x * t ∈ Ideal.span {y} := hJ ▸ Ideal.mul_mem_mul hxm htJ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hxt
  obtain ⟨s, i, hi, hsi⟩ := v.isMaximal.exists_inv htv
  have htt : t * (s * ∑ j ∈ Finset.range N, i ^ j) = 1 - i ^ N := by
    have h1 : s * t = 1 - i := by linear_combination hsi
    calc t * (s * ∑ j ∈ Finset.range N, i ^ j) = (s * t) * ∑ j ∈ Finset.range N, i ^ j := by ring
      _ = 1 - i ^ N := by rw [h1, mul_neg_geom_sum]
  refine ⟨z * (s * ∑ j ∈ Finset.range N, i ^ j), ?_⟩
  set X := algebraMap (𝓞 F) F x
  set Y := algebraMap (𝓞 F) F y
  have hzF : algebraMap (𝓞 F) F z * Y = X * algebraMap (𝓞 F) F t := by
    simp only [X, Y, ← map_mul, hz]
  have httF : algebraMap (𝓞 F) F t * algebraMap (𝓞 F) F (s * ∑ j ∈ Finset.range N, i ^ j) =
      1 - algebraMap (𝓞 F) F (i ^ N) := by
    rw [← map_mul, htt, map_sub, map_one]
  have hZ : algebraMap (𝓞 F) F z = X * algebraMap (𝓞 F) F t / Y := eq_div_of_mul_eq hY hzF
  have key : X / Y - algebraMap (𝓞 F) F (z * (s * ∑ j ∈ Finset.range N, i ^ j)) =
      X / Y * algebraMap (𝓞 F) F (i ^ N) := by
    rw [map_mul, hZ]
    linear_combination (-(X / Y)) * httF
  rw [key, map_mul, valuation_of_algebraMap]
  have hIN : v.intValuation (i ^ N) ≤ WithZero.exp (-(N : ℤ)) :=
    (intValuation_le_pow_iff_mem v _ N).mpr (Ideal.pow_mem_pow hi N)
  exact (mul_le_of_le_one_left' hk).trans hIN

/- English proof (translation)
Establish `hw0 : Valued.v w ≠ 0` using `(Valuation.ne_zero_iff _).mpr hw`. Choose the witnesses or unpack the hypotheses as in `⟨N, hN⟩ : ∃ N : ℕ, WithZero.exp (-(N : ℤ)) < Valued.v w := by`. Use `⟨(-(Valued.v w).log).toNat + 1, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← WithZero.exp_log hw0]`. Rewrite using `[WithZero.exp_lt_exp]`.

Use linear arithmetic over natural numbers and integers. Establish `hU : IsOpen {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w}`. Establish `h` using `(Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict w)).preimage (continuous_id.sub continuous_const : Continuous fun y : v.adicCompletion F ↦ y - a)`. Establish `e : {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w} = (fun y : v.adicCompletion F ↦ y - a) ⁻¹' {x | Valued.v.restrict x < Valued.v.restrict w}`. Use extensionality with `y`.

Conclude with `(Valuation.restrict_lt_iff (R := v.adicCompletion F) Valued.v).symm`. Rewrite using `[e]`. Conclude with `h`. Establish `hs : {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w} ∈ nhds a`. Use `hU.mem_nhds ?_` and prove the remaining obligations.

Simplify using `only [Set.mem_setOf_eq, sub_self, map_zero]`. Conclude with `zero_lt_iff.mpr hw0`. Take `⟨k, hk⟩` from `(denseRange_algebraMap F v).mem_nhds hs`. Simplify using `only [Set.mem_setOf_eq] at hk`. Establish `hak : Valued.v (a - algebraMap F (v.adicCompletion F) k) < Valued.v w`.

Rewrite using `[Valuation.map_sub_swap]` and apply the resulting hypothesis. Establish `hk1 : v.valuation F k ≤ 1`. Rewrite using `[← valued_algebraMap]`. Establish `e : algebraMap F (v.adicCompletion F) k = a - (a - algebraMap F (v.adicCompletion F) k)`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `(Valuation.map_sub _ _ _).trans (max_le ha (hak.le.trans hw1))`. Take `⟨r, hr⟩` from `exists_integer_approx_valuation v k hk1 N`. Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `e : a - algebraMap F (v.adicCompletion F) (r : F) = (a - algebraMap F (v.adicCompletion F) k) + algebraMap F (v.adicCompletion F) (k - algebraMap (𝓞 F) F r)`.

Establish `hr' : (r : F) = algebraMap (𝓞 F) F r` using `rfl`. Rewrite using `[map_sub, ← hr']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `Valuation.map_add_lt _ hak ?_` and prove the remaining obligations.

Rewrite using `[valued_algebraMap]`. Conclude with `lt_of_le_of_lt hr hN`.
-/
theorem exists_int_near (v : HeightOneSpectrum (𝓞 F)) (a w : v.adicCompletion F)
    (ha : Valued.v a ≤ 1) (hw : w ≠ 0) (hw1 : Valued.v w ≤ 1) :
    ∃ r : 𝓞 F, Valued.v (a - algebraMap F (v.adicCompletion F) (r : F)) < Valued.v w := by
  have hw0 : Valued.v w ≠ 0 := (Valuation.ne_zero_iff _).mpr hw
  obtain ⟨N, hN⟩ : ∃ N : ℕ, WithZero.exp (-(N : ℤ)) < Valued.v w := by
    refine ⟨(-(Valued.v w).log).toNat + 1, ?_⟩
    conv_rhs => rw [← WithZero.exp_log hw0]
    rw [WithZero.exp_lt_exp]
    omega
  have hU : IsOpen {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w} := by
    have h := (Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict w)).preimage
      (continuous_id.sub continuous_const : Continuous fun y : v.adicCompletion F ↦ y - a)
    have e : {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w} =
        (fun y : v.adicCompletion F ↦ y - a) ⁻¹'
          {x | Valued.v.restrict x < Valued.v.restrict w} := by
      ext y
      exact (Valuation.restrict_lt_iff (R := v.adicCompletion F) Valued.v).symm
    rw [e]
    exact h
  have hs : {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w} ∈ nhds a := by
    refine hU.mem_nhds ?_
    simp only [Set.mem_setOf_eq, sub_self, map_zero]
    exact zero_lt_iff.mpr hw0
  obtain ⟨k, hk⟩ := (denseRange_algebraMap F v).mem_nhds hs
  simp only [Set.mem_setOf_eq] at hk
  have hak : Valued.v (a - algebraMap F (v.adicCompletion F) k) < Valued.v w := by
    rwa [Valuation.map_sub_swap]
  have hk1 : v.valuation F k ≤ 1 := by
    rw [← valued_algebraMap]
    have e : algebraMap F (v.adicCompletion F) k = a - (a - algebraMap F (v.adicCompletion F) k) := by
      ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le ha (hak.le.trans hw1))
  obtain ⟨r, hr⟩ := exists_integer_approx_valuation v k hk1 N
  refine ⟨r, ?_⟩
  have e : a - algebraMap F (v.adicCompletion F) (r : F) =
      (a - algebraMap F (v.adicCompletion F) k) +
        algebraMap F (v.adicCompletion F) (k - algebraMap (𝓞 F) F r) := by
    have hr' : (r : F) = algebraMap (𝓞 F) F r := rfl
    rw [map_sub, ← hr']
    ring
  rw [e]
  refine Valuation.map_add_lt _ hak ?_
  rw [valued_algebraMap]
  exact lt_of_le_of_lt hr hN

/- English proof (translation)
Establish `hspan : Ideal.span {n} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hn`. Use `set T := (Ideal.finite_factors hspan).toFinset with hT`. Establish `hmemT : ∀ v, v ∈ T ↔ n ∈ v.asIdeal` using `fun v ↦ by`.

Simplify using `[T, Set.Finite.mem_toFinset, Ideal.dvd_span_singleton]`. Establish `hw : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) (n : F) ≠ 0`. Introduce `v h`. Use `valued_algebraMap_int v n` as an intermediate fact. Rewrite `this` using `[h, map_zero, intValuation_if_neg v hn]`.

Conclude with `WithZero.exp_ne_zero this.symm`. Establish `hr : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : 𝓞 F, Valued.v (a v - algebraMap F (v.adicCompletion F) (r : F)) < Valued.v (algebraMap F (v.adicCompletion F) (n : F))` using `fun v ↦ exists_int_near v (a v) _ ((mem_adicCompletionIntegers (𝓞 F) F v).mp (ha v)) (hw v) (by rw [valued_algebraMap_int]; exact intValuation_le_one v n)`. Use `choose r hr using hr`. Take `⟨b, hb⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v : HeightOneSpectrum (𝓞 F) ↦ v.asIdeal) (fun v ↦ (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n})).factors) (fun v _ ↦ v.prime) (fun i _ j _ hij h ↦ hij (HeightOneSpectrum.ext h)) (fun i ↦ r i.1)`. Use `⟨b, fun v ↦ ?_⟩` and prove the remaining obligations.

Establish `hb1 : Valued.v (algebraMap F (v.adicCompletion F) (b : F)) ≤ 1`. Rewrite using `[valued_algebraMap_int]`. Conclude with `intValuation_le_one v b`. Distinguish the cases in `hv : v ∈ T`. Establish `h1` using `(hr v).le`.

Rewrite `h1` using `[valued_algebraMap_int]`. Establish `h2 : Valued.v (algebraMap F (v.adicCompletion F) (r v : F) - algebraMap F (v.adicCompletion F) (b : F)) ≤ v.intValuation n`. Rewrite using `[← map_sub, show (r v : F) - (b : F) = ((r v - b : 𝓞 F) : F) from (map_sub (algebraMap (𝓞 F) F) _ _).symm, valued_algebraMap_int, ← Valuation.map_neg, neg_sub, intValuation_if_neg v hn]`. Conclude with `(intValuation_le_pow_iff_mem v _ _).mpr (hb v hv)`. Establish `e : a v - algebraMap F (v.adicCompletion F) (b : F) = (a v - algebraMap F (v.adicCompletion F) (r v : F)) + (algebraMap F (v.adicCompletion F) (r v : F) - algebraMap F (v.adicCompletion F) (b : F))`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(Valuation.map_add _ _ _).trans (max_le h1 h2)`. Establish `hn1 : v.intValuation n = 1` using `le_antisymm (intValuation_le_one v n) (not_lt.mp fun h ↦ hv ((hmemT v).mpr ((intValuation_lt_one_iff_mem v n).mp h)))`. Rewrite using `[hn1]`.

Conclude with `(Valuation.map_sub _ _ _).trans (max_le ((mem_adicCompletionIntegers (𝓞 F) F v).mp (ha v)) hb1)`.
-/
theorem exists_approx (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F)
    (n : 𝓞 F) (hn : n ≠ 0) :
    ∃ b : 𝓞 F, ∀ v, Valued.v (a v - algebraMap F (v.adicCompletion F) (b : F)) ≤ v.intValuation n := by
  classical
  have hspan : Ideal.span {n} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn
  set T := (Ideal.finite_factors hspan).toFinset with hT
  have hmemT : ∀ v, v ∈ T ↔ n ∈ v.asIdeal := fun v ↦ by
    simp [T, Set.Finite.mem_toFinset, Ideal.dvd_span_singleton]
  have hw : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) (n : F) ≠ 0 := by
    intro v h
    have := valued_algebraMap_int v n
    rw [h, map_zero, intValuation_if_neg v hn] at this
    exact WithZero.exp_ne_zero this.symm
  have hr : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : 𝓞 F,
      Valued.v (a v - algebraMap F (v.adicCompletion F) (r : F)) <
        Valued.v (algebraMap F (v.adicCompletion F) (n : F)) := fun v ↦
    exists_int_near v (a v) _ ((mem_adicCompletionIntegers (𝓞 F) F v).mp (ha v)) (hw v)
      (by rw [valued_algebraMap_int]; exact intValuation_le_one v n)
  choose r hr using hr
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : HeightOneSpectrum (𝓞 F) ↦ v.asIdeal)
    (fun v ↦ (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n})).factors)
    (fun v _ ↦ v.prime) (fun i _ j _ hij h ↦ hij (HeightOneSpectrum.ext h)) (fun i ↦ r i.1)
  refine ⟨b, fun v ↦ ?_⟩
  have hb1 : Valued.v (algebraMap F (v.adicCompletion F) (b : F)) ≤ 1 := by
    rw [valued_algebraMap_int]; exact intValuation_le_one v b
  by_cases hv : v ∈ T
  · have h1 := (hr v).le
    rw [valued_algebraMap_int] at h1
    have h2 : Valued.v (algebraMap F (v.adicCompletion F) (r v : F) -
        algebraMap F (v.adicCompletion F) (b : F)) ≤ v.intValuation n := by
      rw [← map_sub, show (r v : F) - (b : F) = ((r v - b : 𝓞 F) : F) from
        (map_sub (algebraMap (𝓞 F) F) _ _).symm, valued_algebraMap_int, ← Valuation.map_neg,
        neg_sub, intValuation_if_neg v hn]
      exact (intValuation_le_pow_iff_mem v _ _).mpr (hb v hv)
    have e : a v - algebraMap F (v.adicCompletion F) (b : F) =
        (a v - algebraMap F (v.adicCompletion F) (r v : F)) +
          (algebraMap F (v.adicCompletion F) (r v : F) - algebraMap F (v.adicCompletion F) (b : F)) := by
      ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le h1 h2)
  · have hn1 : v.intValuation n = 1 := le_antisymm (intValuation_le_one v n)
      (not_lt.mp fun h ↦ hv ((hmemT v).mpr ((intValuation_lt_one_iff_mem v n).mp h)))
    rw [hn1]
    exact (Valuation.map_sub _ _ _).trans
      (max_le ((mem_adicCompletionIntegers (𝓞 F) F v).mp (ha v)) hb1)

/- English proof (translation)
Take `⟨b, hb⟩` from `exists_approx a ha n hn`. Establish `hnF : (n : F) ≠ 0`. Use `(IsFractionRing.injective (𝓞 F) F).ne hn` as an intermediate fact. Rewrite `this` using `[map_zero]`. Then use the resulting hypothesis. Establish `hA : ∀ (k : F) (v : HeightOneSpectrum (𝓞 F)), (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) v = algebraMap F (v.adicCompletion F) k` using `fun k v ↦ rfl`.

Use `⟨b, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((n : F)⁻¹) * (a - algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F)), fun v ↦ ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_adicCompletionIntegers]`. Express the relevant statement in the definitionally equal form `Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) ((n : F)⁻¹)) v * (a v - (algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F)) v)) ≤ 1`. Rewrite using `[hA, hA, map_mul, map_inv₀, map_inv₀, valued_algebraMap_int]`. Establish `hne : v.intValuation n ≠ 0`.

Rewrite using `[intValuation_if_neg v hn]`. Conclude with `WithZero.exp_ne_zero`. Combine the equalities or inequalities in the displayed calculation. Establish `hbv` using `hb v`. Use `gcongr`.

Use `_ = 1 := inv_mul_cancel₀ hne`. Rewrite using `[← mul_assoc, ← map_mul, mul_inv_cancel₀ hnF, map_one, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_decomp (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F)
    (n : 𝓞 F) (hn : n ≠ 0) :
    ∃ b : 𝓞 F, ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧
      a = algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F) +
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (n : F) * c := by
  obtain ⟨b, hb⟩ := exists_approx a ha n hn
  have hnF : (n : F) ≠ 0 := by
    have := (IsFractionRing.injective (𝓞 F) F).ne hn
    rwa [map_zero] at this
  have hA : ∀ (k : F) (v : HeightOneSpectrum (𝓞 F)),
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) v = algebraMap F (v.adicCompletion F) k :=
    fun k v ↦ rfl
  refine ⟨b, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((n : F)⁻¹) *
    (a - algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F)), fun v ↦ ?_, ?_⟩
  · rw [mem_adicCompletionIntegers]
    change Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) ((n : F)⁻¹)) v *
      (a v - (algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F)) v)) ≤ 1
    rw [hA, hA, map_mul, map_inv₀, map_inv₀, valued_algebraMap_int]
    have hne : v.intValuation n ≠ 0 := by
      rw [intValuation_if_neg v hn]; exact WithZero.exp_ne_zero
    calc (v.intValuation n)⁻¹ * Valued.v (a v - algebraMap F (v.adicCompletion F) (b : F))
        ≤ (v.intValuation n)⁻¹ * v.intValuation n := by
          have hbv := hb v
          gcongr
      _ = 1 := inv_mul_cancel₀ hne
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hnF, map_one, one_mul]
    ring

end Formalism.L2.S.Pv.PsiTrCore
