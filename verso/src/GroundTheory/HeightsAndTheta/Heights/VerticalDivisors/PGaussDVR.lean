import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain WithZero

noncomputable section

section Dedekind

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (v : HeightOneSpectrum A)

/- English proof (translation)
Establish `hlt : v.intValuation a < 1`. Rewrite using `[ha, ← exp_zero, exp_lt_exp]`. Evaluate the numerical expressions. Take `⟨J, hJ⟩` from `(v.intValuation_lt_one_iff_dvd a).mp hlt`. Establish `hJv : ¬ J ≤ v.asIdeal`.

Introduce `hle`. Take `⟨J', hJ'⟩` from `Ideal.dvd_iff_le.mpr hle`. Establish `h2 : v.asIdeal ^ 2 ∣ Ideal.span {a}` using `⟨J', by rw [hJ, hJ', sq, mul_assoc]⟩`. Establish `h3` using `(v.intValuation_le_pow_iff_dvd a 2).mpr h2`. Rewrite `h3` using `[ha, exp_le_exp]`.

Evaluate the numerical expressions using `at h3`. Establish `hJj : ¬ J ^ j ≤ v.asIdeal` using `fun h => hJv (Ideal.IsPrime.le_of_pow_le h)`. Take `⟨t, htJ, htv⟩` from `SetLike.not_le_iff_exists.mp hJj`. Establish `hid : J ^ j * v.asIdeal ^ j = Ideal.span {a ^ j}`. Rewrite using `[← mul_pow, mul_comm, ← hJ, Ideal.span_singleton_pow]`.

Establish `hmem : C t * p ∈ Ideal.span {(C a ^ j : MvPolynomial σ A)}`. Establish `h1 : C t * p ∈ Ideal.map (C : A →+* MvPolynomial σ A) (J ^ j) * Ideal.map (C : A →+* MvPolynomial σ A) (v.asIdeal ^ j)` using `Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ htJ) hp`. Rewrite `h1` using `[← Ideal.map_mul, hid, Ideal.map_span, Set.image_singleton, map_pow]`. Conclude with `h1`. Take `⟨h, hh⟩` from `Ideal.mem_span_singleton'.mp hmem`.

Conclude with `⟨t, htv, h, by rw [← hh, mul_comm]⟩`.
-/
theorem exists_C_mul_eq_C_pow_mul {a : A} (ha : v.intValuation a = exp (-1 : ℤ)) {σ : Type*}
    (j : ℕ) {p : MvPolynomial σ A} (hp : p ∈ Ideal.map (C : A →+* MvPolynomial σ A) (v.asIdeal ^ j)) :
    ∃ t ∉ v.asIdeal, ∃ h : MvPolynomial σ A, C t * p = C a ^ j * h := by
  have hlt : v.intValuation a < 1 := by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num
  obtain ⟨J, hJ⟩ := (v.intValuation_lt_one_iff_dvd a).mp hlt
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hle
    obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.mpr hle
    have h2 : v.asIdeal ^ 2 ∣ Ideal.span {a} := ⟨J', by rw [hJ, hJ', sq, mul_assoc]⟩
    have h3 := (v.intValuation_le_pow_iff_dvd a 2).mpr h2
    rw [ha, exp_le_exp] at h3
    norm_num at h3
  have hJj : ¬ J ^ j ≤ v.asIdeal := fun h => hJv (Ideal.IsPrime.le_of_pow_le h)
  obtain ⟨t, htJ, htv⟩ := SetLike.not_le_iff_exists.mp hJj
  have hid : J ^ j * v.asIdeal ^ j = Ideal.span {a ^ j} := by
    rw [← mul_pow, mul_comm, ← hJ, Ideal.span_singleton_pow]
  have hmem : C t * p ∈ Ideal.span {(C a ^ j : MvPolynomial σ A)} := by
    have h1 : C t * p ∈ Ideal.map (C : A →+* MvPolynomial σ A) (J ^ j) *
        Ideal.map (C : A →+* MvPolynomial σ A) (v.asIdeal ^ j) :=
      Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ htJ) hp
    rw [← Ideal.map_mul, hid, Ideal.map_span, Set.image_singleton, map_pow] at h1
    exact h1
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨t, htv, h, by rw [← hh, mul_comm]⟩

end Dedekind

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Take `⟨m, hm⟩` from `hg`. Apply `le_antisymm` to reduce the goal to its premises. Use `gaussNormOf_le _ zero_le_one fun d => ?_` and prove the remaining obligations. Rewrite using `[coeff_map, ← FinitePlace.norm_embedding]`. Conclude with `FinitePlace.norm_le_one K (v := v) (g.coeff d)`.

Establish `h1` using `le_gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v) (g.map (algebraMap (𝓞 K) K)) m`. Rewrite `h1` using `[coeff_map, ← FinitePlace.norm_embedding, (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr hm]`. Conclude with `h1`.
-/
theorem gaussNorm_map_of_coeff_notMem (v : HeightOneSpectrum (𝓞 K)) {σ : Type*}
    (g : MvPolynomial σ (𝓞 K)) (hg : ∃ m, g.coeff m ∉ v.asIdeal) :
    gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1 := by
  obtain ⟨m, hm⟩ := hg
  apply le_antisymm
  · refine gaussNormOf_le _ zero_le_one fun d => ?_
    rw [coeff_map, ← FinitePlace.norm_embedding]
    exact FinitePlace.norm_le_one K (v := v) (g.coeff d)
  · have h1 := le_gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v)
      (g.map (algebraMap (𝓞 K) K)) m
    rw [coeff_map, ← FinitePlace.norm_embedding,
      (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr hm] at h1
    exact h1

/- English proof (translation)
Rewrite using `[NumberField.HeightOneSpectrum.adicAbv_def, HeightOneSpectrum.valuation_of_algebraMap, ha, WithZeroMulInt.toNNReal_neg_apply _ exp_ne_zero]`. Establish `h1 : Multiplicative.toAdd (unzero (exp_ne_zero (a` using `(-1 : ℤ)))) = -1 := rfl`. Rewrite using `[h1, zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]`.
-/
theorem adicAbv_of_intValuation_eq (v : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K}
    (ha : v.intValuation a = exp (-1 : ℤ)) :
    NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K a) =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, HeightOneSpectrum.valuation_of_algebraMap, ha,
    WithZeroMulInt.toNNReal_neg_apply _ exp_ne_zero]
  have h1 : Multiplicative.toAdd (unzero (exp_ne_zero (a := (-1 : ℤ)))) = -1 := rfl
  rw [h1, zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]

/- English proof (translation)
Use `set φ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) with hφ`. Establish `hav : a ∈ v.asIdeal` using `(v.intValuation_lt_one_iff_mem a).mp (by`. Rewrite using `[ha, ← exp_zero, exp_lt_exp]`. Use the proof step `norm_num)`. Establish `hnu : ¬ IsUnit (φ (C a))`.

Rewrite using `[IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]`. Conclude with `fun h => h (Ideal.mem_map_of_mem _ hav)`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (ParDVR e n v)`. Choose the witnesses or unpack the hypotheses as in `⟨x, s, rfl⟩ : ∃ (x : MvPolynomial (Par e n) (𝓞 K)) (s : (parPrime e n v).primeCompl), IsLocalization.mk' (ParDVR e n v) x s = ϖ := by`. Take `⟨⟨x, s⟩, hxs⟩` from `IsLocalization.mk'_surjective (parPrime e n v).primeCompl ϖ`.

Conclude with `⟨x, s, hxs⟩`. Establish `hx : x ∈ Ideal.map (C : 𝓞 K →+* MvPolynomial (Par e n) (𝓞 K)) (v.asIdeal ^ 1)`. Rewrite using `[pow_one]`. Assume the negation of the conclusion as `hx`. Conclude with `hϖ.not_isUnit ((IsLocalization.AtPrime.isUnit_mk'_iff (ParDVR e n v) (parPrime e n v) x s).mpr hx)`.

Take `⟨t, ht, h, hth⟩` from `exists_C_mul_eq_C_pow_mul v ha 1 hx`. Establish `htu : IsUnit (φ (C t))`. Rewrite using `[IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]`. Introduce `htP`. Conclude with `ht (by simpa using (MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp htP 0)`.

Establish `hx2 : φ x = φ (C a) * (↑htu.unit⁻¹ * φ h)`. Establish `h2` using `congrArg φ hth`. Rewrite `h2` using `[map_mul, map_mul, pow_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, IsUnit.val_inv_mul, one_mul]`.

Use `_ = φ (C a) * (↑htu.unit⁻¹ * φ h) := by rw [h2]; ring`. Establish `hϖ' : IsLocalization.mk' (ParDVR e n v) x s = φ (C a) * (↑htu.unit⁻¹ * φ h * IsLocalization.mk' (ParDVR e n v) 1 s)`. Rewrite using `[IsLocalization.mk'_eq_mul_mk'_one, hx2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hϖ` using `[hϖ']`.

Break down `hϖ.isUnit_or_isUnit rfl with hu | hu` into its components or cases. Conclude with `(hnu hu).elim`. Conclude with `(irreducible_mul_isUnit hu).mp hϖ`.
-/
theorem irreducible_algebraMap_C (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    [IsDiscreteValuationRing (ParDVR e n v)] {a : 𝓞 K} (ha : v.intValuation a = exp (-1 : ℤ)) :
    Irreducible (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a)) := by
  set φ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) with hφ
  have hav : a ∈ v.asIdeal := (v.intValuation_lt_one_iff_mem a).mp (by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num)
  have hnu : ¬ IsUnit (φ (C a)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    exact fun h => h (Ideal.mem_map_of_mem _ hav)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ParDVR e n v)
  obtain ⟨x, s, rfl⟩ : ∃ (x : MvPolynomial (Par e n) (𝓞 K)) (s : (parPrime e n v).primeCompl),
      IsLocalization.mk' (ParDVR e n v) x s = ϖ := by
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.mk'_surjective (parPrime e n v).primeCompl ϖ
    exact ⟨x, s, hxs⟩
  have hx : x ∈ Ideal.map (C : 𝓞 K →+* MvPolynomial (Par e n) (𝓞 K)) (v.asIdeal ^ 1) := by
    rw [pow_one]
    by_contra hx
    exact hϖ.not_isUnit
      ((IsLocalization.AtPrime.isUnit_mk'_iff (ParDVR e n v) (parPrime e n v) x s).mpr hx)
  obtain ⟨t, ht, h, hth⟩ := exists_C_mul_eq_C_pow_mul v ha 1 hx
  have htu : IsUnit (φ (C t)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro htP
    exact ht (by simpa using (MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp htP 0)
  have hx2 : φ x = φ (C a) * (↑htu.unit⁻¹ * φ h) := by
    have h2 := congrArg φ hth
    rw [map_mul, map_mul, pow_one] at h2
    calc φ x = ↑htu.unit⁻¹ * (φ (C t) * φ x) := by
          rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
      _ = φ (C a) * (↑htu.unit⁻¹ * φ h) := by rw [h2]; ring
  have hϖ' : IsLocalization.mk' (ParDVR e n v) x s =
      φ (C a) * (↑htu.unit⁻¹ * φ h * IsLocalization.mk' (ParDVR e n v) 1 s) := by
    rw [IsLocalization.mk'_eq_mul_mk'_one, hx2]
    ring
  rw [hϖ'] at hϖ
  rcases hϖ.isUnit_or_isUnit rfl with hu | hu
  · exact (hnu hu).elim
  · exact (irreducible_mul_isUnit hu).mp hϖ

end NumberField

/- English proof (translation)
Introduce `K _ _ e n v g hg`. Use `h1 K e n v` as an intermediate fact. Take `⟨a, ha⟩` from `v.intValuation_exists_uniformizer`. Use `set φ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) with hφ`. Establish `hav : a ∈ v.asIdeal` using `(v.intValuation_lt_one_iff_mem a).mp (by`.

Rewrite using `[ha, ← exp_zero, exp_lt_exp]`. Use the proof step `norm_num)`. Set `μ : 𝓞 K → ℕ` to `fun b => multiplicity v.asIdeal (Ideal.span {b})`. Establish `hval : ∀ b : 𝓞 K, b ≠ 0 → ∀ k : ℕ, b ∈ v.asIdeal ^ k ↔ k ≤ μ b`. Introduce `b hb k`.

Rewrite using `[← v.intValuation_le_pow_iff_mem, v.intValuation_eq_exp_neg_multiplicity hb, exp_le_exp]`. Simplify using `only [μ]`. Use linear arithmetic over natural numbers and integers. Establish `hne : g.support.Nonempty` using `Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hg)`. Take `⟨d0, hd0, hmin⟩` from `g.support.exists_mem_eq_inf' hne (fun d => μ (g.coeff d))`.

Use `set m := g.support.inf' hne (fun d => μ (g.coeff d)) with hm`. Establish `hgm : g ∈ Ideal.map (C : 𝓞 K →+* MvPolynomial (Par e n) (𝓞 K)) (v.asIdeal ^ m)`. Rewrite using `[MvPolynomial.mem_map_C_iff]`. Introduce `d`. Distinguish the cases in `hd : g.coeff d = 0`.

Rewrite using `[hd]`. Conclude with `Ideal.zero_mem _`. Conclude with `(hval _ hd m).mpr (Finset.inf'_le _ (mem_support_iff.mpr hd))`. Take `⟨t, ht, h, hth⟩` from `exists_C_mul_eq_C_pow_mul v ha m hgm`. Establish `hb0 : g.coeff d0 ≠ 0` using `mem_support_iff.mp hd0`.

Establish `hh : h.coeff d0 ∉ v.asIdeal`. Introduce `hmem`. Establish `hc` using `congrArg (coeff d0) hth`. Rewrite `hc` using `[coeff_C_mul, ← C_pow, coeff_C_mul]`. Establish `h3 : t * g.coeff d0 ∈ v.asIdeal ^ (m + 1)`.

Rewrite using `[hc, pow_succ]`. Conclude with `Ideal.mul_mem_mul (Ideal.pow_mem_pow hav m) hmem`. Establish `h4` using `(v.intValuation_le_pow_iff_mem _ _).mpr h3`. Rewrite `h4` using `[map_mul, HeightOneSpectrum.intValuation_eq_one_iff.mpr ht, one_mul, v.intValuation_le_pow_iff_mem, hval _ hb0]`. Use linear arithmetic over natural numbers and integers.

Establish `htu : IsUnit (φ (C t))`. Rewrite using `[IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]`. Introduce `htP`. Conclude with `ht (by simpa using (MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp htP 0)`. Establish `hhu : IsUnit (φ h)`.

Rewrite using `[IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]`. Introduce `hP`. Conclude with `hh ((MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp hP d0)`. Establish `hord : Ring.ord (ParDVR e n v) (φ g) = m`. Rewrite using `[Ring.ord_eq_addVal]`.

Establish `h0` using `congrArg φ hth`. Rewrite `h0` using `[map_mul φ, map_mul φ, map_pow φ]`. Establish `h2` using `congrArg (IsDiscreteValuationRing.addVal (ParDVR e n v)) h0`. Rewrite `h2` using `[IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer (irreducible_algebraMap_C e n v ha), IsDiscreteValuationRing.addVal_eq_zero_iff.mpr htu, IsDiscreteValuationRing.addVal_eq_zero_ …`. Simplify using `using h2`.

Establish `hK0` using `congrArg (MvPolynomial.map (algebraMap (𝓞 K) K)) hth`. Rewrite `hK0` using `[map_mul (MvPolynomial.map (algebraMap (𝓞 K) K)), map_mul (MvPolynomial.map (algebraMap (𝓞 K) K)), map_pow (MvPolynomial.map (algebraMap (𝓞 K) K)), MvPolynomial.map_C, MvPolynomial.map_C]`. Establish `hK` using `congrArg (gaussNorm v) hK0`. Rewrite `hK` using `[← C_pow, gaussNorm_C_mul, gaussNorm_C_mul, map_pow, adicAbv_of_intValuation_eq v ha, gaussNorm_map_of_coeff_notMem v h ⟨d0, hh⟩, ← FinitePlace.norm_embedding, (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr ht, one_mul, mul_one]`. Establish `hN : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0`.

Conclude with `(NumberField.HeightOneSpectrum.absNorm_ne_zero v)` after adjusting the coercions. Rewrite using `[hord, ENat.toNat_natCast, hK, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hN)]`.
-/
theorem GaussDVR.proof (h1 : ParDVRIsDVR.Statement) : GaussDVR.Statement := by
  intro K _ _ e n v g hg
  have := h1 K e n v
  classical
  obtain ⟨a, ha⟩ := v.intValuation_exists_uniformizer
  set φ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) with hφ
  have hav : a ∈ v.asIdeal := (v.intValuation_lt_one_iff_mem a).mp (by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num)
  let μ : 𝓞 K → ℕ := fun b => multiplicity v.asIdeal (Ideal.span {b})
  have hval : ∀ b : 𝓞 K, b ≠ 0 → ∀ k : ℕ, b ∈ v.asIdeal ^ k ↔ k ≤ μ b := by
    intro b hb k
    rw [← v.intValuation_le_pow_iff_mem, v.intValuation_eq_exp_neg_multiplicity hb, exp_le_exp]
    simp only [μ]
    omega
  have hne : g.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hg)
  obtain ⟨d0, hd0, hmin⟩ := g.support.exists_mem_eq_inf' hne (fun d => μ (g.coeff d))
  set m := g.support.inf' hne (fun d => μ (g.coeff d)) with hm
  have hgm : g ∈ Ideal.map (C : 𝓞 K →+* MvPolynomial (Par e n) (𝓞 K)) (v.asIdeal ^ m) := by
    rw [MvPolynomial.mem_map_C_iff]
    intro d
    by_cases hd : g.coeff d = 0
    · rw [hd]
      exact Ideal.zero_mem _
    · exact (hval _ hd m).mpr (Finset.inf'_le _ (mem_support_iff.mpr hd))
  obtain ⟨t, ht, h, hth⟩ := exists_C_mul_eq_C_pow_mul v ha m hgm
  have hb0 : g.coeff d0 ≠ 0 := mem_support_iff.mp hd0
  have hh : h.coeff d0 ∉ v.asIdeal := by
    intro hmem
    have hc := congrArg (coeff d0) hth
    rw [coeff_C_mul, ← C_pow, coeff_C_mul] at hc
    have h3 : t * g.coeff d0 ∈ v.asIdeal ^ (m + 1) := by
      rw [hc, pow_succ]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hav m) hmem
    have h4 := (v.intValuation_le_pow_iff_mem _ _).mpr h3
    rw [map_mul, HeightOneSpectrum.intValuation_eq_one_iff.mpr ht, one_mul, v.intValuation_le_pow_iff_mem,
      hval _ hb0] at h4
    omega
  have htu : IsUnit (φ (C t)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro htP
    exact ht (by simpa using (MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp htP 0)
  have hhu : IsUnit (φ h) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro hP
    exact hh ((MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp hP d0)
  have hord : Ring.ord (ParDVR e n v) (φ g) = m := by
    rw [Ring.ord_eq_addVal]
    have h0 := congrArg φ hth
    rw [map_mul φ, map_mul φ, map_pow φ] at h0
    have h2 := congrArg (IsDiscreteValuationRing.addVal (ParDVR e n v)) h0
    rw [IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer (irreducible_algebraMap_C e n v ha),
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr htu,
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hhu] at h2
    simpa using h2
  have hK0 := congrArg (MvPolynomial.map (algebraMap (𝓞 K) K)) hth
  rw [map_mul (MvPolynomial.map (algebraMap (𝓞 K) K)), map_mul (MvPolynomial.map (algebraMap (𝓞 K) K)),
    map_pow (MvPolynomial.map (algebraMap (𝓞 K) K)), MvPolynomial.map_C, MvPolynomial.map_C] at hK0
  have hK := congrArg (gaussNorm v) hK0
  rw [← C_pow, gaussNorm_C_mul, gaussNorm_C_mul, map_pow,
    adicAbv_of_intValuation_eq v ha, gaussNorm_map_of_coeff_notMem v h ⟨d0, hh⟩, ← FinitePlace.norm_embedding,
    (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr ht, one_mul, mul_one] at hK
  have hN : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
  rw [hord, ENat.toNat_natCast, hK, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hN)]

end

end GroundTheory.Heights₂.Heights.Vertical
