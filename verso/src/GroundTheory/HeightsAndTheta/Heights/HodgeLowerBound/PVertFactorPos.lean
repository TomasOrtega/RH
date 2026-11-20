import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVertFactorPos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenFibreHomog
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace VertFactorPos

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Rewrite using `[aeval_def, eval_map, algebraMap_int_eq]`.
-/
theorem aeval_eq_eval_map (z : (Σ k, ι k) → ℂ) (F : MRing ι) :
    aeval z F = eval z (map (Int.castRingHom ℂ) F) := by
  rw [aeval_def, eval_map, algebraMap_int_eq]

/- English proof (translation)
Use `⟨fun h => ?_, mem_mCoordIdeal_of_aeval_eq_zero y hF⟩` and prove the remaining obligations. Establish `h' : mConeMap y F = 0` using `RingHom.mem_ker.mp h`. Rewrite `h'` using `[mConeMap_of_isMultiHomog y hF]`. Establish `hm : (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)`. Conclude with `C_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hm)`.
-/
theorem mem_mCoordIdeal_iff_of_homog {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {F : MRing ι}
    {d : K → ℕ} (hF : IsMultiHomog F d) : F ∈ mCoordIdeal y ↔ aeval y F = 0 := by
  refine ⟨fun h => ?_, mem_mCoordIdeal_of_aeval_eq_zero y hF⟩
  have h' : mConeMap y F = 0 := RingHom.mem_ker.mp h
  rw [mConeMap_of_isMultiHomog y hF] at h'
  have hm : (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)
  exact C_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hm)

omit [Fintype K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Use `show X q ∈ RingHom.ker (mConeMap y) ↔ _`. Rewrite using `[RingHom.mem_ker]`. Simplify using `[mConeMap, X_ne_zero]`.
-/
theorem X_mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (q : Σ k, ι k) :
    (X q : MRing ι) ∈ mCoordIdeal y ↔ y q = 0 := by
  show X q ∈ RingHom.ker (mConeMap y) ↔ _
  rw [RingHom.mem_ker]
  simp [mConeMap, X_ne_zero]

/- English proof (translation)
Introduce `F hF`. Use `show F ∈ RingHom.ker (mConeMap z)`. Rewrite using `[RingHom.mem_ker]`. Use extensionality with `m`. Rewrite using `[coeff_zero, ← Finsupp.equivFunOnFinite_symm_coe m, HilbertSamuel.GenFibreHomog.coeff_mConeMap, aeval_eq_eval_map]`.

Conclude with `hz.2 _ (HilbertSamuel.GenFibreHomog.isMultiHomogIdeal_mCoordIdeal y F hF _)`.
-/
theorem mCoordIdeal_le {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) : mCoordIdeal y ≤ mCoordIdeal z := by
  classical
  intro F hF
  show F ∈ RingHom.ker (mConeMap z)
  rw [RingHom.mem_ker]
  ext m
  rw [coeff_zero, ← Finsupp.equivFunOnFinite_symm_coe m,
    HilbertSamuel.GenFibreHomog.coeff_mConeMap, aeval_eq_eval_map]
  exact hz.2 _ (HilbertSamuel.GenFibreHomog.isMultiHomogIdeal_mCoordIdeal y F hF _)

/- English proof (translation)
Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]`.
-/
theorem prod_X_pow_add (d d' : K → ℕ) {R : Type} [CommRing R] :
    (∏ k, (X k : MvPolynomial K R) ^ (d + d') k) =
      (∏ k, (X k : MvPolynomial K R) ^ d k) * ∏ k, (X k : MvPolynomial K R) ^ d' k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]

/- English proof (translation)
Rewrite using `[monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem prod_X_pow_eq_monomial (d : K → ℕ) {R : Type} [CommRing R] :
    (∏ k, (X k : MvPolynomial K R) ^ d k) = monomial (Finsupp.equivFunOnFinite.symm d) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
  simp

/- English proof (translation)
Apply `HilbertSamuel.GenFibreHomog.isMultiHomog_of_weighted` to reduce the goal to its premises. Use `IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, c k⟩ : MRing ι) ^ d k) (fun k => d k • NumbersDVR.blockWeight ι ⟨k, c k⟩) (fun k _ => (isWeightedHomogeneous_X ℤ (NumbersDVR.blockWeight ι) ⟨k, c k⟩).pow (d k))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `[NumbersDVR.blockWeight, Finset.sum_apply, Pi.single_apply]`.
-/
theorem isMultiHomog_chartForm [DecidableEq K] (c : (k : K) → ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) d := by
  apply HilbertSamuel.GenFibreHomog.isMultiHomog_of_weighted
  have := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, c k⟩ : MRing ι) ^ d k)
    (fun k => d k • NumbersDVR.blockWeight ι ⟨k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X ℤ (NumbersDVR.blockWeight ι) ⟨k, c k⟩).pow (d k))
  convert this using 1
  funext k
  simp [NumbersDVR.blockWeight, Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Establish `hPW : mCoordIdeal y ≤ mCoordIdeal z` using `mCoordIdeal_le hz`. Establish `hWp : (mCoordIdeal z).IsPrime` using `RingHom.ker_isPrime _`. Establish `hrel : IsRelevant (mCoordIdeal z)` using `fun k => ⟨c k, fun h => hc k ((X_mem_mCoordIdeal_iff z _).1 h)⟩`. Establish `hpW : (C (p : ℤ) : MRing ι) ∉ mCoordIdeal z`. Introduce `h`.

Establish `h' : mConeMap z (C (p : ℤ)) = 0` using `RingHom.mem_ker.mp h`. Simplify using `[mConeMap, hp] at h'`. Take `⟨u, v, hu, hv, huv⟩` from `hV.unit_off_fibre _ hWp hPW hrel hpW`. Take `⟨bf, bg, hf, hg, hb⟩` from `hV.degrees`. Establish `hfy : aeval y f ≠ 0` using `fun h => hV.num_not_mem ((mem_mCoordIdeal_iff_of_homog y hf).2 h)`.

Establish `hgy : aeval y g ≠ 0` using `fun h => hV.den_not_mem ((mem_mCoordIdeal_iff_of_homog y hg).2 h)`. Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k h => hc k ((X_mem_mCoordIdeal_iff z _).1 (hPW ((X_mem_mCoordIdeal_iff y _).2 h)))`. Establish `hu' : mConeMap z u ≠ 0` using `fun h => hu (RingHom.mem_ker.mpr h)`. Take `⟨m, hm⟩` from `MvPolynomial.ne_zero_iff.1 hu'`. Use `set e : K → ℕ := ⇑m with he`.

Use `set ue := weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e u with hue_def`. Establish `hue : IsMultiHomog ue e` using `HilbertSamuel.GenFibreHomog.isMultiHomog_of_weighted (weightedHomogeneousComponent_isWeightedHomogeneous e u)`. Establish `huez : aeval z ue ≠ 0`. Rewrite `hm` using `[← Finsupp.equivFunOnFinite_symm_coe m, HilbertSamuel.GenFibreHomog.coeff_mConeMap]`. Conclude with `hm`.

Establish `hueW : ue ∉ mCoordIdeal z` using `fun h => huez ((mem_mCoordIdeal_iff_of_homog z hue).1 h)`. Establish `huey : aeval y ue ≠ 0` using `fun h => hueW (hPW ((mem_mCoordIdeal_iff_of_homog y hue).2 h))`. Establish `hrel' : mConeMap y u * (C (aeval y f) * ∏ k, (X k : MvPolynomial K Ω) ^ bf k) = mConeMap y v * (C (aeval y g) * ∏ k, (X k : MvPolynomial K Ω) ^ bg k)`. Establish `h : mConeMap y (u * f - v * g) = 0` using `RingHom.mem_ker.mp huv`. Rewrite `h` using `[map_sub, map_mul, map_mul, sub_eq_zero, mConeMap_of_isMultiHomog y hf, mConeMap_of_isMultiHomog y hg]`.

Conclude with `h`. Establish `hcoef` using `congrArg (coeff (m + Finsupp.equivFunOnFinite.symm bf)) hrel'`. Rewrite `hcoef` using `[prod_X_pow_eq_monomial, prod_X_pow_eq_monomial, C_mul_monomial, C_mul_monomial, coeff_mul_monomial', coeff_mul_monomial', if_pos le_add_self, add_tsub_cancel_right, mul_one, mul_one]`. Establish `hcu : coeff m (mConeMap y u) = aeval y ue`. Rewrite using `[← Finsupp.equivFunOnFinite_symm_coe m, HilbertSamuel.GenFibreHomog.coeff_mConeMap]`.

Rewrite `hcoef` using `[hcu]`. Distinguish the cases in `hle : Finsupp.equivFunOnFinite.symm bg ≤ m + Finsupp.equivFunOnFinite.symm bf`. Use `swap`. Rewrite `hcoef` using `[if_neg hle]`. Conclude with `absurd hcoef (mul_ne_zero huey hfy)`.

Rewrite `hcoef` using `[if_pos hle]`. Use `set d' : K → ℕ := ⇑(m + Finsupp.equivFunOnFinite.symm bf - Finsupp.equivFunOnFinite.symm bg) with hd'`. Use `set a := weightedHomogeneousComponent (NumbersDVR.blockWeight ι) d' v with ha_def`. Establish `ha : IsMultiHomog a d'` using `HilbertSamuel.GenFibreHomog.isMultiHomog_of_weighted (weightedHomogeneousComponent_isWeightedHomogeneous d' v)`. Establish `hcv : coeff (m + Finsupp.equivFunOnFinite.symm bf - Finsupp.equivFunOnFinite.symm bg) (mConeMap y v) = aeval y a`.

Rewrite using `[← Finsupp.equivFunOnFinite_symm_coe (m + Finsupp.equivFunOnFinite.symm bf - Finsupp.equivFunOnFinite.symm bg), HilbertSamuel.GenFibreHomog.coeff_mConeMap]`. Rewrite `hcoef` using `[hcv]`. Establish `hdeg : d' + bg = e + bf`. Use `congrArg (⇑) (tsub_add_cancel_of_le hle)` as an intermediate fact. Simplify `this` using `[hd', he, Finsupp.coe_add]`.

Establish `hkey : a * u - ue * v ∈ mCoordIdeal y` using `by show _ ∈ RingHom.ker (mConeMap y)`. Rewrite using `[RingHom.mem_ker, map_sub, map_mul, map_mul, sub_eq_zero, mConeMap_of_isMultiHomog y ha, mConeMap_of_isMultiHomog y hue]`. Establish `hG : (C (aeval y g) * ∏ k, (X k : MvPolynomial K Ω) ^ bg k) ≠ 0` using `mul_ne_zero (C_ne_zero.2 hgy) (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k))`. Use `mul_right_cancel₀ hG ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[prod_X_pow_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [hrel']; ring`. Establish `haW : a ∉ mCoordIdeal z`. Introduce `h`.

Establish `h2 : ue * v ∈ mCoordIdeal z`. Use `Ideal.sub_mem _ (Ideal.mul_mem_right u _ h) (hPW hkey)` as an intermediate fact. Simplify using `using this`. Break down `hWp.mem_or_mem h2 with h3 | h3` into its components or cases. Conclude with `hueW h3`.

Conclude with `hv h3`. Establish `haz : aeval z a ≠ 0` using `fun h => haW ((mem_mCoordIdeal_iff_of_homog z ha).2 h)`. Establish `hMz : ∀ d : K → ℕ, eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k)) = ∏ k, z ⟨k, c k⟩ ^ d k` using `fun d => by simp [map_prod]`. Establish `hMy : ∀ d : K → ℕ, aeval y (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) = ∏ k, y ⟨k, c k⟩ ^ d k` using `fun d => by simp [map_prod]`. Establish `hMz0 : ∀ d : K → ℕ, (∏ k, z ⟨k, c k⟩ ^ d k) ≠ 0` using `fun d => Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)`.

Establish `hMy0 : ∀ d : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0` using `fun d => Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)`. Establish `hchart : chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k = ∏ k, y ⟨k, c k⟩ ^ bg k`. Rewrite using `[chartMono, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← hb, Pi.neg_apply, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `⟨eval z (map (Int.castRingHom ℂ) (a * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bg k)) / eval z (map (Int.castRingHom ℂ) (ue * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bf k)), ?_, e + bf, a * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bg k, ue * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bf k, ?_, ?_, ?_, ?_, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [map_mul]`. Rewrite using `[hMz, hMz, ← aeval_eq_eval_map, ← aeval_eq_eval_map]`.

Conclude with `div_ne_zero (mul_ne_zero haz (hMz0 _)) (mul_ne_zero huez (hMz0 _))`. Rewrite using `[← hdeg]`. Conclude with `LowerBoundFree.isMultiHomog_mul ha (isMultiHomog_chartForm c bg)`. Conclude with `LowerBoundFree.isMultiHomog_mul hue (isMultiHomog_chartForm c bf)`. Rewrite using `[map_mul, hMy]`.

Conclude with `mul_ne_zero huey (hMy0 _)`. Rewrite using `[map_mul, map_mul, hMy, hMy, ← hchart]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-(chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k)) * hcoef`. Simplify using `only [map_mul]`.

Rewrite using `[hMz, ← aeval_eq_eval_map]`. Conclude with `mul_ne_zero huez (hMz0 _)`.
-/
theorem exists_value {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {p : ℕ} (hp : p ≠ 0) {b : K → ℤ} {f g : MRing ι}
    (hV : IsVerticalDivisorAt (mCoordIdeal y) p b f g) (c : (k : K) → ι k)
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) :
    ∃ v, v ≠ 0 ∧ IsValueAt y (aeval y f / aeval y g * chartMono y c (-b)) z v := by
  classical
  have hPW : mCoordIdeal y ≤ mCoordIdeal z := mCoordIdeal_le hz
  have hWp : (mCoordIdeal z).IsPrime := RingHom.ker_isPrime _
  have hrel : IsRelevant (mCoordIdeal z) := fun k =>
    ⟨c k, fun h => hc k ((X_mem_mCoordIdeal_iff z _).1 h)⟩
  have hpW : (C (p : ℤ) : MRing ι) ∉ mCoordIdeal z := by
    intro h
    have h' : mConeMap z (C (p : ℤ)) = 0 := RingHom.mem_ker.mp h
    simp [mConeMap, hp] at h'
  obtain ⟨u, v, hu, hv, huv⟩ := hV.unit_off_fibre _ hWp hPW hrel hpW
  obtain ⟨bf, bg, hf, hg, hb⟩ := hV.degrees
  have hfy : aeval y f ≠ 0 := fun h => hV.num_not_mem ((mem_mCoordIdeal_iff_of_homog y hf).2 h)
  have hgy : aeval y g ≠ 0 := fun h => hV.den_not_mem ((mem_mCoordIdeal_iff_of_homog y hg).2 h)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h =>
    hc k ((X_mem_mCoordIdeal_iff z _).1 (hPW ((X_mem_mCoordIdeal_iff y _).2 h)))

  have hu' : mConeMap z u ≠ 0 := fun h => hu (RingHom.mem_ker.mpr h)
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hu'
  set e : K → ℕ := ⇑m with he
  set ue := weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e u with hue_def
  have hue : IsMultiHomog ue e := HilbertSamuel.GenFibreHomog.isMultiHomog_of_weighted
    (weightedHomogeneousComponent_isWeightedHomogeneous e u)
  have huez : aeval z ue ≠ 0 := by
    rw [← Finsupp.equivFunOnFinite_symm_coe m, HilbertSamuel.GenFibreHomog.coeff_mConeMap] at hm
    exact hm
  have hueW : ue ∉ mCoordIdeal z := fun h => huez ((mem_mCoordIdeal_iff_of_homog z hue).1 h)
  have huey : aeval y ue ≠ 0 := fun h => hueW (hPW ((mem_mCoordIdeal_iff_of_homog y hue).2 h))

  have hrel' : mConeMap y u * (C (aeval y f) * ∏ k, (X k : MvPolynomial K Ω) ^ bf k) =
      mConeMap y v * (C (aeval y g) * ∏ k, (X k : MvPolynomial K Ω) ^ bg k) := by
    have h : mConeMap y (u * f - v * g) = 0 := RingHom.mem_ker.mp huv
    rw [map_sub, map_mul, map_mul, sub_eq_zero, mConeMap_of_isMultiHomog y hf,
      mConeMap_of_isMultiHomog y hg] at h
    exact h

  have hcoef := congrArg (coeff (m + Finsupp.equivFunOnFinite.symm bf)) hrel'
  rw [prod_X_pow_eq_monomial, prod_X_pow_eq_monomial, C_mul_monomial, C_mul_monomial,
    coeff_mul_monomial', coeff_mul_monomial', if_pos le_add_self, add_tsub_cancel_right, mul_one,
    mul_one] at hcoef
  have hcu : coeff m (mConeMap y u) = aeval y ue := by
    rw [← Finsupp.equivFunOnFinite_symm_coe m, HilbertSamuel.GenFibreHomog.coeff_mConeMap]
  rw [hcu] at hcoef
  by_cases hle : Finsupp.equivFunOnFinite.symm bg ≤ m + Finsupp.equivFunOnFinite.symm bf
  swap
  · rw [if_neg hle] at hcoef
    exact absurd hcoef (mul_ne_zero huey hfy)
  rw [if_pos hle] at hcoef
  set d' : K → ℕ := ⇑(m + Finsupp.equivFunOnFinite.symm bf - Finsupp.equivFunOnFinite.symm bg) with hd'
  set a := weightedHomogeneousComponent (NumbersDVR.blockWeight ι) d' v with ha_def
  have ha : IsMultiHomog a d' := HilbertSamuel.GenFibreHomog.isMultiHomog_of_weighted
    (weightedHomogeneousComponent_isWeightedHomogeneous d' v)
  have hcv : coeff (m + Finsupp.equivFunOnFinite.symm bf - Finsupp.equivFunOnFinite.symm bg)
      (mConeMap y v) = aeval y a := by
    rw [← Finsupp.equivFunOnFinite_symm_coe
      (m + Finsupp.equivFunOnFinite.symm bf - Finsupp.equivFunOnFinite.symm bg),
      HilbertSamuel.GenFibreHomog.coeff_mConeMap]
  rw [hcv] at hcoef

  have hdeg : d' + bg = e + bf := by
    have := congrArg (⇑) (tsub_add_cancel_of_le hle)
    simpa [hd', he, Finsupp.coe_add] using this

  have hkey : a * u - ue * v ∈ mCoordIdeal y := by
    show _ ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker, map_sub, map_mul, map_mul, sub_eq_zero, mConeMap_of_isMultiHomog y ha,
      mConeMap_of_isMultiHomog y hue]
    have hG : (C (aeval y g) * ∏ k, (X k : MvPolynomial K Ω) ^ bg k) ≠ 0 :=
      mul_ne_zero (C_ne_zero.2 hgy) (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k))
    refine mul_right_cancel₀ hG ?_
    calc C (aeval y a) * (∏ k, (X k : MvPolynomial K Ω) ^ d' k) * mConeMap y u *
          (C (aeval y g) * ∏ k, (X k : MvPolynomial K Ω) ^ bg k)
        = C (aeval y a * aeval y g) * (∏ k, (X k : MvPolynomial K Ω) ^ (d' + bg) k) *
            mConeMap y u := by rw [prod_X_pow_add, map_mul]; ring
      _ = C (aeval y ue * aeval y f) * (∏ k, (X k : MvPolynomial K Ω) ^ (e + bf) k) *
            mConeMap y u := by rw [hcoef, hdeg]
      _ = C (aeval y ue) * (∏ k, (X k : MvPolynomial K Ω) ^ e k) *
            (mConeMap y u * (C (aeval y f) * ∏ k, (X k : MvPolynomial K Ω) ^ bf k)) := by
          rw [prod_X_pow_add, map_mul]; ring
      _ = _ := by rw [hrel']; ring
  have haW : a ∉ mCoordIdeal z := by
    intro h
    have h2 : ue * v ∈ mCoordIdeal z := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right u _ h) (hPW hkey)
      simpa using this
    rcases hWp.mem_or_mem h2 with h3 | h3
    · exact hueW h3
    · exact hv h3
  have haz : aeval z a ≠ 0 := fun h => haW ((mem_mCoordIdeal_iff_of_homog z ha).2 h)

  have hMz : ∀ d : K → ℕ, eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k)) =
      ∏ k, z ⟨k, c k⟩ ^ d k := fun d => by simp [map_prod]
  have hMy : ∀ d : K → ℕ, aeval y (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) = ∏ k, y ⟨k, c k⟩ ^ d k :=
    fun d => by simp [map_prod]
  have hMz0 : ∀ d : K → ℕ, (∏ k, z ⟨k, c k⟩ ^ d k) ≠ 0 := fun d =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have hMy0 : ∀ d : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 := fun d =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)
  have hchart : chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k = ∏ k, y ⟨k, c k⟩ ^ bg k := by
    rw [chartMono, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hb, Pi.neg_apply, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k)]
    congr 1
    ring
  refine ⟨eval z (map (Int.castRingHom ℂ) (a * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bg k)) /
    eval z (map (Int.castRingHom ℂ) (ue * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bf k)), ?_,
    e + bf, a * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bg k, ue * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bf k,
    ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [map_mul]
    rw [hMz, hMz, ← aeval_eq_eval_map, ← aeval_eq_eval_map]
    exact div_ne_zero (mul_ne_zero haz (hMz0 _)) (mul_ne_zero huez (hMz0 _))
  · rw [← hdeg]
    exact LowerBoundFree.isMultiHomog_mul ha (isMultiHomog_chartForm c bg)
  · exact LowerBoundFree.isMultiHomog_mul hue (isMultiHomog_chartForm c bf)
  · rw [map_mul, hMy]
    exact mul_ne_zero huey (hMy0 _)
  · rw [map_mul, map_mul, hMy, hMy, ← hchart]
    field_simp
    linear_combination (-(chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k)) * hcoef
  · simp only [map_mul]
    rw [hMz, ← aeval_eq_eval_map]
    exact mul_ne_zero huez (hMz0 _)

end VertFactorPos

open VertFactorPos in

/- English proof (translation)
Introduce `II Ψ _ K _ ι _ Ω _ _ E _ _ D p hp z hz`. Establish `hex : ∃ c : (k : K) → ι k, ∀ k, z ⟨k, c k⟩ ≠ 0` using `⟨fun k => (hz.1 k).choose, fun k => (hz.1 k).choose_spec⟩`. Rewrite using `[ComponentData.vertFactor, dif_pos hex]`. Take `⟨v, hv0, hv⟩` from `exists_value hz (D.S_prime p hp).ne_zero (D.vertical p hp) hex.choose hex.choose_spec`. Rewrite using `[valAt_eq hz hv]`.

Conclude with `mul_pos (norm_pos_iff.2 hv0) (norm_pos_iff.2 (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hex.choose_spec k)))`.
-/
theorem VertFactorPos.proof : VertFactorPos.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D p hp z hz
  have hex : ∃ c : (k : K) → ι k, ∀ k, z ⟨k, c k⟩ ≠ 0 :=
    ⟨fun k => (hz.1 k).choose, fun k => (hz.1 k).choose_spec⟩
  rw [ComponentData.vertFactor, dif_pos hex]
  obtain ⟨v, hv0, hv⟩ := exists_value hz (D.S_prime p hp).ne_zero (D.vertical p hp) hex.choose
    hex.choose_spec
  rw [valAt_eq hz hv]
  exact mul_pos (norm_pos_iff.2 hv0) (norm_pos_iff.2
    (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hex.choose_spec k)))

end GroundTheory.Heights₂.Heights.LowerBoundFree
