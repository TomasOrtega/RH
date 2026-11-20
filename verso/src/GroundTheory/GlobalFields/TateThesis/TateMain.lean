import Mathlib
import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
import GroundTheory.GlobalFields.TateThesis.ArchCharsUnitary

open NumberField IsDedekindDomain Topology Filter MeasureTheory Complex
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

def posRealChar (w : InfinitePlace K) (χ : HeckeCharacter K) : {x : ℝ // 0 < x} →ₜ* Circle where
  toMonoidHom := χ.toIdele.comp (moduleSection w)
  continuous_toFun := χ.continuous_toIdele.comp (continuous_moduleSection w)

def archExponent (w : InfinitePlace K) (χ : HeckeCharacter K) : ℝ :=
  (existsUnique_cpow_of_pos_circle (posRealChar w χ)).exists.choose

/- English proof (translation)
The claim follows from `(existsUnique_cpow_of_pos_circle (posRealChar w χ)).exists.choose_spec t`.
-/
theorem archExponent_spec (w : InfinitePlace K) (χ : HeckeCharacter K) (t : {x : ℝ // 0 < x}) :
    (χ.toIdele (moduleSection w t) : ℂ) = ((t : ℝ) : ℂ) ^ ((archExponent w χ : ℂ) * I) :=
  (existsUnique_cpow_of_pos_circle (posRealChar w χ)).exists.choose_spec t

/- English proof (translation)
The claim follows from `(existsUnique_cpow_of_pos_circle (posRealChar w χ)).unique (existsUnique_cpow_of_pos_circle (posRealChar w χ)).exists.choose_spec h`.
-/
theorem archExponent_unique (w : InfinitePlace K) (χ : HeckeCharacter K) {τ : ℝ}
    (h : ∀ t : {x : ℝ // 0 < x}, (χ.toIdele (moduleSection w t) : ℂ) = ((t : ℝ) : ℂ) ^ ((τ : ℂ) * I)) :
    archExponent w χ = τ :=
  (existsUnique_cpow_of_pos_circle (posRealChar w χ)).unique
    (existsUnique_cpow_of_pos_circle (posRealChar w χ)).exists.choose_spec h

/- English proof (translation)
Use `archExponent_unique w χ⁻¹ fun t ↦ ?_` and prove the remaining obligations. Rewrite using `[toIdele_inv, Circle.coe_inv, archExponent_spec, ← cpow_neg]`. Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem archExponent_inv (w : InfinitePlace K) (χ : HeckeCharacter K) :
    archExponent w χ⁻¹ = -archExponent w χ := by
  refine archExponent_unique w χ⁻¹ fun t ↦ ?_
  rw [toIdele_inv, Circle.coe_inv, archExponent_spec, ← cpow_neg]
  push_cast
  ring_nf

/- English proof (translation)
Use `archExponent_unique w χ fun t ↦ ?_` and prove the remaining obligations. Rewrite using `[hτ, ideleModule_moduleSection]`.
-/
theorem archExponent_eq_of_forall {χ : HeckeCharacter K} {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
    (w : InfinitePlace K) : archExponent w χ = τ := by
  refine archExponent_unique w χ fun t ↦ ?_
  rw [hτ, ideleModule_moduleSection]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Set `w : InfinitePlace K` to `Classical.arbitrary _`. Use `⟨archExponent w χ, fun x ↦ ?_⟩` and prove the remaining obligations. Establish `hv : (moduleSection w (ideleModule K x))⁻¹ * x ∈ normOneSubgroup K`.

Rewrite using `[normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, ideleModule_moduleSection, inv_mul_cancel]`. Establish `hx : x = moduleSection w (ideleModule K x) * ((moduleSection w (ideleModule K x))⁻¹ * x)` using `(mul_inv_cancel_left _ _).symm`. Use `conv_lhs => rw [hx]`. Rewrite using `[map_mul, Circle.coe_mul, archExponent_spec, show χ.toIdele ((moduleSection w (ideleModule K x))⁻¹ * x) = 1 from h ⟨_, hv⟩, Circle.coe_one, mul_one]`. Introduce and unpack `⟨τ, hτ⟩ v`.

Use `Circle.ext ?_` and prove the remaining obligations. Establish `hv : (ideleModule K (v : IdeleGroup K) : ℝ) = 1` using `mem_normOneSubgroup.1 v.2`. Rewrite using `[hτ, hv, ofReal_one, one_cpow, Circle.coe_one]`.
-/
theorem forall_normOne_eq_one_iff (χ : HeckeCharacter K) :
    (∀ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) = 1) ↔
      ∃ τ : ℝ, ∀ x : IdeleGroup K,
        (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I) := by
  constructor
  · intro h
    let w : InfinitePlace K := Classical.arbitrary _
    refine ⟨archExponent w χ, fun x ↦ ?_⟩
    have hv : (moduleSection w (ideleModule K x))⁻¹ * x ∈ normOneSubgroup K := by
      rw [normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, ideleModule_moduleSection,
        inv_mul_cancel]
    have hx : x = moduleSection w (ideleModule K x) * ((moduleSection w (ideleModule K x))⁻¹ * x) :=
      (mul_inv_cancel_left _ _).symm
    conv_lhs => rw [hx]
    rw [map_mul, Circle.coe_mul, archExponent_spec,
      show χ.toIdele ((moduleSection w (ideleModule K x))⁻¹ * x) = 1 from h ⟨_, hv⟩, Circle.coe_one,
      mul_one]
  · rintro ⟨τ, hτ⟩ v
    refine Circle.ext ?_
    have hv : (ideleModule K (v : IdeleGroup K) : ℝ) = 1 := mem_normOneSubgroup.1 v.2
    rw [hτ, hv, ofReal_one, one_cpow, Circle.coe_one]

def thetaFun (w : InfinitePlace K) (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K) (x : ℝ) : ℂ :=
  if hx : 0 < x then thetaIntegral w F χ ⟨x, hx⟩ else 0

/- English proof (translation)
The claim follows from `dif_pos hx`.
-/
theorem thetaFun_of_pos (w : InfinitePlace K) (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K) {x : ℝ}
    (hx : 0 < x) : thetaFun w F χ x = thetaIntegral w F χ ⟨x, hx⟩ :=
  dif_pos hx

/- English proof (translation)
Rewrite using `[continuousOn_iff_continuous_domRestrict]`. Establish `h : (Set.Ioi (0 : ℝ)).domRestrict (thetaFun w F χ) = thetaIntegral w F χ ∘ fun x : Set.Ioi (0 : ℝ) ↦ (⟨x.1, x.2⟩ : {r : ℝ // 0 < r})`. Use function extensionality and compare the values at `x`. Conclude with `thetaFun_of_pos w F χ x.2`. Rewrite using `[h]`.

Conclude with `(continuous_thetaIntegral w hF χ).comp (continuous_subtype_val.subtype_mk _)`.
-/
theorem continuousOn_thetaFun (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) : ContinuousOn (thetaFun w F χ) (Set.Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : (Set.Ioi (0 : ℝ)).domRestrict (thetaFun w F χ) =
      thetaIntegral w F χ ∘ fun x : Set.Ioi (0 : ℝ) ↦ (⟨x.1, x.2⟩ : {r : ℝ // 0 < r}) := by
    funext x
    exact thetaFun_of_pos w F χ x.2
  rw [h]
  exact (continuous_thetaIntegral w hF χ).comp (continuous_subtype_val.subtype_mk _)

/- English proof (translation)
Establish `hx' : 0 < x` using `hx`. Establish `hx1 : 0 < 1 / x` using `one_div_pos.2 hx'`. Rewrite using `[thetaFun_of_pos w F χ hx1, thetaFun_of_pos w _ χ⁻¹ hx', Real.rpow_one, one_mul, smul_eq_mul]`. Establish `h : (⟨1 / x, hx1⟩ : {r : ℝ // 0 < r}) = (⟨x, hx'⟩ : {r : ℝ // 0 < r})⁻¹` using `Subtype.ext (by rw [Positive.coe_inv]; exact one_div x)`. Rewrite using `[h, thetaIntegral_inv w hF χ]`.
-/
theorem thetaFun_one_div (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) (x : ℝ) (hx : x ∈ Set.Ioi 0) :
    thetaFun w F χ (1 / x) = ((1 : ℂ) * ↑(x ^ (1 : ℝ))) • thetaFun w (adelicFourier K F) χ⁻¹ x := by
  have hx' : 0 < x := hx
  have hx1 : 0 < 1 / x := one_div_pos.2 hx'
  rw [thetaFun_of_pos w F χ hx1, thetaFun_of_pos w _ χ⁻¹ hx', Real.rpow_one, one_mul, smul_eq_mul]
  have h : (⟨1 / x, hx1⟩ : {r : ℝ // 0 < r}) = (⟨x, hx'⟩ : {r : ℝ // 0 < r})⁻¹ :=
    Subtype.ext (by rw [Positive.coe_inv]; exact one_div x)
  rw [h, thetaIntegral_inv w hF χ]

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_nat_ge (-r)`. Take `⟨M, hM⟩` from `exists_norm_thetaIntegral_sub_le w hF χ N`. Use `Asymptotics.IsBigO.of_bound M ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx`. Establish `hx0 : 0 < x` using `zero_lt_one.trans_le hx`.

Establish `h` using `hM ⟨x, hx0⟩ hx`. Rewrite `h` using `[← thetaFun_of_pos w F χ hx0]`. Establish `hpow : (x ^ N)⁻¹ ≤ x ^ r`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_neg hx0.le]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hx (by linarith)`.

Establish `hM0 : 0 ≤ M`. Establish `h1 : 0 ≤ (x ^ N)⁻¹ * M` using `(norm_nonneg _).trans h`. Conclude with `(mul_nonneg_iff_of_pos_left (inv_pos.2 (pow_pos hx0 N))).1 h1`. Rewrite using `[Real.norm_of_nonneg (Real.rpow_nonneg hx0.le r), mul_comm M]`. Conclude with `h.trans (mul_le_mul_of_nonneg_right hpow hM0)`.
-/
theorem isBigO_thetaFun_sub (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) (r : ℝ) :
    (fun x ↦ thetaFun w F χ x - thetaConstant F χ) =O[atTop] (· ^ r) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (-r)
  obtain ⟨M, hM⟩ := exists_norm_thetaIntegral_sub_le w hF χ N
  refine Asymptotics.IsBigO.of_bound M ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have h := hM ⟨x, hx0⟩ hx
  rw [← thetaFun_of_pos w F χ hx0] at h
  have hpow : (x ^ N)⁻¹ ≤ x ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hM0 : 0 ≤ M := by
    have h1 : 0 ≤ (x ^ N)⁻¹ * M := (norm_nonneg _).trans h
    exact (mul_nonneg_iff_of_pos_left (inv_pos.2 (pow_pos hx0 N))).1 h1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le r), mul_comm M]
  exact h.trans (mul_le_mul_of_nonneg_right hpow hM0)

def thetaPair (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) : WeakFEPair ℂ where
  f := thetaFun w F χ
  g := thetaFun w (adelicFourier K F) χ⁻¹
  k := 1
  ε := 1
  f₀ := thetaConstant F χ
  g₀ := thetaConstant (adelicFourier K F) χ⁻¹
  hf_int := (continuousOn_thetaFun w hF χ).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_thetaFun w (adelicFourier_mem_schwartzBruhat hF) χ⁻¹).locallyIntegrableOn
    measurableSet_Ioi
  hk := one_pos
  hε := one_ne_zero
  h_feq := thetaFun_one_div w hF χ
  hf_top := isBigO_thetaFun_sub w hF χ
  hg_top := isBigO_thetaFun_sub w (adelicFourier_mem_schwartzBruhat hF) χ⁻¹

/- English proof (translation)
Consider the cases of `P`. Consider the cases of `Q`. Simplify using `only at hf hg hk hε hf₀ hg₀`. Substitute `hf hg hk hε hf₀ hg₀` using the available equality. Both sides reduce to the same expression.
-/
theorem weakFEPair_Λ_congr {P Q : WeakFEPair ℂ} (hf : P.f = Q.f) (hg : P.g = Q.g) (hk : P.k = Q.k)
    (hε : P.ε = Q.ε) (hf₀ : P.f₀ = Q.f₀) (hg₀ : P.g₀ = Q.g₀) : P.Λ = Q.Λ := by
  cases P
  cases Q
  simp only at hf hg hk hε hf₀ hg₀
  subst hf hg hk hε hf₀ hg₀
  rfl

omit [NumberField K] in

/- English proof (translation)
Rewrite using `[hG.tsum_eq_add_tsum_ite 0, add_sub_cancel_left]`. Use `(tsum_congr fun ξ : Kˣ ↦ (if_neg ξ.ne_zero).symm).trans (Function.Injective.tsum_eq Units.val_injective (f := fun ξ ↦ if ξ = 0 then 0 else G ξ) fun ξ hξ ↦ ?_)` and prove the remaining obligations. Establish `h0 : ξ ≠ 0` using `fun h ↦ hξ (by simp [h])`. Conclude with `⟨Units.mk0 ξ h0, rfl⟩`.
-/
theorem tsum_units_eq_tsum_sub {G : K → ℂ} (hG : Summable G) :
    ∑' ξ : Kˣ, G ξ = ∑' ξ : K, G ξ - G 0 := by
  classical
  rw [hG.tsum_eq_add_tsum_ite 0, add_sub_cancel_left]
  refine (tsum_congr fun ξ : Kˣ ↦ (if_neg ξ.ne_zero).symm).trans
    (Function.Injective.tsum_eq Units.val_injective (f := fun ξ ↦ if ξ = 0 then 0 else G ξ)
      fun ξ hξ ↦ ?_)
  have h0 : ξ ≠ 0 := fun h ↦ hξ (by simp [h])
  exact ⟨Units.mk0 ξ h0, rfl⟩

/- English proof (translation)
Rewrite using `[partialZeta_eq_setIntegral w (continuous_of_mem_schwartzBruhat hF), thetaIntegral_sub_thetaConstant w hF χ, ← integral_const_mul]`. Use `integral_congr_ae (Eventually.of_forall fun u ↦ ?_)` and prove the remaining obligations. Use `set y := moduleSection w t * (u : IdeleGroup K)`. Establish `hy : ∀ ξ : Kˣ, ((diagonal K ξ * moduleSection w t * (u : IdeleGroup K) : IdeleGroup K) : 𝔸[K]) = y • algebraMap K 𝔸[K] (ξ : K)` using `fun ξ ↦ by`. Rewrite using `[mul_assoc, Units.val_mul, coe_diagonal, Units.smul_def, smul_eq_mul, mul_comm]`.

Establish `hs : Summable fun ξ : K ↦ F (y • algebraMap K 𝔸[K] ξ)` using `(summable_norm_smul_algebraMap y hF).of_norm`. Use `show (∑' ξ : Kˣ, F ((diagonal K ξ * moduleSection w t * (u : IdeleGroup K) : IdeleGroup K) : 𝔸[K]) * (χ.toIdele y : ℂ)) = _`. Repeatedly rewrite using `[hy]`. Rewrite using `[tsum_mul_right, tsum_units_eq_tsum_sub hs, smul_algebraMap_zero, map_mul, Circle.coe_mul]`. Simplify using `only [adelicTheta]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem partialZeta_eq (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    partialZeta w F χ t =
      (χ.toIdele (moduleSection w t) : ℂ) * (thetaIntegral w F χ t - thetaConstant F χ) := by
  rw [partialZeta_eq_setIntegral w (continuous_of_mem_schwartzBruhat hF),
    thetaIntegral_sub_thetaConstant w hF χ, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
  set y := moduleSection w t * (u : IdeleGroup K)
  have hy : ∀ ξ : Kˣ, ((diagonal K ξ * moduleSection w t * (u : IdeleGroup K) : IdeleGroup K) :
      𝔸[K]) = y • algebraMap K 𝔸[K] (ξ : K) := fun ξ ↦ by
    rw [mul_assoc, Units.val_mul, coe_diagonal, Units.smul_def, smul_eq_mul, mul_comm]
  have hs : Summable fun ξ : K ↦ F (y • algebraMap K 𝔸[K] ξ) :=
    (summable_norm_smul_algebraMap y hF).of_norm
  show (∑' ξ : Kˣ, F ((diagonal K ξ * moduleSection w t * (u : IdeleGroup K) : IdeleGroup K) :
      𝔸[K]) * (χ.toIdele y : ℂ)) = _
  simp_rw [hy]
  rw [tsum_mul_right, tsum_units_eq_tsum_sub hs, smul_algebraMap_zero, map_mul, Circle.coe_mul]
  simp only [adelicTheta]
  ring

/- English proof (translation)
Use `set z := s + (archExponent w χ : ℂ) * I`. Use `set g : ℝ → ℂ := fun x ↦ (thetaFun w F χ x - thetaConstant F χ) * (x : ℂ) ^ z with hg`. Rewrite using `[(globalZeta_eq_integral_partialZeta w hF χ hs).2]`. Establish `h : (fun t : {r : ℝ // 0 < r} ↦ partialZeta w F χ t * ((t : ℝ) : ℂ) ^ s) = fun t : {r : ℝ // 0 < r} ↦ g (t : ℝ)`. Use function extensionality and compare the values at `t`.

Establish `ht : ((t : ℝ) : ℂ) ≠ 0` using `ofReal_ne_zero.2 t.2.ne'`. Rewrite using `[hg]`. Use `beta_reduce`. Rewrite using `[partialZeta_eq w hF χ, archExponent_spec, thetaFun_of_pos w F χ t.2]`. Simplify using `only [z]`.

Rewrite using `[cpow_add _ _ ht]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, integral_posRealMeasure g, mellin]`. Use `setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_` and prove the remaining obligations. Establish `hx0 : (x : ℂ) ≠ 0` using `ofReal_ne_zero.2 (ne_of_gt hx)`.

Simplify using `only [hg, real_smul, smul_eq_mul]`. Rewrite using `[cpow_sub _ _ hx0, cpow_one, ofReal_inv, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem globalZeta_eq_mellin (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    globalZeta F χ s = mellin (fun x ↦ thetaFun w F χ x - thetaConstant F χ)
      (s + (archExponent w χ : ℂ) * I) := by
  set z := s + (archExponent w χ : ℂ) * I
  set g : ℝ → ℂ := fun x ↦ (thetaFun w F χ x - thetaConstant F χ) * (x : ℂ) ^ z with hg
  rw [(globalZeta_eq_integral_partialZeta w hF χ hs).2]
  have h : (fun t : {r : ℝ // 0 < r} ↦ partialZeta w F χ t * ((t : ℝ) : ℂ) ^ s) =
      fun t : {r : ℝ // 0 < r} ↦ g (t : ℝ) := by
    funext t
    have ht : ((t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 t.2.ne'
    rw [hg]
    beta_reduce
    rw [partialZeta_eq w hF χ, archExponent_spec, thetaFun_of_pos w F χ t.2]
    simp only [z]
    rw [cpow_add _ _ ht]
    ring
  rw [h, integral_posRealMeasure g, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt hx)
  simp only [hg, real_smul, smul_eq_mul]
  rw [cpow_sub _ _ hx0, cpow_one, ofReal_inv, div_eq_mul_inv]
  ring

/- English proof (translation)
Establish `hre : (thetaPair w hF χ).k < (s + (archExponent w χ : ℂ) * I).re`. Simplify `hs` using `[thetaPair]`. Rewrite using `[globalZeta_eq_mellin w hF χ hs]`. Conclude with `((thetaPair w hF χ).hasMellin hre).2`.
-/
theorem globalZeta_eq_Λ (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    globalZeta F χ s = (thetaPair w hF χ).Λ (s + (archExponent w χ : ℂ) * I) := by
  have hre : (thetaPair w hF χ).k < (s + (archExponent w χ : ℂ) * I).re := by
    simpa [thetaPair] using hs
  rw [globalZeta_eq_mellin w hF χ hs]
  exact ((thetaPair w hF χ).hasMellin hre).2

open Classical in

def tateZetaAt (w : InfinitePlace K) (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K) (s : ℂ) : ℂ :=
  if hF : F ∈ schwartzBruhat K then (thetaPair w hF χ).Λ (s + (archExponent w χ : ℂ) * I) else 0

open Classical in
/- English proof (translation)
Use function extensionality and compare the values at `s`. Conclude with `dif_pos hF`.
-/
theorem tateZetaAt_eq (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) :
    tateZetaAt w F χ = fun s ↦ (thetaPair w hF χ).Λ (s + (archExponent w χ : ℂ) * I) := by
  funext s
  exact dif_pos hF

/- English proof (translation)
Rewrite using `[tateZetaAt_eq w hF, globalZeta_eq_Λ w hF χ hs]`.
-/
theorem tateZetaAt_eq_globalZeta (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) : tateZetaAt w F χ s = globalZeta F χ s := by
  rw [tateZetaAt_eq w hF, globalZeta_eq_Λ w hF χ hs]

/- English proof (translation)
Establish `hF'` using `adelicFourier_mem_schwartzBruhat hF`. Rewrite using `[tateZetaAt_eq w hF, tateZetaAt_eq w hF', archExponent_inv]`. Use `set P := thetaPair w hF χ`. Establish `hg : (thetaPair w hF' χ⁻¹).g = P.symm.g` using `by show thetaFun w (adelicFourier K (adelicFourier K F)) χ⁻¹⁻¹ = thetaFun w F χ`. Rewrite using `[adelicFourier_adelicFourier hF, inv_inv]`.

Use function extensionality and compare the values at `x`. Simplify using `only [thetaFun, thetaIntegral_neg]`. Establish `hg₀ : (thetaPair w hF' χ⁻¹).g₀ = P.symm.g₀` using `by show thetaConstant (adelicFourier K (adelicFourier K F)) χ⁻¹⁻¹ = thetaConstant F χ`. Rewrite using `[adelicFourier_adelicFourier hF, inv_inv]`. Simplify using `only [thetaConstant, neg_zero]`.

Establish `hε : (thetaPair w hF' χ⁻¹).ε = P.symm.ε` using `by show (1 : ℂ) = (1 : ℂ)⁻¹`. Rewrite using `[inv_one]`. Establish `hQ : (thetaPair w hF' χ⁻¹).Λ = P.symm.Λ` using `weakFEPair_Λ_congr rfl hg rfl hε rfl hg₀`. Establish `h` using `P.functional_equation (s - (archExponent w χ : ℂ) * I)`. Establish `hk : ((P.k : ℝ) : ℂ) = 1` using `by simp [P, thetaPair]`.

Rewrite `h` using `[hk, show P.ε = 1 from rfl, one_smul]`. Simplify using `only`. Rewrite using `[hQ, show (1 - s + (archExponent w χ : ℂ) * I) = 1 - (s - (archExponent w χ : ℂ) * I) by ring, h]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem tateZetaAt_one_sub (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) (s : ℂ) :
    tateZetaAt w F χ (1 - s) = tateZetaAt w (adelicFourier K F) χ⁻¹ s := by
  have hF' := adelicFourier_mem_schwartzBruhat hF
  rw [tateZetaAt_eq w hF, tateZetaAt_eq w hF', archExponent_inv]
  set P := thetaPair w hF χ
  have hg : (thetaPair w hF' χ⁻¹).g = P.symm.g := by
    show thetaFun w (adelicFourier K (adelicFourier K F)) χ⁻¹⁻¹ = thetaFun w F χ
    rw [adelicFourier_adelicFourier hF, inv_inv]
    funext x
    simp only [thetaFun, thetaIntegral_neg]
  have hg₀ : (thetaPair w hF' χ⁻¹).g₀ = P.symm.g₀ := by
    show thetaConstant (adelicFourier K (adelicFourier K F)) χ⁻¹⁻¹ = thetaConstant F χ
    rw [adelicFourier_adelicFourier hF, inv_inv]
    simp only [thetaConstant, neg_zero]
  have hε : (thetaPair w hF' χ⁻¹).ε = P.symm.ε := by
    show (1 : ℂ) = (1 : ℂ)⁻¹
    rw [inv_one]
  have hQ : (thetaPair w hF' χ⁻¹).Λ = P.symm.Λ :=
    weakFEPair_Λ_congr rfl hg rfl hε rfl hg₀
  have h := P.functional_equation (s - (archExponent w χ : ℂ) * I)
  have hk : ((P.k : ℝ) : ℂ) = 1 := by simp [P, thetaPair]
  rw [hk, show P.ε = 1 from rfl, one_smul] at h
  simp only
  rw [hQ, show (1 - s + (archExponent w χ : ℂ) * I) = 1 - (s - (archExponent w χ : ℂ) * I) by ring, h]
  congr 1
  push_cast
  ring

/- English proof (translation)
Rewrite using `[thetaConstant, setIntegral_char_eq_zero hχ, mul_zero]`.
-/
theorem thetaConstant_eq_zero {χ : HeckeCharacter K}
    (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1) (F : 𝔸[K] → ℂ) :
    thetaConstant F χ = 0 := by
  rw [thetaConstant, setIntegral_char_eq_zero hχ, mul_zero]

/- English proof (translation)
Rewrite using `[thetaConstant, setIntegral_char_eq_volume hχ, mul_comm]`.
-/
theorem thetaConstant_eq_volume {χ : HeckeCharacter K}
    (hχ : ∀ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) = 1) (F : 𝔸[K] → ℂ) :
    thetaConstant F χ = ((normOneClassMeasure K Set.univ).toReal : ℂ) * F 0 := by
  rw [thetaConstant, setIntegral_char_eq_volume hχ, mul_comm]

/- English proof (translation)
Establish `hχ' : ∃ v : normOneSubgroup K, χ⁻¹.toIdele (v : IdeleGroup K) ≠ 1`. Take `⟨v, hv⟩` from `hχ`. Conclude with `⟨v, by rw [toIdele_inv, ne_eq, inv_eq_one]; exact hv⟩`. Rewrite using `[tateZetaAt_eq w hF]`. Introduce `s`.

Conclude with `((thetaPair w hF χ).differentiableAt_Λ (Or.inr (thetaConstant_eq_zero hχ F)) (Or.inr (thetaConstant_eq_zero hχ' _))).comp s (differentiableAt_id.add_const _)`.
-/
theorem differentiable_tateZetaAt (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) {χ : HeckeCharacter K}
    (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1) :
    Differentiable ℂ (tateZetaAt w F χ) := by
  have hχ' : ∃ v : normOneSubgroup K, χ⁻¹.toIdele (v : IdeleGroup K) ≠ 1 := by
    obtain ⟨v, hv⟩ := hχ
    exact ⟨v, by rw [toIdele_inv, ne_eq, inv_eq_one]; exact hv⟩
  rw [tateZetaAt_eq w hF]
  intro s
  exact ((thetaPair w hF χ).differentiableAt_Λ (Or.inr (thetaConstant_eq_zero hχ F))
    (Or.inr (thetaConstant_eq_zero hχ' _))).comp s (differentiableAt_id.add_const _)

/- English proof (translation)
Use `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ((continuous_id.add continuous_const).tendsto a |>.mono_left nhdsWithin_le_nhds) ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs`. Conclude with `fun h ↦ hs (add_right_cancel h)`.
-/
theorem tendsto_add_const_nhdsNE (a c : ℂ) :
    Tendsto (fun s : ℂ ↦ s + c) (𝓝[≠] a) (𝓝[≠] (a + c)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuous_id.add continuous_const).tendsto a |>.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact fun h ↦ hs (add_right_cancel h)

section Trivial

variable {χ : HeckeCharacter K} {τ : ℝ}
  (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
include hτ

/- English proof (translation)
The claim follows from `(forall_normOne_eq_one_iff χ).2 ⟨τ, hτ⟩`.
-/
theorem forall_normOne_eq_one_of_forall :
    ∀ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) = 1 :=
  (forall_normOne_eq_one_iff χ).2 ⟨τ, hτ⟩

/- English proof (translation)
Rewrite using `[tateZetaAt_eq w hF, archExponent_eq_of_forall hτ w]`. Use `((thetaPair w hF χ).differentiableAt_Λ (Or.inl ?_) (Or.inl ?_)).comp s (differentiableAt_id.add_const _)` and prove the remaining obligations. Introduce `h`. Conclude with `hs₀ (eq_neg_of_add_eq_zero_left h)`. Introduce `h`.

Establish `hk : ((thetaPair w hF χ).k : ℂ) = 1` using `by simp [thetaPair]`. Rewrite `h` using `[hk]`. Conclude with `hs₁ (by rw [← h]; ring)`.
-/
theorem differentiableAt_tateZetaAt (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) {s : ℂ} (hs₀ : s ≠ -((τ : ℂ) * I)) (hs₁ : s ≠ 1 - (τ : ℂ) * I) :
    DifferentiableAt ℂ (tateZetaAt w F χ) s := by
  rw [tateZetaAt_eq w hF, archExponent_eq_of_forall hτ w]
  refine ((thetaPair w hF χ).differentiableAt_Λ (Or.inl ?_) (Or.inl ?_)).comp s
    (differentiableAt_id.add_const _)
  · intro h
    exact hs₀ (eq_neg_of_add_eq_zero_left h)
  · intro h
    have hk : ((thetaPair w hF χ).k : ℂ) = 1 := by simp [thetaPair]
    rw [hk] at h
    exact hs₁ (by rw [← h]; ring)

/- English proof (translation)
Rewrite using `[tateZetaAt_eq w hF, archExponent_eq_of_forall hτ w]`. Use `set P := thetaPair w hF χ`. Establish `h` using `P.Λ_residue_zero`. Establish `hf₀ : P.f₀ = ((normOneClassMeasure K Set.univ).toReal : ℂ) * F 0` using `thetaConstant_eq_volume (forall_normOne_eq_one_of_forall hτ) F`. Rewrite `h` using `[hf₀]`.

Establish `ht` using `tendsto_add_const_nhdsNE (-((τ : ℂ) * I)) ((τ : ℂ) * I)`. Rewrite `ht` using `[neg_add_cancel]`. Conclude with `h.comp ht`.
-/
theorem tendsto_mul_tateZetaAt_neg (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) :
    Tendsto (fun s ↦ (s + (τ : ℂ) * I) * tateZetaAt w F χ s) (𝓝[≠] (-((τ : ℂ) * I)))
      (𝓝 (-(((normOneClassMeasure K Set.univ).toReal : ℂ) * F 0))) := by
  rw [tateZetaAt_eq w hF, archExponent_eq_of_forall hτ w]
  set P := thetaPair w hF χ
  have h := P.Λ_residue_zero
  have hf₀ : P.f₀ = ((normOneClassMeasure K Set.univ).toReal : ℂ) * F 0 :=
    thetaConstant_eq_volume (forall_normOne_eq_one_of_forall hτ) F
  rw [hf₀] at h
  have ht := tendsto_add_const_nhdsNE (-((τ : ℂ) * I)) ((τ : ℂ) * I)
  rw [neg_add_cancel] at ht
  exact h.comp ht

/- English proof (translation)
Rewrite using `[tateZetaAt_eq w hF, archExponent_eq_of_forall hτ w]`. Use `set P := thetaPair w hF χ`. Establish `h` using `P.Λ_residue_k`. Establish `hg₀ : P.g₀ = ((normOneClassMeasure K Set.univ).toReal : ℂ) * adelicFourier K F 0`. Use `thetaConstant_eq_volume (fun v ↦ ?_) _` and prove the remaining obligations.

Rewrite using `[toIdele_inv, forall_normOne_eq_one_of_forall hτ v, inv_one]`. Establish `hk : ((P.k : ℝ) : ℂ) = 1` using `by simp [P, thetaPair]`. Rewrite `h` using `[hg₀, hk, show P.ε = 1 from rfl, one_smul]`. Establish `ht` using `tendsto_add_const_nhdsNE (1 - (τ : ℂ) * I) ((τ : ℂ) * I)`. Rewrite `ht` using `[sub_add_cancel]`.

Use `(h.comp ht).congr fun s ↦ ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, smul_eq_mul]`. Put the polynomial expressions in normal form.
-/
theorem tendsto_mul_tateZetaAt_one_sub (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) :
    Tendsto (fun s ↦ (s - (1 - (τ : ℂ) * I)) * tateZetaAt w F χ s) (𝓝[≠] (1 - (τ : ℂ) * I))
      (𝓝 (((normOneClassMeasure K Set.univ).toReal : ℂ) * adelicFourier K F 0)) := by
  rw [tateZetaAt_eq w hF, archExponent_eq_of_forall hτ w]
  set P := thetaPair w hF χ
  have h := P.Λ_residue_k
  have hg₀ : P.g₀ = ((normOneClassMeasure K Set.univ).toReal : ℂ) * adelicFourier K F 0 := by
    refine thetaConstant_eq_volume (fun v ↦ ?_) _
    rw [toIdele_inv, forall_normOne_eq_one_of_forall hτ v, inv_one]
  have hk : ((P.k : ℝ) : ℂ) = 1 := by simp [P, thetaPair]
  rw [hg₀, hk, show P.ε = 1 from rfl, one_smul] at h
  have ht := tendsto_add_const_nhdsNE (1 - (τ : ℂ) * I) ((τ : ℂ) * I)
  rw [sub_add_cancel] at ht
  refine (h.comp ht).congr fun s ↦ ?_
  simp only [Function.comp_apply, smul_eq_mul]
  ring_nf

end Trivial

def tateZeta (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K) (s : ℂ) : ℂ :=
  tateZetaAt (Classical.arbitrary (InfinitePlace K)) F χ s

/- English proof (translation)
The claim follows from `tateZetaAt_eq_globalZeta (Classical.arbitrary _) hF χ hs`.
-/
theorem tateZeta_eq_globalZeta {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) (χ : HeckeCharacter K)
    {s : ℂ} (hs : 1 < s.re) : tateZeta F χ s = globalZeta F χ s :=
  tateZetaAt_eq_globalZeta (Classical.arbitrary _) hF χ hs

/- English proof (translation)
Establish `h` using `tateZetaAt_one_sub (Classical.arbitrary (InfinitePlace K)) hF χ (1 - s)`. Rewrite `h` using `[sub_sub_cancel]`. Conclude with `h`.
-/
theorem tateZeta_eq_tateZeta_one_sub {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) (s : ℂ) :
    tateZeta F χ s = tateZeta (adelicFourier K F) χ⁻¹ (1 - s) := by
  have h := tateZetaAt_one_sub (Classical.arbitrary (InfinitePlace K)) hF χ (1 - s)
  rw [sub_sub_cancel] at h
  exact h

/- English proof (translation)
The claim follows from `differentiable_tateZetaAt (Classical.arbitrary _) hF hχ`.
-/
theorem differentiable_tateZeta {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) {χ : HeckeCharacter K}
    (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1) :
    Differentiable ℂ (tateZeta F χ) :=
  differentiable_tateZetaAt (Classical.arbitrary _) hF hχ

/- English proof (translation)
The claim follows from `differentiableAt_tateZetaAt hτ (Classical.arbitrary _) hF hs₀ hs₁`.
-/
theorem differentiableAt_tateZeta {χ : HeckeCharacter K} {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
    {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) {s : ℂ} (hs₀ : s ≠ -((τ : ℂ) * I))
    (hs₁ : s ≠ 1 - (τ : ℂ) * I) : DifferentiableAt ℂ (tateZeta F χ) s :=
  differentiableAt_tateZetaAt hτ (Classical.arbitrary _) hF hs₀ hs₁

/- English proof (translation)
The claim follows from `tendsto_mul_tateZetaAt_neg hτ (Classical.arbitrary _) hF`.
-/
theorem tendsto_mul_tateZeta_neg {χ : HeckeCharacter K} {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
    {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    Tendsto (fun s ↦ (s + (τ : ℂ) * I) * tateZeta F χ s) (𝓝[≠] (-((τ : ℂ) * I)))
      (𝓝 (-(((normOneClassMeasure K Set.univ).toReal : ℂ) * F 0))) :=
  tendsto_mul_tateZetaAt_neg hτ (Classical.arbitrary _) hF

/- English proof (translation)
The claim follows from `tendsto_mul_tateZetaAt_one_sub hτ (Classical.arbitrary _) hF`.
-/
theorem tendsto_mul_tateZeta_one_sub {χ : HeckeCharacter K} {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
    {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    Tendsto (fun s ↦ (s - (1 - (τ : ℂ) * I)) * tateZeta F χ s) (𝓝[≠] (1 - (τ : ℂ) * I))
      (𝓝 (((normOneClassMeasure K Set.univ).toReal : ℂ) * adelicFourier K F 0)) :=
  tendsto_mul_tateZetaAt_one_sub hτ (Classical.arbitrary _) hF

end

end GroundTheory.Global
