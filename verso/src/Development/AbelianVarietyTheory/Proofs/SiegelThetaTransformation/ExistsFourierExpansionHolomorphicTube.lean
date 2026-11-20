import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormLeTsumOfCubeFourierCoeffLe

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory

open MeasureTheory

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open MeasureTheory in
/- English proof (translation)
Establish `hq : IsOpenQuotientMap (Pi.map fun _ : ι ↦ (QuotientAddGroup.mk : ℝ → UnitAddCircle))` using `IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk`. Establish `hfac : Function.FactorsThrough F (Pi.map fun _ : ι ↦ (QuotientAddGroup.mk : ℝ → UnitAddCircle))`. Introduce `x x' hxx'`. Establish `hi : ∀ i, ∃ k : ℤ, x i = x' i + k`. Introduce `i`.

Use `congrFun hxx' i` as an intermediate fact. Simplify using `only [Pi.map_apply] at this`. Take `⟨k, hk⟩` from `AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 this.symm)`. Conclude with `⟨k, by simp at hk; linarith⟩`. Use `choose m hm using hi`.

Establish `: x = x' + fun i ↦ (m i : ℝ)` using `funext fun i ↦ hm i`. Rewrite using `[this, hper]`. Set `q : C(ι → ℝ, UnitAddTorus ι)` to `⟨_, hq.continuous⟩`. Establish `hq' : Topology.IsQuotientMap q` using `hq.isQuotientMap`. Use `⟨hq'.lift ⟨F, hF⟩ hfac, fun x ↦ ?_⟩` and prove the remaining obligations.

Conclude with `congrFun (congrArg DFunLike.coe (hq'.lift_comp ⟨F, hF⟩ hfac)) x`.
-/
private lemma exists_unitAddTorus_lift_of_periodic {ι : Type} [Fintype ι] (F : (ι → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (x : ι → ℝ) (m : ι → ℤ), F (x + fun i ↦ (m i : ℝ)) = F x) :
    ∃ g : C(UnitAddTorus ι, ℂ), ∀ x : ι → ℝ, g (fun i ↦ (x i : UnitAddCircle)) = F x := by
  have hq : IsOpenQuotientMap (Pi.map fun _ : ι ↦ (QuotientAddGroup.mk : ℝ → UnitAddCircle)) :=
    IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk
  have hfac : Function.FactorsThrough F
      (Pi.map fun _ : ι ↦ (QuotientAddGroup.mk : ℝ → UnitAddCircle)) := by
    intro x x' hxx'
    have hi : ∀ i, ∃ k : ℤ, x i = x' i + k := by
      intro i
      have := congrFun hxx' i
      simp only [Pi.map_apply] at this
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 this.symm)
      exact ⟨k, by simp at hk; linarith⟩
    choose m hm using hi
    have : x = x' + fun i ↦ (m i : ℝ) := funext fun i ↦ hm i
    rw [this, hper]
  let q : C(ι → ℝ, UnitAddTorus ι) := ⟨_, hq.continuous⟩
  have hq' : Topology.IsQuotientMap q := hq.isQuotientMap
  refine ⟨hq'.lift ⟨F, hF⟩ hfac, fun x ↦ ?_⟩
  exact congrFun (congrArg DFunLike.coe (hq'.lift_comp ⟨F, hF⟩ hfac)) x

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open MeasureTheory in
/- English proof (translation)
Simplify using `only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]`. Rewrite using `[Finset.mul_sum, Complex.exp_sum]`. Use `Finset.prod_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[fourier_coe_apply]`. Use `push_cast`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma mFourier_apply_coe {ι : Type} [Fintype ι] (ν : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier ν (fun i ↦ (x i : UnitAddCircle)) =
      cexp (2 * π * I * ∑ i, (ν i : ℂ) * x i) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [fourier_coe_apply]
  push_cast
  congr 1
  ring

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open MeasureTheory in
/- English proof (translation)
Rewrite using `[UnitAddTorus.mFourierCoeff_eq_integral _ _ 0]`. Establish `hset : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} = Set.univ.pi fun _ ↦ Set.Ioc (0 : ℝ) 1`. Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `hae : (Set.univ.pi fun _ : ι ↦ Set.Ioc (0 : ℝ) 1) =ᵐ[volume] Set.Icc (0 : ι → ℝ) 1`.

Rewrite using `[volume_pi]`. Conclude with `Measure.univ_pi_Ioc_ae_eq_Icc`. Rewrite using `[hset, setIntegral_congr_set hae]`. Use `setIntegral_congr_fun measurableSet_Icc fun x _ ↦ ?_` and prove the remaining obligations. Simplify using `only [hg, smul_eq_mul, mFourier_apply_coe]`.

Use `congr 2`. Use `push_cast`. Simplify using `only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma mFourierCoeff_lift_eq_integral {ι : Type} [Fintype ι] (g : C(UnitAddTorus ι, ℂ))
    (F : (ι → ℝ) → ℂ) (hg : ∀ x : ι → ℝ, g (fun i ↦ (x i : UnitAddCircle)) = F x) (ν : ι → ℤ) :
    UnitAddTorus.mFourierCoeff g ν =
      ∫ x in Set.Icc (0 : ι → ℝ) 1, cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * x i)) * F x := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ 0]
  have hset : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =
      Set.univ.pi fun _ ↦ Set.Ioc (0 : ℝ) 1 := by
    ext x; simp
  have hae : (Set.univ.pi fun _ : ι ↦ Set.Ioc (0 : ℝ) 1) =ᵐ[volume] Set.Icc (0 : ι → ℝ) 1 := by
    rw [volume_pi]; exact Measure.univ_pi_Ioc_ae_eq_Icc
  rw [hset, setIntegral_congr_set hae]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ ↦ ?_
  simp only [hg, smul_eq_mul, mFourier_apply_coe]
  congr 2
  push_cast
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
open MeasureTheory in

/- English proof (translation)
Introduce `ι _ Ω f hΩo hΩc hf hper`. Use `set T : Set (ι → ℂ) := {z | (fun i => (z i).im) ∈ Ω} with hT`. Establish `him : Continuous fun z : ι → ℂ ↦ fun i ↦ (z i).im` using `continuous_pi fun i ↦ Complex.continuous_im.comp (continuous_apply i)`. Establish `hTo : IsOpen T` using `hΩo.preimage him`. Establish `hTc : IsPreconnected T`.

Use `Convex.isPreconnected ?_` and prove the remaining obligations. Introduce `z hz w hw s t hs ht hst`. Simplify using `only [hT, Set.mem_setOf_eq] at hz hw ⊢`. Use `hΩc hz hw hs ht hst using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Establish `hcont : ContinuousOn f T` using `hf.continuousOn`. Establish `hmemT : ∀ (x y : ι → ℝ), y ∈ Ω → (fun i ↦ (x i : ℂ) + I * y i) ∈ T`. Introduce `x y hy`. Simplify `hy` using `[hT]`.

Set `c : (ι → ℝ) → (ι → ℤ) → ℂ` to `fun y ν ↦ ∫ x in Set.Icc (0 : ι → ℝ) 1, f (fun i => (x i : ℂ) + I * y i) * cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i)))`. Establish `hc_indep : ∀ y ∈ Ω, ∀ y' ∈ Ω, ∀ ν, c y ν = c y' ν`. Introduce `y hy y' hy' ν`. Set `h : (ι → ℂ) → ℂ` to `fun z ↦ f z * cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * z i))`. Establish `hw : ∀ y ∈ Ω, (fun i ↦ I * (y i : ℂ)) ∈ T` using `fun y hy ↦ by simpa [hT] using hy`.

Establish `key` using `_root_.GlobalTheory.Koecher.setIntegral_unitCube_tube (f := h) (U := T) hTo hTc (fun z hz t ↦ by simpa [hT] using hz) (hf.mul (Differentiable.differentiableOn (by fun_prop))) (fun z hz i ↦ by`. Establish `hm` using `hper z hz (Pi.single i 1)`. Establish `hs : (fun j ↦ ((Pi.single i (1 : ℤ) : ι → ℤ) j : ℂ)) = Pi.single i 1`. Apply the tactic sequence `funext j; by_cases hj : j = i <;> simp [Pi.single_apply, hj]`. Rewrite `hm` using `[hs]`.

Simplify using `only [h]`. Rewrite using `[hm]`. Use `congr 1`. Rewrite using `[show ∑ j, (ν j : ℂ) * (z + (Pi.single i (1 : ℂ) : ι → ℂ)) j = ∑ j, (ν j : ℂ) * z j + ν i by`. Simplify using `[Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply]]`.

Rewrite using `[mul_add, neg_add, Complex.exp_add]`. Establish `h1 : cexp (-(2 * π * I * (ν i : ℂ))) = 1`. Rewrite using `[show -(2 * π * I * (ν i : ℂ)) = ((-ν i : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I _`. Rewrite using `[h1, mul_one])`.

Use the proof step `(hw y hy) (hw y' hy')`. Conclude with `key`. Establish `hc_Ico : ∀ y ν, c y ν = ∫ x in Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1), f (fun i => (x i : ℂ) + I * y i) * cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i)))`. Introduce `y ν`. Establish `hae : (Set.univ.pi fun _ : ι ↦ Set.Ico (0 : ℝ) 1) =ᵐ[volume] Set.Icc (0 : ι → ℝ) 1`.

Rewrite using `[volume_pi]`. Conclude with `Measure.univ_pi_Ico_ae_eq_Icc`. Rewrite using `[setIntegral_congr_set hae]`. Establish `hc_bound : ∀ y ∈ Ω, ∀ M : ℝ, (∀ x : ι → ℝ, ‖f (fun i ↦ (x i : ℂ) + I * y i)‖ ≤ M) → ∀ ν, ‖c y ν‖ ≤ Real.exp (2 * π * ∑ i, (ν i : ℝ) * y i) * M`. Introduce `y hy M hM ν`.

Establish `hvol : volume (Set.Icc (0 : ι → ℝ) 1) = 1` using `by simp [Real.volume_Icc_pi]`. Use `(norm_setIntegral_le_of_norm_le_const (C := Real.exp (2 * π * ∑ i, (ν i : ℝ) * y i) * M) (by simp [hvol]) fun x _ ↦ ?_).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_exp, mul_comm]`. Establish `hre : (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i))).re = 2 * π * ∑ i, (ν i : ℝ) * y i`. Simplify using `[Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im, Finset.mul_sum]`.

Rewrite using `[hre]`. Conclude with `mul_le_mul_of_nonneg_left (hM x) (Real.exp_pos _).le`. Simplify using `[Measure.real, hvol]`. Establish `hc_coef : ∀ y ∈ Ω, ∃ g : C(UnitAddTorus ι, ℂ), (∀ x : ι → ℝ, g (fun i ↦ (x i : UnitAddCircle)) = f (fun i ↦ (x i : ℂ) + I * y i)) ∧ ∀ ν, UnitAddTorus.mFourierCoeff g ν = Real.exp (-(2 * π * ∑ i, (ν i : ℝ) * y i)) * c y ν`. Introduce `y hy`.

Establish `hFc : Continuous fun x : ι → ℝ ↦ f (fun i ↦ (x i : ℂ) + I * y i)` using `hcont.comp_continuous (by fun_prop) fun x ↦ hmemT x y hy`. Take `⟨g, hg⟩` from `exists_unitAddTorus_lift_of_periodic _ hFc (fun x m ↦ by`. Use `hper (fun i ↦ (x i : ℂ) + I * y i) (by simpa using hy) m` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.add_apply]`. Use `push_cast`. Use the proof step `ring)`. Use `⟨g, hg, fun ν ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[mFourierCoeff_lift_eq_integral g _ hg ν]`.

Simplify using `only [c]`. Rewrite using `[← integral_const_mul]`. Use `setIntegral_congr_fun measurableSet_Icc fun x _ ↦ ?_` and prove the remaining obligations. Establish `hs : ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i) = ∑ i, (ν i : ℂ) * x i + I * ∑ i, (ν i : ℂ) * y i`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `he : cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i))) = cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * x i)) * cexp (2 * π * ∑ i, (ν i : ℂ) * y i)`. Rewrite using `[← Complex.exp_add, hs]`. Use `congr 1`.

Put the polynomial expressions in normal form. Rewrite using `[I_sq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Use `push_cast`.

Establish `hB : cexp (-(2 * π * ∑ i, (ν i : ℂ) * (y i : ℂ))) * cexp (2 * π * ∑ i, (ν i : ℂ) * y i) = 1`. Rewrite using `[← Complex.exp_add]`. Simplify using the standard rewrite rules. Take the linear combination `-(cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * x i)) * f (fun i ↦ (x i : ℂ) + I * y i)) * hB`. Break down `Set.eq_empty_or_nonempty Ω with hΩ | ⟨y₁, hy₁⟩` into its components or cases.

Use `⟨0, fun z hz ↦ ?_, fun y hy ↦ ?_⟩` and prove the remaining obligations. Simplify using `[hΩ] at hz`. Simplify using `[hΩ] at hy`. Use `⟨c y₁, fun z hz ↦ ?_, fun y hy ν ↦ by rw [hc_indep y₁ hy₁ y hy, hc_Ico]⟩` and prove the remaining obligations. Use `set y₀ : ι → ℝ := fun i ↦ (z i).im with hy₀`.

Use `set x₀ : ι → ℝ := fun i ↦ (z i).re with hx₀`. Establish `hz' : z = fun i ↦ (x₀ i : ℂ) + I * y₀ i`. Use function extensionality and compare the values at `i`. Rewrite using `[mul_comm]`. Conclude with `(Complex.re_add_im _).symm`.

Take `⟨g, hg, hgc⟩` from `hc_coef y₀ hz`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hΩo y₀ hz`. Use `set δ := ε / 2 with hδ`. Establish `hδ0 : 0 < δ` using `by positivity`. Establish `hsub : Metric.closedBall y₀ δ ⊆ Ω` using `(Metric.closedBall_subset_ball (half_lt_self hε)).trans hball`.

Establish `hK : IsCompact ((fun p : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (p.1 i : ℂ) + I * p.2 i) '' (Set.Icc 0 1 ×ˢ Metric.closedBall y₀ δ))` using `(isCompact_Icc.prod (isCompact_closedBall _ _)).image (by fun_prop)`. Establish `hKT : ((fun p : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (p.1 i : ℂ) + I * p.2 i) '' (Set.Icc 0 1 ×ˢ Metric.closedBall y₀ δ)) ⊆ T`. Introduce and unpack `_ ⟨⟨x, y⟩, ⟨-, hy⟩, rfl⟩`. Conclude with `hmemT x y (hsub hy)`. Take `⟨M, hM⟩` from `hK.exists_bound_of_continuousOn (hcont.mono hKT)`.

Establish `hMall : ∀ y ∈ Metric.closedBall y₀ δ, ∀ x : ι → ℝ, ‖f (fun i ↦ (x i : ℂ) + I * y i)‖ ≤ M`. Introduce `y hy x`. Establish `h1` using `hper (fun i ↦ ((Int.fract (x i) : ℝ) : ℂ) + I * y i) (by simpa using hsub hy) (fun i ↦ ⌊x i⌋)`. Establish `heq : ((fun i ↦ ((Int.fract (x i) : ℝ) : ℂ) + I * y i) + fun i ↦ ((⌊x i⌋ : ℤ) : ℂ)) = fun i ↦ (x i : ℂ) + I * y i`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.add_apply, Int.fract]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[heq]`. Rewrite using `[h1]`.

Conclude with `hM _ ⟨(fun i ↦ Int.fract (x i), y), ⟨⟨fun i ↦ Int.fract_nonneg _, fun i ↦ (Int.fract_lt_one _).le⟩, hy⟩, rfl⟩`. Establish `hsum : Summable (UnitAddTorus.mFourierCoeff g)`. Use `Summable.of_norm_bounded ((_root_.GlobalTheory.Koecher.summable_exp_neg_mul_sum_abs (ι := ι) (ε := 2 * π * δ) (by positivity)).mul_left M) fun ν ↦ ?_` and prove the remaining obligations. Use `set s : ι → ℝ := fun i ↦ y₀ i - δ * (Int.sign (ν i) : ℝ) with hsdef`. Establish `hs : s ∈ Metric.closedBall y₀ δ`.

Rewrite using `[Metric.mem_closedBall, dist_pi_le_iff hδ0.le]`. Introduce `i`. Rewrite using `[Real.dist_eq, hsdef]`. Simplify using `only [sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos hδ0]`. Establish `: |(Int.sign (ν i) : ℝ)| ≤ 1`.

Apply the tactic sequence `rcases Int.sign_trichotomy (ν i) with h | h | h <;> simp [h]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hgc ν, hc_indep y₀ hz s (hsub hs), norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← Real.exp_add, mul_comm]`.

Use `congr 2`. Establish `habs : ∀ i, (ν i : ℝ) * (Int.sign (ν i) : ℝ) = |((ν i : ℤ) : ℝ)|`. Introduce `i`. Break down `Int.sign_trichotomy (ν i) with h | h | h` into its components or cases. Rewrite using `[h, Int.cast_one, mul_one, abs_of_pos (by exact_mod_cast Int.sign_eq_one_iff_pos.1 h)]`.

Rewrite using `[h]`. Simplify using `[Int.sign_eq_zero_iff_zero.1 h]`. Rewrite using `[h, Int.cast_neg, Int.cast_one, mul_neg_one, abs_of_neg (by exact_mod_cast Int.sign_eq_neg_one_iff_neg.1 h)]`. Simplify using `only [hsdef, mul_sub, Finset.sum_sub_distrib]`. Rewrite using `[show ∑ i, (ν i : ℝ) * (δ * (Int.sign (ν i) : ℝ)) = δ * ∑ i, |((ν i : ℤ) : ℝ)| by`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← habs]`. Use the proof step `ring]`. Expand and normalize the polynomial expressions, which then agree.

Establish `key` using `UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum (fun i ↦ (x₀ i : UnitAddCircle))`. Rewrite `key` using `[hg]`. Use `key using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `ν`. Rewrite using `[hgc ν, mFourier_apply_coe, hc_indep y₁ hy₁ y₀ hz, smul_eq_mul]`.

Use `conv_lhs => rw [hz']`. Establish `hs : ∑ i, (ν i : ℂ) * ((x₀ i : ℂ) + I * y₀ i) = ∑ i, (ν i : ℂ) * x₀ i + I * ∑ i, (ν i : ℂ) * y₀ i`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `he : cexp (2 * π * I * ∑ i, (ν i : ℂ) * ((x₀ i : ℂ) + I * y₀ i)) = cexp (-(2 * π * ∑ i, (ν i : ℂ) * y₀ i)) * cexp (2 * π * I * ∑ i, (ν i : ℂ) * x₀ i)`. Rewrite using `[← Complex.exp_add, hs]`. Use `congr 1`. Put the polynomial expressions in normal form. Rewrite using `[I_sq]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hz']`.
-/
theorem _root_.GlobalTheory.exists_fourier_expansion_tube :
    ∀ (ι : Type) [Fintype ι] (Ω : Set (ι → ℝ)) (f : (ι → ℂ) → ℂ), IsOpen Ω → Convex ℝ Ω →
      DifferentiableOn ℂ f {z | (fun i => (z i).im) ∈ Ω} →
      (∀ z, (fun i => (z i).im) ∈ Ω → ∀ m : ι → ℤ, f (z + fun i => (m i : ℂ)) = f z) →
      ∃ a : (ι → ℤ) → ℂ, (∀ z, (fun i => (z i).im) ∈ Ω →
        HasSum (fun ν : ι → ℤ => a ν * cexp (2 * π * I * ∑ i, (ν i : ℂ) * z i)) (f z)) ∧
        ∀ y ∈ Ω, ∀ ν : ι → ℤ, a ν = ∫ x in Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1),
          f (fun i => (x i : ℂ) + I * y i) *
            cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i))) := by
  intro ι _ Ω f hΩo hΩc hf hper
  set T : Set (ι → ℂ) := {z | (fun i => (z i).im) ∈ Ω} with hT
  have him : Continuous fun z : ι → ℂ ↦ fun i ↦ (z i).im :=
    continuous_pi fun i ↦ Complex.continuous_im.comp (continuous_apply i)
  have hTo : IsOpen T := hΩo.preimage him
  have hTc : IsPreconnected T := by
    refine Convex.isPreconnected ?_
    intro z hz w hw s t hs ht hst
    simp only [hT, Set.mem_setOf_eq] at hz hw ⊢
    convert hΩc hz hw hs ht hst using 1
    funext i
    simp
  have hcont : ContinuousOn f T := hf.continuousOn

  have hmemT : ∀ (x y : ι → ℝ), y ∈ Ω → (fun i ↦ (x i : ℂ) + I * y i) ∈ T := by
    intro x y hy
    simpa [hT] using hy
  let c : (ι → ℝ) → (ι → ℤ) → ℂ := fun y ν ↦ ∫ x in Set.Icc (0 : ι → ℝ) 1,
    f (fun i => (x i : ℂ) + I * y i) * cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i)))
  have hc_indep : ∀ y ∈ Ω, ∀ y' ∈ Ω, ∀ ν, c y ν = c y' ν := by
    intro y hy y' hy' ν
    let h : (ι → ℂ) → ℂ := fun z ↦ f z * cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * z i))
    have hw : ∀ y ∈ Ω, (fun i ↦ I * (y i : ℂ)) ∈ T := fun y hy ↦ by simpa [hT] using hy
    have key := _root_.GlobalTheory.Koecher.setIntegral_unitCube_tube (f := h) (U := T) hTo hTc
      (fun z hz t ↦ by simpa [hT] using hz)
      (hf.mul (Differentiable.differentiableOn (by fun_prop)))
      (fun z hz i ↦ by
        have hm := hper z hz (Pi.single i 1)
        have hs : (fun j ↦ ((Pi.single i (1 : ℤ) : ι → ℤ) j : ℂ)) = Pi.single i 1 := by
          funext j; by_cases hj : j = i <;> simp [Pi.single_apply, hj]
        rw [hs] at hm
        simp only [h]
        rw [hm]
        congr 1
        rw [show ∑ j, (ν j : ℂ) * (z + (Pi.single i (1 : ℂ) : ι → ℂ)) j =
            ∑ j, (ν j : ℂ) * z j + ν i by
          simp [Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply]]
        rw [mul_add, neg_add, Complex.exp_add]
        have h1 : cexp (-(2 * π * I * (ν i : ℂ))) = 1 := by
          rw [show -(2 * π * I * (ν i : ℂ)) = ((-ν i : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
          exact Complex.exp_int_mul_two_pi_mul_I _
        rw [h1, mul_one])
      (hw y hy) (hw y' hy')
    exact key
  have hc_Ico : ∀ y ν, c y ν = ∫ x in Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1),
      f (fun i => (x i : ℂ) + I * y i) *
        cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i))) := by
    intro y ν
    have hae : (Set.univ.pi fun _ : ι ↦ Set.Ico (0 : ℝ) 1) =ᵐ[volume] Set.Icc (0 : ι → ℝ) 1 := by
      rw [volume_pi]; exact Measure.univ_pi_Ico_ae_eq_Icc
    rw [setIntegral_congr_set hae]
  have hc_bound : ∀ y ∈ Ω, ∀ M : ℝ, (∀ x : ι → ℝ, ‖f (fun i ↦ (x i : ℂ) + I * y i)‖ ≤ M) →
      ∀ ν, ‖c y ν‖ ≤ Real.exp (2 * π * ∑ i, (ν i : ℝ) * y i) * M := by
    intro y hy M hM ν
    have hvol : volume (Set.Icc (0 : ι → ℝ) 1) = 1 := by simp [Real.volume_Icc_pi]
    refine (norm_setIntegral_le_of_norm_le_const
      (C := Real.exp (2 * π * ∑ i, (ν i : ℝ) * y i) * M) (by simp [hvol]) fun x _ ↦ ?_).trans ?_
    · rw [norm_mul, Complex.norm_exp, mul_comm]
      have hre : (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i))).re =
          2 * π * ∑ i, (ν i : ℝ) * y i := by
        simp [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im, Finset.mul_sum]
      rw [hre]
      exact mul_le_mul_of_nonneg_left (hM x) (Real.exp_pos _).le
    · simp [Measure.real, hvol]
  have hc_coef : ∀ y ∈ Ω, ∃ g : C(UnitAddTorus ι, ℂ),
      (∀ x : ι → ℝ, g (fun i ↦ (x i : UnitAddCircle)) = f (fun i ↦ (x i : ℂ) + I * y i)) ∧
      ∀ ν, UnitAddTorus.mFourierCoeff g ν = Real.exp (-(2 * π * ∑ i, (ν i : ℝ) * y i)) * c y ν := by
    intro y hy
    have hFc : Continuous fun x : ι → ℝ ↦ f (fun i ↦ (x i : ℂ) + I * y i) :=
      hcont.comp_continuous (by fun_prop) fun x ↦ hmemT x y hy
    obtain ⟨g, hg⟩ := exists_unitAddTorus_lift_of_periodic _ hFc (fun x m ↦ by
      have := hper (fun i ↦ (x i : ℂ) + I * y i) (by simpa using hy) m
      convert this using 2
      funext i
      simp only [Pi.add_apply]
      push_cast
      ring)
    refine ⟨g, hg, fun ν ↦ ?_⟩
    rw [mFourierCoeff_lift_eq_integral g _ hg ν]
    simp only [c]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun x _ ↦ ?_
    have hs : ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i) =
        ∑ i, (ν i : ℂ) * x i + I * ∑ i, (ν i : ℂ) * y i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    have he : cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i))) =
        cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * x i)) * cexp (2 * π * ∑ i, (ν i : ℂ) * y i) := by
      rw [← Complex.exp_add, hs]
      congr 1
      ring_nf
      rw [I_sq]
      ring
    rw [he]
    push_cast
    have hB : cexp (-(2 * π * ∑ i, (ν i : ℂ) * (y i : ℂ))) *
        cexp (2 * π * ∑ i, (ν i : ℂ) * y i) = 1 := by
      rw [← Complex.exp_add]; simp
    linear_combination -(cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * x i)) *
      f (fun i ↦ (x i : ℂ) + I * y i)) * hB
  rcases Set.eq_empty_or_nonempty Ω with hΩ | ⟨y₁, hy₁⟩
  · refine ⟨0, fun z hz ↦ ?_, fun y hy ↦ ?_⟩
    · simp [hΩ] at hz
    · simp [hΩ] at hy
  refine ⟨c y₁, fun z hz ↦ ?_, fun y hy ν ↦ by rw [hc_indep y₁ hy₁ y hy, hc_Ico]⟩
  set y₀ : ι → ℝ := fun i ↦ (z i).im with hy₀
  set x₀ : ι → ℝ := fun i ↦ (z i).re with hx₀
  have hz' : z = fun i ↦ (x₀ i : ℂ) + I * y₀ i := by
    funext i; rw [mul_comm]; exact (Complex.re_add_im _).symm
  obtain ⟨g, hg, hgc⟩ := hc_coef y₀ hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩo y₀ hz
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hsub : Metric.closedBall y₀ δ ⊆ Ω :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  have hK : IsCompact ((fun p : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (p.1 i : ℂ) + I * p.2 i) ''
      (Set.Icc 0 1 ×ˢ Metric.closedBall y₀ δ)) :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image (by fun_prop)
  have hKT : ((fun p : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (p.1 i : ℂ) + I * p.2 i) ''
      (Set.Icc 0 1 ×ˢ Metric.closedBall y₀ δ)) ⊆ T := by
    rintro _ ⟨⟨x, y⟩, ⟨-, hy⟩, rfl⟩
    exact hmemT x y (hsub hy)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKT)
  have hMall : ∀ y ∈ Metric.closedBall y₀ δ, ∀ x : ι → ℝ,
      ‖f (fun i ↦ (x i : ℂ) + I * y i)‖ ≤ M := by
    intro y hy x
    have h1 := hper (fun i ↦ ((Int.fract (x i) : ℝ) : ℂ) + I * y i) (by simpa using hsub hy)
      (fun i ↦ ⌊x i⌋)
    have heq : ((fun i ↦ ((Int.fract (x i) : ℝ) : ℂ) + I * y i) + fun i ↦ ((⌊x i⌋ : ℤ) : ℂ)) =
        fun i ↦ (x i : ℂ) + I * y i := by
      funext i; simp only [Pi.add_apply, Int.fract]; push_cast; ring
    rw [heq] at h1
    rw [h1]
    exact hM _ ⟨(fun i ↦ Int.fract (x i), y),
      ⟨⟨fun i ↦ Int.fract_nonneg _, fun i ↦ (Int.fract_lt_one _).le⟩, hy⟩, rfl⟩
  have hsum : Summable (UnitAddTorus.mFourierCoeff g) := by
    refine Summable.of_norm_bounded
      ((_root_.GlobalTheory.Koecher.summable_exp_neg_mul_sum_abs (ι := ι) (ε := 2 * π * δ) (by positivity)).mul_left M)
      fun ν ↦ ?_
    set s : ι → ℝ := fun i ↦ y₀ i - δ * (Int.sign (ν i) : ℝ) with hsdef
    have hs : s ∈ Metric.closedBall y₀ δ := by
      rw [Metric.mem_closedBall, dist_pi_le_iff hδ0.le]
      intro i
      rw [Real.dist_eq, hsdef]
      simp only [sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos hδ0]
      have : |(Int.sign (ν i) : ℝ)| ≤ 1 := by
        rcases Int.sign_trichotomy (ν i) with h | h | h <;> simp [h]
      nlinarith
    rw [hgc ν, hc_indep y₀ hz s (hsub hs), norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(2 * π * ∑ i, (ν i : ℝ) * y₀ i)) * ‖c s ν‖
        ≤ Real.exp (-(2 * π * ∑ i, (ν i : ℝ) * y₀ i)) *
            (Real.exp (2 * π * ∑ i, (ν i : ℝ) * s i) * M) :=
          mul_le_mul_of_nonneg_left (hc_bound s (hsub hs) M (hMall s hs) ν) (Real.exp_pos _).le
      _ = M * Real.exp (-(2 * π * δ * ∑ i, |((ν i : ℤ) : ℝ)|)) := by
          rw [← mul_assoc, ← Real.exp_add, mul_comm]
          congr 2
          have habs : ∀ i, (ν i : ℝ) * (Int.sign (ν i) : ℝ) = |((ν i : ℤ) : ℝ)| := by
            intro i
            rcases Int.sign_trichotomy (ν i) with h | h | h
            · rw [h, Int.cast_one, mul_one,
                abs_of_pos (by exact_mod_cast Int.sign_eq_one_iff_pos.1 h)]
            · rw [h]; simp [Int.sign_eq_zero_iff_zero.1 h]
            · rw [h, Int.cast_neg, Int.cast_one, mul_neg_one,
                abs_of_neg (by exact_mod_cast Int.sign_eq_neg_one_iff_neg.1 h)]
          simp only [hsdef, mul_sub, Finset.sum_sub_distrib]
          rw [show ∑ i, (ν i : ℝ) * (δ * (Int.sign (ν i) : ℝ)) = δ * ∑ i, |((ν i : ℤ) : ℝ)| by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ ↦ ?_; rw [← habs]; ring]
          ring
  have key := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum
    (fun i ↦ (x₀ i : UnitAddCircle))
  rw [hg] at key
  convert key using 1
  · funext ν
    rw [hgc ν, mFourier_apply_coe, hc_indep y₁ hy₁ y₀ hz, smul_eq_mul]
    conv_lhs => rw [hz']
    have hs : ∑ i, (ν i : ℂ) * ((x₀ i : ℂ) + I * y₀ i) =
        ∑ i, (ν i : ℂ) * x₀ i + I * ∑ i, (ν i : ℂ) * y₀ i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    have he : cexp (2 * π * I * ∑ i, (ν i : ℂ) * ((x₀ i : ℂ) + I * y₀ i)) =
        cexp (-(2 * π * ∑ i, (ν i : ℂ) * y₀ i)) * cexp (2 * π * I * ∑ i, (ν i : ℂ) * x₀ i) := by
      rw [← Complex.exp_add, hs]
      congr 1
      ring_nf
      rw [I_sq]
      ring
    rw [he]
    push_cast
    ring
  · rw [← hz']

end GlobalTheory
