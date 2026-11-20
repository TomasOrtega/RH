import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphSt

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

/- English proof (translation)
Use `haveI : IsFiniteMeasureOnCompacts μ := ⟨fun _ _ => measure_lt_top μ _⟩`. Conclude with `hf.integrable_of_hasCompactSupport (hK.of_isClosed_subset (isClosed_tsupport f) (subset_univ _))`.
-/
theorem integrable_of_cpt {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [IsFiniteMeasure μ] (hK : IsCompact (univ : Set K)) {f : K → ℂ} (hf : Continuous f) : Integrable f μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun _ _ => measure_lt_top μ _⟩
  exact hf.integrable_of_hasCompactSupport (hK.of_isClosed_subset (isClosed_tsupport f) (subset_univ _))

/- English proof (translation)
Set `b` to `Module.finBasis ℂ W`. Establish `hext : ∀ i, ∃ L : V →ₗ[ℂ] ℂ, ∀ x : W, L x = b.repr x i` using `fun i => by`. Take `⟨L, hL⟩` from `LinearMap.exists_extend (b.coord i)`. Conclude with `⟨L, fun x => by simpa using congrArg (fun f => f x) hL⟩`. Use `choose L hL using hext`.

Use `⟨∑ i, (∫ k, w k * L i (v k) ∂μ) • (b i : V), fun l => ?_⟩` and prove the remaining obligations. Establish `hv' : ∀ k, l (v k) = ∑ i, L i (v k) * l (b i)`. Introduce `k`. Establish `h1` using `b.sum_repr ⟨v k, hv k⟩`. Establish `h2 : v k = ∑ i, (b.repr ⟨v k, hv k⟩ i) • (b i : V)`.

Establish `h3` using `congrArg Subtype.val h1`. Rewrite `h3` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at h3`. Conclude with `h3.symm`. Use `conv_lhs => rw [h2]`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, ← hL i ⟨v k, hv k⟩]`. Rewrite using `[map_sum]`. Repeatedly rewrite using `[map_smul, smul_eq_mul]`.

Establish `hint : ∀ i, Integrable (fun k => w k * L i (v k) * l (b i)) μ` using `fun i => integrable_of_cpt μ hK ((hw.mul (hc (L i))).mul continuous_const)`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[integral_mul_const]`. Use `_ = ∫ k, ∑ i, w k * L i (v k) * l (b i) ∂μ := (integral_finsetSum _ fun i _ => hint i).symm`.

Use `_ = ∫ k, w k * l (v k) ∂μ := by`. Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `only [hv' k, Finset.mul_sum, mul_assoc]`.
-/
theorem finInt {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (hK : IsCompact (univ : Set K)) {V : Type*} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] (v : K → V) (hv : ∀ k, v k ∈ W) (hc : ∀ l : V →ₗ[ℂ] ℂ, Continuous fun k => l (v k))
    (w : K → ℂ) (hw : Continuous w) : ∃ Φ : V, ∀ l : V →ₗ[ℂ] ℂ, l Φ = ∫ k, w k * l (v k) ∂μ := by
  classical
  let b := Module.finBasis ℂ W
  have hext : ∀ i, ∃ L : V →ₗ[ℂ] ℂ, ∀ x : W, L x = b.repr x i := fun i => by
    obtain ⟨L, hL⟩ := LinearMap.exists_extend (b.coord i)
    exact ⟨L, fun x => by simpa using congrArg (fun f => f x) hL⟩
  choose L hL using hext
  refine ⟨∑ i, (∫ k, w k * L i (v k) ∂μ) • (b i : V), fun l => ?_⟩
  have hv' : ∀ k, l (v k) = ∑ i, L i (v k) * l (b i) := by
    intro k
    have h1 := b.sum_repr ⟨v k, hv k⟩
    have h2 : v k = ∑ i, (b.repr ⟨v k, hv k⟩ i) • (b i : V) := by
      have h3 := congrArg Subtype.val h1
      rw [Submodule.coe_sum] at h3
      simp only [Submodule.coe_smul] at h3
      exact h3.symm
    conv_lhs => rw [h2]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, ← hL i ⟨v k, hv k⟩]
  rw [map_sum]
  simp_rw [map_smul, smul_eq_mul]
  have hint : ∀ i, Integrable (fun k => w k * L i (v k) * l (b i)) μ := fun i =>
    integrable_of_cpt μ hK ((hw.mul (hc (L i))).mul continuous_const)
  calc ∑ i, (∫ k, w k * L i (v k) ∂μ) * l (b i) = ∑ i, ∫ k, w k * L i (v k) * l (b i) ∂μ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_mul_const]
    _ = ∫ k, ∑ i, w k * L i (v k) * l (b i) ∂μ := (integral_finsetSum _ fun i _ => hint i).symm
    _ = ∫ k, w k * l (v k) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [hv' k, Finset.mul_sum, mul_assoc]

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `m n ε c t p q e sL ρ hL G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I Λ hG _ _ μ _ _ g y`. Take `⟨hAdil, hAuniq, hAcpt, _hAdet, hAF0c, hAV, hAF0⟩` from `hA`. Take `⟨hCrc, hCzero⟩` from `hC`. Establish `hKc : IsCompact (univ : Set (KR n))` using `hAcpt n`. Establish `hF0 : Continuous (F0 (n` using `n) p q e) := (hAF0 n p q e).1`.

Establish `hF0ne : ∀ k : KR n, F0 p q e (k : GR n) ≠ 0` using `fun k => (hAF0 n p q e).2 k k.2`. Establish `hw : Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹` using `(hF0.comp continuous_subtype_val).inv₀ hF0ne`. Establish `hF01 : F0 (n` using `n) p q e 1 = 1 := by`. Establish `h` using `((hMult n p q e).1 1 1 (KR n).one_mem).1`. Rewrite `h` using `[mul_one]`.

Establish `hne : F0 (n` using `n) p q e 1 ≠ 0 := by simpa using hF0ne 1`. Conclude with `mul_left_cancel₀ hne (by rw [mul_one]; exact h.symm)`. Establish `hRI : ∀ (z k2 : GR n), k2 ∈ KR n → (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (z * k2))) ∂μ) = F0 p q e k2 * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * z)) ∂μ`. Introduce `z k2 hk2`. Rewrite using `[← integral_const_mul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Establish `hk2' : InK (mR k2)` using `hk2`. Establish `h1 : I 1 (g * ι ((k : GR n) * (z * k2))) = F0 p q e k2 * I 1 (g * ι ((k : GR n) * z))`. Rewrite using `[← mul_assoc, map_mul ι, ← mul_assoc g, hG.Ik 1 _ k2 hk2', hL.kvac k2 hk2', map_smul]`. Both sides reduce to the same expression.

Simplify using `only [h1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hRS : ∀ (z k2 : GR n), k2 ∈ KR n → (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (z * k2)) ∂μ) = F0 p q e k2 * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * z) ∂μ`. Introduce `z k2 hk2`. Rewrite using `[← integral_const_mul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← mul_assoc, ((hMult n p q e).1 _ k2 hk2).1]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ (k1 : GR n), k1 ∈ KR n → ∀ (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) → (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (k1 * a 1))) ∂μ) = I 1 g * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a 1)) ∂μ`.

Introduce `k1 hk1 X a ha`. Take `⟨U, F, hUo, hUR, hFc, hF⟩` from `hG.Idil g X a ha`. Establish `hmc : Continuous fun k : KR n => (k : GR n) * k1` using `continuous_subtype_val.mul continuous_const`. Take `⟨V, hVo, hVR, hVc, hVd⟩` from `hAV n p q e X _ (hKc.image hmc)`. Establish `hKm : ∀ k : KR n, (k : GR n) * k1 ∈ KR n` using `fun k => (KR n).mul_mem k.2 hk1`.

Establish `hSm : ∀ k : KR n, (k : GR n) * k1 ∈ (fun k : KR n => (k : GR n) * k1) '' univ` using `fun k => mem_image_of_mem _ (mem_univ _)`. Establish `h0U : (0 : ℂ) ∈ U` using `by simpa using hUR 0`. Establish `h0V : (0 : ℂ) ∈ V` using `by simpa using hVR 0`. Use `set Q : PX m n := (dil c X ^ 0) 1 with hQ0`. Set `Gk : KR n → ℂ → ℂ` to `fun k z => (F0 p q e (k : GR n))⁻¹ * (F ((k : GR n) * k1) z - I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z)`.

Establish `hpm : Continuous fun w : KR n × ℂ => ((w.1 : GR n) * k1, w.2)` using `(hmc.comp continuous_fst).prodMk continuous_snd`. Establish `hc1 : ContinuousOn (fun w : KR n × ℂ => F ((w.1 : GR n) * k1) w.2) (univ ×ˢ (U ∩ V))` using `ContinuousOn.comp (f := fun w : KR n × ℂ => ((w.1 : GR n) * k1, w.2)) (g := fun y : GR n × ℂ => F y.1 y.2) hFc hpm.continuousOn (fun w hw' => ⟨mem_univ _, hw'.2.1⟩)`. Establish `hc2 : ContinuousOn (fun w : KR n × ℂ => holomorphicSectionExtension p q e X ((w.1 : GR n) * k1) w.2) (univ ×ˢ (U ∩ V))` using `ContinuousOn.comp (f := fun w : KR n × ℂ => ((w.1 : GR n) * k1, w.2)) (g := fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) hVc hpm.continuousOn (fun w hw' => ⟨hSm w.1, hw'.2.2⟩)`. Establish `hGc : ContinuousOn (fun w : KR n × ℂ => Gk w.1 w.2) (univ ×ˢ (U ∩ V))` using `((hw.comp continuous_fst).continuousOn).mul (hc1.sub (continuousOn_const.mul hc2))`. Establish `hGd : ∀ k ∈ (univ : Set (KR n)), DifferentiableOn ℂ (Gk k) (U ∩ V)`.

Introduce `k _`. Use `DifferentiableOn.const_mul (DifferentiableOn.sub ?_ (DifferentiableOn.const_mul ?_ _)) _` and prove the remaining obligations. Conclude with `((hF _).1).mono inter_subset_left`. Conclude with `(hVd _ (hSm k)).mono inter_subset_right`. Take `⟨hφd, hφD⟩` from `hHP (KR n) μ univ hKc (by simp) (U ∩ V) Gk (hUo.inter hVo) hGc hGd`.

Establish `hder : ∀ r : ℕ, iteratedDeriv r (fun z => ∫ k, Gk k z ∂μ) 0 = 0`. Introduce `r`. Rewrite using `[hφD 0 ⟨h0U, h0V⟩ r]`. Use `set Qr : PX m n := (dil c X ^ r) 1 with hQr`. Take `⟨W, hWf, hQW, hWst, hWc⟩` from `hL.kfin Qr`.

Use `haveI := hWf`. Establish `hvW : ∀ k : KR n, ρ ((k : GR n) * k1) Qr ∈ W` using `fun k => hWst _ (hKm k) Qr hQW`. Establish `hvc : ∀ l : PX m n →ₗ[ℂ] ℂ, Continuous fun k : KR n => l (ρ ((k : GR n) * k1) Qr)` using `fun l => (hWc Qr hQW l).comp_continuous hmc (fun k => hKm k)`. Take `⟨Φ, hΦ⟩` from `finInt μ hKc W (fun k : KR n => ρ ((k : GR n) * k1) Qr) hvW hvc _ hw`. Establish `hval : ∀ k : KR n, iteratedDeriv r (Gk k) 0 = (F0 p q e (k : GR n))⁻¹ * (I (ρ ((k : GR n) * k1) Qr) g - I 1 g * sL (ρ ((k : GR n) * k1) Qr) 1)`.

Introduce `k`. Establish `hcF : ContDiffAt ℂ r (F ((k : GR n) * k1)) 0` using `((hF _).1.contDiffOn hUo).contDiffAt (hUo.mem_nhds h0U)`. Establish `hcG : ContDiffAt ℂ r (fun z => I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z) 0` using `contDiffAt_const.mul (((hVd _ (hSm k)).contDiffOn hVo).contDiffAt (hVo.mem_nhds h0V))`. Establish `e1 : iteratedDeriv r (Gk k) 0 = (F0 p q e (k : GR n))⁻¹ * iteratedDeriv r (fun z => F ((k : GR n) * k1) z - I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z) 0`. Simplify using `only [Gk]`.

Rewrite using `[iteratedDeriv_const_mul_field]`. Establish `e0 : (fun z => F ((k : GR n) * k1) z - I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z) = F ((k : GR n) * k1) - fun z => I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z` using `rfl`. Rewrite using `[e1, e0, iteratedDeriv_sub hcF hcG]`. Simplify using `only [iteratedDeriv_const_mul_field]`. Rewrite using `[(hF _).2.2 r, hG.Ik Qr g _ (hKm k)]`.

Establish `e2 : iteratedDeriv r (holomorphicSectionExtension p q e X ((k : GR n) * k1)) 0 = sL (ρ ((k : GR n) * k1) Qr) 1`. Establish `h3` using `hCrc (holomorphicSectionExtension p q e X ((k : GR n) * k1)) V hVo hVR (hVd _ (hSm k)) r 0`. Simplify using `only [Complex.ofReal_zero] at h3`. Rewrite using `[← h3]`. Establish `h4 : (fun t : ℝ => holomorphicSectionExtension p q e X ((k : GR n) * k1) t) = fun s => F0 p q e ((k : GR n) * k1 * a s)`.

Use function extensionality and compare the values at `fun s => hAF0c n p q e X a ha _ s`. Rewrite using `[h4, (hD m n ε c t p q e sL ρ hL X a ha _ r).2]`. Rewrite using `[← hL.kact Qr 1 _ (hKm k), one_mul]`. Rewrite using `[e2]`. Set `lg : PX m n →ₗ[ℂ] ℂ` to `(LinearMap.proj g).comp I`.

Set `ly : GR n → PX m n →ₗ[ℂ] ℂ` to `fun y' => (LinearMap.proj y').comp sL`. Establish `hlg : ∀ P, lg P = I P g` using `fun P => rfl`. Establish `hly : ∀ y' P, ly y' P = sL P y'` using `fun y' P => rfl`. Establish `hcv : ∀ l : PX m n →ₗ[ℂ] ℂ, Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ * l (ρ ((k : GR n) * k1) Qr)` using `fun l => hw.mul (hvc l)`. Use `set D : ℂ := iteratedDeriv r (fun s : ℝ => ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a s)) ∂μ) 0 with hDdef`.

Establish `hsL : ∀ y' : GR n, sL Φ y' = F0 p q e y' * D`. Introduce `y'`. Establish `hm' : Continuous fun k : KR n => y' * ((k : GR n) * k1)` using `continuous_const.mul hmc`. Take `⟨V', hV'o, hV'R, hV'c, hV'd⟩` from `hAV n p q e X _ (hKc.image hm')`. Establish `hSm' : ∀ k : KR n, y' * ((k : GR n) * k1) ∈ (fun k : KR n => y' * ((k : GR n) * k1)) '' univ` using `fun k => mem_image_of_mem _ (mem_univ _)`.

Establish `h0V' : (0 : ℂ) ∈ V'` using `by simpa using hV'R 0`. Set `Gk' : KR n → ℂ → ℂ` to `fun k z => (F0 p q e (k : GR n))⁻¹ * holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1)) z`. Establish `hpm' : Continuous fun w : KR n × ℂ => (y' * ((w.1 : GR n) * k1), w.2)` using `(hm'.comp continuous_fst).prodMk continuous_snd`. Establish `hc3 : ContinuousOn (fun w : KR n × ℂ => holomorphicSectionExtension p q e X (y' * ((w.1 : GR n) * k1)) w.2) (univ ×ˢ V')` using `ContinuousOn.comp (f := fun w : KR n × ℂ => (y' * ((w.1 : GR n) * k1), w.2)) (g := fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) hV'c hpm'.continuousOn (fun w hw' => ⟨hSm' w.1, hw'.2⟩)`. Establish `hGc' : ContinuousOn (fun w : KR n × ℂ => Gk' w.1 w.2) (univ ×ˢ V')` using `((hw.comp continuous_fst).continuousOn).mul hc3`.

Establish `hGd' : ∀ k ∈ (univ : Set (KR n)), DifferentiableOn ℂ (Gk' k) V'` using `fun k _ => (hV'd _ (hSm' k)).const_mul _`. Take `⟨hψd, hψD⟩` from `hHP (KR n) μ univ hKc (by simp) V' Gk' hV'o hGc' hGd'`. Establish `step1 : sL Φ y' = ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * iteratedDeriv r (holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1))) 0 ∂μ`. Rewrite using `[← hly, hΦ (ly y')]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations.

Simplify using `only [hly]`. Rewrite using `[← hL.kact Qr y' _ (hKm k), ← (hD m n ε c t p q e sL ρ hL X a ha _ r).2]`. Establish `h3` using `hCrc (holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1))) V' hV'o hV'R (hV'd _ (hSm' k)) r 0`. Simplify using `only [Complex.ofReal_zero] at h3`. Rewrite using `[← h3]`.

Use `congr 2`. Use function extensionality and compare the values at `s`. Conclude with `(hAF0c n p q e X a ha _ s).symm`. Establish `step2 : (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * iteratedDeriv r (holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1))) 0 ∂μ) = iteratedDeriv r (fun z => ∫ k, Gk' k z ∂μ) 0`. Rewrite using `[hψD 0 h0V' r]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `only [Gk', iteratedDeriv_const_mul_field]`. Establish `step3 : iteratedDeriv r (fun z => ∫ k, Gk' k z ∂μ) 0 = iteratedDeriv r (fun t : ℝ => ∫ k, Gk' k t ∂μ) 0`. Establish `h3` using `hCrc _ V' hV'o hV'R hψd r 0`. Simplify using `only [Complex.ofReal_zero] at h3`.

Conclude with `h3.symm`. Establish `step4 : (fun t : ℝ => ∫ k, Gk' k t ∂μ) = fun t : ℝ => F0 p q e y' * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a t)) ∂μ`. Use function extensionality and compare the values at `t`. Rewrite using `[← hSph n p q e μ y' (k1 * a t)]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations.

Simplify using `only [Gk']`. Rewrite using `[hAF0c n p q e X a ha _ t]`. Simplify using `only [mul_assoc]`. Rewrite using `[step1, step2, step3, step4, iteratedDeriv_const_mul_field]`. Establish `hν : sL Φ 1 = D` using `by rw [hsL 1, hF01, one_mul]`.

Establish `hnull : NullSec ε c (Φ - D • 1)`. Use `(hSZ m n ε c t p q e sL ρ hL (Φ - D • 1)).mpr fun y' => ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hsL y', hL.vac y']`. Expand and normalize the polynomial expressions, which then agree. Establish `hLC'` using `hLC m n ε c hL.cpos lg (fun a b P => hG.Iinv g a b P) _ hnull`.

Rewrite `hLC'` using `[map_sub, map_smul, smul_eq_mul, hlg, hlg]`. Establish `hint1` using `integrable_of_cpt μ hKc (hcv lg)`. Establish `hint2` using `integrable_of_cpt μ hKc (hcv (ly 1))`. Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[hval k, hlg, hly]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = lg Φ - I 1 g * ly 1 Φ := by`. Rewrite using `[integral_sub hint1 (hint2.const_mul _), integral_const_mul, hΦ lg, hΦ (ly 1)]`.

Use `_ = 0 := by`. Rewrite using `[hlg, hly, hν]`. Take the linear combination `hLC'`. Establish `hz` using `hCzero (fun z => ∫ k, Gk k z ∂μ) (U ∩ V) (hUo.inter hVo) (fun s => ⟨hUR s, hVR s⟩) hφd hder 1`. Establish `hcI : Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (k1 * a 1)))` using `hw.mul (hG.Icont.comp (continuous_const.mul (hG.ιcont.comp (continuous_subtype_val.mul continuous_const))))`.

Establish `hcS : Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a 1))` using `hw.mul (hF0.comp (continuous_subtype_val.mul continuous_const))`. Establish `hz' : (∫ k : KR n, ((F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (k1 * a 1))) - I 1 g * ((F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a 1)))) ∂μ) = 0`. Rewrite using `[← hz]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Simplify using `only [Gk]`.

Rewrite using `[(hF _).2.1 1, hAF0c n p q e X a ha _ 1]`. Simplify using `only [mul_assoc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hz'` using `[integral_sub (integrable_of_cpt μ hKc hcI) ((integrable_of_cpt μ hKc hcS).const_mul _), integral_const_mul]`. Conclude with `sub_eq_zero.mp hz'`.

Take `⟨k1, k2, a1, X, hk1, hk2, hda1, rfl⟩` from `hKAK n y`. Take `⟨a, ha⟩` from `hAdil n X`. Establish `ha1 : a1 = a 1` using `hAuniq n X 1 a1 (a 1) hda1 (ha 1)`. Substitute `ha1` using the available equality. Rewrite using `[hRI _ k2 hk2, hRS _ k2 hk2, key k1 hk1 X a ha]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem thSph_of' (hA : HelpA) (hC : HelpC) (hKAK : KAK) (hMult : Mult) (hD : DerivativeVacuumDilations) (hSph : Sph)
    (hSZ : SecZero) (hHP : HolParam) (hLC : LC) : ThSph := by
  intro m n ε c t p q e sL ρ hL G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I Λ hG _ _ μ _ _ g y
  obtain ⟨hAdil, hAuniq, hAcpt, _hAdet, hAF0c, hAV, hAF0⟩ := hA
  obtain ⟨hCrc, hCzero⟩ := hC
  have hKc : IsCompact (univ : Set (KR n)) := hAcpt n
  have hF0 : Continuous (F0 (n := n) p q e) := (hAF0 n p q e).1
  have hF0ne : ∀ k : KR n, F0 p q e (k : GR n) ≠ 0 := fun k => (hAF0 n p q e).2 k k.2
  have hw : Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ := (hF0.comp continuous_subtype_val).inv₀ hF0ne
  have hF01 : F0 (n := n) p q e 1 = 1 := by
    have h := ((hMult n p q e).1 1 1 (KR n).one_mem).1
    rw [mul_one] at h
    have hne : F0 (n := n) p q e 1 ≠ 0 := by simpa using hF0ne 1
    exact mul_left_cancel₀ hne (by rw [mul_one]; exact h.symm)
  have hRI : ∀ (z k2 : GR n), k2 ∈ KR n →
      (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (z * k2))) ∂μ) =
        F0 p q e k2 * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * z)) ∂μ := by
    intro z k2 hk2
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have hk2' : InK (mR k2) := hk2
    have h1 : I 1 (g * ι ((k : GR n) * (z * k2))) = F0 p q e k2 * I 1 (g * ι ((k : GR n) * z)) := by
      rw [← mul_assoc, map_mul ι, ← mul_assoc g, hG.Ik 1 _ k2 hk2', hL.kvac k2 hk2', map_smul]
      rfl
    simp only [h1]
    ring
  have hRS : ∀ (z k2 : GR n), k2 ∈ KR n →
      (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (z * k2)) ∂μ) =
        F0 p q e k2 * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * z) ∂μ := by
    intro z k2 hk2
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [← mul_assoc, ((hMult n p q e).1 _ k2 hk2).1]
    ring
  have key : ∀ (k1 : GR n), k1 ∈ KR n → ∀ (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) →
      (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (k1 * a 1))) ∂μ) =
        I 1 g * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a 1)) ∂μ := by
    intro k1 hk1 X a ha
    obtain ⟨U, F, hUo, hUR, hFc, hF⟩ := hG.Idil g X a ha
    have hmc : Continuous fun k : KR n => (k : GR n) * k1 := continuous_subtype_val.mul continuous_const
    obtain ⟨V, hVo, hVR, hVc, hVd⟩ := hAV n p q e X _ (hKc.image hmc)
    have hKm : ∀ k : KR n, (k : GR n) * k1 ∈ KR n := fun k => (KR n).mul_mem k.2 hk1
    have hSm : ∀ k : KR n, (k : GR n) * k1 ∈ (fun k : KR n => (k : GR n) * k1) '' univ :=
      fun k => mem_image_of_mem _ (mem_univ _)
    have h0U : (0 : ℂ) ∈ U := by simpa using hUR 0
    have h0V : (0 : ℂ) ∈ V := by simpa using hVR 0
    set Q : PX m n := (dil c X ^ 0) 1 with hQ0
    let Gk : KR n → ℂ → ℂ := fun k z => (F0 p q e (k : GR n))⁻¹ *
      (F ((k : GR n) * k1) z - I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z)
    have hpm : Continuous fun w : KR n × ℂ => ((w.1 : GR n) * k1, w.2) :=
      (hmc.comp continuous_fst).prodMk continuous_snd
    have hc1 : ContinuousOn (fun w : KR n × ℂ => F ((w.1 : GR n) * k1) w.2) (univ ×ˢ (U ∩ V)) :=
      ContinuousOn.comp (f := fun w : KR n × ℂ => ((w.1 : GR n) * k1, w.2)) (g := fun y : GR n × ℂ => F y.1 y.2)
        hFc hpm.continuousOn (fun w hw' => ⟨mem_univ _, hw'.2.1⟩)
    have hc2 : ContinuousOn (fun w : KR n × ℂ => holomorphicSectionExtension p q e X ((w.1 : GR n) * k1) w.2) (univ ×ˢ (U ∩ V)) :=
      ContinuousOn.comp (f := fun w : KR n × ℂ => ((w.1 : GR n) * k1, w.2))
        (g := fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) hVc hpm.continuousOn (fun w hw' => ⟨hSm w.1, hw'.2.2⟩)
    have hGc : ContinuousOn (fun w : KR n × ℂ => Gk w.1 w.2) (univ ×ˢ (U ∩ V)) :=
      ((hw.comp continuous_fst).continuousOn).mul (hc1.sub (continuousOn_const.mul hc2))
    have hGd : ∀ k ∈ (univ : Set (KR n)), DifferentiableOn ℂ (Gk k) (U ∩ V) := by
      intro k _
      refine DifferentiableOn.const_mul (DifferentiableOn.sub ?_ (DifferentiableOn.const_mul ?_ _)) _
      · exact ((hF _).1).mono inter_subset_left
      · exact (hVd _ (hSm k)).mono inter_subset_right
    obtain ⟨hφd, hφD⟩ := hHP (KR n) μ univ hKc (by simp) (U ∩ V) Gk (hUo.inter hVo) hGc hGd
    have hder : ∀ r : ℕ, iteratedDeriv r (fun z => ∫ k, Gk k z ∂μ) 0 = 0 := by
      intro r
      rw [hφD 0 ⟨h0U, h0V⟩ r]
      set Qr : PX m n := (dil c X ^ r) 1 with hQr
      obtain ⟨W, hWf, hQW, hWst, hWc⟩ := hL.kfin Qr
      haveI := hWf
      have hvW : ∀ k : KR n, ρ ((k : GR n) * k1) Qr ∈ W := fun k => hWst _ (hKm k) Qr hQW
      have hvc : ∀ l : PX m n →ₗ[ℂ] ℂ, Continuous fun k : KR n => l (ρ ((k : GR n) * k1) Qr) := fun l =>
        (hWc Qr hQW l).comp_continuous hmc (fun k => hKm k)
      obtain ⟨Φ, hΦ⟩ := finInt μ hKc W (fun k : KR n => ρ ((k : GR n) * k1) Qr) hvW hvc _ hw

      have hval : ∀ k : KR n, iteratedDeriv r (Gk k) 0 = (F0 p q e (k : GR n))⁻¹ *
          (I (ρ ((k : GR n) * k1) Qr) g - I 1 g * sL (ρ ((k : GR n) * k1) Qr) 1) := by
        intro k
        have hcF : ContDiffAt ℂ r (F ((k : GR n) * k1)) 0 :=
          ((hF _).1.contDiffOn hUo).contDiffAt (hUo.mem_nhds h0U)
        have hcG : ContDiffAt ℂ r (fun z => I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z) 0 :=
          contDiffAt_const.mul (((hVd _ (hSm k)).contDiffOn hVo).contDiffAt (hVo.mem_nhds h0V))
        have e1 : iteratedDeriv r (Gk k) 0 = (F0 p q e (k : GR n))⁻¹ *
            iteratedDeriv r (fun z => F ((k : GR n) * k1) z - I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z) 0 := by
          simp only [Gk]
          rw [iteratedDeriv_const_mul_field]
        have e0 : (fun z => F ((k : GR n) * k1) z - I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z) =
            F ((k : GR n) * k1) - fun z => I 1 g * holomorphicSectionExtension p q e X ((k : GR n) * k1) z := rfl
        rw [e1, e0, iteratedDeriv_sub hcF hcG]
        simp only [iteratedDeriv_const_mul_field]
        rw [(hF _).2.2 r, hG.Ik Qr g _ (hKm k)]
        have e2 : iteratedDeriv r (holomorphicSectionExtension p q e X ((k : GR n) * k1)) 0 = sL (ρ ((k : GR n) * k1) Qr) 1 := by
          have h3 := hCrc (holomorphicSectionExtension p q e X ((k : GR n) * k1)) V hVo hVR (hVd _ (hSm k)) r 0
          simp only [Complex.ofReal_zero] at h3
          rw [← h3]
          have h4 : (fun t : ℝ => holomorphicSectionExtension p q e X ((k : GR n) * k1) t) = fun s => F0 p q e ((k : GR n) * k1 * a s) :=
            funext fun s => hAF0c n p q e X a ha _ s
          rw [h4, (hD m n ε c t p q e sL ρ hL X a ha _ r).2]
          rw [← hL.kact Qr 1 _ (hKm k), one_mul]
        rw [e2]
      let lg : PX m n →ₗ[ℂ] ℂ := (LinearMap.proj g).comp I
      let ly : GR n → PX m n →ₗ[ℂ] ℂ := fun y' => (LinearMap.proj y').comp sL
      have hlg : ∀ P, lg P = I P g := fun P => rfl
      have hly : ∀ y' P, ly y' P = sL P y' := fun y' P => rfl
      have hcv : ∀ l : PX m n →ₗ[ℂ] ℂ, Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ * l (ρ ((k : GR n) * k1) Qr) :=
        fun l => hw.mul (hvc l)

      set D : ℂ := iteratedDeriv r (fun s : ℝ => ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ *
        F0 p q e ((k : GR n) * (k1 * a s)) ∂μ) 0 with hDdef
      have hsL : ∀ y' : GR n, sL Φ y' = F0 p q e y' * D := by
        intro y'
        have hm' : Continuous fun k : KR n => y' * ((k : GR n) * k1) := continuous_const.mul hmc
        obtain ⟨V', hV'o, hV'R, hV'c, hV'd⟩ := hAV n p q e X _ (hKc.image hm')
        have hSm' : ∀ k : KR n, y' * ((k : GR n) * k1) ∈ (fun k : KR n => y' * ((k : GR n) * k1)) '' univ :=
          fun k => mem_image_of_mem _ (mem_univ _)
        have h0V' : (0 : ℂ) ∈ V' := by simpa using hV'R 0
        let Gk' : KR n → ℂ → ℂ := fun k z => (F0 p q e (k : GR n))⁻¹ * holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1)) z
        have hpm' : Continuous fun w : KR n × ℂ => (y' * ((w.1 : GR n) * k1), w.2) :=
          (hm'.comp continuous_fst).prodMk continuous_snd
        have hc3 : ContinuousOn (fun w : KR n × ℂ => holomorphicSectionExtension p q e X (y' * ((w.1 : GR n) * k1)) w.2) (univ ×ˢ V') :=
          ContinuousOn.comp (f := fun w : KR n × ℂ => (y' * ((w.1 : GR n) * k1), w.2))
            (g := fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) hV'c hpm'.continuousOn (fun w hw' => ⟨hSm' w.1, hw'.2⟩)
        have hGc' : ContinuousOn (fun w : KR n × ℂ => Gk' w.1 w.2) (univ ×ˢ V') :=
          ((hw.comp continuous_fst).continuousOn).mul hc3
        have hGd' : ∀ k ∈ (univ : Set (KR n)), DifferentiableOn ℂ (Gk' k) V' := fun k _ =>
          (hV'd _ (hSm' k)).const_mul _
        obtain ⟨hψd, hψD⟩ := hHP (KR n) μ univ hKc (by simp) V' Gk' hV'o hGc' hGd'
        have step1 : sL Φ y' = ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ *
            iteratedDeriv r (holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1))) 0 ∂μ := by
          rw [← hly, hΦ (ly y')]
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [hly]
          rw [← hL.kact Qr y' _ (hKm k), ← (hD m n ε c t p q e sL ρ hL X a ha _ r).2]
          have h3 := hCrc (holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1))) V' hV'o hV'R (hV'd _ (hSm' k)) r 0
          simp only [Complex.ofReal_zero] at h3
          rw [← h3]
          congr 2
          funext s
          exact (hAF0c n p q e X a ha _ s).symm
        have step2 : (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ *
            iteratedDeriv r (holomorphicSectionExtension p q e X (y' * ((k : GR n) * k1))) 0 ∂μ) =
            iteratedDeriv r (fun z => ∫ k, Gk' k z ∂μ) 0 := by
          rw [hψD 0 h0V' r]
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [Gk', iteratedDeriv_const_mul_field]
        have step3 : iteratedDeriv r (fun z => ∫ k, Gk' k z ∂μ) 0 =
            iteratedDeriv r (fun t : ℝ => ∫ k, Gk' k t ∂μ) 0 := by
          have h3 := hCrc _ V' hV'o hV'R hψd r 0
          simp only [Complex.ofReal_zero] at h3
          exact h3.symm
        have step4 : (fun t : ℝ => ∫ k, Gk' k t ∂μ) = fun t : ℝ => F0 p q e y' *
            ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a t)) ∂μ := by
          funext t
          rw [← hSph n p q e μ y' (k1 * a t)]
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [Gk']
          rw [hAF0c n p q e X a ha _ t]
          simp only [mul_assoc]
        rw [step1, step2, step3, step4, iteratedDeriv_const_mul_field]
      have hν : sL Φ 1 = D := by rw [hsL 1, hF01, one_mul]
      have hnull : NullSec ε c (Φ - D • 1) := by
        refine (hSZ m n ε c t p q e sL ρ hL (Φ - D • 1)).mpr fun y' => ?_
        rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hsL y', hL.vac y']
        ring
      have hLC' := hLC m n ε c hL.cpos lg (fun a b P => hG.Iinv g a b P) _ hnull
      rw [map_sub, map_smul, smul_eq_mul, hlg, hlg] at hLC'
      have hint1 := integrable_of_cpt μ hKc (hcv lg)
      have hint2 := integrable_of_cpt μ hKc (hcv (ly 1))
      calc (∫ k : KR n, iteratedDeriv r (Gk k) 0 ∂μ)
          = ∫ k : KR n, ((F0 p q e (k : GR n))⁻¹ * lg (ρ ((k : GR n) * k1) Qr) -
              I 1 g * ((F0 p q e (k : GR n))⁻¹ * ly 1 (ρ ((k : GR n) * k1) Qr))) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
            dsimp only
            rw [hval k, hlg, hly]
            ring
        _ = lg Φ - I 1 g * ly 1 Φ := by
            rw [integral_sub hint1 (hint2.const_mul _), integral_const_mul, hΦ lg, hΦ (ly 1)]
        _ = 0 := by
            rw [hlg, hly, hν]
            linear_combination hLC'
    have hz := hCzero (fun z => ∫ k, Gk k z ∂μ) (U ∩ V) (hUo.inter hVo) (fun s => ⟨hUR s, hVR s⟩) hφd hder 1
    have hcI : Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (k1 * a 1))) :=
      hw.mul (hG.Icont.comp (continuous_const.mul (hG.ιcont.comp (continuous_subtype_val.mul continuous_const))))
    have hcS : Continuous fun k : KR n => (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a 1)) :=
      hw.mul (hF0.comp (continuous_subtype_val.mul continuous_const))
    have hz' : (∫ k : KR n, ((F0 p q e (k : GR n))⁻¹ * I 1 (g * ι ((k : GR n) * (k1 * a 1))) -
        I 1 g * ((F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (k1 * a 1)))) ∂μ) = 0 := by
      rw [← hz]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [Gk]
      rw [(hF _).2.1 1, hAF0c n p q e X a ha _ 1]
      simp only [mul_assoc]
      ring
    rw [integral_sub (integrable_of_cpt μ hKc hcI) ((integrable_of_cpt μ hKc hcS).const_mul _),
      integral_const_mul] at hz'
    exact sub_eq_zero.mp hz'
  obtain ⟨k1, k2, a1, X, hk1, hk2, hda1, rfl⟩ := hKAK n y
  obtain ⟨a, ha⟩ := hAdil n X
  have ha1 : a1 = a 1 := hAuniq n X 1 a1 (a 1) hda1 (ha 1)
  subst ha1
  rw [hRI _ k2 hk2, hRS _ k2 hk2, key k1 hk1 X a ha]
  ring

end PositivityTheory.Rg.Sw.AbsSt
