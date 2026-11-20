import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepresentationUnitaryMulContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SecondCountableFiniteAdelicUnitaryPoints

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.WeakConv

section General

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (μ : Measure G) (π : G → (H →L[ℂ] H))

def IsWeakInt (e : G → ℂ) (T : H →L[ℂ] H) : Prop :=
  Integrable e μ ∧ ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ

variable {μ π}

/- English proof (translation)
Use `Integrable.mono' (hf.norm.mul_const C) (hf.aestronglyMeasurable.mul hc) (ae_of_all _ fun a => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hb a) (norm_nonneg _)`.
-/
private theorem integrable_mul_of_bounded {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f c : α → ℂ} (hf : Integrable f ν) (hc : AEStronglyMeasurable c ν) (C : ℝ)
    (hb : ∀ a, ‖c a‖ ≤ C) : Integrable (fun a => f a * c a) ν := by
  refine Integrable.mono' (hf.norm.mul_const C) (hf.aestronglyMeasurable.mul hc) (ae_of_all _ fun a => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb a) (norm_nonneg _)

omit [Group G] [IsTopologicalGroup G] [SecondCountableTopology G] [CompleteSpace H] in

/- English proof (translation)
Establish `hcm : Continuous fun g => ⟪x, π g y⟫_ℂ` using `continuous_const.inner (hc y)`. Use `integrable_mul_of_bounded he hcm.aestronglyMeasurable (‖x‖ * ‖y‖) fun g => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem integrable_mul_coeff (hn : ∀ g y, ‖π g y‖ = ‖y‖) (hc : ∀ y, Continuous fun g => π g y)
    {e : G → ℂ} (he : Integrable e μ) (x y : H) :
    Integrable (fun g => e g * ⟪x, π g y⟫_ℂ) μ := by
  have hcm : Continuous fun g => ⟪x, π g y⟫_ℂ := continuous_const.inner (hc y)
  refine integrable_mul_of_bounded he hcm.aestronglyMeasurable (‖x‖ * ‖y‖) fun g => ?_
  calc ‖⟪x, π g y⟫_ℂ‖ ≤ ‖x‖ * ‖π g y‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * ‖y‖ := by rw [hn]

omit [Group G] [IsTopologicalGroup G] [SecondCountableTopology G] [TopologicalSpace G] [BorelSpace G] in

/- English proof (translation)
Rewrite using `[← ContinuousLinearMap.adjoint_inner_left, h.2]`. Repeatedly rewrite using `[ContinuousLinearMap.adjoint_inner_left]`.
-/
theorem IsWeakInt.inner_comp {e : G → ℂ} {T : H →L[ℂ] H} (h : IsWeakInt μ π e T) (A : H →L[ℂ] H)
    (x y : H) : ⟪x, A (T y)⟫_ℂ = ∫ g, e g * ⟪x, A (π g y)⟫_ℂ ∂μ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, h.2]
  simp_rw [ContinuousLinearMap.adjoint_inner_left]

/- English proof (translation)
Establish `hP : Integrable (fun z : G × G => e z.1 * e' (z.1⁻¹ * z.2)) (μ.prod μ)`. Establish `h0 : Integrable (fun z : G × G => e z.1 * e' z.2) (μ.prod μ)` using `h.1.mul_prod h'.1`. Conclude with `((measurePreserving_prod_inv_mul μ μ).integrable_comp h0.aestronglyMeasurable).2 h0`. Use `⟨hP.integral_prod_right, fun x y => ?_⟩` and prove the remaining obligations. Establish `hcm : Continuous fun k => ⟪x, π k y⟫_ℂ` using `continuous_const.inner (hc y)`.

Establish `hcm2 : Measurable fun z : G × G => ⟪x, π z.2 y⟫_ℂ` using `hcm.measurable.comp measurable_snd`. Establish `hQ : Integrable (fun z : G × G => e z.1 * e' (z.1⁻¹ * z.2) * ⟪x, π z.2 y⟫_ℂ) (μ.prod μ)`. Use `integrable_mul_of_bounded hP hcm2.aestronglyMeasurable (‖x‖ * ‖y‖) fun z => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hin : ∀ g, ⟪x, π g (T' y)⟫_ℂ = ∫ k, e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ ∂μ`.

Introduce `g`. Rewrite using `[h'.inner_comp (π g) x y]`. Use `(integral_mul_left_eq_self _ g⁻¹).symm.trans ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `k`.

Establish `hk : π g (π (g⁻¹ * k) y) = π k y`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← hm, mul_inv_cancel_left]`. Simplify using `only [hk]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Use extensionality with `g`. Rewrite using `[hin, ← integral_const_mul]`. Use `congr 1`. Use extensionality with `k`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = ∫ k, ∫ g, e g * e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ ∂μ ∂μ := integral_integral_swap (f := fun g k => e g * e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ) hQ`. Use `_ = ∫ k, (∫ g, e g * e' (g⁻¹ * k) ∂μ) * ⟪x, π k y⟫_ℂ ∂μ := by`. Use `congr 1`. Use extensionality with `k`. Rewrite using `[integral_mul_const]`.
-/
theorem IsWeakInt.conv [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (hm : ∀ g h, π (g * h) = (π g).comp (π h))
    (hn : ∀ g y, ‖π g y‖ = ‖y‖) (hc : ∀ y, Continuous fun g => π g y)
    {e e' : G → ℂ} {T T' : H →L[ℂ] H} (h : IsWeakInt μ π e T) (h' : IsWeakInt μ π e' T') :
    IsWeakInt μ π (fun k => ∫ g, e g * e' (g⁻¹ * k) ∂μ) (T.comp T') := by
  have hP : Integrable (fun z : G × G => e z.1 * e' (z.1⁻¹ * z.2)) (μ.prod μ) := by
    have h0 : Integrable (fun z : G × G => e z.1 * e' z.2) (μ.prod μ) := h.1.mul_prod h'.1
    exact ((measurePreserving_prod_inv_mul μ μ).integrable_comp h0.aestronglyMeasurable).2 h0
  refine ⟨hP.integral_prod_right, fun x y => ?_⟩
  have hcm : Continuous fun k => ⟪x, π k y⟫_ℂ := continuous_const.inner (hc y)
  have hcm2 : Measurable fun z : G × G => ⟪x, π z.2 y⟫_ℂ := hcm.measurable.comp measurable_snd
  have hQ : Integrable (fun z : G × G => e z.1 * e' (z.1⁻¹ * z.2) * ⟪x, π z.2 y⟫_ℂ) (μ.prod μ) := by
    refine integrable_mul_of_bounded hP hcm2.aestronglyMeasurable (‖x‖ * ‖y‖) fun z => ?_
    calc ‖⟪x, π z.2 y⟫_ℂ‖ ≤ ‖x‖ * ‖π z.2 y‖ := norm_inner_le_norm _ _
      _ = ‖x‖ * ‖y‖ := by rw [hn]
  have hin : ∀ g, ⟪x, π g (T' y)⟫_ℂ = ∫ k, e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ ∂μ := by
    intro g
    rw [h'.inner_comp (π g) x y]
    refine (integral_mul_left_eq_self _ g⁻¹).symm.trans ?_
    congr 1
    ext k
    have hk : π g (π (g⁻¹ * k) y) = π k y := by
      rw [← ContinuousLinearMap.comp_apply, ← hm, mul_inv_cancel_left]
    simp only [hk]
  calc ⟪x, (T.comp T') y⟫_ℂ = ∫ g, e g * ⟪x, π g (T' y)⟫_ℂ ∂μ := h.2 x (T' y)
    _ = ∫ g, ∫ k, e g * e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ ∂μ ∂μ := by
        congr 1
        ext g
        rw [hin, ← integral_const_mul]
        congr 1
        ext k
        ring
    _ = ∫ k, ∫ g, e g * e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ ∂μ ∂μ :=
        integral_integral_swap (f := fun g k => e g * e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ) hQ
    _ = ∫ k, (∫ g, e g * e' (g⁻¹ * k) ∂μ) * ⟪x, π k y⟫_ℂ ∂μ := by
        congr 1
        ext k
        rw [integral_mul_const]

end General

/- English proof (translation)
Introduce `I μf hH hS fund R hfund hR`. Take `⟨-, hmul, hn, hc⟩` from `GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous I μf fund hfund R hR`. Use `GlobalTheory.CongTop.secondCountable_finiteAdelicPoints I` as an intermediate fact. Establish `hm' : ∀ g h : I.Gf, R (1, g * h) = (R (1, g)).comp (R (1, h))`. Introduce `g h`.

Rewrite using `[← hmul, Prod.mk_mul_mk, one_mul]`. Establish `hn' : ∀ (g : I.Gf) (F : I.L2 μf fund), ‖R (1, g) F‖ = ‖F‖` using `fun g F => hn _ F`. Establish `hc' : ∀ F : I.L2 μf fund, Continuous fun g : I.Gf => R (1, g) F` using `fun F => Continuous.comp (g := fun x : I.GA => R x F) (f := fun g : I.Gf => ((1 : I.Ginf), g)) (hc F) (continuous_const.prodMk continuous_id)`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `e T T' h h'`.

Use `ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun z => ?_` and prove the remaining obligations. Rewrite using `[h.2, h'.2]`. Introduce `e e' T T' h h'`. Use `⟨h.1.add h'.1, fun z y => ?_⟩` and prove the remaining obligations. Establish `i1` using `integrable_mul_coeff (μ := μf) (π := fun g : I.Gf => R (1, g)) hn' hc' h.1 z y`.

Establish `i2` using `integrable_mul_coeff (μ := μf) (π := fun g : I.Gf => R (1, g)) hn' hc' h'.1 z y`. Rewrite using `[ContinuousLinearMap.add_apply, inner_add_right, h.2, h'.2, ← integral_add i1 i2]`. Use `congr 1`. Use extensionality with `g`. Simplify using `only [Pi.add_apply]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `c e T h`. Use `⟨h.1.smul c, fun z y => ?_⟩` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.smul_apply, inner_smul_right, h.2, ← integral_const_mul]`. Use `congr 1`.

Use extensionality with `g`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `e e' T T' _ _ h h'`. Conclude with `IsWeakInt.conv (μ := μf) (π := fun g : I.Gf => R (1, g)) hm' hn' hc' h h'`.

Introduce `e T x h`. Use `ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun z => ?_` and prove the remaining obligations. Establish `hcomm : ∀ g : I.Gf, R (1, g) (R (x, 1) y) = R (x, 1) (R (1, g) y)`. Introduce `g`. Establish `key : R ((1, g) * (x, 1)) = R ((x, 1) * (1, g))`.

Use `congr 1`. Simplify using the standard rewrite rules. Rewrite `key` using `[hmul, hmul]`. Conclude with `congrArg (fun A : I.L2 μf fund →L[ℂ] I.L2 μf fund => A y) key`. Rewrite using `[ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h.2 z (R (x, 1) y), IsWeakInt.inner_comp (μ := μf) (π := fun g : I.Gf => R (1, g)) h (R (x, 1)) z y]`.

Simplify using `only [hcomm]`.
-/
theorem rightConv_unique_add_smul_mul_comm : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)), I.IsFundDom (I.muA μf) fund → I.IsRightReg μf fund R → (∀ e T T', I.IsRConvF μf fund R e T → I.IsRConvF μf fund R e T' → T = T') ∧ (∀ e e' T T', I.IsRConvF μf fund R e T → I.IsRConvF μf fund R e' T' → I.IsRConvF μf fund R (e + e') (T + T')) ∧ (∀ (c : ℂ) e T, I.IsRConvF μf fund R e T → I.IsRConvF μf fund R (c • e) (c • T)) ∧ (∀ e e' T T', Continuous e → Continuous e' → I.IsRConvF μf fund R e T → I.IsRConvF μf fund R e' T' → I.IsRConvF μf fund R (I.convF μf e e') (T.comp T')) ∧ ∀ e T (x : I.Ginf), I.IsRConvF μf fund R e T → T.comp (R (x, 1)) = (R (x, 1)).comp T := by
  intro I μf hH hS fund R hfund hR
  obtain ⟨-, hmul, hn, hc⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous I μf fund hfund R hR
  have := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints I
  have hm' : ∀ g h : I.Gf, R (1, g * h) = (R (1, g)).comp (R (1, h)) := by
    intro g h
    rw [← hmul, Prod.mk_mul_mk, one_mul]
  have hn' : ∀ (g : I.Gf) (F : I.L2 μf fund), ‖R (1, g) F‖ = ‖F‖ := fun g F => hn _ F
  have hc' : ∀ F : I.L2 μf fund, Continuous fun g : I.Gf => R (1, g) F := fun F =>
    Continuous.comp (g := fun x : I.GA => R x F) (f := fun g : I.Gf => ((1 : I.Ginf), g)) (hc F)
      (continuous_const.prodMk continuous_id)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e T T' h h'
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun z => ?_
    rw [h.2, h'.2]
  · intro e e' T T' h h'
    refine ⟨h.1.add h'.1, fun z y => ?_⟩
    have i1 := integrable_mul_coeff (μ := μf) (π := fun g : I.Gf => R (1, g)) hn' hc' h.1 z y
    have i2 := integrable_mul_coeff (μ := μf) (π := fun g : I.Gf => R (1, g)) hn' hc' h'.1 z y
    rw [ContinuousLinearMap.add_apply, inner_add_right, h.2, h'.2, ← integral_add i1 i2]
    congr 1
    ext g
    simp only [Pi.add_apply]
    ring
  · intro c e T h
    refine ⟨h.1.smul c, fun z y => ?_⟩
    rw [ContinuousLinearMap.smul_apply, inner_smul_right, h.2, ← integral_const_mul]
    congr 1
    ext g
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro e e' T T' _ _ h h'
    exact IsWeakInt.conv (μ := μf) (π := fun g : I.Gf => R (1, g)) hm' hn' hc' h h'
  · intro e T x h
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun z => ?_
    have hcomm : ∀ g : I.Gf, R (1, g) (R (x, 1) y) = R (x, 1) (R (1, g) y) := by
      intro g
      have key : R ((1, g) * (x, 1)) = R ((x, 1) * (1, g)) := by
        congr 1
        simp
      rw [hmul, hmul] at key
      exact congrArg (fun A : I.L2 μf fund →L[ℂ] I.L2 μf fund => A y) key
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h.2 z (R (x, 1) y),
      IsWeakInt.inner_comp (μ := μf) (π := fun g : I.Gf => R (1, g)) h (R (x, 1)) z y]
    simp only [hcomm]

end GlobalTheory.WeakConv
