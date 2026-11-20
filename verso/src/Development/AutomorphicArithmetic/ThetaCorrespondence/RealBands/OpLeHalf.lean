import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Transl

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ N a H f hR hf`. Establish `hU` using `transl_small G μ f hf 1 one_pos`. Establish `a0 : a 0 = 1`. Use `hR.add 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`.

Conclude with `(mul_eq_left.mp this.symm)`. Take `⟨D, hD, hk⟩` from `hR.cpt`. Establish `hc : Continuous fun p : ℝ × G => p.2 * a p.1 * p.2⁻¹` using `(continuous_snd.mul (hR.cont.comp continuous_fst)).mul continuous_snd.inv`. Establish `hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ k ∈ D, ∫ g, ‖f ((k * a t * k⁻¹) * g) - f g‖ ∂μ ≤ 1`. Apply `hD.eventually_forall_of_forall_eventually` to reduce the goal to its premises.

Introduce `k _`. Establish `ht : Tendsto (fun p : ℝ × G => p.2 * a p.1 * p.2⁻¹) (𝓝 (0, k)) (𝓝 1)`. Use `hc.tendsto (0, k)` as an intermediate fact. Simplify `this` using `[a0]`. Conclude with `ht.eventually hU`.

Establish `hev' : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k ∈ D, ∫ g, ‖f ((k * a t * k⁻¹) * g) - f g‖ ∂μ ≤ 1` using `hev.filter_mono nhdsWithin_le_nhds`. Take `⟨t, ht, htpos⟩` from `(hev'.and self_mem_nhdsWithin).exists`. Establish `htpos : 0 < t` using `htpos`. Use `⟨Real.pi / t, ?_⟩` and prove the remaining obligations. Introduce and unpack `C h ⟨hcont, hbd, hN, hE⟩ x`.

Take `⟨k, hkD, hk⟩` from `hk x`. Take `⟨m, hm, hkm⟩` from `hk t`. Establish `hb` using `ht k hkD`. Use `set b := k * a t * k⁻¹ with hbdef`. Establish `hneg : ∀ g, h (g⁻¹ * b * x) = - h (g⁻¹ * x)`.

Introduce `g`. Establish `e : g⁻¹ * b * x = g⁻¹ * x * a t * m`. Rewrite using `[mul_assoc, hkm]`. Simplify using `only [mul_assoc]`. Rewrite using `[e, hN _ m hm, hE]`.

Establish `: Real.pi / t * t = Real.pi` using `by field_simp`. Rewrite using `[this, Complex.exp_pi_mul_I]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ∫ g, f (b * g) * h (g⁻¹ * x) ∂μ = - conv μ f h x`. Use `integral_mul_left_eq_self (μ := μ) (fun g => f g * h (g⁻¹ * b * x)) b` as an intermediate fact.

Simplify using `only [mul_inv_rev, inv_mul_cancel_right] at this`. Rewrite using `[this, conv, ← integral_neg]`. Use `congr 1`. Use extensionality with `g`. Rewrite using `[hneg]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hfb : Integrable (fun g => f (b * g)) μ` using `hf.comp_mul_left b`. Establish `hmeas : AEStronglyMeasurable (fun g => h (g⁻¹ * x)) μ` using `(hcont.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable`. Establish `i1 : Integrable (fun g => f (b * g) * h (g⁻¹ * x)) μ` using `hfb.mul_bdd hmeas (Eventually.of_forall fun g => hbd _)`. Establish `i2 : Integrable (fun g => f g * h (g⁻¹ * x)) μ` using `hf.mul_bdd hmeas (Eventually.of_forall fun g => hbd _)`.

Establish `h2 : ∫ g, (f (b * g) - f g) * h (g⁻¹ * x) ∂μ = -2 * conv μ f h x`. Simplify using `only [sub_mul]`. Rewrite using `[integral_sub i1 i2, h1, conv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hC : 0 ≤ C` using `(norm_nonneg _).trans (hbd 1)`.

Establish `h3 : ‖∫ g, (f (b * g) - f g) * h (g⁻¹ * x) ∂μ‖ ≤ C`. Combine the equalities or inequalities in the displayed calculation. Apply `norm_integral_le_of_norm_le ((hfb.sub hf).norm.mul_const C)` to reduce the goal to its premises. Use `Eventually.of_forall fun g => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_left (hbd _) (norm_nonneg _)`. Use `_ = (∫ g, ‖f (b * g) - f g‖ ∂μ) * C := integral_mul_const _ _`. Use `_ ≤ 1 * C := mul_le_mul_of_nonneg_right hb hC`. Use `_ = C := one_mul C`. Rewrite `h3` using `[h2, norm_mul]`.

Simplify using `at h3`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.Lit.Cusp.opLe_half :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (f : G → ℂ),
      IsRay N a H → Integrable f μ → ∃ s : ℝ, OpLe μ N a f s (1 / 2) := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H f hR hf
  have hU := transl_small G μ f hf 1 one_pos
  have a0 : a 0 = 1 := by
    have := hR.add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  obtain ⟨D, hD, hk⟩ := hR.cpt
  have hc : Continuous fun p : ℝ × G => p.2 * a p.1 * p.2⁻¹ :=
    (continuous_snd.mul (hR.cont.comp continuous_fst)).mul continuous_snd.inv
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ k ∈ D, ∫ g, ‖f ((k * a t * k⁻¹) * g) - f g‖ ∂μ ≤ 1 := by
    apply hD.eventually_forall_of_forall_eventually
    intro k _
    have ht : Tendsto (fun p : ℝ × G => p.2 * a p.1 * p.2⁻¹) (𝓝 (0, k)) (𝓝 1) := by
      have := hc.tendsto (0, k)
      simpa [a0] using this
    exact ht.eventually hU
  have hev' : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k ∈ D, ∫ g, ‖f ((k * a t * k⁻¹) * g) - f g‖ ∂μ ≤ 1 :=
    hev.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, htpos⟩ := (hev'.and self_mem_nhdsWithin).exists
  have htpos : 0 < t := htpos
  refine ⟨Real.pi / t, ?_⟩
  rintro C h ⟨hcont, hbd, hN, hE⟩ x
  obtain ⟨k, hkD, hk⟩ := hk x
  obtain ⟨m, hm, hkm⟩ := hk t
  have hb := ht k hkD
  set b := k * a t * k⁻¹ with hbdef
  have hneg : ∀ g, h (g⁻¹ * b * x) = - h (g⁻¹ * x) := by
    intro g
    have e : g⁻¹ * b * x = g⁻¹ * x * a t * m := by
      rw [mul_assoc, hkm]; simp only [mul_assoc]
    rw [e, hN _ m hm, hE]
    have : Real.pi / t * t = Real.pi := by field_simp
    rw [this, Complex.exp_pi_mul_I]; ring
  have h1 : ∫ g, f (b * g) * h (g⁻¹ * x) ∂μ = - conv μ f h x := by
    have := integral_mul_left_eq_self (μ := μ) (fun g => f g * h (g⁻¹ * b * x)) b
    simp only [mul_inv_rev, inv_mul_cancel_right] at this
    rw [this, conv, ← integral_neg]
    congr 1
    ext g
    rw [hneg]; ring
  have hfb : Integrable (fun g => f (b * g)) μ := hf.comp_mul_left b
  have hmeas : AEStronglyMeasurable (fun g => h (g⁻¹ * x)) μ :=
    (hcont.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable
  have i1 : Integrable (fun g => f (b * g) * h (g⁻¹ * x)) μ :=
    hfb.mul_bdd hmeas (Eventually.of_forall fun g => hbd _)
  have i2 : Integrable (fun g => f g * h (g⁻¹ * x)) μ :=
    hf.mul_bdd hmeas (Eventually.of_forall fun g => hbd _)
  have h2 : ∫ g, (f (b * g) - f g) * h (g⁻¹ * x) ∂μ = -2 * conv μ f h x := by
    simp only [sub_mul]
    rw [integral_sub i1 i2, h1, conv]; ring
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbd 1)
  have h3 : ‖∫ g, (f (b * g) - f g) * h (g⁻¹ * x) ∂μ‖ ≤ C := by
    calc _ ≤ ∫ g, ‖f (b * g) - f g‖ * C ∂μ := by
          apply norm_integral_le_of_norm_le ((hfb.sub hf).norm.mul_const C)
          refine Eventually.of_forall fun g => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hbd _) (norm_nonneg _)
      _ = (∫ g, ‖f (b * g) - f g‖ ∂μ) * C := integral_mul_const _ _
      _ ≤ 1 * C := mul_le_mul_of_nonneg_right hb hC
      _ = C := one_mul C
  rw [h2, norm_mul] at h3
  simp at h3
  linarith
