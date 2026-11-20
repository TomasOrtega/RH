import Mathlib

noncomputable section

namespace PositivityTheory.ThKF.L2

open MeasureTheory
open scoped ComplexConjugate Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}

def Inv (Γ : Subgroup G) (F : G → ℂ) : Prop := ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x

/- English proof (translation)
Use `h.smul_of_comm (MulOpposite.op g)` as an intermediate fact. Simplify `this` using `[← Set.image_smul]`.
-/
theorem fd_right (h : IsFundamentalDomain Γ 𝓕 μ) (g : G) : IsFundamentalDomain Γ ((fun x => x * g) '' 𝓕) μ := by
  have := h.smul_of_comm (MulOpposite.op g)
  simpa [← Set.image_smul] using this

/- English proof (translation)
The claim follows from `(Homeomorph.mulRight g).measurableEmbedding`.
-/
theorem emb (g : G) : MeasurableEmbedding fun x : G => x * g := (Homeomorph.mulRight g).measurableEmbedding

/- English proof (translation)
Rewrite using `[← (measurePreserving_mul_right μ g).setIntegral_image_emb (emb g) F 𝓕]`. Conclude with `(fd_right h g).setIntegral_eq h fun γ x => hF γ γ.2 x`.
-/
theorem integral_right {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : IsFundamentalDomain Γ 𝓕 μ) (F : G → E)
    (hF : ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) (g : G) : ∫ x in 𝓕, F (x * g) ∂μ = ∫ x in 𝓕, F x ∂μ := by
  rw [← (measurePreserving_mul_right μ g).setIntegral_image_emb (emb g) F 𝓕]
  exact (fd_right h g).setIntegral_eq h fun γ x => hF γ γ.2 x

/- English proof (translation)
Establish `h1 : IntegrableOn F ((fun x => x * g) '' 𝓕) μ` using `((fd_right h g).integrableOn_iff h fun γ x => hF γ γ.2 x).2 hi`. Conclude with `((measurePreserving_mul_right μ g).integrableOn_image (emb g)).1 h1`.
-/
theorem integrableOn_right {E : Type} [NormedAddCommGroup E] (h : IsFundamentalDomain Γ 𝓕 μ) (F : G → E)
    (hF : ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) (hi : IntegrableOn F 𝓕 μ) (g : G) : IntegrableOn (fun x => F (x * g)) 𝓕 μ := by
  have h1 : IntegrableOn F ((fun x => x * g) '' 𝓕) μ :=
    ((fd_right h g).integrableOn_iff h fun γ x => hF γ γ.2 x).2 hi
  exact ((measurePreserving_mul_right μ g).integrableOn_image (emb g)).1 h1

omit [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [Countable Γ] [IsTopologicalGroup G] [Group G] in
/- English proof (translation)
Use `Integrable.mono' (f2.add g2) ((Complex.continuous_conj.comp hf).mul hg).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [norm_mul, Complex.norm_conj, Pi.add_apply]`. Use polynomial arithmetic with `[sq_nonneg (‖f x‖ - ‖g x‖), norm_nonneg (f x), norm_nonneg (g x)]`.
-/
theorem integrableOn_mul {f g : G → ℂ} (hf : Continuous f) (hg : Continuous g)
    (f2 : IntegrableOn (fun x => ‖f x‖ ^ 2) 𝓕 μ) (g2 : IntegrableOn (fun x => ‖g x‖ ^ 2) 𝓕 μ) :
    IntegrableOn (fun x => conj (f x) * g x) 𝓕 μ := by
  refine Integrable.mono' (f2.add g2) ((Complex.continuous_conj.comp hf).mul hg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_mul, Complex.norm_conj, Pi.add_apply]
  nlinarith [sq_nonneg (‖f x‖ - ‖g x‖), norm_nonneg (f x), norm_nonneg (g x)]

/- English proof (translation)
The claim follows from `integral_right h (fun x => conj (f x) * g x) (fun γ hγ x => by rw [hf γ hγ, hg γ hγ]) a`.
-/
theorem form_right (h : IsFundamentalDomain Γ 𝓕 μ) {f g : G → ℂ} (hf : Inv Γ f) (hg : Inv Γ g) (a : G) :
    ∫ x in 𝓕, conj (f (x * a)) * g (x * a) ∂μ = ∫ x in 𝓕, conj (f x) * g x ∂μ :=
  integral_right h (fun x => conj (f x) * g x) (fun γ hγ x => by rw [hf γ hγ, hg γ hγ]) a

omit [μ.IsMulRightInvariant] in
/- English proof (translation)
Establish `e : ∫ x in 𝓕, conj (f x) * f x ∂μ = ((∫ x in 𝓕, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ)`. Rewrite using `[← integral_complex_ofReal]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `[Complex.conj_mul']`. Rewrite `h0` using `[e, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg (fun x => by positivity) f2]`.

Establish `hm : MeasurableSet {x | f x ≠ 0}` using `(isOpen_ne_fun hc continuous_const).measurableSet`. Establish `h1 : μ ({x | f x ≠ 0} ∩ 𝓕) = 0`. Rewrite using `[← Measure.restrict_apply hm]`. Use `measure_mono_null (fun x hx => ?_) (ae_iff.1 h0)` and prove the remaining obligations. Simplify using `using hx`.

Establish `h2 : μ {x | f x ≠ 0} = 0` using `h.measure_zero_of_invariant _ (fun γ => by`. Use extensionality with `x`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Express the relevant statement in the definitionally equal form `f ((γ⁻¹ : Γ) * x) ≠ 0 ↔ f x ≠ 0`. Rewrite using `[hf _ (γ⁻¹).2]) h1`.

Establish `h3` using `(isOpen_ne_fun hc continuous_const).eq_empty_of_measure_zero h2`. Use function extensionality and compare the values at `x`. Assume the negation of the conclusion as `hx`. Conclude with `(h3 ▸ hx : x ∈ (∅ : Set G))`.
-/
theorem eq_zero (h : IsFundamentalDomain Γ 𝓕 μ) {f : G → ℂ} (hc : Continuous f) (hf : Inv Γ f)
    (f2 : IntegrableOn (fun x => ‖f x‖ ^ 2) 𝓕 μ) (h0 : ∫ x in 𝓕, conj (f x) * f x ∂μ = 0) : f = 0 := by
  have e : ∫ x in 𝓕, conj (f x) * f x ∂μ = ((∫ x in 𝓕, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.conj_mul']
  rw [e, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg (fun x => by positivity) f2] at h0
  have hm : MeasurableSet {x | f x ≠ 0} := (isOpen_ne_fun hc continuous_const).measurableSet
  have h1 : μ ({x | f x ≠ 0} ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply hm]
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 h0)
    simpa using hx
  have h2 : μ {x | f x ≠ 0} = 0 := h.measure_zero_of_invariant _ (fun γ => by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change f ((γ⁻¹ : Γ) * x) ≠ 0 ↔ f x ≠ 0
    rw [hf _ (γ⁻¹).2]) h1
  have h3 := (isOpen_ne_fun hc continuous_const).eq_empty_of_measure_zero h2
  funext x
  by_contra hx
  exact (h3 ▸ hx : x ∈ (∅ : Set G))

/- English proof (translation)
Establish `cg : Continuous fun t : ℝ => γ (Multiplicative.ofAdd t)` using `hγ.comp continuous_ofAdd`. Establish `hd' : ∀ x s, HasDerivAt (fun t : ℝ => F (x * γ (Multiplicative.ofAdd t))) (F₁ (x * γ (Multiplicative.ofAdd s))) s`. Introduce `x s`. Establish `h1` using `hd (x * γ (Multiplicative.ofAdd s))`. Establish `h2 : HasDerivAt (fun t : ℝ => t - s) 1 s` using `(hasDerivAt_id s).sub_const s`.

Establish `h3` using `HasDerivAt.scomp s (by simpa using h1) h2`. Simplify using `only [one_smul] at h3`. Use `h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Use `show F _ = F (x * γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd (t - s)))`. Rewrite using `[mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]`.

Establish `ftc : ∀ x, ∫ s in (0 : ℝ)..1, F₁ (x * γ (Multiplicative.ofAdd s)) = F (x * γ (Multiplicative.ofAdd 1)) - F x`. Introduce `x`. Rewrite using `[intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd' x s) ((c₁.comp (continuous_const.mul cg)).intervalIntegrable _ _)]`. Simplify using the standard rewrite rules. Establish `cj : Continuous fun p : ℝ × G => F₁ (p.2 * γ (Multiplicative.ofAdd p.1))` using `c₁.comp (continuous_snd.mul (cg.comp continuous_fst))`.

Establish `ij : Integrable (Function.uncurry fun (s : ℝ) (x : G) => F₁ (x * γ (Multiplicative.ofAdd s))) ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (μ.restrict 𝓕))`. Use `(integrable_prod_iff cj.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall fun s => integrableOn_right h F₁ hF₁ iF₁ (γ (Multiplicative.ofAdd s)), ?_⟩` and prove the remaining obligations. Establish `: (fun s : ℝ => ∫ x in 𝓕, ‖F₁ (x * γ (Multiplicative.ofAdd s))‖ ∂μ) = fun _ => ∫ x in 𝓕, ‖F₁ x‖ ∂μ`. Use function extensionality and compare the values at `fun s => integral_right h (fun x => ‖F₁ x‖) (fun g hg x => by rw [hF₁ g hg]) _`. Simplify using `only`.

Rewrite using `[this]`. Conclude with `integrable_const _`. Establish `sw` using `integral_integral_swap ij`. Establish `l : ∫ s in Set.Ioc (0 : ℝ) 1, ∫ x in 𝓕, F₁ (x * γ (Multiplicative.ofAdd s)) ∂μ = ∫ x in 𝓕, F₁ x ∂μ`. Simplify using `[integral_right h F₁ hF₁]`.

Establish `r : ∫ x in 𝓕, (∫ s in Set.Ioc (0 : ℝ) 1, F₁ (x * γ (Multiplicative.ofAdd s))) ∂μ = 0`. Simplify using `only [← intervalIntegral.integral_of_le zero_le_one, ftc]`. Rewrite using `[integral_sub (integrableOn_right h F hF iF _) iF, integral_right h F hF, sub_self]`. Rewrite using `[← l, sw, r]`.
-/
theorem integral_deriv [SFinite μ] (h : IsFundamentalDomain Γ 𝓕 μ) (γ : Multiplicative ℝ →* G) (hγ : Continuous γ)
    {F F₁ : G → ℂ} (c₁ : Continuous F₁) (hF : Inv Γ F) (hF₁ : Inv Γ F₁) (iF : IntegrableOn F 𝓕 μ)
    (iF₁ : IntegrableOn F₁ 𝓕 μ) (hd : ∀ x, HasDerivAt (fun t : ℝ => F (x * γ (Multiplicative.ofAdd t))) (F₁ x) 0) :
    ∫ x in 𝓕, F₁ x ∂μ = 0 := by
  have cg : Continuous fun t : ℝ => γ (Multiplicative.ofAdd t) := hγ.comp continuous_ofAdd
  have hd' : ∀ x s, HasDerivAt (fun t : ℝ => F (x * γ (Multiplicative.ofAdd t))) (F₁ (x * γ (Multiplicative.ofAdd s))) s := by
    intro x s
    have h1 := hd (x * γ (Multiplicative.ofAdd s))
    have h2 : HasDerivAt (fun t : ℝ => t - s) 1 s := (hasDerivAt_id s).sub_const s
    have h3 := HasDerivAt.scomp s (by simpa using h1) h2
    simp only [one_smul] at h3
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show F _ = F (x * γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd (t - s)))
    rw [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
  have ftc : ∀ x, ∫ s in (0 : ℝ)..1, F₁ (x * γ (Multiplicative.ofAdd s)) = F (x * γ (Multiplicative.ofAdd 1)) - F x := by
    intro x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd' x s)
      ((c₁.comp (continuous_const.mul cg)).intervalIntegrable _ _)]
    simp
  have cj : Continuous fun p : ℝ × G => F₁ (p.2 * γ (Multiplicative.ofAdd p.1)) :=
    c₁.comp (continuous_snd.mul (cg.comp continuous_fst))
  have ij : Integrable (Function.uncurry fun (s : ℝ) (x : G) => F₁ (x * γ (Multiplicative.ofAdd s)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (μ.restrict 𝓕)) := by
    refine (integrable_prod_iff cj.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall fun s =>
      integrableOn_right h F₁ hF₁ iF₁ (γ (Multiplicative.ofAdd s)), ?_⟩
    have : (fun s : ℝ => ∫ x in 𝓕, ‖F₁ (x * γ (Multiplicative.ofAdd s))‖ ∂μ) = fun _ => ∫ x in 𝓕, ‖F₁ x‖ ∂μ :=
      funext fun s => integral_right h (fun x => ‖F₁ x‖) (fun g hg x => by rw [hF₁ g hg]) _
    simp only
    rw [this]
    exact integrable_const _
  have sw := integral_integral_swap ij
  have l : ∫ s in Set.Ioc (0 : ℝ) 1, ∫ x in 𝓕, F₁ (x * γ (Multiplicative.ofAdd s)) ∂μ = ∫ x in 𝓕, F₁ x ∂μ := by
    simp [integral_right h F₁ hF₁]
  have r : ∫ x in 𝓕, (∫ s in Set.Ioc (0 : ℝ) 1, F₁ (x * γ (Multiplicative.ofAdd s))) ∂μ = 0 := by
    simp only [← intervalIntegral.integral_of_le zero_le_one, ftc]
    rw [integral_sub (integrableOn_right h F hF iF _) iF, integral_right h F hF, sub_self]
  rw [← l, sw, r]

/- English proof (translation)
Establish `i1` using `integrableOn_mul cf₁ cg f₁2 g2`. Establish `i2` using `integrableOn_mul cf cg₁ f2 g₁2`. Rewrite using `[← integral_add i1 i2]`. Use `integral_deriv h γ hγ (F := fun x => conj (f x) * g x) (((Complex.continuous_conj.comp cf₁).mul cg).add ((Complex.continuous_conj.comp cf).mul cg₁)) (fun a ha x => by simp only [hf a ha, hg a ha]) (fun a ha x => by simp only [hf a ha, hg a ha, hf₁ a ha, hg₁ a ha]) (integrableOn_m …` and prove the remaining obligations. Establish `h1 : HasDerivAt (fun t : ℝ => conj (f (x * γ (Multiplicative.ofAdd t)))) (conj (f₁ x)) 0` using `Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (df x)`.

Use `h1.fun_mul (dg x)` as an intermediate fact. Simplify using `only [ofAdd_zero, map_one, mul_one] at this`. Conclude with `this`.
-/
theorem skew [SFinite μ] (h : IsFundamentalDomain Γ 𝓕 μ) (γ : Multiplicative ℝ →* G) (hγ : Continuous γ)
    {f f₁ g g₁ : G → ℂ} (cf : Continuous f) (cf₁ : Continuous f₁) (cg : Continuous g) (cg₁ : Continuous g₁)
    (hf : Inv Γ f) (hf₁ : Inv Γ f₁) (hg : Inv Γ g) (hg₁ : Inv Γ g₁)
    (f2 : IntegrableOn (fun x => ‖f x‖ ^ 2) 𝓕 μ) (f₁2 : IntegrableOn (fun x => ‖f₁ x‖ ^ 2) 𝓕 μ)
    (g2 : IntegrableOn (fun x => ‖g x‖ ^ 2) 𝓕 μ) (g₁2 : IntegrableOn (fun x => ‖g₁ x‖ ^ 2) 𝓕 μ)
    (df : ∀ x, HasDerivAt (fun t : ℝ => f (x * γ (Multiplicative.ofAdd t))) (f₁ x) 0)
    (dg : ∀ x, HasDerivAt (fun t : ℝ => g (x * γ (Multiplicative.ofAdd t))) (g₁ x) 0) :
    ∫ x in 𝓕, conj (f₁ x) * g x ∂μ + ∫ x in 𝓕, conj (f x) * g₁ x ∂μ = 0 := by
  have i1 := integrableOn_mul cf₁ cg f₁2 g2
  have i2 := integrableOn_mul cf cg₁ f2 g₁2
  rw [← integral_add i1 i2]
  refine integral_deriv h γ hγ (F := fun x => conj (f x) * g x)
    (((Complex.continuous_conj.comp cf₁).mul cg).add ((Complex.continuous_conj.comp cf).mul cg₁))
    (fun a ha x => by simp only [hf a ha, hg a ha]) (fun a ha x => by simp only [hf a ha, hg a ha, hf₁ a ha, hg₁ a ha])
    (integrableOn_mul cf cg f2 g2) (i1.add i2) fun x => ?_
  have h1 : HasDerivAt (fun t : ℝ => conj (f (x * γ (Multiplicative.ofAdd t)))) (conj (f₁ x)) 0 :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (df x)
  have := h1.fun_mul (dg x)
  simp only [ofAdd_zero, map_one, mul_one] at this
  exact this

end PositivityTheory.ThKF.L2

end
