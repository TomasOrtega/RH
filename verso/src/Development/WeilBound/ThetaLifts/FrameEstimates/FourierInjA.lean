import Mathlib

open MeasureTheory BoundedContinuousFunction

namespace PositivityTheory.ThKEst.FourInj

/- English proof (translation)
Set `_ : UniformSpace G` to `IsTopologicalAddGroup.rightUniformSpace G`. Establish `: IsUniformAddGroup G` using `isUniformAddGroup_of_addCommGroup`. Establish `: CompleteSpace G` using `IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace`. Establish `: (uniformity G).IsCountablyGenerated` using `IsUniformAddGroup.uniformity_countably_generated`. Establish `: TopologicalSpace.IsCompletelyMetrizableSpace G` using `inferInstance`.

Use `infer_instance`.
-/
theorem polish_of_lc (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] : PolishSpace G := by
  let _ : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  have : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace G := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace
  have : (uniformity G).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : TopologicalSpace.IsCompletelyMetrizableSpace G := inferInstance
  infer_instance

variable {X A : Type} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]

/- English proof (translation)
Set `V : Submodule ℂ (X →ᵇ ℂ)` to `Submodule.span ℂ (Set.range e)`. Establish `hV1 : (1 : X →ᵇ ℂ) ∈ V` using `Submodule.subset_span h1`. Establish `hVmul : ∀ p ∈ V, ∀ q ∈ V, p * q ∈ V`. Introduce `p hp q hq`. Establish `: V * V ≤ V`.

Rewrite using `[Submodule.span_mul_span]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩`. Conclude with `hmul a b`. Conclude with `this (Submodule.mul_mem_mul hp hq)`.

Establish `hVstar : ∀ p ∈ V, star p ∈ V`. Introduce `p hp`. Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`.

Conclude with `Submodule.subset_span (hstar a)`. Consider the case `zero => rw [star_zero]`. Conclude with `V.zero_mem`. Consider the case `add x y _ _ hx hy => rw [star_add]`. Conclude with `V.add_mem hx hy`.

Consider the case `smul c x _ hx => rw [star_smul]`. Conclude with `V.smul_mem _ hx`. Set `S : StarSubalgebra ℂ (X →ᵇ ℂ)` to `{ toSubalgebra := V.toSubalgebra hV1 (fun p q hp hq => hVmul p hp q hq) star_mem' := fun {p} hp => hVstar p hp }`. Establish `hint : ∀ {k : X → ℝ}, Integrable k μ → ∀ g : X →ᵇ ℂ, Integrable (fun x => k x • g x) μ`. Introduce `k hk g`.

Conclude with `hk.smul_bdd ‖g‖ g.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)`. Establish `hV0 : ∀ g ∈ V, ∫ x, h x • g x ∂μ = 0`. Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨a, rfl⟩` from `hx`. Conclude with `h0 a`. Consider the case `zero => simp`. Consider the case `add p q _ _ hp hq`. Simplify using `only [BoundedContinuousFunction.add_apply, smul_add]`.

Rewrite using `[integral_add (hint hi p) (hint hi q), hp, hq, add_zero]`. Consider the case `smul c p _ hp`. Simplify using `only [BoundedContinuousFunction.smul_apply, smul_comm (h _) c]`. Rewrite using `[integral_smul, hp, smul_zero]`. Establish `hfin : ∀ {k : X → ℝ}, Integrable k μ → IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (k x))` using `fun hk => isFiniteMeasure_withDensity_ofReal hk.2`.

Establish `hwd : ∀ {k : X → ℝ}, Integrable k μ → ∀ g : X →ᵇ ℂ, ∫ x, g x ∂(μ.withDensity fun x => ENNReal.ofReal (k x)) = ∫ x, max (k x) 0 • g x ∂μ`. Introduce `k hk g`. Rewrite using `[integral_withDensity_eq_integral_toReal_smul₀ hk.aemeasurable.ennreal_ofReal (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]`. Simplify using `only [ENNReal.toReal_ofReal']`. Use `hfin hi` as an intermediate fact.

Use `hfin hi.neg` as an intermediate fact. Establish `hPP : (μ.withDensity fun x => ENNReal.ofReal (h x)) = μ.withDensity fun x => ENNReal.ofReal ((-h) x)`. Use `ext_of_forall_mem_subalgebra_integral_eq_of_polish (𝕜 := ℂ) (A := S) ?_ ?_` and prove the remaining obligations. Introduce `x y hxy`. Take `⟨a, ha⟩` from `hsep x y hxy`.

Conclude with `⟨e a, ⟨(e a).toContinuousMap, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, rfl⟩, ha⟩`. Introduce `g hg`. Rewrite using `[hwd hi, hwd hi.neg, ← sub_eq_zero, ← integral_sub (hint hi.pos_part g) (hint hi.neg.pos_part g), ← hV0 g hg]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [← sub_smul, Pi.neg_apply, max_zero_sub_max_neg_zero_eq_self]`.

Establish `hae` using `(withDensity_eq_iff hi.aemeasurable.ennreal_ofReal hi.neg.aemeasurable.ennreal_ofReal ((lintegral_ofReal_le_lintegral_enorm h).trans_lt hi.2).ne).1 hPP`. Use `filter_upwards [hae] with x hx`. Use `congrArg ENNReal.toReal hx` as an intermediate fact. Simplify using `only [ENNReal.toReal_ofReal', Pi.neg_apply] at this`. Establish `h2` using `max_zero_sub_max_neg_zero_eq_self (h x)`.

Rewrite `h2` using `[this, sub_self]`. Conclude with `h2.symm`.
-/
theorem real_ae_zero (μ : Measure X) (e : A → X →ᵇ ℂ) (h1 : ∃ a, e a = 1) (hmul : ∀ a b, ∃ c, e c = e a * e b)
    (hstar : ∀ a, ∃ c, e c = star (e a)) (hsep : ∀ x y, x ≠ y → ∃ a, e a x ≠ e a y) {h : X → ℝ}
    (hi : Integrable h μ) (h0 : ∀ a, ∫ x, h x • e a x ∂μ = 0) : h =ᵐ[μ] 0 := by
  let V : Submodule ℂ (X →ᵇ ℂ) := Submodule.span ℂ (Set.range e)
  have hV1 : (1 : X →ᵇ ℂ) ∈ V := Submodule.subset_span h1
  have hVmul : ∀ p ∈ V, ∀ q ∈ V, p * q ∈ V := by
    intro p hp q hq
    have : V * V ≤ V := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
      exact hmul a b
    exact this (Submodule.mul_mem_mul hp hq)
  have hVstar : ∀ p ∈ V, star p ∈ V := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span (hstar a)
    | zero => rw [star_zero]; exact V.zero_mem
    | add x y _ _ hx hy => rw [star_add]; exact V.add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact V.smul_mem _ hx
  let S : StarSubalgebra ℂ (X →ᵇ ℂ) :=
    { toSubalgebra := V.toSubalgebra hV1 (fun p q hp hq => hVmul p hp q hq)
      star_mem' := fun {p} hp => hVstar p hp }
  have hint : ∀ {k : X → ℝ}, Integrable k μ → ∀ g : X →ᵇ ℂ, Integrable (fun x => k x • g x) μ := by
    intro k hk g
    exact hk.smul_bdd ‖g‖ g.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)
  have hV0 : ∀ g ∈ V, ∫ x, h x • g x ∂μ = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact h0 a
    | zero => simp
    | add p q _ _ hp hq =>
      simp only [BoundedContinuousFunction.add_apply, smul_add]
      rw [integral_add (hint hi p) (hint hi q), hp, hq, add_zero]
    | smul c p _ hp =>
      simp only [BoundedContinuousFunction.smul_apply, smul_comm (h _) c]
      rw [integral_smul, hp, smul_zero]
  have hfin : ∀ {k : X → ℝ}, Integrable k μ → IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (k x)) :=
    fun hk => isFiniteMeasure_withDensity_ofReal hk.2
  have hwd : ∀ {k : X → ℝ}, Integrable k μ → ∀ g : X →ᵇ ℂ,
      ∫ x, g x ∂(μ.withDensity fun x => ENNReal.ofReal (k x)) = ∫ x, max (k x) 0 • g x ∂μ := by
    intro k hk g
    rw [integral_withDensity_eq_integral_toReal_smul₀ hk.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal']
  have := hfin hi
  have := hfin hi.neg
  have hPP : (μ.withDensity fun x => ENNReal.ofReal (h x)) = μ.withDensity fun x => ENNReal.ofReal ((-h) x) := by
    refine ext_of_forall_mem_subalgebra_integral_eq_of_polish (𝕜 := ℂ) (A := S) ?_ ?_
    · intro x y hxy
      obtain ⟨a, ha⟩ := hsep x y hxy
      exact ⟨e a, ⟨(e a).toContinuousMap, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, rfl⟩, ha⟩
    · intro g hg
      rw [hwd hi, hwd hi.neg, ← sub_eq_zero, ← integral_sub (hint hi.pos_part g) (hint hi.neg.pos_part g),
        ← hV0 g hg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [← sub_smul, Pi.neg_apply, max_zero_sub_max_neg_zero_eq_self]
  have hae := (withDensity_eq_iff hi.aemeasurable.ennreal_ofReal hi.neg.aemeasurable.ennreal_ofReal
    ((lintegral_ofReal_le_lintegral_enorm h).trans_lt hi.2).ne).1 hPP
  filter_upwards [hae] with x hx
  have := congrArg ENNReal.toReal hx
  simp only [ENNReal.toReal_ofReal', Pi.neg_apply] at this
  have h2 := max_zero_sub_max_neg_zero_eq_self (h x)
  rw [this, sub_self] at h2
  exact h2.symm

/- English proof (translation)
Establish `hint : ∀ {k : X → ℂ}, Integrable k μ → ∀ g : X →ᵇ ℂ, Integrable (fun x => g x * k x) μ`. Introduce `k hk g`. Conclude with `hk.bdd_mul (c := ‖g‖) g.continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)`. Establish `hic : Integrable (fun x => (starRingEnd ℂ) (H x)) μ` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hi`. Establish `hc : ∀ a, ∫ x, e a x * (starRingEnd ℂ) (H x) ∂μ = 0`.

Introduce `a`. Take `⟨c, hc⟩` from `hstar a`. Use `congrArg (starRingEnd ℂ) (h0 c)` as an intermediate fact. Rewrite `this` using `[← integral_conj, map_zero, hc]`. Simplify using `using this`.

Establish `hre : (fun x => (H x).re) =ᵐ[μ] 0`. Use `real_ae_zero μ e h1 hmul hstar hsep hi.re fun a => ?_` and prove the remaining obligations. Establish `: ∀ x, (H x).re • e a x = (1 / 2 : ℂ) * (e a x * H x + e a x * (starRingEnd ℂ) (H x))` using `fun x => by`. Rewrite using `[← mul_add, Complex.add_conj, Complex.real_smul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [this]`. Rewrite using `[integral_const_mul, integral_add (hint hi _) (hint hic _), h0, hc]`. Simplify using the standard rewrite rules. Establish `him : (fun x => (H x).im) =ᵐ[μ] 0`.

Use `real_ae_zero μ e h1 hmul hstar hsep hi.im fun a => ?_` and prove the remaining obligations. Establish `: ∀ x, (H x).im • e a x = (-Complex.I / 2 : ℂ) * (e a x * H x - e a x * (starRingEnd ℂ) (H x))` using `fun x => by`. Rewrite using `[← mul_sub, Complex.sub_conj, Complex.real_smul]`. Use `push_cast`. Take the linear combination `((H x).im * e a x) * Complex.I_mul_I`.

Simplify using `only [this]`. Rewrite using `[integral_const_mul, integral_sub (hint hi _) (hint hic _), h0, hc]`. Simplify using the standard rewrite rules. Use `filter_upwards [hre, him] with x h1 h2`. Conclude with `Complex.ext h1 h2`.
-/
theorem complex_ae_zero (μ : Measure X) (e : A → X →ᵇ ℂ) (h1 : ∃ a, e a = 1) (hmul : ∀ a b, ∃ c, e c = e a * e b)
    (hstar : ∀ a, ∃ c, e c = star (e a)) (hsep : ∀ x y, x ≠ y → ∃ a, e a x ≠ e a y) {H : X → ℂ}
    (hi : Integrable H μ) (h0 : ∀ a, ∫ x, e a x * H x ∂μ = 0) : H =ᵐ[μ] 0 := by
  have hint : ∀ {k : X → ℂ}, Integrable k μ → ∀ g : X →ᵇ ℂ, Integrable (fun x => g x * k x) μ := by
    intro k hk g
    exact hk.bdd_mul (c := ‖g‖) g.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)
  have hic : Integrable (fun x => (starRingEnd ℂ) (H x)) μ :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hi
  have hc : ∀ a, ∫ x, e a x * (starRingEnd ℂ) (H x) ∂μ = 0 := by
    intro a
    obtain ⟨c, hc⟩ := hstar a
    have := congrArg (starRingEnd ℂ) (h0 c)
    rw [← integral_conj, map_zero, hc] at this
    simpa using this
  have hre : (fun x => (H x).re) =ᵐ[μ] 0 := by
    refine real_ae_zero μ e h1 hmul hstar hsep hi.re fun a => ?_
    have : ∀ x, (H x).re • e a x = (1 / 2 : ℂ) * (e a x * H x + e a x * (starRingEnd ℂ) (H x)) := fun x => by
      rw [← mul_add, Complex.add_conj, Complex.real_smul]; push_cast; ring
    simp only [this]
    rw [integral_const_mul, integral_add (hint hi _) (hint hic _), h0, hc]; simp
  have him : (fun x => (H x).im) =ᵐ[μ] 0 := by
    refine real_ae_zero μ e h1 hmul hstar hsep hi.im fun a => ?_
    have : ∀ x, (H x).im • e a x = (-Complex.I / 2 : ℂ) * (e a x * H x - e a x * (starRingEnd ℂ) (H x)) := fun x => by
      rw [← mul_sub, Complex.sub_conj, Complex.real_smul]; push_cast
      linear_combination ((H x).im * e a x) * Complex.I_mul_I
    simp only [this]
    rw [integral_const_mul, integral_sub (hint hi _) (hint hic _), h0, hc]; simp
  filter_upwards [hre, him] with x h1 h2
  exact Complex.ext h1 h2

end PositivityTheory.ThKEst.FourInj
