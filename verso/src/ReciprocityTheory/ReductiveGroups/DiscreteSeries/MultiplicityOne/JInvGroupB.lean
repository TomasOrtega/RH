import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace InvGrp

variable {k r : ℕ}

/- English proof (translation)
Unfold `lmulM`. Use `fun_prop`.
-/
theorem continuous_lmulM (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  unfold lmulM; fun_prop

/- English proof (translation)
Establish `hfm : Measurable f` using `hf.measurable`. Establish `hUc : IsClosed (show Set (Mt k r) from U)` using `hU.closed`. Establish `hUm : MeasurableSet (show Set (Mt k r) from U)` using `hUc.measurableSet`. Establish `h1 : (μ.map f) Uᶜ = 0`. Rewrite using `[Measure.map_apply hfm hUm.compl]`.

Use `measure_mono_null (fun x hx => ?_) hμ.conc` and prove the remaining obligations. Introduce `hxU`. Conclude with `hx (hfU x hxU)`. Establish `h2 : ∀ a ∈ U, (μ.map f).map (lmulM a) = μ.map f`. Introduce `a ha`.

Take `⟨b, hb, hab⟩` from `hl a ha`. Rewrite using `[Measure.map_map (continuous_lmulM a).measurable hfm]`. Establish `: lmulM a ∘ f = f ∘ lmulM b` using `funext hab`. Rewrite using `[this, ← Measure.map_map hfm (continuous_lmulM b).measurable, hμ.left b hb]`. Establish `h3 : ∀ K : Set (Mt k r), IsCompact K → (μ.map f) K < ∞`.

Introduce `K hK`. Rewrite using `[Measure.map_apply hfm hK.measurableSet]`. Establish `: f ⁻¹' K = f '' K`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Conclude with `⟨f x, hx, hff x⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Use `show f (f y) ∈ K`. Rewrite using `[hff]`.

Conclude with `hy`. Rewrite using `[this]`. Conclude with `hμ.finite_compact _ (hK.image hf)`. Take `⟨c, hc⟩` from `HU k r U μ (μ.map f) hU hμ h1 h2 h3`. Establish `hff' : f ∘ f = id` using `funext hff`.

Establish `hback : (μ.map f).map f = μ`. Rewrite using `[Measure.map_map hfm hfm, hff', Measure.map_id]`. Establish `hcc : (c * c) • μ = μ` using `by conv_rhs => rw [← hback]`. Rewrite using `[hc, Measure.map_smul, hc, smul_smul]`. Choose the witnesses or unpack the hypotheses as in `⟨K, hK, hK0⟩ : ∃ K : Set (Mt k r), IsCompact K ∧ μ K ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hμ.ne_zero` to reduce the goal to its premises. Establish `: μ Set.univ = 0`. Rewrite using `[← Metric.iUnion_closedBall_nat (0 : Mt k r)]`.

Conclude with `measure_iUnion_null fun n => hcon _ (isCompact_closedBall _ _)`. Conclude with `Measure.measure_univ_eq_zero.mp this`. Establish `hKt : μ K ≠ ∞` using `(hμ.finite_compact K hK).ne`. Establish `hval : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K`. Use `congrArg (fun ν : Measure (Mt k r) => ν K) hcc` as an intermediate fact.

Simplify using `using this`. Establish `hc1 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1` using `(ENNReal.mul_left_inj hK0 hKt).mp hval`. Establish `hc2 : (c : ℝ) * c = 1`. Establish `: c * c = 1` using `by exact_mod_cast hc1`. Conclude with `this` after adjusting the coercions.

Establish `hcpos : (0 : ℝ) ≤ c` using `c.2`. Establish `hc3 : c = 1`. Establish `: (c : ℝ) = 1` using `by nlinarith`. Conclude with `this` after adjusting the coercions. Rewrite using `[hc, hc3, one_smul]`.
-/
theorem map_invol_eq (HU : HaarUnique) {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {μ : Measure (Mt k r)}
    (hμ : IsHaarOn U μ) (f : Mt k r → Mt k r) (hf : Continuous f) (hff : ∀ x, f (f x) = x)
    (hfU : ∀ x : Mt k r, (x : Mat k r) ∈ U → (f x : Mat k r) ∈ U)
    (hl : ∀ a ∈ U, ∃ b ∈ U, ∀ x, lmulM a (f x) = f (lmulM b x)) : μ.map f = μ := by
  have hfm : Measurable f := hf.measurable
  have hUc : IsClosed (show Set (Mt k r) from U) := hU.closed
  have hUm : MeasurableSet (show Set (Mt k r) from U) := hUc.measurableSet
  have h1 : (μ.map f) Uᶜ = 0 := by
    rw [Measure.map_apply hfm hUm.compl]
    refine measure_mono_null (fun x hx => ?_) hμ.conc
    intro hxU
    exact hx (hfU x hxU)
  have h2 : ∀ a ∈ U, (μ.map f).map (lmulM a) = μ.map f := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hl a ha
    rw [Measure.map_map (continuous_lmulM a).measurable hfm]
    have : lmulM a ∘ f = f ∘ lmulM b := funext hab
    rw [this, ← Measure.map_map hfm (continuous_lmulM b).measurable, hμ.left b hb]
  have h3 : ∀ K : Set (Mt k r), IsCompact K → (μ.map f) K < ∞ := by
    intro K hK
    rw [Measure.map_apply hfm hK.measurableSet]
    have : f ⁻¹' K = f '' K := by
      ext x; constructor
      · intro hx; exact ⟨f x, hx, hff x⟩
      · rintro ⟨y, hy, rfl⟩; show f (f y) ∈ K; rw [hff]; exact hy
    rw [this]
    exact hμ.finite_compact _ (hK.image hf)
  obtain ⟨c, hc⟩ := HU k r U μ (μ.map f) hU hμ h1 h2 h3
  have hff' : f ∘ f = id := funext hff
  have hback : (μ.map f).map f = μ := by
    rw [Measure.map_map hfm hfm, hff', Measure.map_id]
  have hcc : (c * c) • μ = μ := by
    conv_rhs => rw [← hback]
    rw [hc, Measure.map_smul, hc, smul_smul]

  obtain ⟨K, hK, hK0⟩ : ∃ K : Set (Mt k r), IsCompact K ∧ μ K ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hμ.ne_zero
    have : μ Set.univ = 0 := by
      rw [← Metric.iUnion_closedBall_nat (0 : Mt k r)]
      exact measure_iUnion_null fun n => hcon _ (isCompact_closedBall _ _)
    exact Measure.measure_univ_eq_zero.mp this
  have hKt : μ K ≠ ∞ := (hμ.finite_compact K hK).ne
  have hval : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K := by
    have := congrArg (fun ν : Measure (Mt k r) => ν K) hcc
    simpa using this
  have hc1 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hK0 hKt).mp hval
  have hc2 : (c : ℝ) * c = 1 := by
    have : c * c = 1 := by exact_mod_cast hc1
    exact_mod_cast this
  have hcpos : (0 : ℝ) ≤ c := c.2
  have hc3 : c = 1 := by
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  rw [hc, hc3, one_smul]

end InvGrp

end ReciprocityTheory.ChartRestriction.DS.Mult1
