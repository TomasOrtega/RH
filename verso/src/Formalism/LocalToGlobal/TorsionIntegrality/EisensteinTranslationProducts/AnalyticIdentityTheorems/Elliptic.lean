import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine

noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F

/- English proof (translation)
Introduce `L f hf hper z`. Establish `key : ∀ x : ℂ, ∃ ω ∈ L.lattice, ‖x - ω‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖`. Introduce `x`. Establish `hx` using `L.basis.sum_repr x`. Rewrite `hx` using `[Fin.sum_univ_two, L.basis_zero, L.basis_one]`.

Use `⟨(⌊L.basis.repr x 0⌋ : ℂ) * L.ω₁ + (⌊L.basis.repr x 1⌋ : ℂ) * L.ω₂, PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩, ?_⟩` and prove the remaining obligations. Generalize the expression as in `L.basis.repr x 0 = a at hx ⊢`. Generalize the expression as in `L.basis.repr x 1 = b at hx ⊢`. Substitute `hx` using the available equality. Establish `e : a • L.ω₁ + b • L.ω₂ - ((⌊a⌋ : ℂ) * L.ω₁ + (⌊b⌋ : ℂ) * L.ω₂) = ((Int.fract a : ℝ) : ℂ) * L.ω₁ + ((Int.fract b : ℝ) : ℂ) * L.ω₂`.

Simplify using `only [Complex.real_smul, Int.fract]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `hfr : ∀ (r : ℝ) (v : ℂ), ‖((Int.fract r : ℝ) : ℂ) * v‖ ≤ ‖v‖`.

Introduce `r v`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le`. Conclude with `(norm_add_le _ _).trans (add_le_add (hfr a _) (hfr b _))`. Take `⟨C, hC⟩` from `(isCompact_closedBall (0 : ℂ) (‖L.ω₁‖ + ‖L.ω₂‖)).exists_bound_of_continuousOn hf.continuous.continuousOn`.

Establish `hb : Bornology.IsBounded (Set.range f)`. Rewrite using `[isBounded_iff_forall_norm_le]`. Use `⟨C, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨ω, hω, hxω⟩` from `key x`.

Establish `: f x = f (x - ω)`. Use `hper ω hω (x - ω)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Rewrite using `[this]`. Conclude with `hC _ (by simpa using hxω)`.

Conclude with `hf.apply_eq_apply_of_bounded hb z 0`.
-/
theorem elliptic_entire_const : EllipticEntire := by
  intro L f hf hper z
  have key : ∀ x : ℂ, ∃ ω ∈ L.lattice, ‖x - ω‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖ := by
    intro x
    have hx := L.basis.sum_repr x
    rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at hx
    refine ⟨(⌊L.basis.repr x 0⌋ : ℂ) * L.ω₁ + (⌊L.basis.repr x 1⌋ : ℂ) * L.ω₂,
      PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩, ?_⟩
    generalize L.basis.repr x 0 = a at hx ⊢
    generalize L.basis.repr x 1 = b at hx ⊢
    subst hx
    have e : a • L.ω₁ + b • L.ω₂ - ((⌊a⌋ : ℂ) * L.ω₁ + (⌊b⌋ : ℂ) * L.ω₂)
        = ((Int.fract a : ℝ) : ℂ) * L.ω₁ + ((Int.fract b : ℝ) : ℂ) * L.ω₂ := by
      simp only [Complex.real_smul, Int.fract]; push_cast; ring
    rw [e]
    have hfr : ∀ (r : ℝ) (v : ℂ), ‖((Int.fract r : ℝ) : ℂ) * v‖ ≤ ‖v‖ := by
      intro r v
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    exact (norm_add_le _ _).trans (add_le_add (hfr a _) (hfr b _))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (‖L.ω₁‖ + ‖L.ω₂‖)).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  have hb : Bornology.IsBounded (Set.range f) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    obtain ⟨ω, hω, hxω⟩ := key x
    have : f x = f (x - ω) := by
      have := hper ω hω (x - ω)
      rwa [sub_add_cancel] at this
    rw [this]
    exact hC _ (by simpa using hxω)
  exact hf.apply_eq_apply_of_bounded hb z 0

namespace Elliptic

/- English proof (translation)
The claim follows from `tendsto_nhds_unique (h₁.tendsto.mono_left nhdsWithin_le_nhds) ((h₂.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)`.
-/
lemma eq_of_eventuallyEq_nhdsNE {g₁ g₂ : ℂ → ℂ} {z : ℂ} (h₁ : ContinuousAt g₁ z)
    (h₂ : ContinuousAt g₂ z) (h : g₁ =ᶠ[𝓝[≠] z] g₂) : g₁ z = g₂ z :=
  tendsto_nhds_unique (h₁.tendsto.mono_left nhdsWithin_le_nhds)
    ((h₂.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

/- English proof (translation)
Rewrite using `[tendsto_nhdsWithin_iff]`. Use `⟨((continuous_add_right ω).tendsto z).mono_left nhdsWithin_le_nhds, ?_⟩` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with w hw`. Conclude with `fun h => hw (add_right_cancel h)`.
-/
lemma tendsto_add_nhdsNE (z ω : ℂ) : Tendsto (fun w : ℂ => w + ω) (𝓝[≠] z) (𝓝[≠] (z + ω)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨((continuous_add_right ω).tendsto z).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact fun h => hw (add_right_cancel h)

end Elliptic

/- English proof (translation)
Introduce `L f hmer hper hord`. Establish `hM : MeromorphicOn f Set.univ` using `fun z _ => hmer z`. Use `set g := toMeromorphicNFOn f Set.univ with hg_def`. Establish `heq : ∀ z, g =ᶠ[𝓝[≠] z] f` using `fun z => hM.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)`. Establish `han : ∀ z, AnalyticAt ℂ g z` using `fun z => by`.

Establish `hnf` using `meromorphicNFOn_toMeromorphicNFOn f Set.univ (Set.mem_univ z)`. Rewrite using `[← hnf.meromorphicOrderAt_nonneg_iff_analyticAt, meromorphicOrderAt_congr (heq z)]`. Conclude with `hord z`. Establish `hcont : ∀ z, ContinuousAt g z` using `fun z => (han z).continuousAt`. Establish `hdiff : Differentiable ℂ g` using `fun z => (han z).differentiableAt`.

Establish `hpg : IsPeriodic L g`. Introduce `ω hω z`. Establish `hc1 : ContinuousAt (fun w => g (w + ω)) z` using `show ContinuousAt (g ∘ fun w => w + ω) z from (hcont (z + ω)).comp_of_eq (continuous_add_right ω).continuousAt rfl`. Establish `h1 : ∀ᶠ w in 𝓝[≠] z, g (w + ω) = f (w + ω)` using `(Elliptic.tendsto_add_nhdsNE z ω).eventually (heq (z + ω))`. Establish `h2 : (fun w => g (w + ω)) =ᶠ[𝓝[≠] z] g` using `by filter_upwards [h1, heq z] with w hw1 hw2`.

Rewrite using `[hw1, hper ω hω w, hw2]`. Conclude with `Elliptic.eq_of_eventuallyEq_nhdsNE hc1 (hcont z) h2`. Use `⟨g 0, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[← elliptic_entire_const L g hdiff hpg z]`. Conclude with `Elliptic.eq_of_eventuallyEq_nhdsNE hz (hcont z) (heq z).symm`.
-/
theorem elliptic_no_pole_const : EllipticNoPole := by
  intro L f hmer hper hord
  have hM : MeromorphicOn f Set.univ := fun z _ => hmer z
  set g := toMeromorphicNFOn f Set.univ with hg_def
  have heq : ∀ z, g =ᶠ[𝓝[≠] z] f := fun z =>
    hM.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have han : ∀ z, AnalyticAt ℂ g z := fun z => by
    have hnf := meromorphicNFOn_toMeromorphicNFOn f Set.univ (Set.mem_univ z)
    rw [← hnf.meromorphicOrderAt_nonneg_iff_analyticAt, meromorphicOrderAt_congr (heq z)]
    exact hord z
  have hcont : ∀ z, ContinuousAt g z := fun z => (han z).continuousAt
  have hdiff : Differentiable ℂ g := fun z => (han z).differentiableAt
  have hpg : IsPeriodic L g := by
    intro ω hω z
    have hc1 : ContinuousAt (fun w => g (w + ω)) z :=
      show ContinuousAt (g ∘ fun w => w + ω) z from
        (hcont (z + ω)).comp_of_eq (continuous_add_right ω).continuousAt rfl
    have h1 : ∀ᶠ w in 𝓝[≠] z, g (w + ω) = f (w + ω) :=
      (Elliptic.tendsto_add_nhdsNE z ω).eventually (heq (z + ω))
    have h2 : (fun w => g (w + ω)) =ᶠ[𝓝[≠] z] g := by
      filter_upwards [h1, heq z] with w hw1 hw2
      rw [hw1, hper ω hω w, hw2]
    exact Elliptic.eq_of_eventuallyEq_nhdsNE hc1 (hcont z) h2
  refine ⟨g 0, fun z hz => ?_⟩
  rw [← elliptic_entire_const L g hdiff hpg z]
  exact Elliptic.eq_of_eventuallyEq_nhdsNE hz (hcont z) (heq z).symm

end Formalism.L2.Th1.F
