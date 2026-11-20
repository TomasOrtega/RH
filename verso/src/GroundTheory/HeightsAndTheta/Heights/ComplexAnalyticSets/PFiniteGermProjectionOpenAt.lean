import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteGermProjectionOpenAt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticGermComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleFiniteGermProjectionOpenAt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

/- English proof (translation)
Take `⟨r, hr, hball⟩` from `Metric.mem_nhds_iff.1 ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and hfg)`. Distinguish the cases in `hf0 : ∀ z ∈ Metric.ball y r, f z = 0`. Conclude with `Or.inl (Filter.mem_of_superset (Metric.ball_mem_nhds y hr) hf0)`. Use `right push Not at hf0`. Take `⟨p, hp, hfp⟩` from `hf0`.

Establish `hgp : g =ᶠ[𝓝 p] 0` using `by filter_upwards [(hball hp).1.1.continuousAt.eventually_ne hfp, Metric.isOpen_ball.mem_nhds hp] with z hz1 hz2`. Conclude with `(mul_eq_zero.1 (hball hz2).2).resolve_left hz1`. Establish `hgan : AnalyticOnNhd ℂ g (Metric.ball y r)` using `fun z hz => (hball hz).1.2`. Establish `hzero` using `hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y r).isPreconnected hp hgp`. Conclude with `Filter.mem_of_superset (Metric.ball_mem_nhds y hr) fun z hz => by simpa using hzero hz`.
-/
theorem germ_eventually_zero_of_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {y : E}
    (hf : AnalyticAt ℂ f y) (hg : AnalyticAt ℂ g y) (hfg : ∀ᶠ z in 𝓝 y, f z * g z = 0) :
    (∀ᶠ z in 𝓝 y, f z = 0) ∨ (∀ᶠ z in 𝓝 y, g z = 0) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and hfg)
  by_cases hf0 : ∀ z ∈ Metric.ball y r, f z = 0
  · exact Or.inl (Filter.mem_of_superset (Metric.ball_mem_nhds y hr) hf0)
  · right
    push Not at hf0
    obtain ⟨p, hp, hfp⟩ := hf0
    have hgp : g =ᶠ[𝓝 p] 0 := by
      filter_upwards [(hball hp).1.1.continuousAt.eventually_ne hfp, Metric.isOpen_ball.mem_nhds hp]
        with z hz1 hz2
      exact (mul_eq_zero.1 (hball hz2).2).resolve_left hz1
    have hgan : AnalyticOnNhd ℂ g (Metric.ball y r) := fun z hz => (hball hz).1.2
    have hzero := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y r).isPreconnected hp hgp
    exact Filter.mem_of_superset (Metric.ball_mem_nhds y hr) fun z hz => by simpa using hzero hz

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Take `⟨z, hz⟩` from `hprod.exists`. Simplify using `at hz`. Consider the case `insert a s ha ih`.

Establish `hg : AnalyticAt ℂ (fun z => ∏ i ∈ s, h i z) y` using `Finset.analyticAt_fun_prod s fun i hi => han i (Finset.mem_insert_of_mem hi)`. Establish `hprod' : ∀ᶠ z in 𝓝 y, h a z * ∏ i ∈ s, h i z = 0` using `by filter_upwards [hprod] with z hz`. Rewrite `hz` using `[Finset.prod_insert ha]`. Then use the resulting hypothesis. Break down `germ_eventually_zero_of_mul (han a (Finset.mem_insert_self a s)) hg hprod' with h1 | h1` into its components or cases. Conclude with `⟨a, Finset.mem_insert_self a s, h1⟩`.

Take `⟨i, hi, h2⟩` from `ih (fun i hi => han i (Finset.mem_insert_of_mem hi)) h1`. Conclude with `⟨i, Finset.mem_insert_of_mem hi, h2⟩`.
-/
theorem germ_prod_eventually_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (h : ι → E → ℂ) {y : E} (s : Finset ι) (han : ∀ i ∈ s, AnalyticAt ℂ (h i) y)
    (hprod : ∀ᶠ z in 𝓝 y, ∏ i ∈ s, h i z = 0) : ∃ i ∈ s, ∀ᶠ z in 𝓝 y, h i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨z, hz⟩ := hprod.exists
    simp at hz
  | insert a s ha ih =>
    have hg : AnalyticAt ℂ (fun z => ∏ i ∈ s, h i z) y :=
      Finset.analyticAt_fun_prod s fun i hi => han i (Finset.mem_insert_of_mem hi)
    have hprod' : ∀ᶠ z in 𝓝 y, h a z * ∏ i ∈ s, h i z = 0 := by
      filter_upwards [hprod] with z hz
      rwa [Finset.prod_insert ha] at hz
    rcases germ_eventually_zero_of_mul (han a (Finset.mem_insert_self a s)) hg hprod' with h1 | h1
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨i, hi, h2⟩ := ih (fun i hi => han i (Finset.mem_insert_of_mem hi)) h1
      exact ⟨i, Finset.mem_insert_of_mem hi, h2⟩

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Take `⟨N, k, f, hNo, hxN, hf, hXN⟩` from `hX`. Establish `hne : ∃ i, f i x ≠ 0`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`.

Establish `hmem : x ∈ {z | z ∈ N ∧ ∀ i, f i z = 0}` using `⟨hxN, hall⟩`. Rewrite `hmem` using `[← hXN]`. Conclude with `hx hmem.1`. Take `⟨i, hi⟩` from `hne`. Establish `hev : ∀ᶠ z in 𝓝 x, z ∈ X → (fun _ : Fin d → ℂ => (1 : ℂ)) (A z) = 0` using `by filter_upwards [(hf i x hxN).continuousAt.eventually_ne hi, hNo.mem_nhds hxN] with z hz1 hz2 hzX`.

Establish `hmem : z ∈ X ∩ N` using `⟨hzX, hz2⟩`. Rewrite `hmem` using `[hXN]`. Conclude with `absurd (hmem.2 i) hz1`. Take `⟨y, hy⟩` from `(hinj (fun _ => 1) analyticAt_const hev).exists`. Conclude with `one_ne_zero hy`.
-/
theorem mem_of_projection_germ_injective {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {x : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hX : IsAnalyticNear X x)
    (hinj : ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
      ∀ᶠ y in 𝓝 (A x), h y = 0) : x ∈ X := by
  by_contra hx
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  have hne : ∃ i, f i x ≠ 0 := by
    by_contra hall
    push Not at hall
    have hmem : x ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hxN, hall⟩
    rw [← hXN] at hmem
    exact hx hmem.1
  obtain ⟨i, hi⟩ := hne
  have hev : ∀ᶠ z in 𝓝 x, z ∈ X → (fun _ : Fin d → ℂ => (1 : ℂ)) (A z) = 0 := by
    filter_upwards [(hf i x hxN).continuousAt.eventually_ne hi, hNo.mem_nhds hxN] with z hz1 hz2 hzX
    have hmem : z ∈ X ∩ N := ⟨hzX, hz2⟩
    rw [hXN] at hmem
    exact absurd (hmem.2 i) hz1
  obtain ⟨y, hy⟩ := (hinj (fun _ => 1) analyticAt_const hev).exists
  exact one_ne_zero hy

/- English proof (translation)
Introduce `σ _ X x d A hX hiso hinj V hV`. Establish `hxX : x ∈ X` using `mem_of_projection_germ_injective A hX hinj`. Take `⟨n, Y, hY, W, hW, hXW⟩` from `hcomp σ X x hX hxX`. Take `⟨W₀, hW₀, hisoW₀⟩` from `hiso`. Establish `hsome : ∃ i, ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ Y i → h (A z) = 0) → ∀ᶠ y in 𝓝 (A x), h y = 0`.

Assume the negation of the conclusion as `hnone`. Use `push Not at hnone`. Use `choose h han hvan hne using hnone`. Establish `hprod : ∀ᶠ y in 𝓝 (A x), ∏ i ∈ Finset.univ, h i y = 0`. Establish `hpan : AnalyticAt ℂ (fun y => ∏ i ∈ Finset.univ, h i y) (A x)` using `Finset.analyticAt_fun_prod Finset.univ fun i _ => han i`.

Use `hinj (fun y => ∏ i ∈ Finset.univ, h i y) hpan ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_all.2 hvan, hW] with z hz hzW hzX`. Establish `hmem : z ∈ (⋃ i, Y i) ∩ W`. Rewrite using `[← hXW]`. Conclude with `⟨hzX, hzW⟩`.

Take `⟨i, hi⟩` from `Set.mem_iUnion.1 hmem.1`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (hz i hi)`. Take `⟨i, -, hi⟩` from `germ_prod_eventually_zero h Finset.univ (fun i _ => han i) hprod`. Conclude with `hne i (hi.mono fun z hz => not_not.2 hz)`. Take `⟨i, hi⟩` from `hsome`.

Establish `hYX : Y i ∩ W ⊆ X` using `fun z hz => by`. Establish `hmem : z ∈ (⋃ j, Y j) ∩ W` using `⟨Set.mem_iUnion.2 ⟨i, hz.1⟩, hz.2⟩`. Rewrite `hmem` using `[← hXW]`. Conclude with `hmem.1`. Establish `hisoY : ∃ W' ∈ 𝓝 x, ∀ x' ∈ Y i ∩ W', A x' = A x → x' = x` using `⟨W ∩ W₀, Filter.inter_mem hW hW₀, fun x' hx' hAx' => hisoW₀ x' ⟨hYX ⟨hx'.1, hx'.2.1⟩, hx'.2.2⟩ hAx'⟩`.

Establish `himg` using `hirr σ (Y i) x d A (hY i).1 (hY i).2 hisoY hi (V ∩ W) (Filter.inter_mem hV hW)`. Use `Filter.mem_of_superset himg (Set.image_mono ?_)` and prove the remaining obligations. Introduce and unpack `z ⟨hzY, hzV, hzW⟩`. Conclude with `⟨hYX ⟨hzY, hzW⟩, hzV⟩`.
-/
theorem FiniteGermProjectionOpenAt.proof (hcomp : AnalyticGermComponents.Statement)
    (hirr : IrreducibleFiniteGermProjectionOpenAt.Statement) : FiniteGermProjectionOpenAt.Statement := by
  classical
  intro σ _ X x d A hX hiso hinj V hV
  have hxX : x ∈ X := mem_of_projection_germ_injective A hX hinj
  obtain ⟨n, Y, hY, W, hW, hXW⟩ := hcomp σ X x hX hxX
  obtain ⟨W₀, hW₀, hisoW₀⟩ := hiso

  have hsome : ∃ i, ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) →
      (∀ᶠ z in 𝓝 x, z ∈ Y i → h (A z) = 0) → ∀ᶠ y in 𝓝 (A x), h y = 0 := by
    by_contra hnone
    push Not at hnone
    choose h han hvan hne using hnone
    have hprod : ∀ᶠ y in 𝓝 (A x), ∏ i ∈ Finset.univ, h i y = 0 := by
      have hpan : AnalyticAt ℂ (fun y => ∏ i ∈ Finset.univ, h i y) (A x) :=
        Finset.analyticAt_fun_prod Finset.univ fun i _ => han i
      refine hinj (fun y => ∏ i ∈ Finset.univ, h i y) hpan ?_
      filter_upwards [Filter.eventually_all.2 hvan, hW] with z hz hzW hzX
      have hmem : z ∈ (⋃ i, Y i) ∩ W := by
        rw [← hXW]
        exact ⟨hzX, hzW⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmem.1
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hz i hi)
    obtain ⟨i, -, hi⟩ := germ_prod_eventually_zero h Finset.univ (fun i _ => han i) hprod
    exact hne i (hi.mono fun z hz => not_not.2 hz)
  obtain ⟨i, hi⟩ := hsome
  have hYX : Y i ∩ W ⊆ X := fun z hz => by
    have hmem : z ∈ (⋃ j, Y j) ∩ W := ⟨Set.mem_iUnion.2 ⟨i, hz.1⟩, hz.2⟩
    rw [← hXW] at hmem
    exact hmem.1
  have hisoY : ∃ W' ∈ 𝓝 x, ∀ x' ∈ Y i ∩ W', A x' = A x → x' = x :=
    ⟨W ∩ W₀, Filter.inter_mem hW hW₀, fun x' hx' hAx' => hisoW₀ x' ⟨hYX ⟨hx'.1, hx'.2.1⟩, hx'.2.2⟩ hAx'⟩
  have himg := hirr σ (Y i) x d A (hY i).1 (hY i).2 hisoY hi (V ∩ W) (Filter.inter_mem hV hW)
  refine Filter.mem_of_superset himg (Set.image_mono ?_)
  rintro z ⟨hzY, hzV, hzW⟩
  exact ⟨hYX ⟨hzY, hzW⟩, hzV⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
