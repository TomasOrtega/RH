import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionSheetedClosureEquations
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionProperBall
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperSheetedFibreEsymm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGridProductLowerBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountConstant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

/- English proof (translation)
Assume the negation of the conclusion as `hns`. Establish `hlt : LinearMap.range (A : (σ → ℂ) →ₗ[ℂ] (Fin d → ℂ)) < ⊤` using `lt_top_iff_ne_top.2 fun htop => hns (by simpa using LinearMap.range_eq_top.1 htop)`. Take `⟨f, hf0, hfmap⟩` from `Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance`. Establish `hfA : ∀ z, f (A z) = 0` using `fun z => by`. Establish `: f (A z) ∈ (LinearMap.range (A : (σ → ℂ) →ₗ[ℂ] (Fin d → ℂ))).map f` using `⟨A z, ⟨z, rfl⟩, rfl⟩`.

Rewrite `this` using `[hfmap]`. Conclude with `this`. Establish `hev` using `hA (fun y => LinearMap.toContinuousLinearMap f y) ((LinearMap.toContinuousLinearMap f).analyticAt _) (Eventually.of_forall fun z _ => by simpa using hfA z)`. Apply `hf0` to reduce the goal to its premises. Establish `hker : LinearMap.ker f = ⊤`.

Apply `Submodule.eq_top_of_nonempty_interior'` to reduce the goal to its premises. Use `⟨A w, mem_interior_iff_mem_nhds.2 ?_⟩` and prove the remaining obligations. Use `filter_upwards [hev] with y hy`. Simplify using `using hy`. Conclude with `LinearMap.ker_eq_top.1 hker`.
-/
theorem FiniteProjectionSheetedClosureEquations.surjective_of_no_germ {σ : Type} [Fintype σ] {d : ℕ}
    {w : σ → ℂ} {X : Set (σ → ℂ)} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (hA : ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) : Function.Surjective A := by
  by_contra hns
  have hlt : LinearMap.range (A : (σ → ℂ) →ₗ[ℂ] (Fin d → ℂ)) < ⊤ :=
    lt_top_iff_ne_top.2 fun htop => hns (by simpa using LinearMap.range_eq_top.1 htop)
  obtain ⟨f, hf0, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hfA : ∀ z, f (A z) = 0 := fun z => by
    have : f (A z) ∈ (LinearMap.range (A : (σ → ℂ) →ₗ[ℂ] (Fin d → ℂ))).map f := ⟨A z, ⟨z, rfl⟩, rfl⟩
    rw [hfmap] at this
    exact this
  have hev := hA (fun y => LinearMap.toContinuousLinearMap f y)
    ((LinearMap.toContinuousLinearMap f).analyticAt _)
    (Eventually.of_forall fun z _ => by simpa using hfA z)
  apply hf0
  have hker : LinearMap.ker f = ⊤ := by
    apply Submodule.eq_top_of_nonempty_interior'
    refine ⟨A w, mem_interior_iff_mem_nhds.2 ?_⟩
    filter_upwards [hev] with y hy
    simpa using hy
  exact LinearMap.ker_eq_top.1 hker

/- English proof (translation)
Establish `key` using `congrArg (Polynomial.eval a) (Multiset.prod_X_sub_X_eq_sum_esymm m)`. Rewrite `key` using `[Polynomial.eval_multiset_prod, Polynomial.eval_finsetSum]`. Simplify using `only [Multiset.map_map, Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one] at key`. Rewrite using `[key]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem FiniteProjectionSheetedClosureEquations.prod_sub_eq_sum_esymm (m : Multiset ℂ) (a : ℂ) :
    (m.map fun x => a - x).prod =
      ∑ j ∈ Finset.range (Multiset.card m + 1), (-1) ^ j * m.esymm j * a ^ (Multiset.card m - j) := by
  have key := congrArg (Polynomial.eval a) (Multiset.prod_X_sub_X_eq_sum_esymm m)
  rw [Polynomial.eval_multiset_prod, Polynomial.eval_finsetSum] at key
  simp only [Multiset.map_map, Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one] at key
  rw [key]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Introduce `σ _ X w d A hX hiso hA δ hδ hsh`. Establish `hsurj` using `FiniteProjectionSheetedClosureEquations.surjective_of_no_germ A hA`. Distinguish the cases in `hz : ∀ᶠ t in 𝓝 (A w), δ t = 0`. Establish `hz' : ∀ᶠ z in 𝓝 w, δ (A z) = 0` using `(A.continuous.tendsto w).eventually hz`. Use `⟨1, fun _ _ => 1, fun _ => analyticAt_const, ?_, Eventually.of_forall fun z _ h => absurd (h 0) one_ne_zero⟩` and prove the remaining obligations.

Use `filter_upwards [hz'] with z hz0 _ hne`. Conclude with `absurd hz0 hne`. Take `⟨M, hM, hMsh⟩` from `hsh`. Take `⟨ρ, hρ, r, hr, hρM, hK⟩` from `hball σ X w d A hX hiso M hM`. Take `⟨r₂, hr₂, hδr⟩` from `Metric.eventually_nhds_iff_ball.1 hδ.eventually_analyticAt`.

Use `set D : Set (Fin d → ℂ) := Metric.ball (A w) (min r r₂) with hDdef`. Use `set Y : Set (σ → ℂ) := {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ D} with hYdef`. Establish `hDo : IsOpen D` using `Metric.isOpen_ball`. Establish `hDc : IsPreconnected D` using `(convex_ball _ _).isPreconnected`. Establish `hwD : A w ∈ D` using `Metric.mem_ball_self (lt_min hr hr₂)`.

Establish `hmap : Set.MapsTo A Y D` using `fun x hx => hx.2`. Establish `hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}`. Introduce `K hKD hKc`. Establish `hKr : K ⊆ Metric.ball (A w) r` using `hKD.trans (Metric.ball_subset_ball (min_le_left _ _))`. Establish `heq : {x | x ∈ Y ∧ A x ∈ K} = {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K}`.

Use extensionality with `x`. Conclude with `⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hKD h.2⟩, h.2⟩⟩`. Rewrite using `[heq]`. Conclude with `hK K hKr hKc`. Establish `hδD : AnalyticOnNhd ℂ δ D` using `fun t ht => hδr t (Metric.ball_subset_ball (min_le_right _ _) ht)`.

Establish `hne : ∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ D → W.Nonempty → ∃ t ∈ W, δ t ≠ 0`. Introduce and unpack `W hWo hWD ⟨t, ht⟩`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Establish `hev : δ =ᶠ[𝓝 t] 0` using `by filter_upwards [hWo.mem_nhds ht] with s hs`.

Conclude with `hall s hs`. Establish `h0` using `hδD.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc (hWD ht) hev`. Apply `hz` to reduce the goal to its premises. Use `filter_upwards [hDo.mem_nhds hwD] with s hs`. Conclude with `h0 hs`.

Establish `hsec : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O`. Introduce `x hx hδx`. Take `⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩` from `hMsh x ⟨hx.1.1, hρM hx.1.2⟩ hδx`. Use `⟨O ∩ g ⁻¹' Metric.ball w ρ ∩ D, V ∩ Metric.ball w ρ ∩ A ⁻¹' D, g, (hg.continuousOn.isOpen_inter_preimage hO Metric.isOpen_ball).inter hDo, (hV.inter Metric.isOpen_ball).inter (hDo.preimage A.continuous), ⟨⟨hxV, hx.1.2⟩, hx.2⟩, hg.mono fun t ht => ht.1.1, fun y hy => hAg y hy.1.1, …` and prove the remaining obligations. Use extensionality with `z`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨⟨hzX, hzb⟩, hzD⟩, ⟨⟨hzV, -⟩, -⟩⟩`. Establish `hzg : z ∈ g '' O`. Rewrite using `[← hXV]`. Conclude with `⟨hzX, hzV⟩`.

Take `⟨t, ht, rfl⟩` from `hzg`. Use `⟨t, ⟨⟨ht, hzb⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite `hzD` using `[hAg t ht]`. Conclude with `hzD`. Introduce and unpack `⟨t, ⟨⟨ht, htb⟩, htD⟩, rfl⟩`.

Establish `hmem : g t ∈ X ∩ V`. Rewrite using `[hXV]`. Conclude with `⟨t, ht, rfl⟩`. Establish `hA' : A (g t) ∈ D`. Rewrite using `[hAg t ht]`.

Conclude with `htD`. Conclude with `⟨⟨⟨hmem.1, htb⟩, hA'⟩, ⟨⟨hmem.2, htb⟩, hA'⟩⟩`. Take `⟨N, hN⟩` from `hcount σ Y d A D δ hDo hDc hmap hprop hδD fun x hx hx' => by`. Take `⟨O, V, g, hO, hV, hxV, hg, hAg, hYV⟩` from `hsec x hx hx'`. Conclude with `⟨O, V, g, hO, hV, hxV, hg.continuousOn, hAg, hYV⟩`.

Set `l : (σ → Fin (N + 1)) → (σ → ℂ) →L[ℂ] ℂ` to `fun u => ∑ i, ((u i : ℕ) : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i`. Establish `hl : ∀ u z, l u z = ∑ i, ((u i : ℕ) : ℂ) * z i`. Introduce `u z`. Simplify using `[l]`. Use `choose F hFan hFeq using fun u j => hesymm σ Y d A D δ (l u) j hDo hmap hprop hδD hne hsec`.

Set `c : (σ → Fin (N + 1)) → (σ → ℂ) → ℂ` to `fun u z => ∑ j ∈ Finset.range (N + 1), (-1) ^ j * F u j (A z) * l u z ^ (N - j)`. Establish `hfib : ∀ z, A z ∈ D → δ (A z) ≠ 0 → ∃ s : Finset (σ → ℂ), (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = A z} ∧ s.card = N`. Introduce `z hzD hδz`. Establish `h` using `hN (A z) hzD hδz`. Establish `hfin` using `Set.finite_of_encard_eq_coe h`.

Use `⟨hfin.toFinset, hfin.coe_toFinset, ?_⟩` and prove the remaining obligations. Establish `h' : ((hfin.toFinset : Finset (σ → ℂ)) : Set (σ → ℂ)).encard = N`. Rewrite using `[hfin.coe_toFinset]`. Conclude with `h`. Rewrite `h'` using `[Set.encard_coe_eq_coe_finsetCard]`.

Conclude with `h'` after adjusting the coercions. Establish `hprod : ∀ u z, A z ∈ D → δ (A z) ≠ 0 → ∀ s : Finset (σ → ℂ), (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = A z} → s.card = N → c u z = ∏ x ∈ s, (l u z - l u x)`. Introduce `u z hzD hδz s hs hcard`. Establish `hm : Multiset.card (s.val.map (l u)) = N` using `by simp [hcard]`. Establish `key` using `FiniteProjectionSheetedClosureEquations.prod_sub_eq_sum_esymm (s.val.map (l u)) (l u z)`.

Rewrite `key` using `[hm, Multiset.map_map]`. Rewrite using `[Finset.prod_eq_multiset_prod]`. Use `Eq.trans ?_ key.symm` and prove the remaining obligations. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hFeq u j (A z) hzD hδz s hs]`.

Establish `hcan : ∀ u z, A z ∈ D → AnalyticAt ℂ (c u) z`. Introduce `u z hzD`. Use `Finset.analyticAt_fun_sum (𝕜 := ℂ) (f := fun j z => (-1 : ℂ) ^ j * F u j (A z) * l u z ^ (N - j)) _ fun j _ => ?_` and prove the remaining obligations. Establish `h1 : AnalyticAt ℂ (F u j ∘ A) z` using `(hFan u j (A z) hzD).comp (ContinuousLinearMap.analyticAt A z)`. Establish `h2 : AnalyticAt ℂ (fun z => l u z ^ (N - j)) z` using `((l u).analyticAt z).pow _`.

Establish `h0 : AnalyticAt ℂ (fun _ : σ → ℂ => ((-1 : ℂ) ^ j)) z` using `analyticAt_const`. Conclude with `(h0.mul h1).mul h2`. Set `e` to `(Fintype.equivFin (σ → Fin (N + 1))).symm`. Establish `hBw : Metric.ball w ρ ∩ A ⁻¹' D ∈ 𝓝 w` using `(Metric.isOpen_ball.inter (hDo.preimage A.continuous)).mem_nhds ⟨Metric.mem_ball_self hρ, hwD⟩`. Use `⟨Fintype.card (σ → Fin (N + 1)), fun k => c (e k), fun k => hcan _ w hwD, ?_, ?_⟩` and prove the remaining obligations.

Use `filter_upwards [hBw] with z hz hzX hδz k`. Take `⟨s, hs, hcard⟩` from `hfib z hz.2 hδz`. Rewrite using `[hprod _ z hz.2 hδz s hs hcard]`. Establish `hzs : z ∈ (↑s : Set (σ → ℂ))`. Rewrite using `[hs]`.

Conclude with `⟨⟨⟨hzX, hz.1⟩, hz.2⟩, rfl⟩`. Conclude with `Finset.prod_eq_zero hzs (sub_self _)`. Use `filter_upwards [hBw] with z₀ hz₀ hz₀X hall`. Assume the negation of the conclusion as `hcl`. Use `set Z : Set (σ → ℂ) := {x | x ∈ Y ∧ δ (A x) ≠ 0} with hZdef`.

Establish `hZb : Bornology.IsBounded Z` using `Metric.isBounded_ball.subset fun x hx => hx.1.1.2`. Establish `hZsub : Z ⊆ {x | x ∈ X ∧ δ (A x) ≠ 0}` using `fun x hx => ⟨hx.1.1.1, hx.2⟩`. Establish `hZcl : z₀ ∉ closure Z` using `fun h => hcl (closure_mono hZsub h)`. Take `⟨μ, hμ, U, hU, hbound⟩` from `hgrid σ N Z z₀ hZb hZcl`. Establish `hsmall : ∀ᶠ z in 𝓝 z₀, ∀ u, ‖c u z‖ < μ`.

Rewrite using `[Filter.eventually_all]`. Introduce `u`. Establish `h0 : c u z₀ = 0`. Use `hall (e.symm u)` as an intermediate fact. Simplify `this` using `only [Equiv.apply_symm_apply]`.

Establish `hcont : Tendsto (fun x => ‖c u x‖) (𝓝 z₀) (𝓝 ‖c u z₀‖)` using `(hcan u z₀ hz₀.2).continuousAt.norm.tendsto`. Rewrite `hcont` using `[h0, norm_zero]`. Conclude with `hcont.eventually (gt_mem_nhds hμ)`. Take `⟨W, hWsub, hWo, hz₀W⟩` from `mem_nhds_iff.1 (inter_mem (inter_mem hU hsmall) ((hDo.preimage A.continuous).mem_nhds hz₀.2))`. Take `⟨t, ⟨z, hzW, rfl⟩, hδt⟩` from `hne (A '' W) (A.isOpenMap hsurj W hWo) (by rintro t ⟨z, hz, rfl⟩; exact (hWsub hz).2) ⟨A z₀, z₀, hz₀W, rfl⟩`.

Take `⟨⟨hzU, hzc⟩, hzD⟩` from `hWsub hzW`. Take `⟨s, hs, hcard⟩` from `hfib z hzD hδt`. Establish `hsZ : (↑s : Set (σ → ℂ)) ⊆ Z`. Rewrite using `[hs]`. Introduce and unpack `x ⟨hxY, hxA⟩`.

Conclude with `⟨hxY, by rw [hxA]; exact hδt⟩`. Take `⟨u, hu⟩` from `hbound z hzU s hsZ hcard.le`. Establish `hlt` using `hzc u`. Rewrite `hlt` using `[hprod u z hzD hδt s hs hcard]`. Establish `heq : ∏ x ∈ s, (l u z - l u x) = ∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i)`.

Use `Finset.prod_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[hl, hl, ← Finset.sum_sub_distrib]`. Simplify using `[mul_sub]`. Rewrite `hlt` using `[heq]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem FiniteProjectionSheetedClosureEquations.proof
    (hball : FiniteProjectionProperBall.Statement)
    (hcount : UnbranchedProperCountConstant.Statement)
    (hesymm : ProperSheetedFibreEsymm.Statement)
    (hgrid : GridProductLowerBound.Statement) :
    FiniteProjectionSheetedClosureEquations.Statement := by
  intro σ _ X w d A hX hiso hA δ hδ hsh
  classical
  have hsurj := FiniteProjectionSheetedClosureEquations.surjective_of_no_germ A hA
  by_cases hz : ∀ᶠ t in 𝓝 (A w), δ t = 0
  · have hz' : ∀ᶠ z in 𝓝 w, δ (A z) = 0 := (A.continuous.tendsto w).eventually hz
    refine ⟨1, fun _ _ => 1, fun _ => analyticAt_const, ?_,
      Eventually.of_forall fun z _ h => absurd (h 0) one_ne_zero⟩
    filter_upwards [hz'] with z hz0 _ hne
    exact absurd hz0 hne
  obtain ⟨M, hM, hMsh⟩ := hsh
  obtain ⟨ρ, hρ, r, hr, hρM, hK⟩ := hball σ X w d A hX hiso M hM
  obtain ⟨r₂, hr₂, hδr⟩ := Metric.eventually_nhds_iff_ball.1 hδ.eventually_analyticAt
  set D : Set (Fin d → ℂ) := Metric.ball (A w) (min r r₂) with hDdef
  set Y : Set (σ → ℂ) := {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ D} with hYdef
  have hDo : IsOpen D := Metric.isOpen_ball
  have hDc : IsPreconnected D := (convex_ball _ _).isPreconnected
  have hwD : A w ∈ D := Metric.mem_ball_self (lt_min hr hr₂)
  have hmap : Set.MapsTo A Y D := fun x hx => hx.2
  have hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K} := by
    intro K hKD hKc
    have hKr : K ⊆ Metric.ball (A w) r := hKD.trans (Metric.ball_subset_ball (min_le_left _ _))
    have heq : {x | x ∈ Y ∧ A x ∈ K} = {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K} := by
      ext x
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hKD h.2⟩, h.2⟩⟩
    rw [heq]
    exact hK K hKr hKc
  have hδD : AnalyticOnNhd ℂ δ D := fun t ht => hδr t (Metric.ball_subset_ball (min_le_right _ _) ht)
  have hne : ∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ D → W.Nonempty → ∃ t ∈ W, δ t ≠ 0 := by
    rintro W hWo hWD ⟨t, ht⟩
    by_contra hall
    push Not at hall
    have hev : δ =ᶠ[𝓝 t] 0 := by
      filter_upwards [hWo.mem_nhds ht] with s hs
      exact hall s hs
    have h0 := hδD.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc (hWD ht) hev
    apply hz
    filter_upwards [hDo.mem_nhds hwD] with s hs
    exact h0 hs
  have hsec : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O := by
    intro x hx hδx
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hMsh x ⟨hx.1.1, hρM hx.1.2⟩ hδx
    refine ⟨O ∩ g ⁻¹' Metric.ball w ρ ∩ D, V ∩ Metric.ball w ρ ∩ A ⁻¹' D, g,
      (hg.continuousOn.isOpen_inter_preimage hO Metric.isOpen_ball).inter hDo,
      (hV.inter Metric.isOpen_ball).inter (hDo.preimage A.continuous), ⟨⟨hxV, hx.1.2⟩, hx.2⟩,
      hg.mono fun t ht => ht.1.1, fun y hy => hAg y hy.1.1, ?_⟩
    ext z
    constructor
    · rintro ⟨⟨⟨hzX, hzb⟩, hzD⟩, ⟨⟨hzV, -⟩, -⟩⟩
      have hzg : z ∈ g '' O := by
        rw [← hXV]
        exact ⟨hzX, hzV⟩
      obtain ⟨t, ht, rfl⟩ := hzg
      refine ⟨t, ⟨⟨ht, hzb⟩, ?_⟩, rfl⟩
      rw [hAg t ht] at hzD
      exact hzD
    · rintro ⟨t, ⟨⟨ht, htb⟩, htD⟩, rfl⟩
      have hmem : g t ∈ X ∩ V := by
        rw [hXV]
        exact ⟨t, ht, rfl⟩
      have hA' : A (g t) ∈ D := by
        rw [hAg t ht]
        exact htD
      exact ⟨⟨⟨hmem.1, htb⟩, hA'⟩, ⟨⟨hmem.2, htb⟩, hA'⟩⟩
  obtain ⟨N, hN⟩ := hcount σ Y d A D δ hDo hDc hmap hprop hδD fun x hx hx' => by
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ := hsec x hx hx'
    exact ⟨O, V, g, hO, hV, hxV, hg.continuousOn, hAg, hYV⟩
  let l : (σ → Fin (N + 1)) → (σ → ℂ) →L[ℂ] ℂ := fun u =>
    ∑ i, ((u i : ℕ) : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i
  have hl : ∀ u z, l u z = ∑ i, ((u i : ℕ) : ℂ) * z i := by
    intro u z
    simp [l]
  choose F hFan hFeq using fun u j => hesymm σ Y d A D δ (l u) j hDo hmap hprop hδD hne hsec
  let c : (σ → Fin (N + 1)) → (σ → ℂ) → ℂ := fun u z =>
    ∑ j ∈ Finset.range (N + 1), (-1) ^ j * F u j (A z) * l u z ^ (N - j)
  have hfib : ∀ z, A z ∈ D → δ (A z) ≠ 0 → ∃ s : Finset (σ → ℂ),
      (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = A z} ∧ s.card = N := by
    intro z hzD hδz
    have h := hN (A z) hzD hδz
    have hfin := Set.finite_of_encard_eq_coe h
    refine ⟨hfin.toFinset, hfin.coe_toFinset, ?_⟩
    have h' : ((hfin.toFinset : Finset (σ → ℂ)) : Set (σ → ℂ)).encard = N := by
      rw [hfin.coe_toFinset]
      exact h
    rw [Set.encard_coe_eq_coe_finsetCard] at h'
    exact_mod_cast h'
  have hprod : ∀ u z, A z ∈ D → δ (A z) ≠ 0 → ∀ s : Finset (σ → ℂ),
      (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = A z} → s.card = N →
      c u z = ∏ x ∈ s, (l u z - l u x) := by
    intro u z hzD hδz s hs hcard
    have hm : Multiset.card (s.val.map (l u)) = N := by simp [hcard]
    have key := FiniteProjectionSheetedClosureEquations.prod_sub_eq_sum_esymm (s.val.map (l u)) (l u z)
    rw [hm, Multiset.map_map] at key
    rw [Finset.prod_eq_multiset_prod]
    refine Eq.trans ?_ key.symm
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hFeq u j (A z) hzD hδz s hs]
  have hcan : ∀ u z, A z ∈ D → AnalyticAt ℂ (c u) z := by
    intro u z hzD
    refine Finset.analyticAt_fun_sum (𝕜 := ℂ)
      (f := fun j z => (-1 : ℂ) ^ j * F u j (A z) * l u z ^ (N - j)) _ fun j _ => ?_
    have h1 : AnalyticAt ℂ (F u j ∘ A) z := (hFan u j (A z) hzD).comp (ContinuousLinearMap.analyticAt A z)
    have h2 : AnalyticAt ℂ (fun z => l u z ^ (N - j)) z := ((l u).analyticAt z).pow _
    have h0 : AnalyticAt ℂ (fun _ : σ → ℂ => ((-1 : ℂ) ^ j)) z := analyticAt_const
    exact (h0.mul h1).mul h2
  let e := (Fintype.equivFin (σ → Fin (N + 1))).symm
  have hBw : Metric.ball w ρ ∩ A ⁻¹' D ∈ 𝓝 w :=
    (Metric.isOpen_ball.inter (hDo.preimage A.continuous)).mem_nhds ⟨Metric.mem_ball_self hρ, hwD⟩
  refine ⟨Fintype.card (σ → Fin (N + 1)), fun k => c (e k), fun k => hcan _ w hwD, ?_, ?_⟩
  · filter_upwards [hBw] with z hz hzX hδz k
    obtain ⟨s, hs, hcard⟩ := hfib z hz.2 hδz
    rw [hprod _ z hz.2 hδz s hs hcard]
    have hzs : z ∈ (↑s : Set (σ → ℂ)) := by
      rw [hs]
      exact ⟨⟨⟨hzX, hz.1⟩, hz.2⟩, rfl⟩
    exact Finset.prod_eq_zero hzs (sub_self _)
  · filter_upwards [hBw] with z₀ hz₀ hz₀X hall
    by_contra hcl
    set Z : Set (σ → ℂ) := {x | x ∈ Y ∧ δ (A x) ≠ 0} with hZdef
    have hZb : Bornology.IsBounded Z := Metric.isBounded_ball.subset fun x hx => hx.1.1.2
    have hZsub : Z ⊆ {x | x ∈ X ∧ δ (A x) ≠ 0} := fun x hx => ⟨hx.1.1.1, hx.2⟩
    have hZcl : z₀ ∉ closure Z := fun h => hcl (closure_mono hZsub h)
    obtain ⟨μ, hμ, U, hU, hbound⟩ := hgrid σ N Z z₀ hZb hZcl
    have hsmall : ∀ᶠ z in 𝓝 z₀, ∀ u, ‖c u z‖ < μ := by
      rw [Filter.eventually_all]
      intro u
      have h0 : c u z₀ = 0 := by
        have := hall (e.symm u)
        simpa only [Equiv.apply_symm_apply] using this
      have hcont : Tendsto (fun x => ‖c u x‖) (𝓝 z₀) (𝓝 ‖c u z₀‖) :=
        (hcan u z₀ hz₀.2).continuousAt.norm.tendsto
      rw [h0, norm_zero] at hcont
      exact hcont.eventually (gt_mem_nhds hμ)
    obtain ⟨W, hWsub, hWo, hz₀W⟩ :=
      mem_nhds_iff.1 (inter_mem (inter_mem hU hsmall) ((hDo.preimage A.continuous).mem_nhds hz₀.2))
    obtain ⟨t, ⟨z, hzW, rfl⟩, hδt⟩ := hne (A '' W) (A.isOpenMap hsurj W hWo)
      (by rintro t ⟨z, hz, rfl⟩; exact (hWsub hz).2) ⟨A z₀, z₀, hz₀W, rfl⟩
    obtain ⟨⟨hzU, hzc⟩, hzD⟩ := hWsub hzW
    obtain ⟨s, hs, hcard⟩ := hfib z hzD hδt
    have hsZ : (↑s : Set (σ → ℂ)) ⊆ Z := by
      rw [hs]
      rintro x ⟨hxY, hxA⟩
      exact ⟨hxY, by rw [hxA]; exact hδt⟩
    obtain ⟨u, hu⟩ := hbound z hzU s hsZ hcard.le
    have hlt := hzc u
    rw [hprod u z hzD hδt s hs hcard] at hlt
    have heq : ∏ x ∈ s, (l u z - l u x) = ∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i) := by
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [hl, hl, ← Finset.sum_sub_distrib]
      simp [mul_sub]
    rw [heq] at hlt
    linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
