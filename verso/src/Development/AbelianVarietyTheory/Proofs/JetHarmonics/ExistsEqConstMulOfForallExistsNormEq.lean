import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero

namespace GlobalTheory

open Metric Set Filter Topology

/- English proof (translation)
Distinguish the cases in `h0 : ∀ᶠ y in 𝓝 x, Q y = 0`. Use `⟨x, hx, 0, ?_⟩ filter_upwards [h, h0] with y hy hy0` and prove the remaining obligations. Rewrite `hy` using `[hy0, norm_zero, norm_eq_zero]`. Simplify using `[hy]`. Establish `hfr : ∃ᶠ y in 𝓝 x, Q y ≠ 0` using `not_eventually.mp h0`.

Take `⟨z, hz0, hzO, hz⟩` from `(hfr.and_eventually (Filter.Eventually.and (hO.mem_nhds hx) h.eventually_nhds)).exists`. Establish `hzO' : z ∈ O` using `hzO`. Establish `hne : ∀ᶠ y in 𝓝 z, Q y ≠ 0` using `(hQ.continuousOn.continuousAt (hO.mem_nhds hzO')).eventually_ne hz0`. Establish `hall : ∀ᶠ y in 𝓝 z, y ∈ O ∧ Q y ≠ 0 ∧ ‖P y‖ = ‖Q y‖` using `Filter.Eventually.and (hO.mem_nhds hzO') (hne.and hz)`. Take `⟨ε, hε, hb⟩` from `Metric.eventually_nhds_iff_ball.mp hall`.

Establish `hsub : ball z ε ⊆ O` using `fun y hy => (hb y hy).1`. Establish `hd : DifferentiableOn ℂ (fun y => P y / Q y) (ball z ε)`. Simplify using `only [div_eq_mul_inv]`. Conclude with `(hP.mono hsub).mul ((hQ.mono hsub).inv (fun y hy => (hb y hy).2.1))`. Establish `hn : ∀ y ∈ ball z ε, ‖P y / Q y‖ = 1`.

Introduce `y hy`. Rewrite using `[norm_div, (hb y hy).2.2, div_self (norm_ne_zero_iff.mpr (hb y hy).2.1)]`. Establish `hmax : IsMaxOn (norm ∘ fun y => P y / Q y) (ball z ε) z`. Introduce `y hy`. Use `show ‖P y / Q y‖ ≤ ‖P z / Q z‖`.

Rewrite using `[hn y hy, hn z (mem_ball_self hε)]`. Establish `hc` using `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball z ε).isPreconnected isOpen_ball hd (mem_ball_self hε) hmax`. Use `⟨z, hzO', P z / Q z, ?_⟩` and prove the remaining obligations. Use `filter_upwards [ball_mem_nhds z hε] with y hy`. Establish `e : P y / Q y = P z / Q z` using `hc hy`.

Rewrite using `[← e, div_mul_cancel₀ _ (hb y hy).2.1]`.
-/
theorem exists_eventually_eq_mul_of_norm_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {O : Set V} (hO : IsOpen O) {P Q : V → ℂ} (hP : DifferentiableOn ℂ P O) (hQ : DifferentiableOn ℂ Q O)
    {x : V} (hx : x ∈ O) (h : ∀ᶠ y in 𝓝 x, ‖P y‖ = ‖Q y‖) :
    ∃ z ∈ O, ∃ c : ℂ, ∀ᶠ y in 𝓝 z, P y = c * Q y := by
  by_cases h0 : ∀ᶠ y in 𝓝 x, Q y = 0
  · refine ⟨x, hx, 0, ?_⟩
    filter_upwards [h, h0] with y hy hy0
    rw [hy0, norm_zero, norm_eq_zero] at hy
    simp [hy]
  · have hfr : ∃ᶠ y in 𝓝 x, Q y ≠ 0 := not_eventually.mp h0
    obtain ⟨z, hz0, hzO, hz⟩ :=
      (hfr.and_eventually (Filter.Eventually.and (hO.mem_nhds hx) h.eventually_nhds)).exists
    have hzO' : z ∈ O := hzO
    have hne : ∀ᶠ y in 𝓝 z, Q y ≠ 0 :=
      (hQ.continuousOn.continuousAt (hO.mem_nhds hzO')).eventually_ne hz0
    have hall : ∀ᶠ y in 𝓝 z, y ∈ O ∧ Q y ≠ 0 ∧ ‖P y‖ = ‖Q y‖ :=
      Filter.Eventually.and (hO.mem_nhds hzO') (hne.and hz)
    obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.mp hall
    have hsub : ball z ε ⊆ O := fun y hy => (hb y hy).1
    have hd : DifferentiableOn ℂ (fun y => P y / Q y) (ball z ε) := by
      simp only [div_eq_mul_inv]
      exact (hP.mono hsub).mul ((hQ.mono hsub).inv (fun y hy => (hb y hy).2.1))
    have hn : ∀ y ∈ ball z ε, ‖P y / Q y‖ = 1 := by
      intro y hy
      rw [norm_div, (hb y hy).2.2, div_self (norm_ne_zero_iff.mpr (hb y hy).2.1)]
    have hmax : IsMaxOn (norm ∘ fun y => P y / Q y) (ball z ε) z := by
      intro y hy
      show ‖P y / Q y‖ ≤ ‖P z / Q z‖
      rw [hn y hy, hn z (mem_ball_self hε)]
    have hc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball z ε).isPreconnected
      isOpen_ball hd (mem_ball_self hε) hmax
    refine ⟨z, hzO', P z / Q z, ?_⟩
    filter_upwards [ball_mem_nhds z hε] with y hy
    have e : P y / Q y = P z / Q z := hc hy
    rw [← e, div_mul_cancel₀ _ (hb y hy).2.1]

/- English proof (translation)
Introduce `V _ _ _ ι _ O hO hc hne P Q hP hQ h`. Use `haveI : CompleteSpace V := FiniteDimensional.complete ℂ V`. Use `haveI : BaireSpace O := hO.baireSpace`. Use `haveI : Nonempty O := hne.to_subtype`. Establish `hcl : ∀ i, IsClosed {x : O | ‖P x‖ = ‖Q i x‖}` using `fun i => isClosed_eq (hP.continuousOn.restrict.norm) ((hQ i).continuousOn.restrict.norm)`.

Establish `hcov : ⋃ i, {x : O | ‖P x‖ = ‖Q i x‖} = univ`. Use `eq_univ_of_forall fun x => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `h x x.2`. Conclude with `mem_iUnion.mpr ⟨i, hi⟩`. Take `⟨i, x, hx⟩` from `nonempty_interior_of_iUnion_of_closed hcl hcov`.

Establish `hx1 : ∀ᶠ y : O in 𝓝 x, ‖P y‖ = ‖Q i y‖` using `mem_interior_iff_mem_nhds.mp hx`. Establish `hx2 : ∀ᶠ y in 𝓝 (x : V), ‖P y‖ = ‖Q i y‖`. Rewrite using `[← hO.isOpenEmbedding_subtypeVal.map_nhds_eq x]`. Conclude with `hx1`. Take `⟨z, hz, c, hzc⟩` from `exists_eventually_eq_mul_of_norm_eq hO hP (hQ i) x.2 hx2`.

Use `⟨i, c, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hd : DifferentiableOn ℂ (fun y => P y - c * Q i y) O` using `hP.sub ((hQ i).const_mul c)`. Use `ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_eventually hO hc hd hz (by filter_upwards [hzc] with y hy; simp [hy]) y hy` as an intermediate fact. Conclude with `sub_eq_zero.mp this`.
-/
theorem exists_eq_const_mul_of_forall_exists_norm_eq :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (ι : Type) [Countable ι]
      (O : Set V), IsOpen O → IsPreconnected O → O.Nonempty → ∀ (P : V → ℂ) (Q : ι → V → ℂ),
      DifferentiableOn ℂ P O → (∀ i, DifferentiableOn ℂ (Q i) O) → (∀ x ∈ O, ∃ i, ‖P x‖ = ‖Q i x‖) →
      ∃ (i : ι) (c : ℂ), ∀ x ∈ O, P x = c * Q i x := by
  intro V _ _ _ ι _ O hO hc hne P Q hP hQ h
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  haveI : BaireSpace O := hO.baireSpace
  haveI : Nonempty O := hne.to_subtype
  have hcl : ∀ i, IsClosed {x : O | ‖P x‖ = ‖Q i x‖} := fun i =>
    isClosed_eq (hP.continuousOn.restrict.norm) ((hQ i).continuousOn.restrict.norm)
  have hcov : ⋃ i, {x : O | ‖P x‖ = ‖Q i x‖} = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨i, hi⟩ := h x x.2
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hcov
  have hx1 : ∀ᶠ y : O in 𝓝 x, ‖P y‖ = ‖Q i y‖ := mem_interior_iff_mem_nhds.mp hx
  have hx2 : ∀ᶠ y in 𝓝 (x : V), ‖P y‖ = ‖Q i y‖ := by
    rw [← hO.isOpenEmbedding_subtypeVal.map_nhds_eq x]
    exact hx1
  obtain ⟨z, hz, c, hzc⟩ := exists_eventually_eq_mul_of_norm_eq hO hP (hQ i) x.2 hx2
  refine ⟨i, c, fun y hy => ?_⟩
  have hd : DifferentiableOn ℂ (fun y => P y - c * Q i y) O := hP.sub ((hQ i).const_mul c)
  have := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_eventually hO hc hd hz
    (by filter_upwards [hzc] with y hy; simp [hy]) y hy
  exact sub_eq_zero.mp this

end GlobalTheory
