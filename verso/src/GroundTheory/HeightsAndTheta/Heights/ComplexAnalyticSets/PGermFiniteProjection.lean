import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermFiniteProjection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

/- English proof (translation)
Take `⟨r, hr, han⟩` from `ha.exists_ball_analyticOnNhd`. Use `filter_upwards [Metric.ball_mem_nhds a hr] with y hy`. Distinguish the cases in `hv : y - a = 0`. Establish `hya : y = a` using `sub_eq_zero.1 hv`. Establish `h0` using `(hl 0).self_of_nhds`.

Simplify `h0` using `[hya]`. Establish `hvpos : 0 < ‖y - a‖` using `norm_pos_iff.2 hv`. Establish `hmaps : ∀ t ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖), a + t • (y - a) ∈ Metric.ball a r`. Introduce `t ht`. Rewrite `ht` using `[Metric.mem_ball, dist_zero_right, lt_div_iff₀ hvpos]`.

Rewrite using `[Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]`. Conclude with `ht`. Establish `hg : AnalyticOnNhd ℂ (fun t : ℂ => h (a + t • (y - a))) (Metric.ball (0 : ℂ) (r / ‖y - a‖))`. Introduce `t ht`. Establish `h1 : AnalyticAt ℂ (fun t : ℂ => a + t • (y - a)) t` using `by fun_prop`.

Conclude with `AnalyticAt.comp (g := h) (f := fun s : ℂ => a + s • (y - a)) (han _ (hmaps t ht)) h1`. Establish `h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖)`. Rewrite using `[Metric.mem_ball, dist_zero_right, norm_one, one_lt_div hvpos, ← dist_eq_norm]`. Conclude with `hy`. Establish `h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖)` using `Metric.mem_ball_self (div_pos hr hvpos)`.

Establish `hz` using `hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (0 : ℂ) _).isPreconnected h0 (by filter_upwards [hl (y - a)] with t ht using ht) h1`. Simplify using `using hz`.
-/
theorem eventually_eq_zero_of_lines {d : ℕ} {h : (Fin d → ℂ) → ℂ} {a : Fin d → ℂ}
    (ha : AnalyticAt ℂ h a) (hl : ∀ v : Fin d → ℂ, ∀ᶠ t in 𝓝 (0 : ℂ), h (a + t • v) = 0) :
    ∀ᶠ y in 𝓝 a, h y = 0 := by
  obtain ⟨r, hr, han⟩ := ha.exists_ball_analyticOnNhd
  filter_upwards [Metric.ball_mem_nhds a hr] with y hy
  by_cases hv : y - a = 0
  · have hya : y = a := sub_eq_zero.1 hv
    have h0 := (hl 0).self_of_nhds
    simpa [hya] using h0
  have hvpos : 0 < ‖y - a‖ := norm_pos_iff.2 hv
  have hmaps : ∀ t ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖), a + t • (y - a) ∈ Metric.ball a r := by
    intro t ht
    rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hvpos] at ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact ht
  have hg : AnalyticOnNhd ℂ (fun t : ℂ => h (a + t • (y - a))) (Metric.ball (0 : ℂ) (r / ‖y - a‖)) := by
    intro t ht
    have h1 : AnalyticAt ℂ (fun t : ℂ => a + t • (y - a)) t := by fun_prop
    exact AnalyticAt.comp (g := h) (f := fun s : ℂ => a + s • (y - a)) (han _ (hmaps t ht)) h1
  have h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖) := by
    rw [Metric.mem_ball, dist_zero_right, norm_one, one_lt_div hvpos, ← dist_eq_norm]
    exact hy
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖) := Metric.mem_ball_self (div_pos hr hvpos)
  have hz := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (0 : ℂ) _).isPreconnected h0
    (by filter_upwards [hl (y - a)] with t ht using ht) h1
  simpa using hz

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `hne (eventually_eq_zero_of_lines ha fun v => ?_)` and prove the remaining obligations. Establish `h1 : AnalyticAt ℂ (fun t : ℂ => a + t • v) 0` using `by fun_prop`. Establish `ha' : AnalyticAt ℂ h (a + (0 : ℂ) • v)` using `by simpa using ha`. Break down `(AnalyticAt.comp (g := h) (f := fun s : ℂ => a + s • v) ha' h1).eventually_eq_zero_or_eventually_ne_zero with h0 | h0` into its components or cases.

Conclude with `h0`. Conclude with `absurd ⟨v, h0⟩ hcon`.
-/
theorem exists_line_eventually_ne_zero {d : ℕ} {h : (Fin d → ℂ) → ℂ} {a : Fin d → ℂ}
    (ha : AnalyticAt ℂ h a) (hne : ¬ ∀ᶠ y in 𝓝 a, h y = 0) :
    ∃ v : Fin d → ℂ, ∀ᶠ t in 𝓝[≠] (0 : ℂ), h (a + t • v) ≠ 0 := by
  by_contra hcon
  refine hne (eventually_eq_zero_of_lines ha fun v => ?_)
  have h1 : AnalyticAt ℂ (fun t : ℂ => a + t • v) 0 := by fun_prop
  have ha' : AnalyticAt ℂ h (a + (0 : ℂ) • v) := by simpa using ha
  rcases (AnalyticAt.comp (g := h) (f := fun s : ℂ => a + s • v) ha' h1).eventually_eq_zero_or_eventually_ne_zero with h0 | h0
  · exact h0
  · exact absurd ⟨v, h0⟩ hcon

/- English proof (translation)
Establish `hrank : Module.finrank ℂ ((Fin d → ℂ) ⧸ (ℂ ∙ v)) = Module.finrank ℂ (Fin (d - 1) → ℂ)`. Establish `h1` using `Submodule.finrank_quotient_add_finrank (ℂ ∙ v)`. Rewrite `h1` using `[finrank_span_singleton hv, Module.finrank_fin_fun]`. Rewrite using `[Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers.

Set `e` to `LinearEquiv.ofFinrankEq _ _ hrank`. Use `⟨LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ (ℂ ∙ v).mkQ), fun y y' hyy => ?_⟩` and prove the remaining obligations. Establish `hq : (ℂ ∙ v).mkQ y = (ℂ ∙ v).mkQ y'` using `e.injective hyy`. Rewrite `hq` using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_span_singleton]`. Take `⟨t, ht⟩` from `hq`.

Conclude with `⟨t, by rw [ht]; abel⟩`.
-/
theorem exists_proj_fibres_line {d : ℕ} (v : Fin d → ℂ) (hv : v ≠ 0) :
    ∃ π : (Fin d → ℂ) →L[ℂ] (Fin (d - 1) → ℂ), ∀ y y', π y = π y' → ∃ t : ℂ, y = y' + t • v := by
  have hrank : Module.finrank ℂ ((Fin d → ℂ) ⧸ (ℂ ∙ v)) = Module.finrank ℂ (Fin (d - 1) → ℂ) := by
    have h1 := Submodule.finrank_quotient_add_finrank (ℂ ∙ v)
    rw [finrank_span_singleton hv, Module.finrank_fin_fun] at h1
    rw [Module.finrank_fin_fun]
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hrank
  refine ⟨LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ (ℂ ∙ v).mkQ), fun y y' hyy => ?_⟩
  have hq : (ℂ ∙ v).mkQ y = (ℂ ∙ v).mkQ y' := e.injective hyy
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_span_singleton] at hq
  obtain ⟨t, ht⟩ := hq
  exact ⟨t, by rw [ht]; abel⟩

/- English proof (translation)
Introduce `σ _ X w _ hirr`. Establish `hw : w ∈ X` using `hirr.1`. Establish `hP : ∃ d : ℕ, ∃ A : (σ → ℂ) →L[ℂ] (Fin d → ℂ), ∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w`. Set `e : (σ → ℂ) ≃ₗ[ℂ] (Fin (Fintype.card σ) → ℂ)` to `LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm`. Conclude with `⟨Fintype.card σ, LinearMap.toContinuousLinearMap e.toLinearMap, Set.univ, univ_mem, fun x _ hx => e.injective hx⟩`.

Take `⟨A, W, hW, hAW⟩` from `Nat.find_spec hP`. Use `⟨Nat.find hP, A, ⟨W, hW, hAW⟩, fun h hh hXh => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hAw : h (A w) = 0` using `hXh.self_of_nhds hw`. Take `⟨v, hv⟩` from `exists_line_eventually_ne_zero hh hne`.

Establish `hv0 : v ≠ 0`. Introduce and unpack `rfl`. Take `⟨t, ht⟩` from `hv.exists`. Simplify using `[hAw] at ht`. Establish `hd : Nat.find hP - 1 < Nat.find hP`.

Establish `: 0 < Nat.find hP` using `Nat.pos_of_ne_zero fun h0 => hv0 (funext fun i => (Fin.cast h0 i).elim0)`. Use linear arithmetic over natural numbers and integers. Take `⟨π, hπ⟩` from `exists_proj_fibres_line v hv0`. Take `⟨ε, hε, hεv⟩` from `Metric.mem_nhdsWithin_iff.1 hv`. Establish `hvpos : 0 < ‖v‖` using `norm_pos_iff.2 hv0`.

Establish `hcont : ∀ᶠ x in 𝓝 w, A x ∈ Metric.ball (A w) (ε * ‖v‖)` using `A.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (mul_pos hε hvpos))`. Use `Nat.find_min hP hd ⟨π.comp A, W ∩ {x | (x ∈ X → h (A x) = 0) ∧ A x ∈ Metric.ball (A w) (ε * ‖v‖)}, inter_mem hW (hXh.and hcont), ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨hxX, hxW, hxh, hxb⟩ hπx`. Apply `hAW x ⟨hxX, hxW⟩` to reduce the goal to its premises. Take `⟨t, ht⟩` from `hπ (A x) (A w) hπx`.

Distinguish the cases in `ht0 : t = 0`. Simplify `ht` using `[ht0]`. It suffices to derive a contradiction. Establish `htε : t ∈ Metric.ball (0 : ℂ) ε`. Rewrite using `[Metric.mem_ball, dist_zero_right]`.

Establish `hb : ‖t • v‖ < ε * ‖v‖`. Rewrite `hxb` using `[Metric.mem_ball, dist_eq_norm, ht, add_sub_cancel_left]`. Conclude with `hxb`. Rewrite `hb` using `[norm_smul]`. Conclude with `lt_of_mul_lt_mul_right hb hvpos.le`.

Conclude with `hεv ⟨htε, ht0⟩ (by rw [← ht]; exact hxh hxX)`.
-/
theorem GermFiniteProjection.proof : GermFiniteProjection.Statement := by
  intro σ _ X w _ hirr
  classical
  have hw : w ∈ X := hirr.1
  have hP : ∃ d : ℕ, ∃ A : (σ → ℂ) →L[ℂ] (Fin d → ℂ), ∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w := by
    let e : (σ → ℂ) ≃ₗ[ℂ] (Fin (Fintype.card σ) → ℂ) :=
      LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm
    exact ⟨Fintype.card σ, LinearMap.toContinuousLinearMap e.toLinearMap, Set.univ, univ_mem,
      fun x _ hx => e.injective hx⟩
  obtain ⟨A, W, hW, hAW⟩ := Nat.find_spec hP
  refine ⟨Nat.find hP, A, ⟨W, hW, hAW⟩, fun h hh hXh => ?_⟩
  by_contra hne
  have hAw : h (A w) = 0 := hXh.self_of_nhds hw
  obtain ⟨v, hv⟩ := exists_line_eventually_ne_zero hh hne
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hv.exists
    simp [hAw] at ht
  have hd : Nat.find hP - 1 < Nat.find hP := by
    have : 0 < Nat.find hP := Nat.pos_of_ne_zero fun h0 => hv0 (funext fun i => (Fin.cast h0 i).elim0)
    omega
  obtain ⟨π, hπ⟩ := exists_proj_fibres_line v hv0
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhdsWithin_iff.1 hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hcont : ∀ᶠ x in 𝓝 w, A x ∈ Metric.ball (A w) (ε * ‖v‖) :=
    A.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (mul_pos hε hvpos))
  refine Nat.find_min hP hd ⟨π.comp A, W ∩ {x | (x ∈ X → h (A x) = 0) ∧ A x ∈ Metric.ball (A w) (ε * ‖v‖)},
    inter_mem hW (hXh.and hcont), ?_⟩
  rintro x ⟨hxX, hxW, hxh, hxb⟩ hπx
  apply hAW x ⟨hxX, hxW⟩
  obtain ⟨t, ht⟩ := hπ (A x) (A w) hπx
  by_cases ht0 : t = 0
  · simpa [ht0] using ht
  exfalso
  have htε : t ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    have hb : ‖t • v‖ < ε * ‖v‖ := by
      rw [Metric.mem_ball, dist_eq_norm, ht, add_sub_cancel_left] at hxb
      exact hxb
    rw [norm_smul] at hb
    exact lt_of_mul_lt_mul_right hb hvpos.le
  exact hεv ⟨htε, ht0⟩ (by rw [← ht]; exact hxh hxX)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
