import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphSt

noncomputable section

open Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

/- English proof (translation)
Rewrite using `[iteratedDeriv_eq_iterate]`. Conclude with `(hf.analyticOnNhd hV).iterated_deriv r`.
-/
theorem anNhd_iter {f : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (r : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv r f) V := by
  rw [iteratedDeriv_eq_iterate]
  exact (hf.analyticOnNhd hV).iterated_deriv r

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[iteratedDeriv_succ, ih]`. Use function extensionality and compare the values at `s`.

Rewrite using `[iteratedDeriv_succ]`. Establish `hd : DifferentiableAt ℂ (iteratedDeriv n f) (s : ℂ)` using `((anNhd_iter hV hf n) s (hR s)).differentiableAt`. Conclude with `hd.hasDerivAt.comp_ofReal.deriv`.
-/
theorem real_iter (f : ℂ → ℂ) (V : Set ℂ) (hV : IsOpen V) (hR : ∀ s : ℝ, (s : ℂ) ∈ V)
    (hf : DifferentiableOn ℂ f V) (r : ℕ) :
    iteratedDeriv r (fun t : ℝ => f t) = fun s : ℝ => iteratedDeriv r f s := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [iteratedDeriv_succ]
    have hd : DifferentiableAt ℂ (iteratedDeriv n f) (s : ℂ) :=
      ((anNhd_iter hV hf n) s (hR s)).differentiableAt
    exact hd.hasDerivAt.comp_ofReal.deriv

/- English proof (translation)
Use `⟨fun f V hV hR hf r s => congrFun (real_iter f V hV hR hf r) s, ?_⟩` and prove the remaining obligations. Introduce `f V hV hR hf h0 s`. Establish `hA` using `hf.analyticOnNhd hV`. Establish `h0V : (0 : ℂ) ∈ V` using `by simpa using hR 0`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.mp hV 0 h0V`.

Establish `hloc : f =ᶠ[𝓝 (0 : ℂ)] 0` using `by filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with z hz`. Rewrite using `[← Complex.taylorSeries_eq_on_ball' hz (hf.mono hball)]`. Simplify using `[h0]`. Establish `hpre : IsPreconnected (Set.range ((↑) : ℝ → ℂ))` using `(isConnected_range Complex.continuous_ofReal).isPreconnected`. Establish `hsub` using `hpre.subset_connectedComponentIn (x := (0 : ℂ)) ⟨0, by simp⟩ (by rintro _ ⟨t, rfl⟩; exact hR t)`.

Establish `hEq` using `(hA.mono (connectedComponentIn_subset V 0)).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_connectedComponentIn (mem_connectedComponentIn h0V) hloc`. Simplify using `using hEq (hsub ⟨s, rfl⟩)`.
-/
theorem helpC : HelpC := by
  refine ⟨fun f V hV hR hf r s => congrFun (real_iter f V hV hR hf r) s, ?_⟩
  intro f V hV hR hf h0 s
  have hA := hf.analyticOnNhd hV
  have h0V : (0 : ℂ) ∈ V := by simpa using hR 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 0 h0V
  have hloc : f =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with z hz
    rw [← Complex.taylorSeries_eq_on_ball' hz (hf.mono hball)]
    simp [h0]
  have hpre : IsPreconnected (Set.range ((↑) : ℝ → ℂ)) :=
    (isConnected_range Complex.continuous_ofReal).isPreconnected
  have hsub := hpre.subset_connectedComponentIn (x := (0 : ℂ)) ⟨0, by simp⟩
    (by rintro _ ⟨t, rfl⟩; exact hR t)
  have hEq := (hA.mono (connectedComponentIn_subset V 0)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_connectedComponentIn (mem_connectedComponentIn h0V) hloc
  simpa using hEq (hsub ⟨s, rfl⟩)

end PositivityTheory.Rg.Sw.AbsSt
