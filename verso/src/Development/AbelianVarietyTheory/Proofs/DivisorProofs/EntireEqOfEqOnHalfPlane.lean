import Mathlib

namespace GlobalTheory.EntireFunctionHalfPlane

open Filter Topology

/- English proof (translation)
Establish `hf' : AnalyticOnNhd ℂ f Set.univ` using `fun z _ => hf.analyticAt z`. Establish `hg' : AnalyticOnNhd ℂ g Set.univ` using `fun z _ => hg.analyticAt z`. Establish `hopen : IsOpen {s : ℂ | a < s.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hmem : ((a + 1 : ℝ) : ℂ) ∈ {s : ℂ | a < s.re}`. Simplify using the standard rewrite rules.

Establish `hev : f =ᶠ[𝓝 ((a + 1 : ℝ) : ℂ)] g` using `Filter.eventually_of_mem (hopen.mem_nhds hmem) (fun s hs => h s hs)`. Conclude with `AnalyticOnNhd.eq_of_eventuallyEq hf' hg' hev`.
-/
theorem entire_eq_of_eqOn_halfPlane {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (a : ℝ) (h : ∀ s : ℂ, a < s.re → f s = g s) : f = g := by
  have hf' : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hg' : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have hopen : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((a + 1 : ℝ) : ℂ) ∈ {s : ℂ | a < s.re} := by
    simp
  have hev : f =ᶠ[𝓝 ((a + 1 : ℝ) : ℂ)] g :=
    Filter.eventually_of_mem (hopen.mem_nhds hmem) (fun s hs => h s hs)
  exact AnalyticOnNhd.eq_of_eventuallyEq hf' hg' hev

end GlobalTheory.EntireFunctionHalfPlane
