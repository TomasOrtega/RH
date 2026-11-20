import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

/- English proof (translation)
Introduce `n M _ z f hz hf s w hs hzs`. Take `⟨e, hxe, rfl⟩` from `hz (s w)`. Establish `hchart : IsChart n e e` using `fun _ _ => rfl`. Establish `hw : e (s w) = w` using `hzs.self_of_nhds`. Establish `htarget : e.target ∈ 𝓝 w`.

Rewrite using `[← hw]`. Conclude with `e.open_target.mem_nhds (e.map_source hxe)`. Establish `hsrc : ∀ᶠ v in 𝓝 w, s v ∈ e.source` using `hs (e.open_source.mem_nhds hxe)`. Establish `heq : f ∘ e.symm =ᶠ[𝓝 w] f ∘ s` using `by filter_upwards [hsrc, hzs] with v h1 h2`. Simplify using `only [Function.comp_apply]`.

Rewrite using `[show e.symm v = s v by rw [← e.left_inv h1, h2]]`. Conclude with `((hf e hchart).differentiableAt htarget).congr_of_eventuallyEq heq.symm`.
-/
theorem holoSection : holoSectionStatement.{u} := by
  intro n M _ z f hz hf s w hs hzs
  obtain ⟨e, hxe, rfl⟩ := hz (s w)
  have hchart : IsChart n e e := fun _ _ => rfl
  have hw : e (s w) = w := hzs.self_of_nhds
  have htarget : e.target ∈ 𝓝 w := by
    rw [← hw]
    exact e.open_target.mem_nhds (e.map_source hxe)
  have hsrc : ∀ᶠ v in 𝓝 w, s v ∈ e.source := hs (e.open_source.mem_nhds hxe)
  have heq : f ∘ e.symm =ᶠ[𝓝 w] f ∘ s := by
    filter_upwards [hsrc, hzs] with v h1 h2
    simp only [Function.comp_apply]
    rw [show e.symm v = s v by rw [← e.left_inv h1, h2]]
  exact ((hf e hchart).differentiableAt htarget).congr_of_eventuallyEq heq.symm

end ReciprocityTheory.L2DbarEstimates.Norm
