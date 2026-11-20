import ReciprocityTheory.L2DbarEstimates.SymmetricSections.Sheets
import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

/- English proof (translation)
Introduce `n M _ z U u hcov hU hfinU hholo k w hw`. Establish `hloc : IsLocalHomeomorph z`. Rewrite using `[isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]`. Use `hcov.isLocalHomeomorphOn` as an intermediate fact. Rewrite `this` using `[Set.preimage_eq_univ_iff.mpr (by rintro _ ⟨x, rfl⟩; exact hU x)]`. Then use the resulting hypothesis.

Take `⟨W, d, s, hW, hwW, hcont, hzs, hvals⟩` from `sheets n M z U u hcov w hw (hfinU w hw)`. Establish `hWn : W ∈ 𝓝 w` using `hW.mem_nhds hwW`. Establish `hdiff : ∀ i, DifferentiableAt ℂ (fun v => u (s i v)) w` using `fun i => hsec n M z u hloc hholo (s i) w ((hcont i).continuousAt hWn) (Filter.eventually_of_mem hWn (hzs i))`. Establish `heq : (fun v => ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ t, u (s i v)) =ᶠ[𝓝 w] fiberSymm n z u k` using `by filter_upwards [hWn] with v hv`. Rewrite using `[fiberSymm, hvals v hv, Finset.esymm_map_val]`.

Use `DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm` and prove the remaining obligations. Establish `hprod : ∀ t : Finset (Fin d), DifferentiableAt ℂ (fun v => ∏ i ∈ t, u (s i v)) w`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert a t ha ih`. Simplify using `only [Finset.prod_insert ha]`. Conclude with `(hdiff a).mul ih`. Conclude with `DifferentiableAt.fun_sum fun t _ => hprod t`.
-/
theorem symmDiff_of_holoSection (hsec : holoSectionStatement.{u}) : symmDiffStatement.{u} := by
  intro n M _ z U u hcov hU hfinU hholo k w hw
  have hloc : IsLocalHomeomorph z := by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    have := hcov.isLocalHomeomorphOn
    rwa [Set.preimage_eq_univ_iff.mpr (by rintro _ ⟨x, rfl⟩; exact hU x)] at this
  obtain ⟨W, d, s, hW, hwW, hcont, hzs, hvals⟩ := sheets n M z U u hcov w hw (hfinU w hw)
  have hWn : W ∈ 𝓝 w := hW.mem_nhds hwW
  have hdiff : ∀ i, DifferentiableAt ℂ (fun v => u (s i v)) w := fun i =>
    hsec n M z u hloc hholo (s i) w ((hcont i).continuousAt hWn)
      (Filter.eventually_of_mem hWn (hzs i))
  have heq : (fun v => ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ t, u (s i v))
      =ᶠ[𝓝 w] fiberSymm n z u k := by
    filter_upwards [hWn] with v hv
    rw [fiberSymm, hvals v hv, Finset.esymm_map_val]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
  have hprod : ∀ t : Finset (Fin d), DifferentiableAt ℂ (fun v => ∏ i ∈ t, u (s i v)) w := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hdiff a).mul ih
  exact DifferentiableAt.fun_sum fun t _ => hprod t

end ReciprocityTheory.L2DbarEstimates.Norm
