import Mathlib

namespace GlobalTheory.NormBoundTheorem

/- English proof (translation)
Introduce `M ι T _ _ Y t h`. Set `L : (ι →₀ ℚ) →ₗ[ℚ] (M → ℚ)` to `Finsupp.linearCombination ℚ Y`. Set `L' : (ι →₀ ℚ) →ₗ[ℚ] T` to `Finsupp.linearCombination ℚ t`. Establish `hker : LinearMap.ker L ≤ LinearMap.ker L'`. Introduce `x hx`.

Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Simplify using `only [L, L', Finsupp.linearCombination_apply, Finsupp.sum] at hx ⊢`. Conclude with `h x.support (fun i => x i) hx`. Set `g0 : LinearMap.range L →ₗ[ℚ] T` to `((LinearMap.ker L).liftQ L' hker).comp (L.quotKerEquivRange.symm : LinearMap.range L →ₗ[ℚ] _)`. Take `⟨g, hg⟩` from `LinearMap.exists_extend g0`.

Use `⟨g.toAddMonoidHom, fun i => ?_⟩` and prove the remaining obligations. Establish `hmem : Y i ∈ LinearMap.range L` using `⟨Finsupp.single i 1, by simp [L]⟩`. Establish `h1 : g (Y i) = g0 ⟨Y i, hmem⟩`. Rewrite using `[← hg]`. Both sides reduce to the same expression.

Use `show g (Y i) = t i`. Rewrite using `[h1]`. Establish `h2 : (⟨Y i, hmem⟩ : LinearMap.range L) = ⟨L (Finsupp.single i 1), LinearMap.mem_range_self L _⟩` using `by ext1; simp [L]`. Rewrite using `[h2]`. Simplify using `only [g0, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.quotKerEquivRange_symm_apply_image, Submodule.liftQ_apply]`.

Simplify using `[L']`.
-/
theorem main : ∀ (M ι T : Type) [inst : AddCommGroup T] [inst_1 : Module ℚ T] (Y : ι → M → ℚ) (t : ι → T), (∀ (s : Finset ι) (c : ι → ℚ), ∑ i ∈ s, c i • Y i = (0 : M → ℚ) → ∑ i ∈ s, c i • t i = (0 : T)) → ∃ (Ξ : (M → ℚ) →+ T), ∀ (i : ι), (Ξ : (M → ℚ) → T) (Y i) = t i := by
  intro M ι T _ _ Y t h
  classical
  let L : (ι →₀ ℚ) →ₗ[ℚ] (M → ℚ) := Finsupp.linearCombination ℚ Y
  let L' : (ι →₀ ℚ) →ₗ[ℚ] T := Finsupp.linearCombination ℚ t
  have hker : LinearMap.ker L ≤ LinearMap.ker L' := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    simp only [L, L', Finsupp.linearCombination_apply, Finsupp.sum] at hx ⊢
    exact h x.support (fun i => x i) hx
  let g0 : LinearMap.range L →ₗ[ℚ] T :=
    ((LinearMap.ker L).liftQ L' hker).comp (L.quotKerEquivRange.symm : LinearMap.range L →ₗ[ℚ] _)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend g0
  refine ⟨g.toAddMonoidHom, fun i => ?_⟩
  have hmem : Y i ∈ LinearMap.range L := ⟨Finsupp.single i 1, by simp [L]⟩
  have h1 : g (Y i) = g0 ⟨Y i, hmem⟩ := by
    rw [← hg]; rfl
  show g (Y i) = t i
  rw [h1]
  have h2 : (⟨Y i, hmem⟩ : LinearMap.range L) = ⟨L (Finsupp.single i 1), LinearMap.mem_range_self L _⟩ := by
    ext1; simp [L]
  rw [h2]
  simp only [g0, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.liftQ_apply]
  simp [L']

end GlobalTheory.NormBoundTheorem
