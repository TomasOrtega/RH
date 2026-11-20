import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection

noncomputable section

open Filter Topology

namespace UpperTheory.V.Cj.H

set_option maxHeartbeats 400000 in
/- English proof (translation)
Introduce `I J L c cn hcn hlim`. Set `ψ : (J →₀ ℂ) →ₗ[ℂ] (I →₀ ℂ)` to `Finsupp.linearCombination ℂ L`. Set `φ : (J →₀ ℂ) →ₗ[ℂ] ℂ` to `Finsupp.linearCombination ℂ c`. Establish `hsum : ∀ (b : I → ℂ) (v : I →₀ ℂ), (v.sum fun i x => x * b i) = Finsupp.linearCombination ℂ b v`. Introduce `b v`.

Rewrite using `[Finsupp.linearCombination_apply]`. Both sides reduce to the same expression. Establish `hcomp : ∀ (b : I → ℂ), (Finsupp.linearCombination ℂ b) ∘ₗ ψ = Finsupp.linearCombination ℂ (fun j => Finsupp.linearCombination ℂ b (L j))`. Introduce `b`. Apply `Finsupp.lhom_ext` to reduce the goal to its premises.

Introduce `j x`. Simplify using `[ψ, Finsupp.linearCombination_single]`. Establish `hker : LinearMap.ker ψ ≤ LinearMap.ker φ`. Introduce `a ha`. Rewrite `ha`, the goal using `[LinearMap.mem_ker]`.

Establish `h0 : ∀ k, Finsupp.linearCombination ℂ (cn k) a = 0`. Introduce `k`. Take `⟨b, hb⟩` from `hcn k`. Establish `h1` using `congrArg (fun m => m a) (hcomp b)`. Simplify using `only [LinearMap.comp_apply, ha, map_zero] at h1`.

Rewrite using `[show cn k = fun j => Finsupp.linearCombination ℂ b (L j) from`. Use function extensionality and compare the values at `fun j => ((hsum b (L j)).symm.trans (hb j)).symm]`. Conclude with `h1.symm`. Establish `hT : Tendsto (fun k => Finsupp.linearCombination ℂ (cn k) a) atTop (𝓝 (φ a))`. Simplify using `only [φ, Finsupp.linearCombination_apply, Finsupp.sum]`.

Apply `tendsto_finset_sum` to reduce the goal to its premises. Introduce `j _`. Conclude with `(hlim j).const_smul (a j)`. Simplify using `only [h0] at hT`. Conclude with `tendsto_nhds_unique hT tendsto_const_nhds`.

Set `f0 : LinearMap.range ψ →ₗ[ℂ] ℂ` to `((LinearMap.ker ψ).liftQ φ hker) ∘ₗ (ψ.quotKerEquivRange.symm : LinearMap.range ψ →ₗ[ℂ] (J →₀ ℂ) ⧸ LinearMap.ker ψ)`. Take `⟨g, hg⟩` from `LinearMap.exists_extend f0`. Establish `hgψ : ∀ a, g (ψ a) = φ a`. Introduce `a`. Establish `h2` using `congrArg (fun m => m ⟨ψ a, LinearMap.mem_range_self ψ a⟩) hg`.

Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply] at h2`. Rewrite using `[h2]`. Simplify using `[f0, LinearMap.quotKerEquivRange_symm_apply_image]`. Establish `hgb : Finsupp.linearCombination ℂ (fun i => g (Finsupp.single i 1)) = g`. Apply `Finsupp.lhom_ext` to reduce the goal to its premises.

Introduce `i x`. Rewrite using `[Finsupp.linearCombination_single, ← map_smul, Finsupp.smul_single_one]`. Use `⟨fun i => g (Finsupp.single i 1), fun j => ?_⟩` and prove the remaining obligations. Use `(hsum (fun i => g (Finsupp.single i 1)) (L j)).trans ?_` and prove the remaining obligations. Rewrite using `[hgb]`.

Establish `h3` using `hgψ (Finsupp.single j 1)`. Simplify `h3` using `[ψ, φ, Finsupp.linearCombination_single]`.
-/
theorem absSolve : AbsSolve := by
  intro I J L c cn hcn hlim
  classical
  let ψ : (J →₀ ℂ) →ₗ[ℂ] (I →₀ ℂ) := Finsupp.linearCombination ℂ L
  let φ : (J →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ c
  have hsum : ∀ (b : I → ℂ) (v : I →₀ ℂ),
      (v.sum fun i x => x * b i) = Finsupp.linearCombination ℂ b v := by
    intro b v
    rw [Finsupp.linearCombination_apply]
    rfl
  have hcomp : ∀ (b : I → ℂ), (Finsupp.linearCombination ℂ b) ∘ₗ ψ
      = Finsupp.linearCombination ℂ (fun j => Finsupp.linearCombination ℂ b (L j)) := by
    intro b
    apply Finsupp.lhom_ext
    intro j x
    simp [ψ, Finsupp.linearCombination_single]
  have hker : LinearMap.ker ψ ≤ LinearMap.ker φ := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have h0 : ∀ k, Finsupp.linearCombination ℂ (cn k) a = 0 := by
      intro k
      obtain ⟨b, hb⟩ := hcn k
      have h1 := congrArg (fun m => m a) (hcomp b)
      simp only [LinearMap.comp_apply, ha, map_zero] at h1
      rw [show cn k = fun j => Finsupp.linearCombination ℂ b (L j) from
        funext fun j => ((hsum b (L j)).symm.trans (hb j)).symm]
      exact h1.symm
    have hT : Tendsto (fun k => Finsupp.linearCombination ℂ (cn k) a) atTop (𝓝 (φ a)) := by
      simp only [φ, Finsupp.linearCombination_apply, Finsupp.sum]
      apply tendsto_finset_sum
      intro j _
      exact (hlim j).const_smul (a j)
    simp only [h0] at hT
    exact tendsto_nhds_unique hT tendsto_const_nhds
  let f0 : LinearMap.range ψ →ₗ[ℂ] ℂ :=
    ((LinearMap.ker ψ).liftQ φ hker) ∘ₗ
      (ψ.quotKerEquivRange.symm : LinearMap.range ψ →ₗ[ℂ] (J →₀ ℂ) ⧸ LinearMap.ker ψ)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f0
  have hgψ : ∀ a, g (ψ a) = φ a := by
    intro a
    have h2 := congrArg (fun m => m ⟨ψ a, LinearMap.mem_range_self ψ a⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h2]
    simp [f0, LinearMap.quotKerEquivRange_symm_apply_image]
  have hgb : Finsupp.linearCombination ℂ (fun i => g (Finsupp.single i 1)) = g := by
    apply Finsupp.lhom_ext
    intro i x
    rw [Finsupp.linearCombination_single, ← map_smul, Finsupp.smul_single_one]
  refine ⟨fun i => g (Finsupp.single i 1), fun j => ?_⟩
  refine (hsum (fun i => g (Finsupp.single i 1)) (L j)).trans ?_
  rw [hgb]
  have h3 := hgψ (Finsupp.single j 1)
  simpa [ψ, φ, Finsupp.linearCombination_single] using h3

end UpperTheory.V.Cj.H
