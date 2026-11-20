import Mathlib
open scoped InnerProductSpace
open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Establish `hnorm : ∀ x y, ‖u y - u x‖ = Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ) - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ))`. Introduce `x y`. Rewrite using `[← hu, ← hu, ← hu, inner_self_eq_norm_sq, inner_self_eq_norm_sq, ← norm_sub_sq, Real.sqrt_sq (norm_nonneg _)]`. Establish `hcont : Continuous u`. Rewrite using `[continuous_iff_continuousAt]`.

Introduce `x`. Rewrite using `[ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]`. Establish `hc : Continuous (fun y : (∀ i, H i) => Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ) - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ)))` using `by fun_prop`. Establish `key : Tendsto (fun y => ‖u y - u x‖) (𝓝 x) (𝓝 ‖u x - u x‖)`. Establish `e : (fun y => ‖u y - u x‖) = fun y => Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ) - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ))`.

Use function extensionality and compare the values at `fun y => hnorm x y`. Rewrite using `[e, hnorm x x]`. Conclude with `hc.tendsto x`. Simplify using `using key`. Use `set S := Submodule.span ℂ (Set.range (fun x : (∀ i, W i) => u (fun i => (x i : H i)))) with hS`.

Establish `hpi : Dense (Set.pi Set.univ (fun i => (W i : Set (H i))))` using `dense_pi Set.univ (fun i _ => hW i)`. Establish `hsub : Set.range u ⊆ closure (S : Set Hs)`. Introduce and unpack `_ ⟨x, rfl⟩`. Use `map_mem_closure hcont (hpi x) ?_` and prove the remaining obligations. Introduce `y hy`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨fun i => ⟨y i, hy i (Set.mem_univ i)⟩, rfl⟩`. Establish `hle : Submodule.span ℂ (Set.range u) ≤ S.topologicalClosure`. Rewrite using `[Submodule.span_le, Submodule.topologicalClosure_coe]`. Conclude with `hsub`.

Establish `h2 : Dense (S.topologicalClosure : Set Hs)` using `hd.mono hle`. Rewrite `h2` using `[Submodule.topologicalClosure_coe, dense_closure]`. Then use the resulting hypothesis.
-/
theorem dense_span_tensor_of_dense_subspaces {ι : Type} [Fintype ι] {H : ι → Type}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type}
    [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (u : (∀ i, H i) → Hs)
    (W : ∀ i, Submodule ℂ (H i)) (hu : ∀ x y, ⟪u x, u y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range u) : Set Hs))
    (hW : ∀ i, Dense (W i : Set (H i))) :
    Dense (Submodule.span ℂ (Set.range (fun x : (∀ i, W i) => u (fun i => (x i : H i)))) :
      Set Hs) := by
  have hnorm : ∀ x y, ‖u y - u x‖ = Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ)
      - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ)) := by
    intro x y
    rw [← hu, ← hu, ← hu, inner_self_eq_norm_sq, inner_self_eq_norm_sq, ← norm_sub_sq,
      Real.sqrt_sq (norm_nonneg _)]
  have hcont : Continuous u := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hc : Continuous (fun y : (∀ i, H i) => Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ)
        - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ))) := by
      fun_prop
    have key : Tendsto (fun y => ‖u y - u x‖) (𝓝 x) (𝓝 ‖u x - u x‖) := by
      have e : (fun y => ‖u y - u x‖) = fun y => Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ)
          - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ)) :=
        funext fun y => hnorm x y
      rw [e, hnorm x x]
      exact hc.tendsto x
    simpa using key
  set S := Submodule.span ℂ (Set.range (fun x : (∀ i, W i) => u (fun i => (x i : H i))))
    with hS
  have hpi : Dense (Set.pi Set.univ (fun i => (W i : Set (H i)))) :=
    dense_pi Set.univ (fun i _ => hW i)
  have hsub : Set.range u ⊆ closure (S : Set Hs) := by
    rintro _ ⟨x, rfl⟩
    refine map_mem_closure hcont (hpi x) ?_
    intro y hy
    apply Submodule.subset_span
    exact ⟨fun i => ⟨y i, hy i (Set.mem_univ i)⟩, rfl⟩
  have hle : Submodule.span ℂ (Set.range u) ≤ S.topologicalClosure := by
    rw [Submodule.span_le, Submodule.topologicalClosure_coe]
    exact hsub
  have h2 : Dense (S.topologicalClosure : Set Hs) := hd.mono hle
  rwa [Submodule.topologicalClosure_coe, dense_closure] at h2

end GlobalTheory
