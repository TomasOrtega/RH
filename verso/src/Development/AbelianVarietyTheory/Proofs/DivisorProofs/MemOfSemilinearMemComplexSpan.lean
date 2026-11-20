import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `K V W ι _ _ _ _ _ _ σ j b hli U x hx`. Assume the negation of the conclusion as `hxU`. Take `⟨f, hfx, hfU⟩` from `U.exists_dual_map_eq_bot_of_notMem hxU inferInstance`. Take `⟨L, hL⟩` from `(Finsupp.linearCombination ℂ (fun k => j (b k))).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hli)`. Set `g : W →ₗ[ℂ] ℂ` to `(Finsupp.linearCombination ℂ (fun k => σ (f (b k)))).comp L`.

Establish `hb : ∀ k, g (j (b k)) = σ (f (b k))`. Introduce `k`. Establish `h1 : L (j (b k)) = Finsupp.single k 1`. Use `LinearMap.congr_fun hL (Finsupp.single k 1)` as an intermediate fact. Simplify using `using this`.

Simplify using `[g, h1]`. Establish `hg : ∀ v, g (j v) = σ (f v)`. Introduce `v`. Establish `hv : v ∈ Submodule.span K (Set.range b)` using `by rw [b.span_eq]; trivial`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem y hy => obtain ⟨k, rfl⟩ := hy`. Conclude with `hb k`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => simp [hy, hz]`. Consider the case `smul a y _ hy => rw [j.map_smulₛₗ, map_smul, map_smul, hy]`.

Simplify using the standard rewrite rules. Establish `hle : Submodule.span ℂ (j '' (U : Set V)) ≤ LinearMap.ker g`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Establish `: f u = 0`.

Establish `: f u ∈ U.map f` using `⟨u, hu, rfl⟩`. Rewrite `this` using `[hfU]`. Simplify using `using this`. Simplify using `[hg, this]`. Establish `h0 : σ (f x) = 0` using `by rw [← hg]; exact hle hx`.

Conclude with `hfx (by simpa using h0)`.
-/
theorem mem_of_semilinear_mem_complex_span : ∀ {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V), LinearIndependent ℂ (fun k => j (b k)) → ∀ (U : Submodule K V) (x : V), j x ∈ Submodule.span ℂ (j '' (U : Set V)) → x ∈ U := by
  intro K V W ι _ _ _ _ _ _ σ j b hli U x hx
  by_contra hxU
  obtain ⟨f, hfx, hfU⟩ := U.exists_dual_map_eq_bot_of_notMem hxU inferInstance
  obtain ⟨L, hL⟩ := (Finsupp.linearCombination ℂ (fun k => j (b k))).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hli)
  let g : W →ₗ[ℂ] ℂ := (Finsupp.linearCombination ℂ (fun k => σ (f (b k)))).comp L
  have hb : ∀ k, g (j (b k)) = σ (f (b k)) := by
    intro k
    have h1 : L (j (b k)) = Finsupp.single k 1 := by
      have := LinearMap.congr_fun hL (Finsupp.single k 1)
      simpa using this
    simp [g, h1]
  have hg : ∀ v, g (j v) = σ (f v) := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
    induction hv using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hb k
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy => rw [j.map_smulₛₗ, map_smul, map_smul, hy]; simp
  have hle : Submodule.span ℂ (j '' (U : Set V)) ≤ LinearMap.ker g := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have : f u = 0 := by
      have : f u ∈ U.map f := ⟨u, hu, rfl⟩
      rw [hfU] at this
      simpa using this
    simp [hg, this]
  have h0 : σ (f x) = 0 := by rw [← hg]; exact hle hx
  exact hfx (by simpa using h0)

end GlobalTheory
