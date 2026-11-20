import Mathlib

namespace GlobalTheory.GramLinearMap

/- English proof (translation)
Proceed by induction on `x using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add x₁ x₂ h₁ h₂`. Simplify using `only [map_add, LinearMap.add_apply, add_mul, mul_add, h₁, h₂]`. Consider the case `single u a`.

Proceed by induction on `y using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add y₁ y₂ h₁ h₂`. Simplify using `only [map_add, add_mul, mul_add, h₁, h₂]`. Consider the case `single v b`.

Simplify using `only [Finsupp.linearCombination_single, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]`. Take the linear combination `(b * (starRingEnd ℂ) a) * h u v`.
-/
theorem gram_comb {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ} {U : Type}
    (f : U → P) (f' : U → P') {c d : ℂ}
    (h : ∀ u v : U, B (f u) (f v) * c = d * B' (f' u) (f' v)) (x y : U →₀ ℂ) :
    B (Finsupp.linearCombination ℂ f x) (Finsupp.linearCombination ℂ f y) * c =
      d * B' (Finsupp.linearCombination ℂ f' x) (Finsupp.linearCombination ℂ f' y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, add_mul, mul_add, h₁, h₂]
  | single u a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, add_mul, mul_add, h₁, h₂]
    | single v b =>
      simp only [Finsupp.linearCombination_single, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      linear_combination (b * (starRingEnd ℂ) a) * h u v

/- English proof (translation)
Use `set T := Finsupp.linearCombination ℂ f with hT`. Use `set T' := Finsupp.linearCombination ℂ f' with hT'`. Establish `hker : ∀ x, T' x = 0 → T x = 0`. Introduce `x hx`. Apply `hB` to reduce the goal to its premises.

Use `gram_comb f f' h x x` as an intermediate fact. Rewrite `this` using `[← hT, ← hT', hx]`. Simplify `this` using `[hc]`. Take `⟨g, hg⟩` from `T'.rangeRestrict.exists_rightInverse_of_surjective T'.range_rangeRestrict`. Take `⟨ψ, hψ⟩` from `LinearMap.exists_extend (T ∘ₗ g)`.

Use `⟨ψ, fun u => ?_⟩` and prove the remaining obligations. Establish `h1 : T' (Finsupp.single u 1) = f' u` using `by simp [hT']`. Establish `h2 : T (Finsupp.single u 1) = f u` using `by simp [hT]`. Set `z : LinearMap.range T'` to `⟨f' u, _, h1⟩`. Establish `h3 : ψ (f' u) = T (g z)` using `LinearMap.congr_fun hψ z`.

Establish `h4 : T' (g z) = f' u` using `congrArg Subtype.val (LinearMap.congr_fun hg z)`. Establish `h5 : T (g z - Finsupp.single u 1) = 0` using `hker _ (by rw [map_sub, h4, h1, sub_self])`. Rewrite `h5` using `[map_sub, sub_eq_zero]`. Rewrite using `[h3, h5, h2]`.
-/
theorem exists_linearMap_of_gram {P : Type} [AddCommGroup P] [Module ℂ P]
    {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ} {U : Type}
    (f : U → P) (f' : U → P') (hB : ∀ y : P, B y y = 0 → y = 0) {c d : ℂ} (hc : c ≠ 0)
    (h : ∀ u v : U, B (f u) (f v) * c = d * B' (f' u) (f' v)) :
    ∃ ψ : P' →ₗ[ℂ] P, ∀ u : U, ψ (f' u) = f u := by
  set T := Finsupp.linearCombination ℂ f with hT
  set T' := Finsupp.linearCombination ℂ f' with hT'
  have hker : ∀ x, T' x = 0 → T x = 0 := by
    intro x hx
    apply hB
    have := gram_comb f f' h x x
    rw [← hT, ← hT', hx] at this
    simpa [hc] using this
  obtain ⟨g, hg⟩ := T'.rangeRestrict.exists_rightInverse_of_surjective T'.range_rangeRestrict
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (T ∘ₗ g)
  refine ⟨ψ, fun u => ?_⟩
  have h1 : T' (Finsupp.single u 1) = f' u := by simp [hT']
  have h2 : T (Finsupp.single u 1) = f u := by simp [hT]
  let z : LinearMap.range T' := ⟨f' u, _, h1⟩
  have h3 : ψ (f' u) = T (g z) := LinearMap.congr_fun hψ z
  have h4 : T' (g z) = f' u := congrArg Subtype.val (LinearMap.congr_fun hg z)
  have h5 : T (g z - Finsupp.single u 1) = 0 := hker _ (by rw [map_sub, h4, h1, sub_self])
  rw [map_sub, sub_eq_zero] at h5
  rw [h3, h5, h2]

end GlobalTheory.GramLinearMap
