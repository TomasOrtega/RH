import Mathlib

namespace GlobalTheory

/- English proof (translation)
Use `set U := LinearMap.range P`. Set `T : V →ₗ[ℂ] Module.Dual ℂ U` to `(B.domRestrict U).flip`. Establish `hT : ∀ ψ (u : U), T ψ u = B u ψ` using `fun _ _ => rfl`. Establish `hcoann : (LinearMap.range T).dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce `u hu`. Rewrite `hu` using `[Submodule.mem_dualCoannihilator]`. Establish `: (u : V) = 0` using `hL u (fun ψ => by`. Use `hu (T ψ) ⟨ψ, rfl⟩` as an intermediate fact. Simplify `this)` using `[hT]`.

Simplify using `using Subtype.ext this`. Establish `hsurj : LinearMap.range T = ⊤`. Establish `h` using `Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range T)`. Rewrite `h` using `[hcoann]`. Rewrite using `[← h]`.

Conclude with `Submodule.dualAnnihilator_bot`. Establish `: f.domRestrict U ∈ LinearMap.range T` using `by rw [hsurj]; trivial`. Take `⟨ψ, hψ⟩` from `this`. Use `⟨P' ψ, fun φ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hadj]`.

Establish `h1 : T ψ ⟨P φ, φ, rfl⟩ = f (P φ)` using `by rw [hψ]; rfl`. Rewrite `h1` using `[hT]`. Rewrite using `[h1]`. Conclude with `congrArg (fun g : V →ₗ[ℂ] ℂ => g φ) hf`.
-/
theorem functional_fixed_by_idempotent_represented
    {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hL : ∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) (_hR : ∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0)
    (P P' : Module.End ℂ V) (_hP : P ∘ₗ P = P) (hfin : FiniteDimensional ℂ (LinearMap.range P))
    (hadj : ∀ φ ψ, B (P φ) ψ = B φ (P' ψ)) (f : V →ₗ[ℂ] ℂ) (hf : f ∘ₗ P = f) :
    ∃ ψ, ∀ φ, B φ ψ = f φ := by
  set U := LinearMap.range P

  let T : V →ₗ[ℂ] Module.Dual ℂ U := (B.domRestrict U).flip
  have hT : ∀ ψ (u : U), T ψ u = B u ψ := fun _ _ => rfl
  have hcoann : (LinearMap.range T).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_dualCoannihilator] at hu
    have : (u : V) = 0 := hL u (fun ψ => by
      have := hu (T ψ) ⟨ψ, rfl⟩
      simpa [hT] using this)
    simpa using Subtype.ext this
  have hsurj : LinearMap.range T = ⊤ := by
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range T)
    rw [hcoann] at h
    rw [← h]
    exact Submodule.dualAnnihilator_bot
  have : f.domRestrict U ∈ LinearMap.range T := by rw [hsurj]; trivial
  obtain ⟨ψ, hψ⟩ := this
  refine ⟨P' ψ, fun φ => ?_⟩
  rw [← hadj]
  have h1 : T ψ ⟨P φ, φ, rfl⟩ = f (P φ) := by rw [hψ]; rfl
  rw [hT] at h1
  rw [h1]
  exact congrArg (fun g : V →ₗ[ℂ] ℂ => g φ) hf

end GlobalTheory
