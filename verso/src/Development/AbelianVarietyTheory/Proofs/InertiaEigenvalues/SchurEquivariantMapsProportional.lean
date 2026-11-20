import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective ξ (LinearMap.ker_eq_bot.mpr hξ)`. Establish `hgx : ∀ v, g (ξ v) = v` using `fun v => by`. Simplify using `using LinearMap.congr_fun hg v`. Use `set A : Module.End ℂ W := g ∘ₗ φ with hA`. Establish `hxA : ∀ w, ξ (A w) = φ w`.

Introduce `w`. Take `⟨v, hv⟩` from `hr (LinearMap.mem_range_self φ w)`. Simplify using `only [hA, LinearMap.comp_apply, ← hv, hgx]`. Establish `hcomm : ∀ h w, A (ρ h w) = ρ h (A w)`. Introduce `h w`.

Apply `hξ` to reduce the goal to its premises. Rewrite using `[hxA, hφe, hξe, hxA]`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue A`. Take `⟨v, hv⟩` from `hc.exists_hasEigenvector`. Establish `hAv : A v = c • v` using `hv.apply_eq_smul`.

Set `U : Submodule ℂ W` to `LinearMap.ker (A - c • LinearMap.id)`. Establish `hmemU : ∀ u, u ∈ U ↔ A u = c • u`. Introduce `u`. Simplify using `[U, sub_eq_zero]`. Establish `hstab : ∀ h, U.map (ρ h) ≤ U`.

Introduce `h x hx`. Take `⟨u, hu, rfl⟩` from `Submodule.mem_map.mp hx`. Rewrite `hu`, the goal using `[hmemU]`. Rewrite using `[hcomm, hu, map_smul]`. Establish `hne : U ≠ ⊥`.

Introduce `hU`. Establish `: v ∈ U` using `(hmemU v).mpr hAv`. Rewrite `this` using `[hU, Submodule.mem_bot]`. Conclude with `hv.2 this`. Establish `htop : U = ⊤` using `(hirr U hstab).resolve_left hne`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Use extensionality with `w`. Establish `hw : w ∈ U` using `htop ▸ Submodule.mem_top`. Rewrite `hw` using `[hmemU]`. Rewrite using `[LinearMap.smul_apply, ← hxA, hw, map_smul]`.
-/
theorem schur_proportional_of_range_le
    (H W X : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    [AddCommGroup X] [Module ℂ X] (ρ : H → Module.End ℂ W) (a : H → Module.End ℂ X)
    (φ ξ : W →ₗ[ℂ] X)
    (hirr : ∀ U : Submodule ℂ W, (∀ h, U.map (ρ h) ≤ U) → U = ⊥ ∨ U = ⊤)
    (hξ : Function.Injective ξ) (hr : LinearMap.range φ ≤ LinearMap.range ξ)
    (hφe : ∀ h w, φ (ρ h w) = a h (φ w)) (hξe : ∀ h w, ξ (ρ h w) = a h (ξ w)) :
    ∃ c : ℂ, φ = c • ξ := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ξ (LinearMap.ker_eq_bot.mpr hξ)
  have hgx : ∀ v, g (ξ v) = v := fun v => by
    simpa using LinearMap.congr_fun hg v
  set A : Module.End ℂ W := g ∘ₗ φ with hA
  have hxA : ∀ w, ξ (A w) = φ w := by
    intro w
    obtain ⟨v, hv⟩ := hr (LinearMap.mem_range_self φ w)
    simp only [hA, LinearMap.comp_apply, ← hv, hgx]
  have hcomm : ∀ h w, A (ρ h w) = ρ h (A w) := by
    intro h w
    apply hξ
    rw [hxA, hφe, hξe, hxA]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hAv : A v = c • v := hv.apply_eq_smul
  let U : Submodule ℂ W := LinearMap.ker (A - c • LinearMap.id)
  have hmemU : ∀ u, u ∈ U ↔ A u = c • u := by
    intro u
    simp [U, sub_eq_zero]
  have hstab : ∀ h, U.map (ρ h) ≤ U := by
    intro h x hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    rw [hmemU] at hu ⊢
    rw [hcomm, hu, map_smul]
  have hne : U ≠ ⊥ := by
    intro hU
    have : v ∈ U := (hmemU v).mpr hAv
    rw [hU, Submodule.mem_bot] at this
    exact hv.2 this
  have htop : U = ⊤ := (hirr U hstab).resolve_left hne
  refine ⟨c, ?_⟩
  ext w
  have hw : w ∈ U := htop ▸ Submodule.mem_top
  rw [hmemU] at hw
  rw [LinearMap.smul_apply, ← hxA, hw, map_smul]

/- English proof (translation)
Introduce `H W X _ _ _ _ _ _ _ ρ a φ ξ hirr hξ hr hφe hξe` and use `schur_proportional_of_range_le H W X ρ a φ ξ hirr hξ hr hφe hξe`.
-/
theorem schur_proportional :
    ∀ (H W X : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] [AddCommGroup X] [Module ℂ X] (ρ : H → Module.End ℂ W) (a : H → Module.End ℂ X) (φ ξ : W →ₗ[ℂ] X), (∀ U : Submodule ℂ W, (∀ h, U.map (ρ h) ≤ U) → U = ⊥ ∨ U = ⊤) → Function.Injective ξ → LinearMap.range φ ≤ LinearMap.range ξ → (∀ h w, φ (ρ h w) = a h (φ w)) → (∀ h w, ξ (ρ h w) = a h (ξ w)) → ∃ c : ℂ, φ = c • ξ :=
  fun H W X _ _ _ _ _ _ _ ρ a φ ξ hirr hξ hr hφe hξe =>
    schur_proportional_of_range_le H W X ρ a φ ξ hirr hξ hr hφe hξe

end GlobalTheory
