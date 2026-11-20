import Mathlib

namespace GlobalTheory

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem schur_proportional :
    ∀ (H W X : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] [AddCommGroup X] [Module ℂ X] (ρ : H → Module.End ℂ W) (a : H → Module.End ℂ X) (φ ξ : W →ₗ[ℂ] X), (∀ U : Submodule ℂ W, (∀ h, U.map (ρ h) ≤ U) → U = ⊥ ∨ U = ⊤) → Function.Injective ξ → LinearMap.range φ ≤ LinearMap.range ξ → (∀ h w, φ (ρ h w) = a h (φ w)) → (∀ h w, ξ (ρ h w) = a h (ξ w)) → ∃ c : ℂ, φ = c • ξ :=
  fun H W X _ _ _ _ _ _ _ ρ a φ ξ hirr hξ hr hφe hξe =>
    schur_proportional_of_range_le H W X ρ a φ ξ hirr hξ hr hφe hξe

end GlobalTheory
