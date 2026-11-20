import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite

namespace GlobalTheory.Proof.CoeffSpan

/- English proof (translation)
Set `T : Module.Dual ℂ (Module.End ℂ W) →ₗ[ℂ] (K → ℂ)` to `{ toFun := fun φ k => φ (ρ k) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range T`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `f ⟨ℓ, w, rfl⟩`. Use `⟨{ toFun := fun A => ℓ (A w), map_add' := fun A B => by simp, map_smul' := fun c A => by simp }, ?_⟩` and prove the remaining obligations.

Both sides reduce to the same expression. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem finiteDimensional_coeffSpan (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let T : Module.Dual ℂ (Module.End ℂ W) →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun φ k => φ (ρ k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    refine ⟨{ toFun := fun A => ℓ (A w), map_add' := fun A B => by simp, map_smul' := fun c A => by simp }, ?_⟩
    rfl
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.Proof.CoeffSpan
