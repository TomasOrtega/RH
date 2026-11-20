import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

/- English proof (translation)
Introduce `l _ B _ _ _ _ _ _ X _ f hf`. Set `b` to `Module.finBasis ℚ_[l] B`. Set `M` to `Algebra.leftMulMatrix b`. Set `E : (Fin (Module.finrank ℚ_[l] B) → ℚ_[l]) →ₗ[ℚ_[l]] B` to `b.equivFun.symm.toLinearMap`. Establish `key : ∀ u : Bˣ, ((u⁻¹ : Bˣ) : B) = E (Matrix.mulVec (M (u : B))⁻¹ (b.repr 1))`.

Introduce `u`. Establish `hinv : (M (u : B))⁻¹ = M ((u⁻¹ : Bˣ) : B)`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Rewrite using `[hinv, Algebra.leftMulMatrix_mulVec_repr, mul_one]`.

Simplify using `[E]`. Establish `hM : Continuous fun y : B => M y` using `IsModuleTopology.continuous_of_linearMap M.toLinearMap`. Establish `hE : Continuous E` using `LinearMap.continuous_on_pi E`. Establish `hcomp : Continuous fun x => E (Matrix.mulVec (M (f x : B))⁻¹ (b.repr 1))`. Use `hE.comp ?_` and prove the remaining obligations.

Use `Continuous.matrix_mulVec ?_ continuous_const` and prove the remaining obligations. Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Use `ContinuousAt.comp (f := fun x => M (f x : B)) (g := Inv.inv) ?_ (hM.comp hf).continuousAt` and prove the remaining obligations. Apply `continuousAt_matrix_inv` to reduce the goal to its premises.

Establish `hdet : IsUnit (M (f x : B)).det`. Establish `: IsUnit (M (f x : B))` using `(f x).isUnit.map M`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 this`. Take `⟨d, hd⟩` from `hdet`. Rewrite using `[← hd]`.

Conclude with `NormedRing.inverse_continuousAt d`. Simplify `hcomp` using `only [← key]`.
-/
theorem UpperTheory.continuous_units_inv_of_continuous_coe_finite_Qp_algebra :
    ∀ {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] {X : Type} [TopologicalSpace X] (f : X → Bˣ), Continuous (fun x => (f x : B)) → Continuous fun x => (((f x)⁻¹ : Bˣ) : B) := by
  intro l _ B _ _ _ _ _ _ X _ f hf
  classical
  let b := Module.finBasis ℚ_[l] B
  let M := Algebra.leftMulMatrix b
  let E : (Fin (Module.finrank ℚ_[l] B) → ℚ_[l]) →ₗ[ℚ_[l]] B := b.equivFun.symm.toLinearMap
  have key : ∀ u : Bˣ, ((u⁻¹ : Bˣ) : B) = E (Matrix.mulVec (M (u : B))⁻¹ (b.repr 1)) := by
    intro u
    have hinv : (M (u : B))⁻¹ = M ((u⁻¹ : Bˣ) : B) := by
      apply Matrix.inv_eq_left_inv
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hinv, Algebra.leftMulMatrix_mulVec_repr, mul_one]
    simp [E]
  have hM : Continuous fun y : B => M y :=
    IsModuleTopology.continuous_of_linearMap M.toLinearMap
  have hE : Continuous E := LinearMap.continuous_on_pi E
  have hcomp : Continuous fun x => E (Matrix.mulVec (M (f x : B))⁻¹ (b.repr 1)) := by
    refine hE.comp ?_
    refine Continuous.matrix_mulVec ?_ continuous_const
    rw [continuous_iff_continuousAt]
    intro x
    refine ContinuousAt.comp (f := fun x => M (f x : B)) (g := Inv.inv) ?_ (hM.comp hf).continuousAt
    apply continuousAt_matrix_inv
    have hdet : IsUnit (M (f x : B)).det := by
      have : IsUnit (M (f x : B)) := (f x).isUnit.map M
      exact (Matrix.isUnit_iff_isUnit_det _).1 this
    obtain ⟨d, hd⟩ := hdet
    rw [← hd]
    exact NormedRing.inverse_continuousAt d
  simpa only [← key] using hcomp
