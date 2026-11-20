import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

namespace GlobalTheory.EnvelopingExtension

/- English proof (translation)
Set `f : L →ₗ[ℝ] A` to `{ toFun := ρ map_add' := hadd map_smul' := fun c X => by`. Rewrite using `[hsmul]`. Conclude with `Complex.coe_smul c (ρ X) }`. Set `F : ℂ ⊗[ℝ] L →ₗ[ℂ] A` to `f.liftBaseChange ℂ`. Establish `hF : ∀ (a : ℂ) (x : L), F (a ⊗ₜ x) = a • ρ x` using `fun a x => by`.

Simplify using `[F, f, LinearMap.liftBaseChange_tmul]`. Establish `hlie : ∀ u v : ℂ ⊗[ℝ] L, F ⁅u, v⁆ = ⁅F u, F v⁆`. Introduce `u v`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add u₁ u₂ h₁ h₂ => rw [add_lie, map_add, h₁, h₂, map_add, add_lie]`. Consider the case `tmul a x`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add v₁ v₂ h₁ h₂ => rw [lie_add, map_add, h₁, h₂, map_add, lie_add]`.

Consider the case `tmul b y`. Rewrite using `[LieAlgebra.ExtendScalars.bracket_tmul, hF, hF, hF, hbr, Ring.lie_def, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm b a, smul_sub]`. Set `G : ℂ ⊗[ℝ] L →ₗ⁅ℂ⁆ A` to `{ F with map_lie' := fun {u v} => hlie u v }`. Use `⟨UniversalEnvelopingAlgebra.lift ℂ G, fun X => ?_⟩` and prove the remaining obligations. Rewrite using `[UniversalEnvelopingAlgebra.lift_ι_apply]`.

Express the relevant statement in the definitionally equal form `F ((1 : ℂ) ⊗ₜ X) = ρ X`. Rewrite using `[hF, one_smul]`.
-/
theorem exists_algHom_of_real (L : Type) [LieRing L] [LieAlgebra ℝ L] (A : Type) [Ring A] [Algebra ℂ A] (ρ : L → A)
    (hadd : ∀ X Y, ρ (X + Y) = ρ X + ρ Y) (hsmul : ∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X)
    (hbr : ∀ X Y, ρ ⁅X, Y⁆ = ρ X * ρ Y - ρ Y * ρ X) :
    ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) →ₐ[ℂ] A,
      ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  let f : L →ₗ[ℝ] A :=
    { toFun := ρ
      map_add' := hadd
      map_smul' := fun c X => by
        rw [hsmul]
        exact Complex.coe_smul c (ρ X) }
  let F : ℂ ⊗[ℝ] L →ₗ[ℂ] A := f.liftBaseChange ℂ
  have hF : ∀ (a : ℂ) (x : L), F (a ⊗ₜ x) = a • ρ x := fun a x => by
    simp [F, f, LinearMap.liftBaseChange_tmul]
  have hlie : ∀ u v : ℂ ⊗[ℝ] L, F ⁅u, v⁆ = ⁅F u, F v⁆ := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u₁ u₂ h₁ h₂ => rw [add_lie, map_add, h₁, h₂, map_add, add_lie]
    | tmul a x =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v₁ v₂ h₁ h₂ => rw [lie_add, map_add, h₁, h₂, map_add, lie_add]
      | tmul b y =>
        rw [LieAlgebra.ExtendScalars.bracket_tmul, hF, hF, hF, hbr, Ring.lie_def,
          smul_mul_smul_comm, smul_mul_smul_comm, mul_comm b a, smul_sub]
  let G : ℂ ⊗[ℝ] L →ₗ⁅ℂ⁆ A := { F with map_lie' := fun {u v} => hlie u v }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ G, fun X => ?_⟩
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  change F ((1 : ℂ) ⊗ₜ X) = ρ X
  rw [hF, one_smul]

/- English proof (translation)
Introduce `n J A _ _ ρ hadd hsmul hbr`. Conclude with `exists_algHom_of_real _ A ρ hadd hsmul fun X Y => hbr X Y ⁅X, Y⁆ (by`. Rewrite using `[LieSubalgebra.coe_bracket, Ring.lie_def])`.
-/
theorem exists_algHom_unitary : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J) →ₐ[ℂ] A, ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  intro n J A _ _ ρ hadd hsmul hbr
  exact exists_algHom_of_real _ A ρ hadd hsmul fun X Y => hbr X Y ⁅X, Y⁆ (by
    rw [LieSubalgebra.coe_bracket, Ring.lie_def])

end GlobalTheory.EnvelopingExtension

end
