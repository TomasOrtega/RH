import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

open Module Module.Basis in

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components.

Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem charpoly_eq_restrict_mul_mapQ {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A) :
    LinearMap.charpoly g = LinearMap.charpoly (g.restrict hg) *
      LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) := by
  classical
  let bA := Module.finBasis F A
  let bQ := Module.finBasis F (V ⧸ A)
  let b := sumQuot bA bQ
  have hmat : LinearMap.toMatrix b b g = Matrix.fromBlocks (LinearMap.toMatrix bA bA (g.restrict hg))
      (Matrix.of fun i j => b.repr (g (b (Sum.inr j))) (Sum.inl i)) 0
      (LinearMap.toMatrix bQ bQ (A.mapQ A g (fun x hx => hg x hx))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₁, b, sumQuot_inl]
      rw [sumQuot_repr_inl_of_mem bA bQ _ (hg _ (bA j).2)]
      rfl
    · simp [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, b]
    · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₁, b, sumQuot_inl,
        Matrix.zero_apply]
      exact sumQuot_repr_inr_of_mem bA bQ _ (hg _ (bA j).2) i
    · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₂, b]
      rw [sumQuot_repr_inr, ← sumQuot_inr bA bQ j, Submodule.mapQ_apply]
      rfl
  rw [← LinearMap.charpoly_toMatrix g b, hmat, Matrix.charpoly_fromBlocks_zero₂₁,
    LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.
-/
theorem charpoly_block : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A),
    LinearMap.charpoly g = LinearMap.charpoly (g.restrict hg) *
      LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) ∧
    ∀ h ∈ nilRad A, LinearMap.charpoly (g + h) = LinearMap.charpoly g := by
  intro F _ V _ _ _ A g hg
  refine ⟨charpoly_eq_restrict_mul_mapQ A g hg, ?_⟩
  rintro h ⟨himg, hker⟩
  have hgh : ∀ x ∈ A, (g + h) x ∈ A := fun x hx => by
    simpa [LinearMap.add_apply, hker x hx] using hg x hx
  have hres : (g + h).restrict hgh = g.restrict hg := by
    ext x
    simp [LinearMap.restrict_apply, hker x x.2]
  have hquot : A.mapQ A (g + h) (fun x hx => hgh x hx) = A.mapQ A g (fun x hx => hg x hx) := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq]
    simpa [LinearMap.add_apply] using himg x
  rw [charpoly_eq_restrict_mul_mapQ A (g + h) hgh, charpoly_eq_restrict_mul_mapQ A g hg, hres, hquot]

end GlobalTheory.CuspGL
