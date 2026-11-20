import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

open Module Module.Basis in

/- English proof (translation)
Set `bA` to `Module.finBasis F A`. Set `bQ` to `Module.finBasis F (V ⧸ A)`. Set `b` to `sumQuot bA bQ`. Establish `hmat : LinearMap.toMatrix b b g = Matrix.fromBlocks (LinearMap.toMatrix bA bA (g.restrict hg)) (Matrix.of fun i j => b.repr (g (b (Sum.inr j))) (Sum.inl i)) 0 (LinearMap.toMatrix bQ bQ (A.mapQ A g (fun x hx => hg x hx)))`. Use extensionality with `i j`.

Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`. Simplify using `only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₁, b, sumQuot_inl]`. Rewrite using `[sumQuot_repr_inl_of_mem bA bQ _ (hg _ (bA j).2)]`. Both sides reduce to the same expression. Simplify using `[LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, b]`.

Simplify using `only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₁, b, sumQuot_inl, Matrix.zero_apply]`. Conclude with `sumQuot_repr_inr_of_mem bA bQ _ (hg _ (bA j).2) i`. Simplify using `only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₂, b]`. Rewrite using `[sumQuot_repr_inr, ← sumQuot_inr bA bQ j, Submodule.mapQ_apply]`. Both sides reduce to the same expression.

Rewrite using `[← LinearMap.charpoly_toMatrix g b, hmat, Matrix.charpoly_fromBlocks_zero₂₁, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]`.
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
Introduce `F _ V _ _ _ A g hg`. Use `⟨charpoly_eq_restrict_mul_mapQ A g hg, ?_⟩` and prove the remaining obligations. Introduce and unpack `h ⟨himg, hker⟩`. Establish `hgh : ∀ x ∈ A, (g + h) x ∈ A` using `fun x hx => by`. Simplify `hg x hx` using `[LinearMap.add_apply, hker x hx]`.

Establish `hres : (g + h).restrict hgh = g.restrict hg`. Use extensionality with `x`. Simplify using `[LinearMap.restrict_apply, hker x x.2]`. Establish `hquot : A.mapQ A (g + h) (fun x hx => hgh x hx) = A.mapQ A g (fun x hx => hg x hx)`. Apply `Submodule.linearMap_qext` to reduce the goal to its premises.

Use extensionality with `x`. Simplify using `only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]`. Rewrite using `[Submodule.Quotient.eq]`. Simplify `himg x` using `[LinearMap.add_apply]`. Rewrite using `[charpoly_eq_restrict_mul_mapQ A (g + h) hgh, charpoly_eq_restrict_mul_mapQ A g hg, hres, hquot]`.
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
