import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.HermitianNormSquare

/- English proof (translation)
Use `letI : PreInnerProductSpace.Core ℂ V := c.toCore`. Establish `hl : ∀ (s : Finset (Fin n)) (f : Fin n → V) (y : V), c.inner (∑ a ∈ s, f a) y = ∑ a ∈ s, c.inner (f a) y`. Introduce `s f y`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using InnerProductSpace.Core.inner_zero_left (𝕜 := ℂ) y`.

Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, ← ih]`. Conclude with `InnerProductSpace.Core.inner_add_left (𝕜 := ℂ) _ _ _`. Establish `hr : ∀ (s : Finset (Fin n)) (f : Fin n → V) (x : V), c.inner x (∑ a ∈ s, f a) = ∑ a ∈ s, c.inner x (f a)`. Introduce `s f x`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using InnerProductSpace.Core.inner_zero_right (𝕜 := ℂ) x`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, ← ih]`. Conclude with `InnerProductSpace.Core.inner_add_right (𝕜 := ℂ) _ _ _`.

Rewrite using `[hl]`. Simplify using `only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ), hr, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ)]`. Simplify using `only [RCLike.star_def, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem core_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (c : InnerProductSpace.Core ℂ V) {n : ℕ}
    (e : Fin n → V) (w : Fin n → ℂ) :
    c.inner (∑ a, w a • e a) (∑ a, w a • e a)
      = star w ⬝ᵥ ((Matrix.of fun a b => c.inner (e a) (e b)) *ᵥ w) := by
  letI : PreInnerProductSpace.Core ℂ V := c.toCore
  have hl : ∀ (s : Finset (Fin n)) (f : Fin n → V) (y : V),
      c.inner (∑ a ∈ s, f a) y = ∑ a ∈ s, c.inner (f a) y := by
    intro s f y
    induction s using Finset.induction_on with
    | empty => simpa using InnerProductSpace.Core.inner_zero_left (𝕜 := ℂ) y
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      exact InnerProductSpace.Core.inner_add_left (𝕜 := ℂ) _ _ _
  have hr : ∀ (s : Finset (Fin n)) (f : Fin n → V) (x : V),
      c.inner x (∑ a ∈ s, f a) = ∑ a ∈ s, c.inner x (f a) := by
    intro s f x
    induction s using Finset.induction_on with
    | empty => simpa using InnerProductSpace.Core.inner_zero_right (𝕜 := ℂ) x
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      exact InnerProductSpace.Core.inner_add_right (𝕜 := ℂ) _ _ _
  rw [hl]
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ), hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ)]
  simp only [RCLike.star_def, Complex.star_def]
  ring

end PositivityTheory.Xgn.HermitianNormSquare

/- English proof (translation)
Introduce `L _ _ B σ n ε Γ hΓ w`. Establish `hx : (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a : GroundTheory.Heights₂.Heights.Fibre σ B.carrier) = ∑ a, w a • ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.smul_tmul']`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `w a = w a * 1`. Rewrite using `[_root_.mul_one]`. Establish `hM : Γ = Matrix.of fun a b => (B.metric.form σ).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a) ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b)`. Use extensionality with `a b`. Conclude with `hΓ a b`.

Unfold `sqAt`. Rewrite using `[hx, hM, ← PositivityTheory.Xgn.HermitianNormSquare.core_sum]`.
-/
theorem PositivityTheory.Xgn.hermitian_norm_square_formula : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (ε : Fin n → B.carrier) (Γ : Matrix (Fin n) (Fin n) ℂ),
    (∀ a b, Γ a b = (B.metric.form σ).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b)) → ∀ w : Fin n → ℂ,
    sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) = (star w ⬝ᵥ (Γ *ᵥ w)).re := by
  intro L _ _ B σ n ε Γ hΓ w
  have hx : (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a :
      GroundTheory.Heights₂.Heights.Fibre σ B.carrier)
      = ∑ a, w a • ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul']
    congr 1
    change w a = w a * 1
    rw [_root_.mul_one]
  have hM : Γ = Matrix.of fun a b => (B.metric.form σ).inner
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b) := by
    ext a b
    exact hΓ a b
  unfold sqAt
  rw [hx, hM, ← PositivityTheory.Xgn.HermitianNormSquare.core_sum]
