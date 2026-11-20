import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompletelyReducibleKroneckerOfSpanEqTopStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleToMatrixIffIsSemisimpleRepres
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Establish `: FiniteDimensional ℂ V` using `Module.Finite.of_basis b`. Establish `h1` using `span_range_eq_top_of_isIrreducible G V ρ h`. Establish `h2 : Set.range ((LinearMap.toMatrixAlgEquiv b : Module.End ℂ V →* Matrix ι ι ℂ).comp ρ) = (LinearMap.toMatrix b b).toLinearMap '' Set.range ρ`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite using `[h2, ← Submodule.map_span, h1, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `(LinearMap.toMatrix b b).surjective`.
-/
theorem span_range_toMatrix_eq_top_of_isIrreducible {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (b : Module.Basis ι ℂ V) (h : ρ.IsIrreducible) :
    Submodule.span ℂ (Set.range
      ((LinearMap.toMatrixAlgEquiv b : Module.End ℂ V →* Matrix ι ι ℂ).comp ρ)) = ⊤ := by
  have : FiniteDimensional ℂ V := Module.Finite.of_basis b
  have h1 := span_range_eq_top_of_isIrreducible G V ρ h
  have h2 : Set.range ((LinearMap.toMatrixAlgEquiv b : Module.End ℂ V →* Matrix ι ι ℂ).comp ρ) =
      (LinearMap.toMatrix b b).toLinearMap '' Set.range ρ := by
    rw [← Set.range_comp]; rfl
  rw [h2, ← Submodule.map_span, h1, Submodule.map_top, LinearMap.range_eq_top]
  exact (LinearMap.toMatrix b b).surjective

/- English proof (translation)
Introduce `G _ V _ _ ρ W _ _ ρ' _ _ h h'`. Set `b` to `Module.finBasis ℂ V`. Set `b'` to `Module.finBasis ℂ W`. Establish `key` using `GlobalTheory.T.isCompletelyReducible_kronecker_of_span_eq_top _ _ G _ _ (span_range_toMatrix_eq_top_of_isIrreducible ρ b h) (span_range_toMatrix_eq_top_of_isIrreducible ρ' b' h')`. Rewrite using `[← ss_range_toMatrix_iff_isSemisimpleRepresentation _ G _ _ (b.tensorProduct b')]`.

Use `key using 3 with g` and compare the differences between its conclusion and the goal. Rewrite using `[Representation.tprod_apply, TensorProduct.toMatrix_map]`. Both sides reduce to the same expression.
-/
theorem isSemisimpleRepresentation_tprod_of_isIrreducible :
    ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W], ρ.IsIrreducible → ρ'.IsIrreducible → (ρ.tprod ρ').IsSemisimpleRepresentation := by
  intro G _ V _ _ ρ W _ _ ρ' _ _ h h'
  let b := Module.finBasis ℂ V
  let b' := Module.finBasis ℂ W
  have key := GlobalTheory.T.isCompletelyReducible_kronecker_of_span_eq_top _ _ G _ _ (span_range_toMatrix_eq_top_of_isIrreducible ρ b h)
    (span_range_toMatrix_eq_top_of_isIrreducible ρ' b' h')
  rw [← ss_range_toMatrix_iff_isSemisimpleRepresentation _ G _ _ (b.tensorProduct b')]
  convert key using 3 with g
  rw [Representation.tprod_apply, TensorProduct.toMatrix_map]
  rfl

end GlobalTheory.ClassFin
