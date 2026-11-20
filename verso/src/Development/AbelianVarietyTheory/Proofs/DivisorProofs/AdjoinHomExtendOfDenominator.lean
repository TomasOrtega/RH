import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyAlgHomAdjoin

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin`. Consider the case `exact _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin`. Consider the case `(apply _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin ..)`.
-/
theorem adjoin_hom_extend_of_denominator (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω]
    [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S) (hψ : ψ h ≠ 0) (T : Set F)
    (hT : ∀ x ∈ T, (h : F) * x ∈ S) : Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  first
  | exact @_root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin
  | exact _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin
  | (apply _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin ..)

end GlobalTheory
