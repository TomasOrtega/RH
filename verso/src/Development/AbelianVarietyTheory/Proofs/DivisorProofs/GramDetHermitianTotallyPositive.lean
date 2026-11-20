import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveMulVecMapBasis
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.UnitaryClasses

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[gramOn, hform, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply, IsCMField.complexEmbedding_complexConj, mul_ite, ite_mul, Finset.sum_ite_eq]`.
-/
theorem gramOn_one_map_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (V : Submodule E (Fin n → E)) (τ : E →+* ℂ) :
    (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).map τ =
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) :
        Matrix (Fin n) (Fin (Module.finrank E V)) ℂ)ᴴ *
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k)) := by
  ext i j
  simp [gramOn, hform, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
    IsCMField.complexEmbedding_complexConj, mul_ite, ite_mul, Finset.sum_ite_eq]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis`. Consider the case `exact _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis`. Consider the case `(apply _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis ..)`.
-/
theorem gramOn_basis_mulVec_injective {E : Type} [Field E] {n : ℕ}
    (V : Submodule E (Fin n → E)) (τ : E →+* ℂ) :
    Function.Injective (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) :
        Matrix (Fin n) (Fin (Module.finrank E V)) ℂ).mulVec := by
  first
  | exact @_root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis
  | exact _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis
  | (apply _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> assumption)
  | (intros; apply _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis ..)

/- English proof (translation)
Introduce `E _ _ _ n V`. Establish `key : ∀ τ : E →+* ℂ, 0 < τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det`. Introduce `τ`. Rewrite using `[RingHom.map_det]`. Establish `: τ.mapMatrix (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V) = (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).map τ` using `rfl`.

Rewrite using `[this, gramOn_one_map_eq]`. Conclude with `(Matrix.PosDef.conjTranspose_mul_self _ (gramOn_basis_mulVec_injective V τ)).det_pos`. Use `⟨fun h0 => ?_, fun τ => ?_⟩` and prove the remaining obligations. Establish `τ0` using `(Classical.arbitrary (NumberField.InfinitePlace E)).embedding`. Use `key τ0` as an intermediate fact.

Rewrite `this` using `[h0, map_zero]`. Conclude with `lt_irrefl _ this`. Establish `h` using `Complex.lt_def.mp (key τ)`. Use `⟨(τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det).re, h.1, ?_⟩` and prove the remaining obligations. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Simplify using `using h.2.symm`.
-/
theorem gramOn_one_det_totallyPositive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (V : Submodule E (Fin n → E)), (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det ≠ 0 ∧ ∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det = r := by
  intro E _ _ _ n V
  have key : ∀ τ : E →+* ℂ, 0 < τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det := by
    intro τ
    rw [RingHom.map_det]
    have : τ.mapMatrix (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V) =
        (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).map τ := rfl
    rw [this, gramOn_one_map_eq]
    exact (Matrix.PosDef.conjTranspose_mul_self _ (gramOn_basis_mulVec_injective V τ)).det_pos
  refine ⟨fun h0 => ?_, fun τ => ?_⟩
  · have τ0 := (Classical.arbitrary (NumberField.InfinitePlace E)).embedding
    have := key τ0
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  · have h := Complex.lt_def.mp (key τ)
    refine ⟨(τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det).re, h.1, ?_⟩
    apply Complex.ext
    · simp
    · simpa using h.2.symm

end GlobalTheory.UnitaryClasses
