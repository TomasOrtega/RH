import Development.EtaleCohomology.EtaleTrace.LCoverCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem pn_sep (k : Type) [Field k] (d : ℕ) : IsSeparated (PNto k d) := by
  unfold PNto; infer_instance

/- English proof (translation)
Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem algebraMap_field_homogeneousDegreeZero_surjective (k : Type) [Field k] (d : ℕ) :
    Function.Surjective (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0)) := by
  rintro ⟨x, hx⟩
  refine ⟨MvPolynomial.coeff 0 x, ?_⟩
  apply Subtype.ext
  have h0 := (MvPolynomial.mem_homogeneousSubmodule 0 x).1 hx
  have h : x = C (coeff 0 x) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 ((MvPolynomial.totalDegree_zero_iff_isHomogeneous _).2 h0)
  show (algebraMap k (MvPolynomial (Fin (d + 1)) k)) (coeff 0 x) = x
  conv_rhs => rw [h]
  rfl

instance ft0 (k : Type) [Field k] (d : ℕ) :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0) (MvPolynomial (Fin (d+1)) k) := by
  have : IsScalarTower k (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0) (MvPolynomial (Fin (d+1)) k) := by
    exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType k _ _

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pn_lft (k : Type) [Field k] (d : ℕ) : LocallyOfFiniteType (PNto k d) := by
  unfold PNto
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k 0)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ (algebraMap_field_homogeneousDegreeZero_surjective k d)
  infer_instance

def PNIntegral : Prop := ∀ (k : Type) [Field k] (d : ℕ), IsIntegral (PN k d)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem PNBasic_of (h : PNIntegral) : PNBasic := fun k _ d => ⟨h k d, pn_sep k d, pn_lft k d⟩

end LateralTheory.EtaleTrace.Cov
