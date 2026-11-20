import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr

noncomputable section

namespace Formalism.L2.Pj.CompFin

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem finiteType_zero (R : Type) [CommRing R] (N : ℕ) :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) := by
  classical
  refine ⟨⟨Finset.univ.image MvPolynomial.X, ?_⟩⟩
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact Subalgebra.algebraMap_mem _ (⟨MvPolynomial.C r, (MvPolynomial.mem_homogeneousSubmodule _ _).2
      (MvPolynomial.isHomogeneous_C _ r)⟩ : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (by simp))

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem quasiCompact_str (R : Type) [CommRing R] (N : ℕ) : QuasiCompact (PSpace.str R N) := by
  haveI := finiteType_zero R N
  unfold PSpace.str
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem quasiCompact_alt (Xo : Moduli Dw l) : QuasiCompact Xo.s := by
  obtain ⟨N, i, -, hq, h⟩ := Xo.qproj
  haveI := hq
  haveI := quasiCompact_str (KA l) N
  rw [← h]
  infer_instance

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Prove the components needed by the constructor for the conclusion.

A detailed English derivation is pending.
-/
theorem isNoetherian_XF (Xo : Moduli Dw l) (c : Coeff l) : IsNoetherian (Xo.XF c) := by
  obtain ⟨N, i, hi, hq, h⟩ := Xo.qproj
  haveI := hq
  haveI := hi
  haveI := finiteType_zero (KA l) N
  have hsurj : Function.Surjective
      (algebraMap (KA l) (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (KA l) 0)) := by
    rintro ⟨x, hx⟩
    have hx' := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hx
    refine ⟨MvPolynomial.coeff 0 x, Subtype.ext ?_⟩
    rcases eq_or_ne x 0 with rfl | h0
    · simp
    · exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (hx'.totalDegree h0)).symm
  haveI : IsClosedImmersion
      (spMap (algebraMap (KA l) (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (KA l) 0))) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  haveI : LocallyOfFiniteType Xo.s := by
    rw [← h]
    unfold PSpace.str
    infer_instance
  haveI := quasiCompact_alt Xo
  constructor

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite_comp (Xo : Moduli Dw l) (c : Coeff l) : Finite (Comp Xo c) := by
  haveI := isNoetherian_XF Xo c
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype

end Formalism.L2.Pj.CompFin
