import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr

noncomputable section

namespace Formalism.L2.Pj.CompFin

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Use `⟨⟨Finset.univ.image MvPolynomial.X, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce and unpack `p -`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C r`.

Conclude with `Subalgebra.algebraMap_mem _ (⟨MvPolynomial.C r, (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C _ r)⟩ : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)`. Consider the case `add p q hp hq => exact Subalgebra.add_mem _ hp hq`. Consider the case `mul_X p i hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (by simp))`.
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
Use `haveI := finiteType_zero R N`. Unfold `PSpace.str`. Use `infer_instance`.
-/
theorem quasiCompact_str (R : Type) [CommRing R] (N : ℕ) : QuasiCompact (PSpace.str R N) := by
  haveI := finiteType_zero R N
  unfold PSpace.str
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

/- English proof (translation)
Take `⟨N, i, -, hq, h⟩` from `Xo.qproj`. Use `haveI := hq`. Use `haveI := quasiCompact_str (KA l) N`. Rewrite using `[← h]`. Use `infer_instance`.
-/
theorem quasiCompact_alt (Xo : Moduli Dw l) : QuasiCompact Xo.s := by
  obtain ⟨N, i, -, hq, h⟩ := Xo.qproj
  haveI := hq
  haveI := quasiCompact_str (KA l) N
  rw [← h]
  infer_instance

/- English proof (translation)
Take `⟨N, i, hi, hq, h⟩` from `Xo.qproj`. Use `haveI := hq`. Use `haveI := hi`. Use `haveI := finiteType_zero (KA l) N`. Establish `hsurj : Function.Surjective (algebraMap (KA l) (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (KA l) 0))`.

Introduce and unpack `⟨x, hx⟩`. Establish `hx'` using `(MvPolynomial.mem_homogeneousSubmodule _ _).1 hx`. Use `⟨MvPolynomial.coeff 0 x, Subtype.ext ?_⟩` and prove the remaining obligations. Break down `eq_or_ne x 0 with rfl | h0` into its components or cases. Simplify using the standard rewrite rules.

Conclude with `(MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (hx'.totalDegree h0)).symm`. Use `haveI : IsClosedImmersion (spMap (algebraMap (KA l) (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (KA l) 0))) := IsClosedImmersion.spec_of_surjective _ hsurj`. Use `haveI : LocallyOfFiniteType Xo.s := by`. Rewrite using `[← h]`. Unfold `PSpace.str`.

Use `infer_instance`. Use `haveI := quasiCompact_alt Xo`. Prove the components needed by the constructor for the conclusion.
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
Use `haveI := isNoetherian_XF Xo c`. Conclude with `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype`.
-/
theorem finite_comp (Xo : Moduli Dw l) (c : Coeff l) : Finite (Comp Xo c) := by
  haveI := isNoetherian_XF Xo c
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype

end Formalism.L2.Pj.CompFin
