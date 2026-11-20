import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry GroundTheory.Arith.SchemeCoh

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
lemma polySection_congr {A : Type u} [CommRing A] {N n : ℕ} {P Q : MvPolynomial (Fin (N + 1)) A}
    (hP : P ∈ ProjSpace.grading A N n) (hQ : Q ∈ ProjSpace.grading A N n) (h : P = Q) :
    polySection hP = polySection hQ := by
  subst h; rfl

def monomialBasisGrading (A : Type u) [CommRing A] (N n : ℕ) :
    Module.Basis {a : Fin (N + 1) →₀ ℕ // a.degree = n} A (ProjSpace.grading A N n) :=
  (MvPolynomial.basisRestrictSupport A {a : Fin (N + 1) →₀ ℕ | a.degree = n}).map
    (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (σ := Fin (N + 1)) (R := A) n).symm)

/- English proof (translation)
Establish `h : monomialBasisGrading A N n a = ⟨_, monomial_mem_grading (A` using `A) a.1 a.2⟩ := by`. Rewrite using `[Module.Basis.apply_eq_iff]`. Use extensionality with `b`. Simplify using `only [monomialBasisGrading, MvPolynomial.basisRestrictSupport, Module.Basis.map_repr, Finsupp.single_apply, Subtype.ext_iff]`. Express the relevant statement in the definitionally equal form `MvPolynomial.coeff b.1 (MvPolynomial.monomial a.1 (1 : A)) = _`.

Rewrite using `[MvPolynomial.coeff_monomial]`. Rewrite using `[h]`.
-/
lemma monomialBasisGrading_apply (A : Type u) [CommRing A] (N n : ℕ)
    (a : {a : Fin (N + 1) →₀ ℕ // a.degree = n}) :
    (monomialBasisGrading A N n a : MvPolynomial (Fin (N + 1)) A) = MvPolynomial.monomial a.1 1 := by
  have h : monomialBasisGrading A N n a = ⟨_, monomial_mem_grading (A := A) a.1 a.2⟩ := by
    rw [Module.Basis.apply_eq_iff]
    ext b
    simp only [monomialBasisGrading, MvPolynomial.basisRestrictSupport, Module.Basis.map_repr,
      Finsupp.single_apply, Subtype.ext_iff]
    change MvPolynomial.coeff b.1 (MvPolynomial.monomial a.1 (1 : A)) = _
    rw [MvPolynomial.coeff_monomial]
  rw [h]

/- English proof (translation)
Introduce `A _ N n`. Take `⟨e, he⟩` from `h A N n`. Use `⟨(monomialBasisGrading A N n).map e, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.map_apply, he]`. Conclude with `polySection_congr _ _ (monomialBasisGrading_apply A N n a)`.
-/
theorem MonomialBasis.proof (h : PolySections.Statement.{u}) : MonomialBasis.Statement.{u} := by
  intro A _ N n
  obtain ⟨e, he⟩ := h A N n
  refine ⟨(monomialBasisGrading A N n).map e, fun a => ?_⟩
  rw [Module.Basis.map_apply, he]
  exact polySection_congr _ _ (monomialBasisGrading_apply A N n a)

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
