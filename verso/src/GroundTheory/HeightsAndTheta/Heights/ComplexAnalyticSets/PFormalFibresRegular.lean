import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatNormalFibres
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegular
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibreQuotient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegularPolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

/- English proof (translation)
Introduce `k A _ _ _ hA m hm P _`. Take `⟨n, f, hf⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hA`. Establish `hfs : Function.Surjective (f : MvPolynomial (Fin n) k →+* A)` using `hf`. Take `⟨P', -, ⟨e⟩⟩` from `hQ (MvPolynomial (Fin n) k) A (f : MvPolynomial (Fin n) k →+* A) hfs inferInstance m P`. Establish `hM : (m.comap (f : MvPolynomial (Fin n) k →+* A)).IsMaximal` using `Ideal.comap_isMaximal_of_surjective _ hfs (H := hm)`.

Use `hP k n _ hM P'.asIdeal` as an intermediate fact. Conclude with `IsRegularLocalRing.of_ringEquiv e.symm`.
-/
theorem FormalFibresRegular.proof (hQ : FormalFibreQuotient.Statement)
    (hP : FormalFibresRegularPolynomial.Statement) : FormalFibresRegular.Statement := by
  intro k A _ _ _ hA m hm P _
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hA
  have hfs : Function.Surjective (f : MvPolynomial (Fin n) k →+* A) := hf
  obtain ⟨P', -, ⟨e⟩⟩ :=
    hQ (MvPolynomial (Fin n) k) A (f : MvPolynomial (Fin n) k →+* A) hfs inferInstance m P
  have hM : (m.comap (f : MvPolynomial (Fin n) k →+* A)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ hfs (H := hm)
  have := hP k n _ hM P'.asIdeal
  exact IsRegularLocalRing.of_ringEquiv e.symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
