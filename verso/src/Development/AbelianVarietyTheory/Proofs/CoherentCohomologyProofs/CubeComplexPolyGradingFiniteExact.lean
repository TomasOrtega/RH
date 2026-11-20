import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexExactAtOfMonomialBasis
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TopClassSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsMonomialBasisCechCubePolynomialGradingStatement

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Use `Set.Finite.subset ((Set.finite_Icc (fun _ : ι => n) (fun _ => 0)).preimage Subtype.val_injective.injOn) ?_` and prove the remaining obligations. Introduce and unpack `⟨a, ha⟩ h`. Establish `h' : ∀ i, a i < 0` using `fun i => Finset.filter_eq_self.1 h i (Finset.mem_univ i)`. Use `⟨fun i => ?_, fun i => (h' i).le⟩` and prove the remaining obligations. Use `Finset.add_sum_erase Finset.univ a (Finset.mem_univ i)` as an intermediate fact.

Establish `h2 : ∑ j ∈ Finset.univ.erase i, a j ≤ 0` using `Finset.sum_nonpos fun j _ => (h' j).le`. Express the relevant statement in the definitionally equal form `n ≤ a i`. Use linear arithmetic over natural numbers and integers.
-/
theorem finite_neg_sum_eq (ι : Type) [Fintype ι] (n : ℤ) :
    {a : {a : ι → ℤ // ∑ i, a i = n} |
      Finset.univ.filter (fun i => a.1 i < 0) = Finset.univ}.Finite := by
  classical
  refine Set.Finite.subset ((Set.finite_Icc (fun _ : ι => n) (fun _ => 0)).preimage
    Subtype.val_injective.injOn) ?_
  rintro ⟨a, ha⟩ h
  have h' : ∀ i, a i < 0 := fun i => Finset.filter_eq_self.1 h i (Finset.mem_univ i)
  refine ⟨fun i => ?_, fun i => (h' i).le⟩
  have := Finset.add_sum_erase Finset.univ a (Finset.mem_univ i)
  have h2 : ∑ j ∈ Finset.univ.erase i, a j ≤ 0 := Finset.sum_nonpos fun j _ => (h' j).le
  change n ≤ a i
  omega

/- English proof (translation)
Introduce `ι _ _ R _ n`. Take `⟨b, hb⟩` from `GlobalTheory.T.exists_monomial_basis_cechCube_polynomialGrading ι R n`. Establish `h1` using `GlobalTheory.cubeComplex_exactAt_of_monomialBasis ι R _ _ _ b hb`. Establish `h2` using `GlobalTheory.CubeTop.main ι R _ _ _ b hb`. Use `⟨fun p => ?_, fun hn p => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hp : p = Fintype.card ι`. Substitute `hp` using the available equality. Conclude with `h2.2 (finite_neg_sum_eq ι n)`. Use `ModuleCat.subsingleton_of_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h1 p hp)) infer_instance` as an intermediate fact. Distinguish the cases in `hp : p = Fintype.card ι`.

Substitute `hp` using the available equality. Use `h2.1 ?_` and prove the remaining obligations. Introduce and unpack `⟨a, ha⟩ h`. Establish `h' : ∀ i, a i < 0` using `fun i => Finset.filter_eq_self.1 h i (Finset.mem_univ i)`. Establish `: ∑ i, a i ≤ 0` using `Finset.sum_nonpos fun j _ => (h' j).le`.

Use linear arithmetic over natural numbers and integers. Conclude with `h1 p hp`.
-/
theorem cubeComplex_polyGrading_finite_exact : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (n : ℤ), (∀ p, Module.Finite R ((cubeComplex (grCube ι (polyGrading ι R) n)).homology p)) ∧ (1 ≤ n → ∀ p, (cubeComplex (grCube ι (polyGrading ι R) n)).ExactAt p) := by
  intro ι _ _ R _ n
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_monomial_basis_cechCube_polynomialGrading ι R n
  have h1 := GlobalTheory.cubeComplex_exactAt_of_monomialBasis ι R _ _ _ b hb
  have h2 := GlobalTheory.CubeTop.main ι R _ _ _ b hb
  refine ⟨fun p => ?_, fun hn p => ?_⟩
  · by_cases hp : p = Fintype.card ι
    · subst hp
      exact h2.2 (finite_neg_sum_eq ι n)
    · have := ModuleCat.subsingleton_of_isZero
        ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h1 p hp))
      infer_instance
  · by_cases hp : p = Fintype.card ι
    · subst hp
      refine h2.1 ?_
      rintro ⟨a, ha⟩ h
      have h' : ∀ i, a i < 0 := fun i => Finset.filter_eq_self.1 h i (Finset.mem_univ i)
      have : ∑ i, a i ≤ 0 := Finset.sum_nonpos fun j _ => (h' j).le
      omega
    · exact h1 p hp

end GlobalTheory
