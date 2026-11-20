import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Use `IsIntegrallyClosed.of_localization_maximal ?_` and prove the remaining obligations. Introduce `p _ _`. Set `y : PrimeSpectrum Γ(S, U)` to `⟨p, inferInstance⟩`. Establish `hmem : hU.fromSpec y ∈ U`. Rewrite using `[← SetLike.mem_coe, ← hU.range_fromSpec]`.

Conclude with `⟨_, rfl⟩`. Use `letI := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨hU.fromSpec y, hmem⟩`. Use `haveI : IsLocalization.AtPrime (S.presheaf.stalk (hU.fromSpec y)) p := hU.isLocalization_stalk' y hmem`. Take `⟨_, hint⟩` from `hN (hU.fromSpec y)`. Use `haveI := hint`.

Conclude with `IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv p.primeCompl (S.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime p)).toRingEquiv`.
-/
private theorem normal_affineOpen_integrallyClosed (S : Scheme.{0}) (hN : Nml S) (U : S.Opens) (hU : IsAffineOpen U)
    [IsDomain Γ(S, U)] : IsIntegrallyClosed Γ(S, U) := by
  refine IsIntegrallyClosed.of_localization_maximal ?_
  intro p _ _
  let y : PrimeSpectrum Γ(S, U) := ⟨p, inferInstance⟩
  have hmem : hU.fromSpec y ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  letI := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨hU.fromSpec y, hmem⟩
  haveI : IsLocalization.AtPrime (S.presheaf.stalk (hU.fromSpec y)) p := hU.isLocalization_stalk' y hmem
  obtain ⟨_, hint⟩ := hN (hU.fromSpec y)
  haveI := hint
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (S.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime p)).toRingEquiv

/- English proof (translation)
Introduce `S _ hN s`. Take `⟨U, hU, hs, -⟩` from `exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial`. Use `haveI : Nonempty U := ⟨⟨s, hs⟩⟩`. Use `haveI : IsDomain Γ(S, U) := IsIntegral.component_integral U`. Conclude with `⟨U, hU, hs, inferInstance, normal_affineOpen_integrallyClosed S hN U hU⟩`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.nmlInt_of :
    NmlInt := by
  intro S _ hN s
  obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨s, hs⟩⟩
  haveI : IsDomain Γ(S, U) := IsIntegral.component_integral U
  exact ⟨U, hU, hs, inferInstance, normal_affineOpen_integrallyClosed S hN U hU⟩
