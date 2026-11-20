import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `R B _ _ _ _ z`. Set `z' : PrimeSpectrum B` to `z`. Use `haveI : z'.asIdeal.IsPrime := z'.isPrime`. Use `haveI : Algebra.QuasiFiniteAt R z'.asIdeal := inferInstance`. Take `⟨R', _, _, hEt, P, _, _, e, he, P', hP', hlo, hq, heP, -, -, huniq⟩` from `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (z'.asIdeal.under R) z'.asIdeal`.

Establish `pb` using `(isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R R' B)).flip`. Use `⟨⟨Spec (CommRingCat.of R'), Spec (CommRingCat.of (TensorProduct R R' B)), _, _, _, pb⟩, ((PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum (TensorProduct R R' B))) : Set (PrimeSpectrum (TensorProduct R R' B))), (⟨P', hP'⟩ : PrimeSpectrum (TensorProduct R R' B)), …` and prove the remaining obligations. Conclude with `HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hEt)`. Conclude with `PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩`. Conclude with `heP`.

Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Conclude with `hq`. Introduce `v' hv' hr`. Establish `h1 : (v' : PrimeSpectrum (TensorProduct R R' B)).asIdeal.LiesOver P`. Prove the components needed by the constructor for the conclusion.

Establish `h2 : Ideal.comap (algebraMap R' (TensorProduct R R' B)) (v' : PrimeSpectrum (TensorProduct R R' B)).asIdeal = Ideal.comap (algebraMap R' (TensorProduct R R' B)) P'` using `congrArg PrimeSpectrum.asIdeal hr`. Rewrite using `[Ideal.under, h2]`. Conclude with `hlo.over`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Conclude with `huniq _ (PrimeSpectrum.isPrime _) h1 hv'`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.isolateSpec_of :
    IsolateSpec := by
  intro R B _ _ _ _ z
  let z' : PrimeSpectrum B := z
  haveI : z'.asIdeal.IsPrime := z'.isPrime
  haveI : Algebra.QuasiFiniteAt R z'.asIdeal := inferInstance
  obtain ⟨R', _, _, hEt, P, _, _, e, he, P', hP', hlo, hq, heP, -, -, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (z'.asIdeal.under R) z'.asIdeal
  have pb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R R' B)).flip
  refine ⟨⟨Spec (CommRingCat.of R'), Spec (CommRingCat.of (TensorProduct R R' B)), _, _, _, pb⟩,
    ((PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum (TensorProduct R R' B))) :
      Set (PrimeSpectrum (TensorProduct R R' B))),
    (⟨P', hP'⟩ : PrimeSpectrum (TensorProduct R R' B)), ?_, ?_, ?_, ?_, ?_⟩
  · exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hEt)
  · exact PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  · exact heP
  · apply PrimeSpectrum.ext
    exact hq
  · intro v' hv' hr
    have h1 : (v' : PrimeSpectrum (TensorProduct R R' B)).asIdeal.LiesOver P := by
      constructor
      have h2 : Ideal.comap (algebraMap R' (TensorProduct R R' B))
          (v' : PrimeSpectrum (TensorProduct R R' B)).asIdeal =
          Ideal.comap (algebraMap R' (TensorProduct R R' B)) P' :=
        congrArg PrimeSpectrum.asIdeal hr
      rw [Ideal.under, h2]
      exact hlo.over
    apply PrimeSpectrum.ext
    exact huniq _ (PrimeSpectrum.isPrime _) h1 hv'
