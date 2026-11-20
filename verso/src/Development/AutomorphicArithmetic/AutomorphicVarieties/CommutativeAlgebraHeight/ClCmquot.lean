import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CmOfRegular
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyCM

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

/- English proof (translation)
Use `letI := φ.toAlgebra`. Take `⟨n, g, hg⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf.finiteType`. Set `N : Ideal (MvPolynomial (Fin n) P)` to `Ideal.comap g.toRingHom (maximalIdeal R)`. Use `haveI : N.IsMaximal := Ideal.comap_isMaximal_of_surjective g.toRingHom hg`. Establish `hgC : g.toRingHom.comp MvPolynomial.C = φ`.

Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Use `show g (MvPolynomial.C x) = φ x`. Rewrite using `[← MvPolynomial.algebraMap_eq, g.commutes]`. Both sides reduce to the same expression. Establish `hC : Ideal.comap MvPolynomial.C N = maximalIdeal P`.

Establish `h` using `congrArg PrimeSpectrum.asIdeal (IsLocalRing.comap_closedPoint φ)`. Use `show Ideal.comap MvPolynomial.C (Ideal.comap g.toRingHom (maximalIdeal R)) = maximalIdeal P`. Rewrite using `[Ideal.comap_comap, hgC]`. Conclude with `h`. Take `⟨hcm, -⟩` from `isCM_localization_mvPolynomial hP n N hC`.

Establish `hu : ∀ y : N.primeCompl, IsUnit (g.toRingHom y)` using `fun y => IsLocalRing.notMem_maximalIdeal.mp y.2`. Use `⟨Localization.AtPrime N, inferInstance, inferInstance, IsLocalization.lift hu, hcm, ?_⟩` and prove the remaining obligations. Introduce `r`. Take `⟨p, rfl⟩` from `hg r`. Conclude with `⟨algebraMap _ _ p, IsLocalization.lift_eq hu p⟩`.
-/
private theorem UpperTheory.V.CA.cmquot_of_finite {P R : Type} [CommRing P] [IsLocalRing P] [CommRing R]
    [IsLocalRing R] (hP : IsCM P) (φ : P →+* R) (hf : φ.Finite) [IsLocalHom φ] : IsCMQuot R := by
  letI := φ.toAlgebra
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf.finiteType
  let N : Ideal (MvPolynomial (Fin n) P) := Ideal.comap g.toRingHom (maximalIdeal R)
  haveI : N.IsMaximal := Ideal.comap_isMaximal_of_surjective g.toRingHom hg
  have hgC : g.toRingHom.comp MvPolynomial.C = φ := by
    refine RingHom.ext fun x => ?_
    show g (MvPolynomial.C x) = φ x
    rw [← MvPolynomial.algebraMap_eq, g.commutes]
    rfl
  have hC : Ideal.comap MvPolynomial.C N = maximalIdeal P := by
    have h := congrArg PrimeSpectrum.asIdeal (IsLocalRing.comap_closedPoint φ)
    show Ideal.comap MvPolynomial.C (Ideal.comap g.toRingHom (maximalIdeal R)) = maximalIdeal P
    rw [Ideal.comap_comap, hgC]
    exact h
  obtain ⟨hcm, -⟩ := isCM_localization_mvPolynomial hP n N hC
  have hu : ∀ y : N.primeCompl, IsUnit (g.toRingHom y) := fun y =>
    IsLocalRing.notMem_maximalIdeal.mp y.2
  refine ⟨Localization.AtPrime N, inferInstance, inferInstance, IsLocalization.lift hu, hcm, ?_⟩
  intro r
  obtain ⟨p, rfl⟩ := hg r
  exact ⟨algebraMap _ _ p, IsLocalization.lift_eq hu p⟩

/- English proof (translation)
Introduce `O _ _ _ _ R _ _ _ hR`. Use `haveI := hR.noeth`. Take `⟨n, a, ha⟩` from `Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian (maximalIdeal R))`. Establish `hspan : Ideal.span (Set.range a) = maximalIdeal R` using `ha`. Establish `hmem : ∀ s, a s ∈ maximalIdeal R`.

Introduce `s`. Rewrite using `[← hspan]`. Conclude with `Ideal.subset_span ⟨s, rfl⟩`. Establish `hrad : maximalIdeal R ≤ (Ideal.span (Set.range a) ⊔ Ideal.map (algebraMap O R) (maximalIdeal O)).radical`. Rewrite using `[hspan]`.

Conclude with `le_sup_left.trans Ideal.le_radical`. Take `⟨φ, -, hfin, hloc⟩` from `cl_mvps O R hR (Fin n) a hmem hrad`. Use `haveI := hloc`. Conclude with `cmquot_of_finite (cl_cm.1 O n).1 φ hfin`.
-/
theorem UpperTheory.V.CA.cl_cmquot :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R], IsCL O R → IsCMQuot R := by
  intro O _ _ _ _ R _ _ _ hR
  haveI := hR.noeth
  obtain ⟨n, a, ha⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian (maximalIdeal R))
  have hspan : Ideal.span (Set.range a) = maximalIdeal R := ha
  have hmem : ∀ s, a s ∈ maximalIdeal R := by
    intro s
    rw [← hspan]
    exact Ideal.subset_span ⟨s, rfl⟩
  have hrad : maximalIdeal R ≤
      (Ideal.span (Set.range a) ⊔ Ideal.map (algebraMap O R) (maximalIdeal O)).radical := by
    rw [hspan]
    exact le_sup_left.trans Ideal.le_radical
  obtain ⟨φ, -, hfin, hloc⟩ := cl_mvps O R hR (Fin n) a hmem hrad
  haveI := hloc
  exact cmquot_of_finite (cl_cm.1 O n).1 φ hfin
