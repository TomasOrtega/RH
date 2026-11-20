import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Use `⟨(Spec.preimage x).hom, ?_⟩` and prove the remaining obligations. Simplify using `[Spec.map_preimage]`.
-/
private lemma exists_hom {R Ω : Type} [CommRing R] [Field Ω] (x : gp Ω ⟶ Spec (CommRingCat.of R)) :
    ∃ φ : R →+* Ω, x = Spec.map (CommRingCat.ofHom φ) := by
  refine ⟨(Spec.preimage x).hom, ?_⟩
  simp [Spec.map_preimage]

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
private lemma map_comp' {R S Ω : Type} [CommRing R] [CommRing S] [CommRing Ω] (a : R →+* S) (φ : S →+* Ω) :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom (φ.comp a)) := by
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Use `Spec.map_injective h` as an intermediate fact. Simplify using `using congrArg CommRingCat.Hom.hom this`.
-/
private lemma map_inj' {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  simpa using congrArg CommRingCat.Hom.hom this

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [pt]`. Use `show a ∈ (Ideal.comap f (IsLocalRing.closedPoint Ω).asIdeal) ↔ _`. Simplify using `[IsLocalRing.closedPoint, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.
-/
private lemma pt_map {R Ω : Type} [CommRing R] [Field Ω] (f : R →+* Ω) :
    (pt (Spec.map (CommRingCat.ofHom f))).asIdeal = RingHom.ker f := by
  ext a
  simp only [pt]
  show a ∈ (Ideal.comap f (IsLocalRing.closedPoint Ω).asIdeal) ↔ _
  simp [IsLocalRing.closedPoint, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/- English proof (translation)
Introduce `hsf hgt A B _ _ _ _ _ _`. Take `⟨L, _, _, _, _, _, _, hfin, hsp⟩` from `hsf A B`. Use `set C := integralClosure A L`. Establish `hinj : Function.Injective (algebraMap A C)`. Introduce `a b hab`.

Establish `h1 : algebraMap A L a = algebraMap A L b`. Use `congrArg (fun c : C => (c : L)) hab` as an intermediate fact. Simplify using `using this`. Rewrite `h1` using `[IsScalarTower.algebraMap_apply A (FractionRing A) L a, IsScalarTower.algebraMap_apply A (FractionRing A) L b]`. Conclude with `IsFractionRing.injective A (FractionRing A) ((algebraMap (FractionRing A) L).injective h1)`.

Establish `key : ∀ {Ω : Type} [Field Ω] (φ : C →+* Ω), RingHom.ker (φ.comp (algebraMap A C)) = ⊥ → RingHom.ker φ = ⊥`. Introduce `Ω _ φ h`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := A)` to reduce the goal to its premises. Rewrite using `[RingHom.comap_ker]`. Conclude with `h`.

Use `⟨Spec (CommRingCat.of C), Spec.map (CommRingCat.ofHom (algebraMap A C)), (B →ₐ[A] C), fun j => Spec.map (CommRingCat.ofHom (j : B →+* C)), fun j => (⟨RingHom.ker (j : B →+* C), RingHom.ker_isPrime _⟩ : PrimeSpectrum B), ?_, ?_, hfin, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `IsIntegralHom.SpecMap_iff.mpr (fun x => Algebra.IsIntegral.isIntegral x)`. Use `⟨fun p => ?_⟩` and prove the remaining obligations. Establish `hp : p.asIdeal.IsPrime` using `p.isPrime`. Take `⟨Q, -, hQ, hQc⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := C) p.asIdeal ⊥ (by`.

Rewrite using `[Ideal.comap_bot_of_injective _ hinj]`. Conclude with `bot_le)`. Conclude with `⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQc⟩`. Introduce `j`. Rewrite using `[map_comp']`.

Use `congr 2`. Conclude with `j.comp_algebraMap`. Introduce `Ω _ x x' hxx`. Take `⟨φ, rfl⟩` from `exists_hom x`. Take `⟨φ', rfl⟩` from `exists_hom x'`.

Simplify using `only [map_comp'] at hxx`. Take `⟨g, hg⟩` from `hgt A L Ω φ φ' (map_inj' hxx)`. Set `e : (B →ₐ[A] C) ≃ (B →ₐ[A] C)` to `{ toFun := fun j => (g.symm : C →ₐ[A] C).comp j invFun := fun j => (g : C →ₐ[A] C).comp j left_inv := fun j => by`. Use extensionality with `b`. Simplify using the standard rewrite rules.

Use `right_inv := fun j => by`. Use extensionality with `b`. Simplify using `}`. Use `⟨e, fun j => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [map_comp']`.

Use `congr 2`. Use extensionality with `b`. Simplify using `[e, hg]`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use extensionality with `b`.

Simplify using `[e]`. Introduce `Ω _ x z hz hbot`. Take `⟨φ, rfl⟩` from `exists_hom x`. Take `⟨ζ, rfl⟩` from `exists_hom z`. Simplify using `only [map_comp'] at hz`.

Rewrite `hbot` using `[map_comp', pt_map]`. Establish `hφ : Function.Injective φ` using `(RingHom.injective_iff_ker_eq_bot φ).mpr (key φ hbot)`. Establish `hiff : ∀ j : B →ₐ[A] C, Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (j : B →+* C)) = Spec.map (CommRingCat.ofHom ζ) ↔ φ.comp (j : B →+* C) = ζ`. Introduce `j`. Rewrite using `[map_comp']`.

Conclude with `⟨map_inj', fun h => by rw [h]⟩`. Take `⟨j0, hj0, hu⟩` from `hsp Ω φ ζ ((RingHom.injective_iff_ker_eq_bot _).mpr hbot) (map_inj' hz)`. Use `⟨⟨j0, (hiff j0).2 hj0, fun j hj => hu j ((hiff j).1 hj)⟩, fun j hj => ?_⟩` and prove the remaining obligations. Rewrite `hj` using `[hiff]`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises.

Rewrite using `[pt_map, ← hj]`. Use extensionality with `b`. Simplify using `[map_eq_zero_iff _ hφ]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.splitCover_of :
    SplitField → GalTrans → SplitCover := by
  intro hsf hgt A B _ _ _ _ _ _
  obtain ⟨L, _, _, _, _, _, _, hfin, hsp⟩ := hsf A B
  set C := integralClosure A L
  have hinj : Function.Injective (algebraMap A C) := by
    intro a b hab
    have h1 : algebraMap A L a = algebraMap A L b := by
      have := congrArg (fun c : C => (c : L)) hab
      simpa using this
    rw [IsScalarTower.algebraMap_apply A (FractionRing A) L a,
      IsScalarTower.algebraMap_apply A (FractionRing A) L b] at h1
    exact IsFractionRing.injective A (FractionRing A) ((algebraMap (FractionRing A) L).injective h1)
  have key : ∀ {Ω : Type} [Field Ω] (φ : C →+* Ω),
      RingHom.ker (φ.comp (algebraMap A C)) = ⊥ → RingHom.ker φ = ⊥ := by
    intro Ω _ φ h
    apply Ideal.eq_bot_of_comap_eq_bot (R := A)
    rw [RingHom.comap_ker]
    exact h
  refine ⟨Spec (CommRingCat.of C), Spec.map (CommRingCat.ofHom (algebraMap A C)), (B →ₐ[A] C),
    fun j => Spec.map (CommRingCat.ofHom (j : B →+* C)),
    fun j => (⟨RingHom.ker (j : B →+* C), RingHom.ker_isPrime _⟩ : PrimeSpectrum B),
    ?_, ?_, hfin, ?_, ?_, ?_⟩
  · exact IsIntegralHom.SpecMap_iff.mpr (fun x => Algebra.IsIntegral.isIntegral x)
  · refine ⟨fun p => ?_⟩
    have hp : p.asIdeal.IsPrime := p.isPrime
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := C) p.asIdeal ⊥ (by
      rw [Ideal.comap_bot_of_injective _ hinj]
      exact bot_le)
    exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQc⟩
  · intro j
    rw [map_comp']
    congr 2
    exact j.comp_algebraMap
  · intro Ω _ x x' hxx
    obtain ⟨φ, rfl⟩ := exists_hom x
    obtain ⟨φ', rfl⟩ := exists_hom x'
    simp only [map_comp'] at hxx
    obtain ⟨g, hg⟩ := hgt A L Ω φ φ' (map_inj' hxx)
    let e : (B →ₐ[A] C) ≃ (B →ₐ[A] C) :=
      { toFun := fun j => (g.symm : C →ₐ[A] C).comp j
        invFun := fun j => (g : C →ₐ[A] C).comp j
        left_inv := fun j => by
          ext b
          simp
        right_inv := fun j => by
          ext b
          simp }
    refine ⟨e, fun j => ⟨?_, ?_⟩⟩
    · simp only [map_comp']
      congr 2
      ext b
      simp [e, hg]
    · apply PrimeSpectrum.ext
      ext b
      simp [e]
  · intro Ω _ x z hz hbot
    obtain ⟨φ, rfl⟩ := exists_hom x
    obtain ⟨ζ, rfl⟩ := exists_hom z
    simp only [map_comp'] at hz
    rw [map_comp', pt_map] at hbot
    have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).mpr (key φ hbot)
    have hiff : ∀ j : B →ₐ[A] C, Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom (j : B →+* C)) = Spec.map (CommRingCat.ofHom ζ) ↔
        φ.comp (j : B →+* C) = ζ := by
      intro j
      rw [map_comp']
      exact ⟨map_inj', fun h => by rw [h]⟩
    obtain ⟨j0, hj0, hu⟩ := hsp Ω φ ζ ((RingHom.injective_iff_ker_eq_bot _).mpr hbot) (map_inj' hz)
    refine ⟨⟨j0, (hiff j0).2 hj0, fun j hj => hu j ((hiff j).1 hj)⟩, fun j hj => ?_⟩
    rw [hiff] at hj
    apply PrimeSpectrum.ext
    rw [pt_map, ← hj]
    ext b
    simp [map_eq_zero_iff _ hφ]
