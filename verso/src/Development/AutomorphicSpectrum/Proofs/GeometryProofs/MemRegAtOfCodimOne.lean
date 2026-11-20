import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkSpecializes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemRangeOfIntegralAtHeightOneOver

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Take `⟨U, hU, hp, -⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (x := p.1) (U := ⊤) trivial`. Establish `hg : genPt ξ ∈ U` using `p.2.mem_open U.2 hp`. Set `e` to `RegAtRing.stalkEquiv h p`. Set `P' : Ideal (X.presheaf.stalk p.1)` to `P.comap (e : X.presheaf.stalk p.1 →+* regAt ξ p)`. Establish `hP' : P'.IsPrime` using `Ideal.comap_isPrime _ _`.

Use `letI algP := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p.1, hp⟩ : U)`. Establish `localization₂` using `hU.isLocalization_stalk ⟨p.1, hp⟩`. Set `𝔮 : Ideal Γ(X, U)` to `P'.comap (algebraMap Γ(X, U) (X.presheaf.stalk p.1))`. Establish `h𝔮 : 𝔮.IsPrime` using `Ideal.comap_isPrime _ _`. Set `y : PrimeSpectrum Γ(X, U)` to `⟨𝔮, h𝔮⟩`.

Establish `hyU : hU.fromSpec y ∈ U`. Establish `: hU.fromSpec y ∈ Set.range hU.fromSpec` using `⟨y, rfl⟩`. Rewrite `this` using `[hU.range_fromSpec]`. Then use the resulting hypothesis. Establish `hsp : hU.fromSpec y ⤳ p.1`. Establish `hle : y ≤ hU.primeIdealOf ⟨p.1, hp⟩`.

Express the relevant statement in the definitionally equal form `𝔮 ≤ (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal`. Rewrite using `[← IsLocalization.AtPrime.comap_maximalIdeal (X.presheaf.stalk p.1) (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal]`. Conclude with `Ideal.comap_mono (IsLocalRing.le_maximalIdeal hP'.ne_top)`. Use `((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hU.fromSpec.continuous` as an intermediate fact. Rewrite `this` using `[hU.fromSpec_primeIdealOf]`. Then use the resulting hypothesis.

Establish `hgy : genPt ξ ⤳ hU.fromSpec y`. Establish `hle : hU.primeIdealOf ⟨genPt ξ, hg⟩ ≤ y`. Express the relevant statement in the definitionally equal form `(hU.primeIdealOf ⟨genPt ξ, hg⟩).asIdeal ≤ 𝔮`. Introduce `r hr`. Use `letI algG := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨genPt ξ, hg⟩ : U)`.

Establish `locG` using `hU.isLocalization_stalk ⟨genPt ξ, hg⟩`. Establish `hnu : ¬ IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk (genPt ξ)) r)`. Rewrite `hr` using `[← IsLocalization.AtPrime.comap_maximalIdeal (X.presheaf.stalk (genPt ξ)) (hU.primeIdealOf ⟨genPt ξ, hg⟩).asIdeal]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 hr`. Establish `hz : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hg r) = 0`.

Assume the negation of the conclusion as `hne`. Take `⟨w, hw⟩` from `h.bij.2 ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hg r))⁻¹`. Apply `hnu` to reduce the goal to its premises. Use `IsUnit.of_mul_eq_one w (h.bij.1 ?_)` and prove the remaining obligations. Use `erw [map_mul, hw, map_one]`.

Conclude with `mul_inv_cancel₀ hne`. Establish `hz' : X.presheaf.germ U p.1 hp r = 0`. Apply `h.inj p` to reduce the goal to its premises. Rewrite using `[RegAtRing.genMap_germ p U hp hg, hz, map_zero]`. Express the relevant statement in the definitionally equal form `algebraMap Γ(X, U) (X.presheaf.stalk p.1) r ∈ P'`.

Use `erw [hz']`. Conclude with `P'.zero_mem`. Use `((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hU.fromSpec.continuous` as an intermediate fact. Rewrite `this` using `[hU.fromSpec_primeIdealOf]`. Then use the resulting hypothesis. Use `letI algY : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec y, hyU⟩ : U)`.

Establish `locY : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal` using `hU.isLocalization_stalk' y hyU`. Establish `locY' : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) 𝔮` using `locY`. Use `⟨⟨hU.fromSpec y, hgy⟩, hsp, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ringKrullDim (X.presheaf.stalk (hU.fromSpec y)) = (𝔮.height : WithBot ℕ∞)` using `IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 (X.presheaf.stalk (hU.fromSpec y))`. Establish `h2 : 𝔮.height = P'.height` using `IsLocalization.height_comap (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal.primeCompl P'`.

Establish `h3 : P'.height = P.height` using `RingEquiv.height_comap e P`. Express the relevant statement in the definitionally equal form `ringKrullDim (X.presheaf.stalk (hU.fromSpec y)) = _`. Rewrite using `[h1, h2, h3]`. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨⟨r, t⟩, he⟩` from `IsLocalization.surj y.asIdeal.primeCompl (S := X.presheaf.stalk (hU.fromSpec y)) x`.

Establish `he' : x * (X.presheaf.germ U (hU.fromSpec y) hyU).hom t.1 = (X.presheaf.germ U (hU.fromSpec y) hyU).hom r` using `he`. Establish `hgt` using `RegAtMono.genMap_germ_eq ξ p ⟨hU.fromSpec y, hgy⟩ hsp U hp hyU`. Use `⟨e ((X.presheaf.germ U p.1 hp).hom t.1), e ((X.presheaf.germ U p.1 hp).hom r), ?_, ?_⟩` and prove the remaining obligations. Conclude with `t.2`. Express the relevant statement in the definitionally equal form `genMap ξ ⟨hU.fromSpec y, hgy⟩ x * genMap ξ p ((X.presheaf.germ U p.1 hp).hom t.1) = genMap ξ p ((X.presheaf.germ U p.1 hp).hom r)`.

Rewrite using `[← hgt, ← hgt, ← map_mul]`. Conclude with `congrArg _ he'`.
-/
theorem exists_point_of_prime {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (h : IsCptGen ξ) (p : Cpt ξ) (P : Ideal (regAt ξ p)) (hP : P.IsPrime) :
    ∃ q : Cpt ξ, q.1 ⤳ p.1 ∧ ringKrullDim (X.presheaf.stalk q.1) = (P.height : WithBot ℕ∞) ∧
      ∀ a ∈ regAt ξ q, ∃ s t : regAt ξ p, s ∉ P ∧ a * s = t := by
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := p.1) (U := ⊤) trivial
  have hg : genPt ξ ∈ U := p.2.mem_open U.2 hp
  let e := RegAtRing.stalkEquiv h p
  let P' : Ideal (X.presheaf.stalk p.1) := P.comap (e : X.presheaf.stalk p.1 →+* regAt ξ p)
  have hP' : P'.IsPrime := Ideal.comap_isPrime _ _
  letI algP := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p.1, hp⟩ : U)
  have localization₂ := hU.isLocalization_stalk ⟨p.1, hp⟩
  let 𝔮 : Ideal Γ(X, U) := P'.comap (algebraMap Γ(X, U) (X.presheaf.stalk p.1))
  have h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  let y : PrimeSpectrum Γ(X, U) := ⟨𝔮, h𝔮⟩
  have hyU : hU.fromSpec y ∈ U := by
    have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at this

  have hsp : hU.fromSpec y ⤳ p.1 := by
    have hle : y ≤ hU.primeIdealOf ⟨p.1, hp⟩ := by
      change 𝔮 ≤ (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal
      rw [← IsLocalization.AtPrime.comap_maximalIdeal (X.presheaf.stalk p.1)
        (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hP'.ne_top)
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf] at this

  have hgy : genPt ξ ⤳ hU.fromSpec y := by
    have hle : hU.primeIdealOf ⟨genPt ξ, hg⟩ ≤ y := by
      change (hU.primeIdealOf ⟨genPt ξ, hg⟩).asIdeal ≤ 𝔮
      intro r hr
      letI algG := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨genPt ξ, hg⟩ : U)
      have locG := hU.isLocalization_stalk ⟨genPt ξ, hg⟩
      have hnu : ¬ IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk (genPt ξ)) r) := by
        rw [← IsLocalization.AtPrime.comap_maximalIdeal (X.presheaf.stalk (genPt ξ))
          (hU.primeIdealOf ⟨genPt ξ, hg⟩).asIdeal] at hr
        exact (IsLocalRing.mem_maximalIdeal _).1 hr
      have hz : (Scheme.stalkClosedPointTo ξ).hom
          (X.presheaf.germ U (genPt ξ) hg r) = 0 := by
        by_contra hne
        obtain ⟨w, hw⟩ := h.bij.2 ((Scheme.stalkClosedPointTo ξ).hom
          (X.presheaf.germ U (genPt ξ) hg r))⁻¹
        apply hnu
        refine IsUnit.of_mul_eq_one w (h.bij.1 ?_)
        erw [map_mul, hw, map_one]
        exact mul_inv_cancel₀ hne
      have hz' : X.presheaf.germ U p.1 hp r = 0 := by
        apply h.inj p
        rw [RegAtRing.genMap_germ p U hp hg, hz, map_zero]
      change algebraMap Γ(X, U) (X.presheaf.stalk p.1) r ∈ P'
      erw [hz']
      exact P'.zero_mem
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf] at this
  letI algY : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec y, hyU⟩ : U)
  have locY : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y hyU
  have locY' : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) 𝔮 := locY
  refine ⟨⟨hU.fromSpec y, hgy⟩, hsp, ?_, ?_⟩
  · have h1 : ringKrullDim (X.presheaf.stalk (hU.fromSpec y)) = (𝔮.height : WithBot ℕ∞) :=
      IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 (X.presheaf.stalk (hU.fromSpec y))
    have h2 : 𝔮.height = P'.height :=
      IsLocalization.height_comap (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal.primeCompl P'
    have h3 : P'.height = P.height := RingEquiv.height_comap e P
    change ringKrullDim (X.presheaf.stalk (hU.fromSpec y)) = _
    rw [h1, h2, h3]
  · rintro _ ⟨x, rfl⟩
    obtain ⟨⟨r, t⟩, he⟩ := IsLocalization.surj y.asIdeal.primeCompl
      (S := X.presheaf.stalk (hU.fromSpec y)) x
    have he' : x * (X.presheaf.germ U (hU.fromSpec y) hyU).hom t.1 =
        (X.presheaf.germ U (hU.fromSpec y) hyU).hom r := he
    have hgt := RegAtMono.genMap_germ_eq ξ p ⟨hU.fromSpec y, hgy⟩ hsp U hp hyU
    refine ⟨e ((X.presheaf.germ U p.1 hp).hom t.1), e ((X.presheaf.germ U p.1 hp).hom r), ?_, ?_⟩
    · exact t.2
    · change genMap ξ ⟨hU.fromSpec y, hgy⟩ x * genMap ξ p ((X.presheaf.germ U p.1 hp).hom t.1) =
        genMap ξ p ((X.presheaf.germ U p.1 hp).hom r)
      rw [← hgt, ← hgt, ← map_mul]
      exact congrArg _ he'

/- English proof (translation)
Introduce `X Ω _ ξ _ h hn p a ha`. Take `⟨hfr, hno, -⟩` from `RegAtRing.regAt_ring X Ω ξ h p`. Establish `: IsFractionRing (regAt ξ p) Ω` using `hfr`. Establish `: IsNoetherianRing (regAt ξ p)` using `hno inferInstance`. Establish `: IsIntegrallyClosed (regAt ξ p)`.

Rewrite using `[isIntegrallyClosed_iff Ω]`. Introduce `x hx`. Conclude with `⟨⟨x, hn p x hx⟩, rfl⟩`. Take `⟨t, d, hd, rfl⟩` from `IsFractionRing.div_surjective (A := regAt ξ p) a`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`.

Establish `hd1 : algebraMap (regAt ξ p) Ω d ≠ 0`. Simplify using `using hd0`. Take `⟨b, hb⟩` from `mem_range_of_integral_at_heightOne_over (regAt ξ p) Ω d (algebraMap (regAt ξ p) Ω t / algebraMap (regAt ξ p) Ω d) hd0 ⟨1, t, by field_simp⟩ (fun P hP h1 _ => by`. Take `⟨q, hq, hdim, hiff⟩` from `exists_point_of_prime h p P hP`. Establish `hmem` using `ha q hq (by rw [hdim]; simp [h1])`.

Take `⟨s, u, hs, hsu⟩` from `hiff _ hmem`. Conclude with `⟨u, s, hs, by rw [mul_comm]; exact hsu.symm⟩)`. Rewrite using `[← hb]`. Conclude with `b.2`.
-/
theorem mem_regAt_of_codim_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    [IsLocallyNoetherian X], IsCptGen ξ → NormalCpt ξ → ∀ (p : Cpt ξ) (a : Ω),
    (∀ q : Cpt ξ, q.1 ⤳ p.1 → ringKrullDim (X.presheaf.stalk q.1) = 1 → a ∈ regAt ξ q) →
    a ∈ regAt ξ p := by
  intro X Ω _ ξ _ h hn p a ha
  obtain ⟨hfr, hno, -⟩ := RegAtRing.regAt_ring X Ω ξ h p
  have : IsFractionRing (regAt ξ p) Ω := hfr
  have : IsNoetherianRing (regAt ξ p) := hno inferInstance
  have : IsIntegrallyClosed (regAt ξ p) := by
    rw [isIntegrallyClosed_iff Ω]
    intro x hx
    exact ⟨⟨x, hn p x hx⟩, rfl⟩
  obtain ⟨t, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := regAt ξ p) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd1 : algebraMap (regAt ξ p) Ω d ≠ 0 := by
    simpa using hd0
  obtain ⟨b, hb⟩ := mem_range_of_integral_at_heightOne_over (regAt ξ p) Ω d
    (algebraMap (regAt ξ p) Ω t / algebraMap (regAt ξ p) Ω d) hd0
    ⟨1, t, by field_simp⟩
    (fun P hP h1 _ => by
      obtain ⟨q, hq, hdim, hiff⟩ := exists_point_of_prime h p P hP
      have hmem := ha q hq (by rw [hdim]; simp [h1])
      obtain ⟨s, u, hs, hsu⟩ := hiff _ hmem
      exact ⟨u, s, hs, by rw [mul_comm]; exact hsu.symm⟩)
  rw [← hb]
  exact b.2

end GlobalTheory.CompanionTheory.Ar.Flat
