import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain

namespace GlobalTheory

/- English proof (translation)
Introduce `A _ _ P _ x hx hxP hreg`. Use `set R := Localization.AtPrime P`. Use `set J : Ideal A := Ideal.span {x} with hJdef`. Establish `hJP : RingHom.ker (Ideal.Quotient.mk J) ≤ P`. Rewrite using `[Ideal.mk_ker, hJdef, Ideal.span_le, Set.singleton_subset_iff]`.

Conclude with `hxP`. Establish `hle : J ≤ (J.map (algebraMap A R)).comap (algebraMap A R)` using `Ideal.le_comap_map`. Use `letI : Algebra (A ⧸ J) (R ⧸ J.map (algebraMap A R)) := (Ideal.quotientMap _ _ hle).toAlgebra`. Establish `hl` using `IsLocalization.of_surjective P.primeCompl R (S' := R ⧸ J.map (algebraMap A R)) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl (by rw [Ideal.mk_ker, Ideal.mk_ker])`. Establish `hm : (P.map (Ideal.Quotient.mk J)).IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hJP`.

Establish `e : P.primeCompl.map (Ideal.Quotient.mk J) = (P.map (Ideal.Quotient.mk J)).primeCompl`. Establish `hc : (P.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = P`. Rewrite using `[Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJP]`. Use extensionality with `y`. Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z', hz', e⟩ hz`. Conclude with `hz' (hc.le (show Ideal.Quotient.mk J z' ∈ _ from e ▸ hz))`. Conclude with `fun hz => ⟨z, fun h => hz (Ideal.mem_map_of_mem _ h), rfl⟩`. Rewrite `hl` using `[e]`.

Use `IsRegularRing.isRegularLocalRing_localization (P.map (Ideal.Quotient.mk J))` as an intermediate fact. Use `haveI : IsRegularLocalRing (R ⧸ J.map (algebraMap A R)) := IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (P.map (Ideal.Quotient.mk J)).primeCompl (Localization.AtPrime (P.map (Ideal.Quotient.mk J))) _).toRingEquiv`. Establish `hdom : IsDomain (R ⧸ J.map (algebraMap A R))` using `(isDomain_and_isIntegrallyClosed_of_isRegularLocalRing _).1`. Establish `hmap : J.map (algebraMap A R) = Ideal.span {algebraMap A R x}`. Rewrite using `[hJdef, Ideal.map_span, Set.image_singleton]`.

Rewrite `hdom` using `[hmap]`. Establish `hprime : (Ideal.span {algebraMap A R x}).IsPrime` using `(Ideal.Quotient.isDomain_iff_prime _).1 hdom`. Establish `hne : algebraMap A R x ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises.

Conclude with `IsLocalization.injective R (P.primeCompl_le_nonZeroDivisors) (by simpa using h0)`. Conclude with `(Ideal.span_singleton_prime hne).1 hprime`.
-/
theorem prime_algebraMap_localization_of_isRegularRing_quotient :
    ∀ (A : Type) [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime] (x : A), x ≠ 0 → x ∈ P →
      IsRegularRing (A ⧸ Ideal.span {x}) → Prime (algebraMap A (Localization.AtPrime P) x) := by
  intro A _ _ P _ x hx hxP hreg
  set R := Localization.AtPrime P
  set J : Ideal A := Ideal.span {x} with hJdef
  have hJP : RingHom.ker (Ideal.Quotient.mk J) ≤ P := by
    rw [Ideal.mk_ker, hJdef, Ideal.span_le, Set.singleton_subset_iff]; exact hxP
  have hle : J ≤ (J.map (algebraMap A R)).comap (algebraMap A R) := Ideal.le_comap_map
  letI : Algebra (A ⧸ J) (R ⧸ J.map (algebraMap A R)) := (Ideal.quotientMap _ _ hle).toAlgebra
  have hl := IsLocalization.of_surjective P.primeCompl R (S' := R ⧸ J.map (algebraMap A R))
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
    (by rw [Ideal.mk_ker, Ideal.mk_ker])
  have hm : (P.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hJP
  have e : P.primeCompl.map (Ideal.Quotient.mk J) = (P.map (Ideal.Quotient.mk J)).primeCompl := by
    have hc : (P.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = P := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJP]
    ext y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨z', hz', e⟩ hz
      exact hz' (hc.le (show Ideal.Quotient.mk J z' ∈ _ from e ▸ hz))
    · exact fun hz => ⟨z, fun h => hz (Ideal.mem_map_of_mem _ h), rfl⟩
  rw [e] at hl
  have := IsRegularRing.isRegularLocalRing_localization (P.map (Ideal.Quotient.mk J))
  haveI : IsRegularLocalRing (R ⧸ J.map (algebraMap A R)) :=
    IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (P.map (Ideal.Quotient.mk J)).primeCompl
      (Localization.AtPrime (P.map (Ideal.Quotient.mk J))) _).toRingEquiv
  have hdom : IsDomain (R ⧸ J.map (algebraMap A R)) :=
    (isDomain_and_isIntegrallyClosed_of_isRegularLocalRing _).1
  have hmap : J.map (algebraMap A R) = Ideal.span {algebraMap A R x} := by
    rw [hJdef, Ideal.map_span, Set.image_singleton]
  rw [hmap] at hdom
  have hprime : (Ideal.span {algebraMap A R x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).1 hdom
  have hne : algebraMap A R x ≠ 0 := by
    intro h0
    apply hx
    exact IsLocalization.injective R (P.primeCompl_le_nonZeroDivisors) (by simpa using h0)
  exact (Ideal.span_singleton_prime hne).1 hprime

end GlobalTheory
