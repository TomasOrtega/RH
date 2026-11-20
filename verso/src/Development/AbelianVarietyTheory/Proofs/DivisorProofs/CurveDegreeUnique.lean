import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitMulPowOfMaximalIdealEqSpan
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
open IsLocalRing Polynomial

namespace GlobalTheory.EtalePolyDvr

/- English proof (translation)
Introduce `A _ _ _ _ E _ _ _ _ _ Q _ P _ p _ hp hP`. Use `haveI hE : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing A[X] E`. Use `haveI hR : IsNoetherianRing (Localization.AtPrime Q) := IsLocalization.isNoetherianRing Q.primeCompl _ hE`. Use `haveI hLPn : IsNoetherianRing (Localization.AtPrime P) := IsLocalization.isNoetherianRing P.primeCompl _ hR`. Set `Q' : Ideal E` to `P.comap (algebraMap E (Localization.AtPrime Q))`.

Use `haveI hQ' : Q'.IsPrime := Ideal.comap_isPrime _ _`. Use `haveI hLoc : IsLocalization.AtPrime (Localization.AtPrime P) Q' := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization Q.primeCompl (Localization.AtPrime P) P`. Set `e : Localization.AtPrime Q' ≃ₐ[E] Localization.AtPrime P` to `IsLocalization.algEquiv Q'.primeCompl _ _`. Use `haveI hAp : IsDomain (Localization.AtPrime p) := IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors`. Use `haveI hApd : IsDiscreteValuationRing (Localization.AtPrime p) := GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp _`.

Establish `hAL : ∀ a : A, algebraMap A (Localization.AtPrime Q') a = algebraMap E (Localization.AtPrime Q') (algebraMap A E a)` using `fun a => IsScalarTower.algebraMap_apply A E _ a`. Establish `hALP : ∀ a : A, algebraMap A (Localization.AtPrime P) a = algebraMap E (Localization.AtPrime P) (algebraMap A E a)` using `fun a => by`. Both sides reduce to the same expression. Establish `he : ∀ a : A, e (algebraMap A (Localization.AtPrime Q') a) = algebraMap A (Localization.AtPrime P) a`. Introduce `a`.

Rewrite using `[hAL, hALP, e.commutes]`. Establish `hunder : Q'.comap (algebraMap A[X] E) = p.map C`. Rewrite using `[← hP]`. Use `show Ideal.comap _ (Ideal.comap _ P) = _`. Rewrite using `[Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]`.

Establish `hunderA : ∀ a : A, algebraMap A E a ∈ Q' ↔ a ∈ p`. Introduce `a`. Rewrite using `[IsScalarTower.algebraMap_apply A A[X] E, ← Ideal.mem_comap, hunder, Polynomial.algebraMap_eq, Ideal.mem_map_C_iff]`. Use `⟨fun h => by simpa using h 0, fun h n => ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_C]`.

Use `split_ifs`. Conclude with `h`. Conclude with `p.zero_mem`. Establish `hcomp : (algebraMap A[X] (Localization.AtPrime Q')).comp C = algebraMap A (Localization.AtPrime Q')`. Use extensionality with `a`.

Simplify using `only [RingHom.comp_apply]`. Rewrite using `[hAL, IsScalarTower.algebraMap_apply A A[X] E, Polynomial.algebraMap_eq, IsScalarTower.algebraMap_apply A[X] E (Localization.AtPrime Q')]`. Establish `hun : Algebra.IsUnramifiedAt A[X] Q'` using `inferInstance`. Set `p0 : Ideal A[X]` to `Q'.under A[X]`. Set `` to `Localization.AtPrime.algebraOfLiesOver p0 Q'`.

Establish `hm` using `((Algebra.isUnramifiedAt_iff_map_eq A[X] p0 Q').mp hun).2`. Establish `hp0 : p0 = p.map C` using `hunder`. Establish `hunit : ∀ a : A, a ∉ p → IsUnit (algebraMap A (Localization.AtPrime Q') a)`. Introduce `a ha`. Assume the negation of the conclusion as `h`.

Apply `ha` to reduce the goal to its premises. Rewrite using `[← hunderA, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q') Q', ← hAL]`. Conclude with `h`. Use `haveI hflatE : Module.Flat A E := Module.Flat.trans A A[X] E`. Use `haveI hflatL : Module.Flat A (Localization.AtPrime Q') := Module.Flat.trans A E _`.

Establish `key : ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime p) π) → ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) ∧ Irreducible (algebraMap A (Localization.AtPrime P) π)`. Introduce `π hπ`. Establish `hπp : π ∈ p`. Rewrite using `[← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p π]`. Conclude with `hπ.not_isUnit`.

Establish `hπ0 : π ≠ 0` using `by rintro rfl; exact hπ.ne_zero (map_zero _)`. Establish `hmAp` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπ`. Establish `hmL : maximalIdeal (Localization.AtPrime Q') = Ideal.span {algebraMap A (Localization.AtPrime Q') π}`. Rewrite using `[← hm, hp0, Ideal.map_map, hcomp]`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Establish `h1 : algebraMap A (Localization.AtPrime p) a ∈ maximalIdeal _` using `(IsLocalization.AtPrime.to_map_mem_maximal_iff _ p a).mpr ha`. Rewrite `h1` using `[hmAp, Ideal.mem_span_singleton']`. Take `⟨c, hc⟩` from `h1`.

Take `⟨⟨b, s⟩, rfl⟩` from `IsLocalization.mk'_surjective p.primeCompl c`. Establish `h2 : algebraMap A (Localization.AtPrime p) (a * s) = algebraMap A (Localization.AtPrime p) (b * π)`. Rewrite using `[map_mul, map_mul, ← hc, mul_right_comm, IsLocalization.mk'_spec]`. Take `⟨t, ht⟩` from `(IsLocalization.eq_iff_exists p.primeCompl _).mp h2`. Establish `hts : (t : A) * s ∉ p` using `p.primeCompl.mul_mem t.2 s.2`.

Rewrite using `[Ideal.mem_comap, Ideal.mem_span_singleton, ← (hunit _ hts).dvd_mul_right, ← map_mul]`. Establish `h3 : a * ((t : A) * s) = π * ((t : A) * b)` using `by linear_combination ht`. Rewrite using `[h3, map_mul]`. Conclude with `dvd_mul_right _ _`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`.

Conclude with `Ideal.mem_map_of_mem _ hπp`. Establish `hreg : ∀ x : Localization.AtPrime Q', algebraMap A _ π * x = 0 → x = 0`. Introduce `x hx`. Use `Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Localization.AtPrime Q') (mem_nonZeroDivisors_of_ne_zero hπ0)` as an intermediate fact. Conclude with `this (show π • x = π • (0 : Localization.AtPrime Q') by`.

Rewrite using `[smul_zero, Algebra.smul_def, hx])`. Establish `hmem : ∀ y : Localization.AtPrime Q', e y ∈ maximalIdeal (Localization.AtPrime P) ↔ y ∈ maximalIdeal _`. Introduce `y`. Simplify using `only [mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]`. Establish `hmLP : maximalIdeal (Localization.AtPrime P) = Ideal.span {algebraMap A (Localization.AtPrime P) π}`.

Use extensionality with `x`. Take `⟨y, rfl⟩` from `e.surjective x`. Rewrite using `[hmem, hmL, Ideal.mem_span_singleton, Ideal.mem_span_singleton, ← he, map_dvd_iff]`. Establish `hregP : ∀ x : Localization.AtPrime P, algebraMap A _ π * x = 0 → x = 0`. Introduce `x hx`.

Take `⟨y, rfl⟩` from `e.surjective x`. Rewrite `hx` using `[← he, ← map_mul, map_eq_zero_iff _ e.injective]`. Rewrite using `[hreg y hx, map_zero]`. Conclude with `GlobalTheory.Pat.dvr_of_maximalIdeal_eq_span hmLP hregP`. Use `⟨?_, fun π hπ => (key π hπ).2.2⟩` and prove the remaining obligations.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective p.primeCompl ϖ`. Establish `ha : Irreducible (algebraMap A (Localization.AtPrime p) a)`. Establish `h` using `IsLocalization.mk'_spec (Localization.AtPrime p) a s`. Rewrite using `[← h]`.

Conclude with `(irreducible_mul_isUnit (IsLocalization.map_units _ s)).mpr hϖ`. Take `⟨hd, hdvr, -⟩` from `key a ha`. Conclude with `⟨hd, hdvr⟩`.
-/
theorem isDiscreteValuationRing_atPrime_of_etale_polynomial :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (E : Type) [CommRing E] [Algebra A[X] E] [Algebra A E] [IsScalarTower A A[X] E]
    [Algebra.Etale A[X] E] (Q : Ideal E) [Q.IsPrime] (P : Ideal (Localization.AtPrime Q)) [P.IsPrime]
    (p : Ideal A) [p.IsPrime], p.height = 1 →
    P.comap (algebraMap A[X] (Localization.AtPrime Q)) = p.map (Polynomial.C : A →+* A[X]) →
    (∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P)) ∧
      ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime p) π) →
        Irreducible (algebraMap A (Localization.AtPrime P) π) := by
  intro A _ _ _ _ E _ _ _ _ _ Q _ P _ p _ hp hP
  classical
  haveI hE : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing A[X] E
  haveI hR : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ hE
  haveI hLPn : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ hR
  let Q' : Ideal E := P.comap (algebraMap E (Localization.AtPrime Q))
  haveI hQ' : Q'.IsPrime := Ideal.comap_isPrime _ _
  haveI hLoc : IsLocalization.AtPrime (Localization.AtPrime P) Q' :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization Q.primeCompl
      (Localization.AtPrime P) P
  let e : Localization.AtPrime Q' ≃ₐ[E] Localization.AtPrime P :=
    IsLocalization.algEquiv Q'.primeCompl _ _
  haveI hAp : IsDomain (Localization.AtPrime p) :=
    IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors
  haveI hApd : IsDiscreteValuationRing (Localization.AtPrime p) :=
    GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp _
  have hAL : ∀ a : A, algebraMap A (Localization.AtPrime Q') a =
      algebraMap E (Localization.AtPrime Q') (algebraMap A E a) := fun a =>
    IsScalarTower.algebraMap_apply A E _ a
  have hALP : ∀ a : A, algebraMap A (Localization.AtPrime P) a =
      algebraMap E (Localization.AtPrime P) (algebraMap A E a) := fun a => by
    rfl
  have he : ∀ a : A, e (algebraMap A (Localization.AtPrime Q') a) =
      algebraMap A (Localization.AtPrime P) a := by
    intro a; rw [hAL, hALP, e.commutes]
  have hunder : Q'.comap (algebraMap A[X] E) = p.map C := by
    rw [← hP]
    show Ideal.comap _ (Ideal.comap _ P) = _
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  have hunderA : ∀ a : A, algebraMap A E a ∈ Q' ↔ a ∈ p := by
    intro a
    rw [IsScalarTower.algebraMap_apply A A[X] E, ← Ideal.mem_comap, hunder,
      Polynomial.algebraMap_eq, Ideal.mem_map_C_iff]
    refine ⟨fun h => by simpa using h 0, fun h n => ?_⟩
    rw [Polynomial.coeff_C]
    split_ifs
    · exact h
    · exact p.zero_mem
  have hcomp : (algebraMap A[X] (Localization.AtPrime Q')).comp C =
      algebraMap A (Localization.AtPrime Q') := by
    ext a
    simp only [RingHom.comp_apply]
    rw [hAL, IsScalarTower.algebraMap_apply A A[X] E, Polynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply A[X] E (Localization.AtPrime Q')]
  have hun : Algebra.IsUnramifiedAt A[X] Q' := inferInstance
  let p0 : Ideal A[X] := Q'.under A[X]
  let := Localization.AtPrime.algebraOfLiesOver p0 Q'
  have hm := ((Algebra.isUnramifiedAt_iff_map_eq A[X] p0 Q').mp hun).2
  have hp0 : p0 = p.map C := hunder
  have hunit : ∀ a : A, a ∉ p → IsUnit (algebraMap A (Localization.AtPrime Q') a) := by
    intro a ha
    by_contra h
    apply ha
    rw [← hunderA, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q') Q', ← hAL]
    exact h
  haveI hflatE : Module.Flat A E := Module.Flat.trans A A[X] E
  haveI hflatL : Module.Flat A (Localization.AtPrime Q') := Module.Flat.trans A E _
  have key : ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime p) π) →
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) ∧
        Irreducible (algebraMap A (Localization.AtPrime P) π) := by
    intro π hπ
    have hπp : π ∈ p := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p π]
      exact hπ.not_isUnit
    have hπ0 : π ≠ 0 := by rintro rfl; exact hπ.ne_zero (map_zero _)
    have hmAp := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπ
    have hmL : maximalIdeal (Localization.AtPrime Q') =
        Ideal.span {algebraMap A (Localization.AtPrime Q') π} := by
      rw [← hm, hp0, Ideal.map_map, hcomp]
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        have h1 : algebraMap A (Localization.AtPrime p) a ∈ maximalIdeal _ :=
          (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p a).mpr ha
        rw [hmAp, Ideal.mem_span_singleton'] at h1
        obtain ⟨c, hc⟩ := h1
        obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl c
        have h2 : algebraMap A (Localization.AtPrime p) (a * s) =
            algebraMap A (Localization.AtPrime p) (b * π) := by
          rw [map_mul, map_mul, ← hc, mul_right_comm, IsLocalization.mk'_spec]
        obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists p.primeCompl _).mp h2
        have hts : (t : A) * s ∉ p := p.primeCompl.mul_mem t.2 s.2
        rw [Ideal.mem_comap, Ideal.mem_span_singleton,
          ← (hunit _ hts).dvd_mul_right, ← map_mul]
        have h3 : a * ((t : A) * s) = π * ((t : A) * b) := by linear_combination ht
        rw [h3, map_mul]
        exact dvd_mul_right _ _
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact Ideal.mem_map_of_mem _ hπp
    have hreg : ∀ x : Localization.AtPrime Q', algebraMap A _ π * x = 0 → x = 0 := by
      intro x hx
      have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Localization.AtPrime Q')
        (mem_nonZeroDivisors_of_ne_zero hπ0)
      exact this (show π • x = π • (0 : Localization.AtPrime Q') by
        rw [smul_zero, Algebra.smul_def, hx])
    have hmem : ∀ y : Localization.AtPrime Q',
        e y ∈ maximalIdeal (Localization.AtPrime P) ↔ y ∈ maximalIdeal _ := by
      intro y
      simp only [mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    have hmLP : maximalIdeal (Localization.AtPrime P) =
        Ideal.span {algebraMap A (Localization.AtPrime P) π} := by
      ext x
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [hmem, hmL, Ideal.mem_span_singleton, Ideal.mem_span_singleton, ← he, map_dvd_iff]
    have hregP : ∀ x : Localization.AtPrime P, algebraMap A _ π * x = 0 → x = 0 := by
      intro x hx
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [← he, ← map_mul, map_eq_zero_iff _ e.injective] at hx
      rw [hreg y hx, map_zero]
    exact GlobalTheory.Pat.dvr_of_maximalIdeal_eq_span hmLP hregP
  refine ⟨?_, fun π hπ => (key π hπ).2.2⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl ϖ
  have ha : Irreducible (algebraMap A (Localization.AtPrime p) a) := by
    have h := IsLocalization.mk'_spec (Localization.AtPrime p) a s
    rw [← h]
    exact (irreducible_mul_isUnit (IsLocalization.map_units _ s)).mpr hϖ
  obtain ⟨hd, hdvr, -⟩ := key a ha
  exact ⟨hd, hdvr⟩

end GlobalTheory.EtalePolyDvr
