import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

open NumberField IsDedekindDomain Formalism.L2.Pj IsLocalRing

namespace GlobalTheory.GaussPoint

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩ n`. Rewrite using `[PowerSeries.coeff_C_mul]`. Conclude with `dvd_mul_right _ _`. Introduce `h choose c hc using h`.

Use `⟨PowerSeries.mk c, ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]`.
-/
theorem C_dvd_iff {V : Type*} [CommRing V] (a : V) (f : PowerSeries V) :
    PowerSeries.C a ∣ f ↔ ∀ n, a ∣ PowerSeries.coeff n f := by
  constructor
  · rintro ⟨g, rfl⟩ n
    rw [PowerSeries.coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose c hc using h
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

/- English proof (translation)
Establish `h1 : (Ideal.span {a}).IsPrime` using `(Ideal.span_singleton_prime ha.ne_zero).2 ha`. Establish `h2 : Ideal.span {(PowerSeries.C a : PowerSeries V)} = RingHom.ker (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {a})))`. Use extensionality with `f`. Rewrite using `[Ideal.mem_span_singleton, C_dvd_iff, RingHom.mem_ker, PowerSeries.ext_iff]`. Use `forall_congr' fun n => ?_` and prove the remaining obligations.

Rewrite using `[PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Rewrite using `[h2]`. Conclude with `RingHom.ker_isPrime _`.
-/
theorem isPrime_span_C {V : Type*} [CommRing V] {a : V} (ha : Prime a) :
    (Ideal.span {(PowerSeries.C a : PowerSeries V)}).IsPrime := by
  have h1 : (Ideal.span {a}).IsPrime := (Ideal.span_singleton_prime ha.ne_zero).2 ha
  have h2 : Ideal.span {(PowerSeries.C a : PowerSeries V)} =
      RingHom.ker (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {a}))) := by
    ext f
    rw [Ideal.mem_span_singleton, C_dvd_iff, RingHom.mem_ker, PowerSeries.ext_iff]
    refine forall_congr' fun n => ?_
    rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [h2]
  exact RingHom.ker_isPrime _

section Val

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]

/- English proof (translation)
Rewrite using `[valV, HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero hπ.maximalIdeal_eq`.
-/
theorem valV_irreducible {π : V} (hπ : Irreducible π) :
    valV V (algebraMap V K π) = WithZero.exp (-1 : ℤ) := by
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero hπ.maximalIdeal_eq

/- English proof (translation)
Rewrite using `[valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]`. Conclude with `fun h => h hu`.
-/
theorem valV_unit {u : V} (hu : IsUnit u) : valV V (algebraMap V K u) = 1 := by
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact fun h => h hu

/- English proof (translation)
Establish `key : ∀ a : V, valV V' (i (algebraMap V K a)) = valV V (algebraMap V K a)`. Introduce `a`. Distinguish the cases in `ha : a = 0`. Simplify using `[ha]`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ`.

Rewrite using `[hi]`. Simplify using `only [map_mul, map_pow]`. Rewrite using `[valV_unit u.isUnit, valV_unit (u.isUnit.map f), valV_irreducible hπ, valV_irreducible hπ']`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := V) x`. Simplify using `only [vV, map_div₀, key]`.
-/
theorem vV_map_eq {V' K' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [Field K'] [Algebra V' K'] [IsFractionRing V' K'] (f : V →+* V') (i : K →+* K')
    (hi : ∀ a, i (algebraMap V K a) = algebraMap V' K' (f a)) {π : V} (hπ : Irreducible π)
    (hπ' : Irreducible (f π)) (x : K) : vV V' (i x) = vV V x := by
  have key : ∀ a : V, valV V' (i (algebraMap V K a)) = valV V (algebraMap V K a) := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    rw [hi]
    simp only [map_mul, map_pow]
    rw [valV_unit u.isUnit, valV_unit (u.isUnit.map f), valV_irreducible hπ, valV_irreducible hπ']
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  simp only [vV, map_div₀, key]

end Val

/- English proof (translation)
Set `R` to `PowerSeries T.V`. Set `P : Ideal R` to `Ideal.span {(PowerSeries.C ϖ : PowerSeries T.V)}`. Use `haveI hP : P.IsPrime := isPrime_span_C hϖ.prime`. Set `L` to `Localization.AtPrime P`. Establish `hinj : Function.Injective (algebraMap R L)` using `IsLocalization.injective L P.primeCompl_le_nonZeroDivisors`.

Establish `hm : maximalIdeal L = Ideal.span {algebraMap R L (PowerSeries.C ϖ)}`. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]`. Establish `hC0 : (PowerSeries.C ϖ : R) ≠ 0` using `fun h => hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))`. Establish `hn : ¬ IsNilpotent (algebraMap R L (PowerSeries.C ϖ))`. Rewrite using `[IsNilpotent.map_iff hinj]`.

Conclude with `fun h => hC0 h.eq_zero`. Take `⟨_, hdvr, hirr⟩` from `isDiscreteValuationRing_of_maximalIdeal_eq_span hm hn`. Set `S` to `AdicCompletion (maximalIdeal L) L`. Set `ev : R →+* S` to `(algebraMap L S).comp (algebraMap R L)`. Establish `hev : Function.Injective ev` using `(algebraMap_adicCompletion_injective_of_dvr L).comp hinj`.

Establish `hirr' : Irreducible (ev (PowerSeries.C ϖ))` using `irreducible_algebraMap_adicCompletion_of_dvr hirr`. Establish `hunit : ∀ s : R, ¬ PowerSeries.C ϖ ∣ s → IsUnit (ev s)` using `fun s hs => (IsLocalization.map_units L (⟨s, fun h => hs (Ideal.mem_span_singleton.1 h)⟩ : P.primeCompl)).map (algebraMap L S)`. Use `haveI : CharZero S := charZero_of_injective_ringHom (f := ev.comp PowerSeries.C) (hev.comp PowerSeries.C_injective)`. Set `T' : CDVR` to `{ V := S }`. Set `g : T.V →+* T'.Fr` to `(algebraMap T'.V T'.Fr).comp (ev.comp PowerSeries.C)`.

Establish `hg : Function.Injective g` using `(IsFractionRing.injective T'.V T'.Fr).comp (hev.comp PowerSeries.C_injective)`. Establish `hi : ∀ a, IsFractionRing.lift (K` using `T.Fr) hg (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (ev (PowerSeries.C a)) := fun a => IsFractionRing.lift_algebraMap hg a`. Use `⟨T', ev, IsFractionRing.lift hg, hev, hunit _ ?_, fun s hs => ?_, hi, vV_map_eq (ev.comp PowerSeries.C) _ hi hϖ hirr'⟩` and prove the remaining obligations. Rewrite using `[C_dvd_iff]`. Introduce `h`.

Establish `h1` using `h 1`. Rewrite `h1` using `[PowerSeries.coeff_one_X]`. Conclude with `hϖ.not_isUnit (isUnit_of_dvd_one h1)`. Assume the negation of the conclusion as `h`. Conclude with `hirr'.not_isUnit (isUnit_of_dvd_unit hs (hunit s h))`.
-/
theorem exists_gaussPoint (T : CDVR) (ϖ : T.V) (hϖ : Irreducible ϖ) :
    ∃ (T' : CDVR) (ev : PowerSeries T.V →+* T'.V) (i : T.Fr →+* T'.Fr), Function.Injective ev ∧
      IsUnit (ev PowerSeries.X) ∧ (∀ s, ev (PowerSeries.C ϖ) ∣ ev s → PowerSeries.C ϖ ∣ s) ∧
      (∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (ev (PowerSeries.C a))) ∧
      ∀ x, vV T'.V (i x) = vV T.V x := by
  let R := PowerSeries T.V
  let P : Ideal R := Ideal.span {(PowerSeries.C ϖ : PowerSeries T.V)}
  haveI hP : P.IsPrime := isPrime_span_C hϖ.prime
  let L := Localization.AtPrime P
  have hinj : Function.Injective (algebraMap R L) :=
    IsLocalization.injective L P.primeCompl_le_nonZeroDivisors
  have hm : maximalIdeal L = Ideal.span {algebraMap R L (PowerSeries.C ϖ)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hC0 : (PowerSeries.C ϖ : R) ≠ 0 := fun h =>
    hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))
  have hn : ¬ IsNilpotent (algebraMap R L (PowerSeries.C ϖ)) := by
    rw [IsNilpotent.map_iff hinj]
    exact fun h => hC0 h.eq_zero
  obtain ⟨_, hdvr, hirr⟩ := isDiscreteValuationRing_of_maximalIdeal_eq_span hm hn
  let S := AdicCompletion (maximalIdeal L) L
  let ev : R →+* S := (algebraMap L S).comp (algebraMap R L)
  have hev : Function.Injective ev :=
    (algebraMap_adicCompletion_injective_of_dvr L).comp hinj
  have hirr' : Irreducible (ev (PowerSeries.C ϖ)) :=
    irreducible_algebraMap_adicCompletion_of_dvr hirr
  have hunit : ∀ s : R, ¬ PowerSeries.C ϖ ∣ s → IsUnit (ev s) := fun s hs =>
    (IsLocalization.map_units L (⟨s, fun h => hs (Ideal.mem_span_singleton.1 h)⟩ :
      P.primeCompl)).map (algebraMap L S)
  haveI : CharZero S := charZero_of_injective_ringHom
    (f := ev.comp PowerSeries.C) (hev.comp PowerSeries.C_injective)
  let T' : CDVR := { V := S }
  let g : T.V →+* T'.Fr := (algebraMap T'.V T'.Fr).comp (ev.comp PowerSeries.C)
  have hg : Function.Injective g :=
    (IsFractionRing.injective T'.V T'.Fr).comp (hev.comp PowerSeries.C_injective)
  have hi : ∀ a, IsFractionRing.lift (K := T.Fr) hg (algebraMap T.V T.Fr a) =
      algebraMap T'.V T'.Fr (ev (PowerSeries.C a)) := fun a => IsFractionRing.lift_algebraMap hg a
  refine ⟨T', ev, IsFractionRing.lift hg, hev, hunit _ ?_, fun s hs => ?_, hi,
    vV_map_eq (ev.comp PowerSeries.C) _ hi hϖ hirr'⟩
  · rw [C_dvd_iff]
    intro h
    have h1 := h 1
    rw [PowerSeries.coeff_one_X] at h1
    exact hϖ.not_isUnit (isUnit_of_dvd_one h1)
  · by_contra h
    exact hirr'.not_isUnit (isUnit_of_dvd_unit hs (hunit s h))

end GlobalTheory.GaussPoint
