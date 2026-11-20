import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

namespace GlobalTheory

/- English proof (translation)
Set `` to `Ideal.Quotient.field m`. Use `ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int` as an intermediate fact. Establish `: Module.Finite ℤ (R ⧸ m)` using `finite_of_finite_type_of_isJacobsonRing ℤ _`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Establish `hinj : Function.Injective (algebraMap ℤ (R ⧸ m))`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `ha0`. Apply `h a ha0` to reduce the goal to its premises.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Simplify using `using ha`. Establish `hF : IsField ℤ` using `(Algebra.IsIntegral.isField_iff_isField hinj).mpr (Field.toIsField (R ⧸ m))`. Conclude with `Int.not_isField hF`.
-/
theorem exists_intCast_mem_of_isMaximal (R : Type*) [CommRing R] [Algebra.FiniteType ℤ R]
    (m : Ideal R) [m.IsMaximal] : ∃ p : ℤ, p ≠ 0 ∧ algebraMap ℤ R p ∈ m := by
  let := Ideal.Quotient.field m
  have := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have : Module.Finite ℤ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ _
  by_contra h
  push Not at h
  have hinj : Function.Injective (algebraMap ℤ (R ⧸ m)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    apply h a ha0
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using ha
  have hF : IsField ℤ :=
    (Algebra.IsIntegral.isField_iff_isField hinj).mpr (Field.toIsField (R ⧸ m))
  exact Int.not_isField hF

/- English proof (translation)
Introduce `R _ _ _ _ m hm g hg`. Establish `: IsNoetherianRing R` using `Algebra.FiniteType.isNoetherianRing ℤ R`. Take `⟨p₀, hp₀, hp₀m⟩` from `exists_intCast_mem_of_isMaximal R m`. Take `⟨p, hp⟩` from `(IsPrincipalIdealRing.principal (m.comap (algebraMap ℤ R))).principal`. Establish `hp' : m.comap (algebraMap ℤ R) = Ideal.span {p}` using `hp`.

Establish `hp0 : p ≠ 0`. Introduce and unpack `rfl`. Establish `: p₀ ∈ m.comap (algebraMap ℤ R)` using `hp₀m`. Rewrite `this` using `[hp']`. Conclude with `hp₀ (by simpa using this)`.

Establish `hpprime : Prime p`. Rewrite using `[← Ideal.span_singleton_prime hp0, ← hp']`. Use `infer_instance`. Establish `hpm : algebraMap ℤ R p ∈ m`. Establish `: p ∈ m.comap (algebraMap ℤ R)` using `hp' ▸ Ideal.mem_span_singleton_self p`.

Conclude with `this`. Use `set x : R := algebraMap ℤ R p * g with hx`. Establish `hx0 : x ≠ 0` using `mul_ne_zero (by simpa using hp0) hg`. Take `⟨q, ⟨hqp, hqm, hxq⟩, hmax⟩` from `set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) {q : Ideal R | q.IsPrime ∧ q ≤ m ∧ x ∉ q} ⟨⊥, Ideal.isPrime_bot, bot_le, by simpa using hx0⟩`. Express the relevant statement in the definitionally equal form `Ideal R at q`.

Establish `hpq : algebraMap ℤ R p ∉ q` using `fun h => hxq (q.mul_mem_right _ h)`. Establish `hinj : Function.Injective (algebraMap ℤ (R ⧸ q))`. Establish `hq' : (q.comap (algebraMap ℤ R)).IsPrime` using `inferInstance`. Establish `hbot : q.comap (algebraMap ℤ R) = ⊥`. Assume the negation of the conclusion as `hne`.

Establish `hM : (q.comap (algebraMap ℤ R)).IsMaximal` using `IsPrime.to_maximal_ideal hne`. Use `hM.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (Ideal.comap_mono (f := algebraMap ℤ R) hqm)` as an intermediate fact. Apply `hpq` to reduce the goal to its premises. Establish `h2 : p ∈ q.comap (algebraMap ℤ R)` using `this ▸ hpm`. Conclude with `h2`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Establish `: a ∈ q.comap (algebraMap ℤ R)`. Rewrite using `[Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]`. Simplify using `using ha`.

Rewrite `this` using `[hbot, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `hsurj` using `Ideal.Quotient.mk_surjective (I := q)`. Use `⟨q, hqp, hqm, fun h => hxq (q.mul_mem_left _ h), charZero_of_injective_algebraMap hinj, ?_⟩` and prove the remaining obligations. Establish `hm' : (m.map (Ideal.Quotient.mk q)).IsMaximal` using `Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)`. Establish `hcm : (m.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = m`.

Rewrite using `[Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]`. Conclude with `sup_eq_left.mpr hqm`. Establish `h1 : (m.map (Ideal.Quotient.mk q)).height ≤ 1`. Use `height_le_one_of_forall_mem _ (f := Ideal.Quotient.mk q x) (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hxq) ?_` and prove the remaining obligations. Introduce `P hP hP0 hPm`.

Assume the negation of the conclusion as `hxP`. Use `hmax (P.comap (Ideal.Quotient.mk q)) ⟨inferInstance, ?_, hxP⟩ ?_` and prove the remaining obligations. Conclude with `hcm ▸ Ideal.comap_mono hPm`. Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations. Introduce `a ha`.

Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]`. Conclude with `P.zero_mem`. Introduce `e`. Apply `hP0` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`.

Introduce `b hb`. Take `⟨a, rfl⟩` from `hsurj b`. Establish `: a ∈ q` using `e ▸ hb`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr this`. Establish `: Algebra.QuasiFiniteAt ℤ (m.map (Ideal.Quotient.mk q))` using `quasiFiniteAt_of_height_le_one _ h1 p (fun e => hp0 (hinj (by simpa using e))) (Ideal.mem_map_of_mem _ hpm)`.

Establish `: FaithfulSMul ℤ (R ⧸ q)` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr hinj`. Conclude with `isAlgebraic_of_quasiFiniteAt ℤ (R ⧸ q) (m.map (Ideal.Quotient.mk q))`.
-/
theorem exists_horizontal_prime_le_of_isMaximal :
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] [CharZero R] (𝔪 : Ideal R),
      𝔪.IsMaximal → ∀ g : R, g ≠ 0 → ∃ q : Ideal R, q.IsPrime ∧ q ≤ 𝔪 ∧ g ∉ q ∧
        CharZero (R ⧸ q) ∧ Algebra.IsAlgebraic ℤ (R ⧸ q) := by
  intro R _ _ _ _ m hm g hg
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨p₀, hp₀, hp₀m⟩ := exists_intCast_mem_of_isMaximal R m
  obtain ⟨p, hp⟩ := (IsPrincipalIdealRing.principal (m.comap (algebraMap ℤ R))).principal
  have hp' : m.comap (algebraMap ℤ R) = Ideal.span {p} := hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    have : p₀ ∈ m.comap (algebraMap ℤ R) := hp₀m
    rw [hp'] at this
    exact hp₀ (by simpa using this)
  have hpprime : Prime p := by
    rw [← Ideal.span_singleton_prime hp0, ← hp']
    infer_instance
  have hpm : algebraMap ℤ R p ∈ m := by
    have : p ∈ m.comap (algebraMap ℤ R) := hp' ▸ Ideal.mem_span_singleton_self p
    exact this
  set x : R := algebraMap ℤ R p * g with hx
  have hx0 : x ≠ 0 := mul_ne_zero (by simpa using hp0) hg
  obtain ⟨q, ⟨hqp, hqm, hxq⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {q : Ideal R | q.IsPrime ∧ q ≤ m ∧ x ∉ q}
    ⟨⊥, Ideal.isPrime_bot, bot_le, by simpa using hx0⟩
  change Ideal R at q
  have hpq : algebraMap ℤ R p ∉ q := fun h => hxq (q.mul_mem_right _ h)
  have hinj : Function.Injective (algebraMap ℤ (R ⧸ q)) := by
    have hq' : (q.comap (algebraMap ℤ R)).IsPrime := inferInstance
    have hbot : q.comap (algebraMap ℤ R) = ⊥ := by
      by_contra hne
      have hM : (q.comap (algebraMap ℤ R)).IsMaximal := IsPrime.to_maximal_ideal hne
      have := hM.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (Ideal.comap_mono (f := algebraMap ℤ R) hqm)
      apply hpq
      have h2 : p ∈ q.comap (algebraMap ℤ R) := this ▸ hpm
      exact h2
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ q.comap (algebraMap ℤ R) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      simpa using ha
    rwa [hbot, Ideal.mem_bot] at this
  have hsurj := Ideal.Quotient.mk_surjective (I := q)
  refine ⟨q, hqp, hqm, fun h => hxq (q.mul_mem_left _ h), charZero_of_injective_algebraMap hinj, ?_⟩
  have hm' : (m.map (Ideal.Quotient.mk q)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)
  have hcm : (m.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have h1 : (m.map (Ideal.Quotient.mk q)).height ≤ 1 := by
    refine height_le_one_of_forall_mem _ (f := Ideal.Quotient.mk q x)
      (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hxq) ?_
    intro P hP hP0 hPm
    by_contra hxP
    refine hmax (P.comap (Ideal.Quotient.mk q)) ⟨inferInstance, ?_, hxP⟩ ?_
    · exact hcm ▸ Ideal.comap_mono hPm
    · refine lt_of_le_of_ne ?_ ?_
      · intro a ha
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
        exact P.zero_mem
      · intro e
        apply hP0
        rw [eq_bot_iff]
        intro b hb
        obtain ⟨a, rfl⟩ := hsurj b
        have : a ∈ q := e ▸ hb
        exact Ideal.Quotient.eq_zero_iff_mem.mpr this
  have : Algebra.QuasiFiniteAt ℤ (m.map (Ideal.Quotient.mk q)) :=
    quasiFiniteAt_of_height_le_one _ h1 p (fun e => hp0 (hinj (by simpa using e)))
      (Ideal.mem_map_of_mem _ hpm)
  have : FaithfulSMul ℤ (R ⧸ q) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact isAlgebraic_of_quasiFiniteAt ℤ (R ⧸ q) (m.map (Ideal.Quotient.mk q))

end GlobalTheory
