import Mathlib

namespace GlobalTheory.DenominatorExists

open NumberField

/- English proof (translation)
Distinguish the cases in `h0 : P = ⊥`. Use `⟨b, a, ?_, Or.inr (mul_comm _ _)⟩` and prove the remaining obligations. Rewrite using `[h0]`. Simplify using `using hb`. Use `haveI : IsDiscreteValuationRing (Localization.AtPrime P) := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h0 _`.

Establish `hinj : Function.Injective (algebraMap R (Localization.AtPrime P))` using `IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors`. Take `⟨c, hc⟩` from `ValuationRing.cond (algebraMap R (Localization.AtPrime P) a) (algebraMap R (Localization.AtPrime P) b)`. Take `⟨⟨t, s⟩, hts⟩` from `IsLocalization.surj P.primeCompl c`. Simplify using `only at hts`. Use `⟨s, t, s.2, ?_⟩` and prove the remaining obligations.

Break down `hc with hc | hc` into its components or cases. Use `left`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, ← hts, ← mul_assoc, hc]`. Use `right`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, ← hts, ← mul_assoc, hc]`.
-/
theorem exists_mul_eq {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R) [hP : P.IsPrime]
    (a b : R) (hb : b ≠ 0) :
    ∃ s t : R, s ∉ P ∧ (a * t = b * s ∨ b * t = a * s) := by
  by_cases h0 : P = ⊥
  · refine ⟨b, a, ?_, Or.inr (mul_comm _ _)⟩
    rw [h0]; simpa using hb
  · haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h0 _
    have hinj : Function.Injective (algebraMap R (Localization.AtPrime P)) :=
      IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R (Localization.AtPrime P) a)
      (algebraMap R (Localization.AtPrime P) b)
    obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.surj P.primeCompl c
    simp only at hts
    refine ⟨s, t, s.2, ?_⟩
    rcases hc with hc | hc
    · left
      apply hinj
      rw [map_mul, map_mul, ← hts, ← mul_assoc, hc]
    · right
      apply hinj
      rw [map_mul, map_mul, ← hts, ← mul_assoc, hc]

/- English proof (translation)
Establish `hz : IsIntegral ℤ (algebraMap L Ω (s : L))` using `s.2.map (algebraMap L Ω).toIntAlgHom`. Establish `hA : IsIntegral A (algebraMap L Ω (s : L))` using `hz.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hA`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem mem_of_integer {L Ω : Type} [Field L] [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω) (s : 𝓞 L) : algebraMap L Ω (s : L) ∈ A := by
  have hz : IsIntegral ℤ (algebraMap L Ω (s : L)) := s.2.map (algebraMap L Ω).toIntAlgHom
  have hA : IsIntegral A (algebraMap L Ω (s : L)) := hz.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hA
  rw [← hy]
  exact y.2

/- English proof (translation)
Set `f : 𝓞 L →+* A` to `((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A (fun s => mem_of_integer A s)`. Set `P : Ideal (𝓞 L)` to `(IsLocalRing.maximalIdeal A).comap f`. Use `haveI : P.IsPrime := Ideal.comap_isPrime f _`. Establish `hle : ∀ s : 𝓞 L, A.valuation (algebraMap L Ω (s : L)) ≤ 1` using `fun s => (A.valuation_le_one_iff _).mpr (mem_of_integer A s)`. Establish `hP : ∀ s : 𝓞 L, s ∉ P → A.valuation (algebraMap L Ω (s : L)) = 1`.

Introduce `s hs`. Use `le_antisymm (hle s) (not_lt.mp fun h => hs ?_)` and prove the remaining obligations. Conclude with `Ideal.mem_comap.mpr ((A.valuation_lt_one_iff (f s)).mpr h)`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 L) x`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`.

Establish `hb1 : (b : L) ≠ 0` using `by exact_mod_cast hb0`. Express the relevant statement in the definitionally equal form `A.valuation (algebraMap L Ω ((a : L) / (b : L))) ≤ 1 at hx`. Express the relevant statement in the definitionally equal form `∃ s t : 𝓞 L, A.valuation (algebraMap L Ω (s : L)) = 1 ∧ (s : L) * ((a : L) / (b : L)) = (t : L)`. Take `⟨s, t, hs, h | h⟩` from `exists_mul_eq P a b hb0`. Establish `h' : (a : L) * t = b * s` using `by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h`.

Establish `e : (t : L) * ((a : L) / (b : L)) = s`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h'`. Use `⟨t, s, le_antisymm (hle t) ?_, e⟩` and prove the remaining obligations. Establish `h1` using `hP s hs`.

Rewrite `h1` using `[← e, map_mul, map_mul]`. Rewrite using `[← h1]`. Conclude with `mul_le_of_le_one_right' hx`. Establish `h' : (b : L) * t = a * s` using `by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h`. Use `⟨s, t, hP s hs, ?_⟩` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-h'`.
-/
theorem exists_denominator {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω) (x : L) (hx : A.valuation (algebraMap L Ω x) ≤ 1) :
    ∃ s t : 𝓞 L, A.valuation (algebraMap L Ω (s : L)) = 1 ∧ (s : L) * x = (t : L) := by
  let f : 𝓞 L →+* A :=
    ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A (fun s => mem_of_integer A s)
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  haveI : P.IsPrime := Ideal.comap_isPrime f _
  have hle : ∀ s : 𝓞 L, A.valuation (algebraMap L Ω (s : L)) ≤ 1 :=
    fun s => (A.valuation_le_one_iff _).mpr (mem_of_integer A s)
  have hP : ∀ s : 𝓞 L, s ∉ P → A.valuation (algebraMap L Ω (s : L)) = 1 := by
    intro s hs
    refine le_antisymm (hle s) (not_lt.mp fun h => hs ?_)
    exact Ideal.mem_comap.mpr ((A.valuation_lt_one_iff (f s)).mpr h)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : (b : L) ≠ 0 := by exact_mod_cast hb0
  change A.valuation (algebraMap L Ω ((a : L) / (b : L))) ≤ 1 at hx
  change ∃ s t : 𝓞 L, A.valuation (algebraMap L Ω (s : L)) = 1 ∧
    (s : L) * ((a : L) / (b : L)) = (t : L)
  obtain ⟨s, t, hs, h | h⟩ := exists_mul_eq P a b hb0
  · have h' : (a : L) * t = b * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h
    have e : (t : L) * ((a : L) / (b : L)) = s := by
      field_simp
      linear_combination h'
    refine ⟨t, s, le_antisymm (hle t) ?_, e⟩
    have h1 := hP s hs
    rw [← e, map_mul, map_mul] at h1
    rw [← h1]
    exact mul_le_of_le_one_right' hx
  · have h' : (b : L) * t = a * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h
    refine ⟨s, t, hP s hs, ?_⟩
    field_simp
    linear_combination -h'

end GlobalTheory.DenominatorExists
