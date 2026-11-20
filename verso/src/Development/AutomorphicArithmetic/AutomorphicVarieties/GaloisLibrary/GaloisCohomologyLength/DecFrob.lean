import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

namespace UpperTheory.V.LDataCardLeFinrank.DecompositionFrobenius

variable (l : ℕ) [hl : Fact l.Prime]

/- English proof (translation)
Rewrite using `[← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]`. Conclude with `Nat.prime_iff_prime_int.mp hl.out`.
-/
private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
  exact Nat.prime_iff_prime_int.mp hl.out

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

/- English proof (translation)
Use `show Nat.card (𝓞 ℚ ⧸ Ideal.span {((l : ℕ) : 𝓞 ℚ)}) = l`. Establish `hJ : Ideal.span {((l : ℕ) : ℤ)} = Ideal.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {((l : ℕ) : 𝓞 ℚ)})`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Rewrite using `[Nat.card_congr ((Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv hJ).trans (Int.quotientSpanNatEquivZMod l)).toEquiv, Nat.card_zmod]`.
-/
private theorem normV_vQ : normV (vQ l) = l := by
  show Nat.card (𝓞 ℚ ⧸ Ideal.span {((l : ℕ) : 𝓞 ℚ)}) = l
  have hJ : Ideal.span {((l : ℕ) : ℤ)} = Ideal.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {((l : ℕ) : 𝓞 ℚ)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [Nat.card_congr ((Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv hJ).trans (Int.quotientSpanNatEquivZMod l)).toEquiv, Nat.card_zmod]

variable {l} {Ω : Type} [Field Ω]

/- English proof (translation)
Use `show _ ∈ Ideal.span _ ↔ _`. Rewrite using `[Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv]`. Simplify using the standard rewrite rules.
-/
private theorem intCast_mem_vQ (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
  show _ ∈ Ideal.span _ ↔ _
  rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv]
  simp

/- English proof (translation)
Rewrite using `[ValuationSubring.valuation_le_one_iff]`. Conclude with `intCast_mem A n`.
-/
private theorem val_intCast_le_one (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff]
  exact intCast_mem A n

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hn`. Establish `hirr : Irreducible ((l : ℕ) : ℤ)` using `(Nat.prime_iff_prime_int.mp hl.out).irreducible`. Take `⟨a, b, hab⟩` from `hirr.coprime_iff_not_dvd.mpr hn`.

Establish `h1 : A.valuation (((a * ((l : ℕ) : ℤ) + b * n : ℤ)) : Ω) < 1`. Use `push_cast`. Apply `Valuation.map_add_lt` to reduce the goal to its premises. Rewrite using `[Valuation.map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) (by exact_mod_cast hA)`.

Rewrite using `[Valuation.map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h`. Rewrite `h1` using `[hab]`. Simplify using `at h1`. Introduce and unpack `⟨k, rfl⟩`.

Use `push_cast`. Rewrite using `[Valuation.map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) (by exact_mod_cast hA)`.
-/
private theorem val_intCast_lt_one_iff (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  constructor
  · intro h
    by_contra hn
    have hirr : Irreducible ((l : ℕ) : ℤ) := (Nat.prime_iff_prime_int.mp hl.out).irreducible
    obtain ⟨a, b, hab⟩ := hirr.coprime_iff_not_dvd.mpr hn
    have h1 : A.valuation (((a * ((l : ℕ) : ℤ) + b * n : ℤ)) : Ω) < 1 := by
      push_cast
      apply Valuation.map_add_lt
      · rw [Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) (by exact_mod_cast hA)
      · rw [Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h
    rw [hab] at h1
    simp at h1
  · rintro ⟨k, rfl⟩
    push_cast
    rw [Valuation.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) (by exact_mod_cast hA)

/- English proof (translation)
Introduce `x`. Take `⟨n, rfl⟩ : ∃ n : ℤ, x = (n : 𝓞 ℚ)` from `⟨Rat.ringOfIntegersEquiv x, Rat.ringOfIntegersEquiv.injective (by simp)⟩`. Rewrite using `[intCast_mem_vQ, ← val_intCast_lt_one_iff A hA n]`. Simplify using the standard rewrite rules.
-/
private theorem isPlaceOver_vQ [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = (n : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, Rat.ringOfIntegersEquiv.injective (by simp)⟩
  rw [intCast_mem_vQ, ← val_intCast_lt_one_iff A hA n]
  simp

end UpperTheory.V.LDataCardLeFinrank.DecompositionFrobenius

open UpperTheory.V.LDataCardLeFinrank.DecompositionFrobenius in
/- English proof (translation)
Introduce `Ω _ _ _ l _ A hA`. Establish `hP : IsPlaceOver (F` using `ℚ) A (vQ l) := isPlaceOver_vQ A (by exact_mod_cast hA)`. Take `⟨σ, hσD, hσ⟩` from `exists_isFrob hP`. Rewrite `hσ` using `[normV_vQ]`. Use `⟨σ, hσD, fun m hm ζ hζ => ?_⟩` and prove the remaining obligations.

Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `(Fact.out : l.Prime).one_lt.ne' (by simpa using hm)`. Establish `hζv : A.valuation ζ ≤ 1`. Assume the negation of the conclusion as `h`.

Establish `h2` using `one_lt_pow' (not_le.mp h) hm0`. Rewrite `h2` using `[← map_pow, hζ, map_one]`. Conclude with `lt_irrefl _ h2`. Establish `key` using `(ineFixRoots ℚ Ω l A hA m hm (ζ ^ l) (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow])).1`. Apply `key (σ ζ)` to reduce the goal to its premises.

Rewrite using `[← map_pow, hζ, map_one]`. Conclude with `hσ ζ hζv`.
-/
theorem UpperTheory.V.LDataCardLeFinrank.decFrob :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∃ g ∈ Dec (F := ℚ) A, ∀ m : ℕ, m.Coprime l → ∀ ζ : Ω, ζ ^ m = 1 → g ζ = ζ ^ l := by
  intro Ω _ _ _ l _ A hA
  have hP : IsPlaceOver (F := ℚ) A (vQ l) := isPlaceOver_vQ A (by exact_mod_cast hA)
  obtain ⟨σ, hσD, hσ⟩ := exists_isFrob hP
  rw [normV_vQ] at hσ
  refine ⟨σ, hσD, fun m hm ζ hζ => ?_⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Fact.out : l.Prime).one_lt.ne' (by simpa using hm)
  have hζv : A.valuation ζ ≤ 1 := by
    by_contra h
    have h2 := one_lt_pow' (not_le.mp h) hm0
    rw [← map_pow, hζ, map_one] at h2
    exact lt_irrefl _ h2
  have key := (ineFixRoots ℚ Ω l A hA m hm (ζ ^ l) (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow])).1
  apply key (σ ζ)
  · rw [← map_pow, hζ, map_one]
  · exact hσ ζ hζv
