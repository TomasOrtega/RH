import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.MaxIdealPow

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Take `⟨r, hr⟩` from `X_dvd_sub_C (p := g)`. Establish `hg : g = C (g.coeff 0) + X * r` using `by rw [← hr]; ring`. Use `⟨((aeval (⟨y, hy⟩ : A) r : A) : Ω), SetLike.coe_mem _, ?_⟩` and prove the remaining obligations. Establish `h1 : aeval y r = ((aeval (⟨y, hy⟩ : A) r : A) : Ω)` using `aeval_algebraMap_apply Ω (⟨y, hy⟩ : A) r`. Use `conv_lhs => rw [hg]`.

Rewrite using `[map_add, map_mul, aeval_C, aeval_X, h1]`. Simplify using the standard rewrite rules.
-/
theorem aeval_eq_coeff_zero_add (A : ValuationSubring Ω) (g : ℤ[X]) {y : Ω} (hy : y ∈ A) :
    ∃ w ∈ A, aeval y g = ((g.coeff 0 : ℤ) : Ω) + y * w := by
  obtain ⟨r, hr⟩ := X_dvd_sub_C (p := g)
  have hg : g = C (g.coeff 0) + X * r := by rw [← hr]; ring
  refine ⟨((aeval (⟨y, hy⟩ : A) r : A) : Ω), SetLike.coe_mem _, ?_⟩
  have h1 : aeval y r = ((aeval (⟨y, hy⟩ : A) r : A) : Ω) :=
    aeval_algebraMap_apply Ω (⟨y, hy⟩ : A) r
  conv_lhs => rw [hg]
  rw [map_add, map_mul, aeval_C, aeval_X, h1]
  simp

/- English proof (translation)
Set `I : Ideal ℤ` to `P.asIdeal.comap (Int.castRingHom (𝓞 E))`. Take `⟨a, ha⟩` from `Submodule.IsPrincipal.principal I`. Establish `hmem : ∀ n : ℤ, A.valuation (n : Ω) < 1 ↔ a ∣ n`. Introduce `n`. Establish `h1` using `hP (n : 𝓞 E)`.

Establish `h2 : (algebraMap E Ω) (((n : 𝓞 E)) : E) = (n : Ω)` using `by simp`. Rewrite `h1` using `[h2]`. Rewrite using `[h1]`. Establish `h3 : (n : 𝓞 E) ∈ P.asIdeal ↔ n ∈ I` using `by simp [I]`. Rewrite using `[h3, ha, Submodule.mem_span_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`. Conclude with `Dvd.intro_left k rfl`. Introduce and unpack `⟨k, rfl⟩; exact ⟨k, by rw [smul_eq_mul, mul_comm]⟩`. Use `⟨a.natAbs, ?_, ?_, fun n => by rw [hmem n, Int.natAbs_dvd]⟩` and prove the remaining obligations.

Introduce `h0`. Establish `ha0 : a = 0` using `Int.natAbs_eq_zero.mp h0`. Establish `hN` using `Ideal.absNorm_mem P.asIdeal`. Establish `hNv : A.valuation (((Ideal.absNorm P.asIdeal : ℕ) : ℤ) : Ω) < 1`. Establish `h1` using `(hP ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)).mpr hN`.

Simplify using `using h1`. Rewrite `hNv` using `[hmem, ha0, zero_dvd_iff]`. Establish `: Ideal.absNorm P.asIdeal = 0` using `by exact_mod_cast hNv`. Conclude with `P.ne_bot (Ideal.absNorm_eq_zero_iff.mp this)`. Introduce `h1`.

Establish `: A.valuation ((1 : ℤ) : Ω) < 1`. Rewrite using `[hmem, ← Int.natAbs_dvd, h1]`. Simplify using the standard rewrite rules. Simplify using `at this`.
-/
theorem exists_nat_of_isPlaceOver (E : Type) [Field E] [NumberField E] [Algebra E Ω]
    (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (hP : IsPlaceOver (F := E) A P) :
    ∃ p : ℕ, p ≠ 0 ∧ p ≠ 1 ∧ ∀ n : ℤ, A.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  let I : Ideal ℤ := P.asIdeal.comap (Int.castRingHom (𝓞 E))
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have hmem : ∀ n : ℤ, A.valuation (n : Ω) < 1 ↔ a ∣ n := by
    intro n
    have h1 := hP (n : 𝓞 E)
    have h2 : (algebraMap E Ω) (((n : 𝓞 E)) : E) = (n : Ω) := by simp
    rw [h2] at h1
    rw [h1]
    have h3 : (n : 𝓞 E) ∈ P.asIdeal ↔ n ∈ I := by simp [I]
    rw [h3, ha, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨k, rfl⟩; exact Dvd.intro_left k rfl
    · rintro ⟨k, rfl⟩; exact ⟨k, by rw [smul_eq_mul, mul_comm]⟩
  refine ⟨a.natAbs, ?_, ?_, fun n => by rw [hmem n, Int.natAbs_dvd]⟩
  · intro h0
    have ha0 : a = 0 := Int.natAbs_eq_zero.mp h0
    have hN := Ideal.absNorm_mem P.asIdeal
    have hNv : A.valuation (((Ideal.absNorm P.asIdeal : ℕ) : ℤ) : Ω) < 1 := by
      have h1 := (hP ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)).mpr hN
      simpa using h1
    rw [hmem, ha0, zero_dvd_iff] at hNv
    have : Ideal.absNorm P.asIdeal = 0 := by exact_mod_cast hNv
    exact P.ne_bot (Ideal.absNorm_eq_zero_iff.mp this)
  · intro h1
    have : A.valuation ((1 : ℤ) : Ω) < 1 := by
      rw [hmem, ← Int.natAbs_dvd, h1]; simp
    simp at this

end GlobalTheory.MaxIdealPow

namespace GlobalTheory.MaxIdealPow

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A P hP x c hx hc hc0 hvx`. Take `⟨p, hp0, hp1, hpv⟩` from `exists_nat_of_isPlaceOver E A P hP`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap E Ω).injective`. Establish `hvp : A.valuation (p : Ω) < 1`. Use `(hpv p).2 dvd_rfl` as an intermediate fact.

Simplify using `using this`. Establish `hvp0 : A.valuation (p : Ω) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`. Conclude with `hp0` after adjusting the coercions. Establish `hunit : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → A.valuation (n : Ω) = 1` using `fun n hn => le_antisymm ((A.valuation_le_one_iff _).2 (intCast_mem A n)) (not_lt.1 (fun h => hn ((hpv n).1 h)))`.

Establish `hxA : x ∈ A` using `ReciprocityTheory.Gal.mem_of_isIntegral_int A hx`. Establish `hcA : c ∈ A` using `ReciprocityTheory.Gal.mem_of_isIntegral_int A hc`. Establish `hstep2 : ∃ s : ℕ, A.valuation x ^ s ≤ A.valuation (p : Ω)` using `by haveI : Fact (1 < p) := ⟨by omega⟩`. Set `f` to `minpoly ℤ x`. Establish `hfm : f.Monic` using `minpoly.monic hx`.

Set `fb` to `f.map (Int.castRingHom (ZMod p))`. Establish `hfb0 : fb ≠ 0` using `(hfm.map _).ne_zero`. Take `⟨q, hq, hqX⟩` from `exists_eq_pow_rootMultiplicity_mul_and_not_dvd fb hfb0 0`. Simplify using `only [map_zero, sub_zero] at hq hqX`. Use `set s := rootMultiplicity 0 fb`.

Establish `hq0 : q.coeff 0 ≠ 0` using `fun h => hqX (X_dvd_iff.mpr h)`. Take `⟨g, hg⟩` from `map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective q`. Establish `hker : f - X ^ s * g ∈ RingHom.ker (mapRingHom (Int.castRingHom (ZMod p)))`. Rewrite using `[RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X, hg]`. Conclude with `sub_eq_zero.mpr hq`.

Rewrite `hker` using `[ker_mapRingHom, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]`. Take `⟨h, hh⟩` from `hker`. Establish `hev` using `congrArg (aeval x) hh`. Rewrite `hev` using `[map_sub, map_mul, map_pow, aeval_X, minpoly.aeval, map_mul, aeval_C]`. Establish `hg0 : ¬ (p : ℤ) ∣ g.coeff 0`.

Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Introduce `h0`. Apply `hq0` to reduce the goal to its premises. Rewrite using `[← hg, coeff_map]`. Simplify using `using h0`.

Take `⟨w, hwA, hw⟩` from `aeval_eq_coeff_zero_add A g hxA`. Establish `hvg : A.valuation (aeval x g) = 1`. Rewrite using `[hw, Valuation.map_add_eq_of_lt_left, hunit _ hg0]`. Rewrite using `[hunit _ hg0, Valuation.map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hhA : aeval x h ∈ A`. Take `⟨w', hw'A, hw'⟩` from `aeval_eq_coeff_zero_add A h hxA`. Rewrite using `[hw']`. Conclude with `add_mem (intCast_mem A _) (mul_mem hxA hw'A)`. Use `⟨s, ?_⟩` and prove the remaining obligations.

Establish `hev2 : x ^ s * aeval x g = -((algebraMap ℤ Ω p) * aeval x h)`. Rewrite using `[← hev]`. Expand and normalize the polynomial expressions, which then agree. Use `congrArg A.valuation hev2` as an intermediate fact. Rewrite `this` using `[Valuation.map_neg, Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hvg, mul_one]`.

Rewrite using `[this]`. Establish `hp' : (algebraMap ℤ Ω (p : ℤ)) = (p : Ω)` using `by simp`. Rewrite using `[hp']`. Combine the equalities or inequalities in the displayed calculation. Establish `hstep3 : ∃ t : ℕ, A.valuation (p : Ω) ^ t ≤ A.valuation c`.

Set `f` to `minpoly ℤ c`. Establish `hf0 : f ≠ 0` using `(minpoly.monic hc).ne_zero`. Take `⟨f₁, hf, hfX⟩` from `exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0`. Simplify using `only [map_zero, sub_zero] at hf hfX`. Establish `ha0 : f₁.coeff 0 ≠ 0` using `fun h => hfX (X_dvd_iff.mpr h)`.

Establish `hev : aeval c f₁ = 0`. Establish `h1` using `minpoly.aeval ℤ c`. Express the relevant statement in the definitionally equal form `aeval c f = 0 at h1`. Rewrite `h1` using `[hf, map_mul, map_pow, aeval_X]`. Conclude with `(mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hc0)`.

Take `⟨w, hwA, hw⟩` from `aeval_eq_coeff_zero_add A f₁ hcA`. Rewrite `hw` using `[hev]`. Establish `hle : A.valuation ((f₁.coeff 0 : ℤ) : Ω) ≤ A.valuation c`. Establish `he : ((f₁.coeff 0 : ℤ) : Ω) = -(c * w)` using `by linear_combination -hw`. Rewrite using `[he, Valuation.map_neg, Valuation.map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hn0 : (f₁.coeff 0).natAbs ≠ 0` using `Int.natAbs_ne_zero.mpr ha0`. Take `⟨t, u, hu, hfac⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp1`. Use `⟨t, le_trans (le_of_eq ?_) hle⟩` and prove the remaining obligations. Establish `habs : A.valuation ((f₁.coeff 0 : ℤ) : Ω) = A.valuation (((f₁.coeff 0).natAbs : ℤ) : Ω)`.

Break down `Int.natAbs_eq (f₁.coeff 0) with h | h` into its components or cases. Rewrite using `[← h]`. Use `conv_lhs => rw [h]`. Rewrite using `[Int.cast_neg, Valuation.map_neg]`. Rewrite using `[habs, hfac]`.

Establish `hu1 : A.valuation ((u : ℤ) : Ω) = 1` using `hunit u (by exact_mod_cast hu)`. Use `push_cast`. Rewrite using `[Valuation.map_mul, Valuation.map_pow]`. Move the coercions through the operations in `at hu1`. Rewrite using `[hu1, mul_one]`.

Take `⟨s, hs⟩` from `hstep2`. Take `⟨t, ht⟩` from `hstep3`. Use `⟨s * (t + 1), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_pow_lt_valuation : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → ∀ x c : Ω, IsIntegral ℤ x → IsIntegral ℤ c → c ≠ 0 → A.valuation x < 1 → ∃ k : ℕ, A.valuation x ^ k < A.valuation c := by
  intro E Ω _ _ _ _ _ A P hP x c hx hc hc0 hvx
  obtain ⟨p, hp0, hp1, hpv⟩ := exists_nat_of_isPlaceOver E A P hP
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hvp : A.valuation (p : Ω) < 1 := by
    have := (hpv p).2 dvd_rfl
    simpa using this
  have hvp0 : A.valuation (p : Ω) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact_mod_cast hp0
  have hunit : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → A.valuation (n : Ω) = 1 := fun n hn =>
    le_antisymm ((A.valuation_le_one_iff _).2 (intCast_mem A n))
      (not_lt.1 (fun h => hn ((hpv n).1 h)))
  have hxA : x ∈ A := ReciprocityTheory.Gal.mem_of_isIntegral_int A hx
  have hcA : c ∈ A := ReciprocityTheory.Gal.mem_of_isIntegral_int A hc

  have hstep2 : ∃ s : ℕ, A.valuation x ^ s ≤ A.valuation (p : Ω) := by
    haveI : Fact (1 < p) := ⟨by omega⟩
    let f := minpoly ℤ x
    have hfm : f.Monic := minpoly.monic hx
    let fb := f.map (Int.castRingHom (ZMod p))
    have hfb0 : fb ≠ 0 := (hfm.map _).ne_zero
    obtain ⟨q, hq, hqX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd fb hfb0 0
    simp only [map_zero, sub_zero] at hq hqX
    set s := rootMultiplicity 0 fb
    have hq0 : q.coeff 0 ≠ 0 := fun h => hqX (X_dvd_iff.mpr h)
    obtain ⟨g, hg⟩ := map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective q
    have hker : f - X ^ s * g ∈ RingHom.ker (mapRingHom (Int.castRingHom (ZMod p))) := by
      rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, map_X, hg]
      exact sub_eq_zero.mpr hq
    rw [ker_mapRingHom, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton] at hker
    obtain ⟨h, hh⟩ := hker
    have hev := congrArg (aeval x) hh
    rw [map_sub, map_mul, map_pow, aeval_X, minpoly.aeval, map_mul, aeval_C] at hev
    have hg0 : ¬ (p : ℤ) ∣ g.coeff 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro h0; apply hq0; rw [← hg, coeff_map]; simpa using h0
    obtain ⟨w, hwA, hw⟩ := aeval_eq_coeff_zero_add A g hxA
    have hvg : A.valuation (aeval x g) = 1 := by
      rw [hw, Valuation.map_add_eq_of_lt_left, hunit _ hg0]
      rw [hunit _ hg0, Valuation.map_mul]
      calc A.valuation x * A.valuation w ≤ A.valuation x * 1 :=
            mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hwA) |>.trans_eq (mul_one _).symm
        _ = A.valuation x := mul_one _
        _ < 1 := hvx
    have hhA : aeval x h ∈ A := by
      obtain ⟨w', hw'A, hw'⟩ := aeval_eq_coeff_zero_add A h hxA
      rw [hw']; exact add_mem (intCast_mem A _) (mul_mem hxA hw'A)
    refine ⟨s, ?_⟩
    have hev2 : x ^ s * aeval x g = -((algebraMap ℤ Ω p) * aeval x h) := by
      rw [← hev]; ring
    have := congrArg A.valuation hev2
    rw [Valuation.map_neg, Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hvg,
      mul_one] at this
    rw [this]
    have hp' : (algebraMap ℤ Ω (p : ℤ)) = (p : Ω) := by simp
    rw [hp']
    calc A.valuation (p : Ω) * A.valuation (aeval x h) ≤ A.valuation (p : Ω) * 1 :=
          mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hhA) |>.trans_eq (mul_one _).symm
      _ = A.valuation (p : Ω) := mul_one _

  have hstep3 : ∃ t : ℕ, A.valuation (p : Ω) ^ t ≤ A.valuation c := by
    let f := minpoly ℤ c
    have hf0 : f ≠ 0 := (minpoly.monic hc).ne_zero
    obtain ⟨f₁, hf, hfX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
    simp only [map_zero, sub_zero] at hf hfX
    have ha0 : f₁.coeff 0 ≠ 0 := fun h => hfX (X_dvd_iff.mpr h)
    have hev : aeval c f₁ = 0 := by
      have h1 := minpoly.aeval ℤ c
      change aeval c f = 0 at h1
      rw [hf, map_mul, map_pow, aeval_X] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hc0)
    obtain ⟨w, hwA, hw⟩ := aeval_eq_coeff_zero_add A f₁ hcA
    rw [hev] at hw
    have hle : A.valuation ((f₁.coeff 0 : ℤ) : Ω) ≤ A.valuation c := by
      have he : ((f₁.coeff 0 : ℤ) : Ω) = -(c * w) := by linear_combination -hw
      rw [he, Valuation.map_neg, Valuation.map_mul]
      calc A.valuation c * A.valuation w ≤ A.valuation c * 1 :=
            mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 hwA) |>.trans_eq (mul_one _).symm
        _ = A.valuation c := mul_one _
    have hn0 : (f₁.coeff 0).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha0
    obtain ⟨t, u, hu, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp1
    refine ⟨t, le_trans (le_of_eq ?_) hle⟩
    have habs : A.valuation ((f₁.coeff 0 : ℤ) : Ω) = A.valuation (((f₁.coeff 0).natAbs : ℤ) : Ω) := by
      rcases Int.natAbs_eq (f₁.coeff 0) with h | h
      · rw [← h]
      · conv_lhs => rw [h]
        rw [Int.cast_neg, Valuation.map_neg]
    rw [habs, hfac]
    have hu1 : A.valuation ((u : ℤ) : Ω) = 1 := hunit u (by exact_mod_cast hu)
    push_cast
    rw [Valuation.map_mul, Valuation.map_pow]
    push_cast at hu1
    rw [hu1, mul_one]
  obtain ⟨s, hs⟩ := hstep2
  obtain ⟨t, ht⟩ := hstep3
  refine ⟨s * (t + 1), ?_⟩
  calc A.valuation x ^ (s * (t + 1)) = (A.valuation x ^ s) ^ (t + 1) := pow_mul _ _ _
    _ ≤ A.valuation (p : Ω) ^ (t + 1) := pow_le_pow_left₀ zero_le' hs _
    _ = A.valuation (p : Ω) ^ t * A.valuation (p : Ω) := pow_succ _ _
    _ < A.valuation (p : Ω) ^ t * 1 :=
        mul_lt_mul_of_pos_left hvp (zero_lt_iff.mpr (pow_ne_zero _ hvp0))
    _ = A.valuation (p : Ω) ^ t := mul_one _
    _ ≤ A.valuation c := ht

end GlobalTheory.MaxIdealPow
