import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr
open scoped Pointwise

namespace UpperTheory.V.Chr.RationalPlaces

variable (l : ℕ) [hl : Fact l.Prime]

/- English proof (translation)
Establish `h : Prime ((l : ℤ))` using `Nat.prime_iff_prime_int.mp hl.out`. Establish `e : Rat.ringOfIntegersEquiv ((l : ℕ) : 𝓞 ℚ) = (l : ℤ)` using `map_natCast _ l`. Rewrite `h` using `[← e]`. Conclude with `(MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ)).mp h`.
-/
private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℤ)) := Nat.prime_iff_prime_int.mp hl.out
  have e : Rat.ringOfIntegersEquiv ((l : ℕ) : 𝓞 ℚ) = (l : ℤ) := map_natCast _ l
  rw [← e] at h
  exact (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ)).mp h

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

variable {l} {Ω : Type} [Field Ω]

/- English proof (translation)
Unfold `IsPlaceOver`. Introduce `x`. Use `set m : ℤ := Rat.ringOfIntegersEquiv x with hmdef`. Establish `hx : algebraMap ℚ Ω (x : ℚ) = (m : Ω)`. Establish `e : ((m : ℤ) : ℚ) = (x : ℚ)`.

Rewrite using `[hmdef, Rat.ringOfIntegersEquiv_apply_coe]`. Rewrite using `[← e, map_intCast]`. Establish `hmem : x ∈ (vQ l).asIdeal ↔ (l : ℤ) ∣ m`. Express the relevant statement in the definitionally equal form `x ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _`. Rewrite using `[Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast]`.

Establish `hA' : A.valuation ((l : ℤ) : Ω) < 1`. Rewrite using `[Int.cast_natCast]`. Conclude with `hA`. Establish `hint : ∀ k : ℤ, A.valuation (k : Ω) ≤ 1` using `fun k => (ValuationSubring.valuation_le_one_iff A _).mpr (intCast_mem A k)`. Rewrite using `[hx, hmem]`.

Prove the components needed by the constructor for the conclusion. Introduce `hm`. Assume the negation of the conclusion as `hnd`. Establish `hirr : Irreducible (l : ℤ)` using `(Nat.prime_iff_prime_int.mp hl.out).irreducible`. Take `⟨a, b, hab⟩` from `(hirr.coprime_iff_not_dvd).mpr hnd`.

Establish `h1 : ((a : Ω) * (l : ℤ) + (b : Ω) * (m : Ω)) = 1`. Use `congrArg (fun z : ℤ => (z : Ω)) hab` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Conclude with `this`. Establish `hle : A.valuation (1 : Ω) < 1`.

Rewrite using `[← h1]`. Use `lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) hA'`. Rewrite using `[map_mul]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) hm`. Rewrite `hle` using `[map_one]`. Conclude with `lt_irrefl _ hle`. Introduce and unpack `⟨k, hk⟩`. Rewrite using `[hk, Int.cast_mul, map_mul]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (hint k)) hA'`.
-/
private theorem isPlaceOver_vQ [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω)
    (hA : A.valuation ((l : ℕ) : Ω) < 1) : IsPlaceOver (F := ℚ) A (vQ l) := by
  unfold IsPlaceOver
  intro x
  set m : ℤ := Rat.ringOfIntegersEquiv x with hmdef
  have hx : algebraMap ℚ Ω (x : ℚ) = (m : Ω) := by
    have e : ((m : ℤ) : ℚ) = (x : ℚ) := by
      rw [hmdef, Rat.ringOfIntegersEquiv_apply_coe]
    rw [← e, map_intCast]
  have hmem : x ∈ (vQ l).asIdeal ↔ (l : ℤ) ∣ m := by
    change x ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _
    rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast]
  have hA' : A.valuation ((l : ℤ) : Ω) < 1 := by
    rw [Int.cast_natCast]
    exact hA
  have hint : ∀ k : ℤ, A.valuation (k : Ω) ≤ 1 := fun k =>
    (ValuationSubring.valuation_le_one_iff A _).mpr (intCast_mem A k)
  rw [hx, hmem]
  constructor
  · intro hm
    by_contra hnd
    have hirr : Irreducible (l : ℤ) := (Nat.prime_iff_prime_int.mp hl.out).irreducible
    obtain ⟨a, b, hab⟩ := (hirr.coprime_iff_not_dvd).mpr hnd
    have h1 : ((a : Ω) * (l : ℤ) + (b : Ω) * (m : Ω)) = 1 := by
      have := congrArg (fun z : ℤ => (z : Ω)) hab
      push_cast at this ⊢
      exact this
    have hle : A.valuation (1 : Ω) < 1 := by
      rw [← h1]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) hA'
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) hm
    rw [map_one] at hle
    exact lt_irrefl _ hle
  · rintro ⟨k, hk⟩
    rw [hk, Int.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint k)) hA'

/- English proof (translation)
The claim follows from `(A.valuation_le_one_iff _).mpr (natCast_mem A n)`.
-/
private theorem val_natCast_le_one (A : ValuationSubring Ω) (n : ℕ) : A.valuation (n : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (natCast_mem A n)

/- English proof (translation)
Use `revert hn`. Proceed by induction on `n using Nat.recOnMul with`. Consider the case `zero => intro h`. Conclude with `absurd rfl h`. Consider the case `one => intro _`.

Simplify using the standard rewrite rules. Consider the case `prime p hp`. Introduce `_`. Rewrite using `[hp.primeFactors]`. Simplify using the standard rewrite rules.

Consider the case `mul a b iha ihb`. Introduce `hab`. Establish `ha : a ≠ 0` using `left_ne_zero_of_mul hab`. Establish `hb : b ≠ 0` using `right_ne_zero_of_mul hab`. Establish `key : A.valuation (a : Ω) * A.valuation (b : Ω) < 1 ↔ A.valuation (a : Ω) < 1 ∨ A.valuation (b : Ω) < 1`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `e1 : A.valuation (a : Ω) = 1` using `le_antisymm (val_natCast_le_one A a) hc.1`.

Establish `e2 : A.valuation (b : Ω) = 1` using `le_antisymm (val_natCast_le_one A b) hc.2`. Rewrite `h` using `[e1, e2, one_mul]`. Conclude with `lt_irrefl _ h`. Introduce and unpack `(h | h)`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (val_natCast_le_one A b)) h`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (val_natCast_le_one A a)) h`. Rewrite using `[Nat.cast_mul, map_mul, Nat.primeFactors_mul ha hb, key, iha ha, ihb hb]`. Simplify using `only [Finset.mem_union]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨p, hp, h⟩ | ⟨p, hp, h⟩) exacts [⟨p, Or.inl hp, h⟩, ⟨p, Or.inr hp, h⟩]`.

Introduce and unpack `⟨p, hp | hp, h⟩ exacts [Or.inl ⟨p, hp, h⟩, Or.inr ⟨p, hp, h⟩]`.
-/
private theorem val_lt_one_iff (A : ValuationSubring Ω) (n : ℕ) (hn : n ≠ 0) :
    A.valuation (n : Ω) < 1 ↔ ∃ p ∈ n.primeFactors, A.valuation (p : Ω) < 1 := by
  revert hn
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _; simp
  | prime p hp =>
    intro _
    rw [hp.primeFactors]
    simp
  | mul a b iha ihb =>
    intro hab
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    have key : A.valuation (a : Ω) * A.valuation (b : Ω) < 1 ↔
        A.valuation (a : Ω) < 1 ∨ A.valuation (b : Ω) < 1 := by
      constructor
      · intro h
        by_contra hc
        push_neg at hc
        have e1 : A.valuation (a : Ω) = 1 := le_antisymm (val_natCast_le_one A a) hc.1
        have e2 : A.valuation (b : Ω) = 1 := le_antisymm (val_natCast_le_one A b) hc.2
        rw [e1, e2, one_mul] at h
        exact lt_irrefl _ h
      · rintro (h | h)
        · exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_natCast_le_one A b)) h
        · exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_natCast_le_one A a)) h
    rw [Nat.cast_mul, map_mul, Nat.primeFactors_mul ha hb, key, iha ha, ihb hb]
    simp only [Finset.mem_union]
    constructor
    · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
      exacts [⟨p, Or.inl hp, h⟩, ⟨p, Or.inr hp, h⟩]
    · rintro ⟨p, hp | hp, h⟩
      exacts [Or.inl ⟨p, hp, h⟩, Or.inr ⟨p, hp, h⟩]

/- English proof (translation)
Set `x : (⊥ : Subring Ω)` to `⟨(p : Ω), natCast_mem _ p⟩`. Establish `hI : Ideal.span {x} ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top]`. Introduce `hu`. Take `⟨y, hy⟩` from `hu.exists_right_inv`.

Take `⟨m, hm⟩` from `Subring.mem_bot.mp y.2`. Establish `h1 : (((p : ℤ) * m : ℤ) : Ω) = ((1 : ℤ) : Ω)`. Establish `hv` using `congrArg Subtype.val hy`. Use `push_cast`. Rewrite using `[hm]`.

Conclude with `hv`. Establish `h2 : (p : ℤ) * m = 1` using `Int.cast_injective h1`. Establish `h3 : IsUnit (p : ℤ)` using `isUnit_iff_exists_inv.mpr ⟨m, h2⟩`. Rewrite `h3` using `[Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast]`. Conclude with `hp.ne_one h3`.

Take `⟨B, -, hB⟩` from `Ideal.image_subset_nonunits_valuationSubring _ hI`. Conclude with `⟨B, (B.mem_nonunits_iff).mp (hB ⟨x, Ideal.subset_span rfl, rfl⟩)⟩`.
-/
private theorem exists_place [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  let x : (⊥ : Subring Ω) := ⟨(p : Ω), natCast_mem _ p⟩
  have hI : Ideal.span {x} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨m, hm⟩ := Subring.mem_bot.mp y.2
    have h1 : (((p : ℤ) * m : ℤ) : Ω) = ((1 : ℤ) : Ω) := by
      have hv := congrArg Subtype.val hy
      push_cast
      rw [hm]
      exact hv
    have h2 : (p : ℤ) * m = 1 := Int.cast_injective h1
    have h3 : IsUnit (p : ℤ) := isUnit_iff_exists_inv.mpr ⟨m, h2⟩
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h3
    exact hp.ne_one h3
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨B, (B.mem_nonunits_iff).mp (hB ⟨x, Ideal.subset_span rfl, rfl⟩)⟩

end UpperTheory.V.Chr.RationalPlaces

open UpperTheory.V.Chr.RationalPlaces in
/- English proof (translation)
Introduce `Ω _ _ _`. Use `⟨fun p hp => exists_place p hp, fun A n hn => val_lt_one_iff A n hn, ?_⟩` and prove the remaining obligations. Introduce `p A A' hp hA hA'`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Take `⟨σ, hσ⟩` from `exists_smul_eq_of_isPlaceOver (isPlaceOver_vQ A hA) (isPlaceOver_vQ A' hA')`.

Establish `hL : IsLift (RingEquiv.refl ℚ) (σ⁻¹ : G ℚ Ω).toRingEquiv` using `fun x => AlgEquiv.commutes _ x`. Establish `hmem : ∀ x : Ω, (σ⁻¹ : G ℚ Ω).toRingEquiv x ∈ A ↔ x ∈ A'`. Introduce `x`. Rewrite using `[← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`. Both sides reduce to the same expression.

Establish `hconj : ∀ g : G ℚ Ω, (σ⁻¹)⁻¹ * g * σ⁻¹ = conjGal hL g`. Introduce `g`. Use extensionality with `x`. Both sides reduce to the same expression. Use `⟨σ⁻¹, ?_, ?_⟩` and prove the remaining obligations.

Introduce `g hg`. Rewrite using `[hconj]`. Conclude with `conjGal_mem_Dec hL hmem hg`. Introduce `g hg`. Rewrite using `[hconj]`.

Conclude with `conjGal_mem_Ine hL hmem hg`.
-/
theorem UpperTheory.V.Chr.placesQ :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω], (∀ p : ℕ, p.Prime → ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1) ∧
          (∀ (A : ValuationSubring Ω) (n : ℕ), n ≠ 0 → (A.valuation (n : Ω) < 1 ↔ ∃ p ∈ n.primeFactors, A.valuation (p : Ω) < 1)) ∧
          ∀ (p : ℕ) (A A' : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 → A'.valuation (p : Ω) < 1 →
            ∃ u : G ℚ Ω, (∀ x ∈ Dec (F := ℚ) A, u⁻¹ * x * u ∈ Dec (F := ℚ) A') ∧ ∀ x ∈ Ine (F := ℚ) A, u⁻¹ * x * u ∈ Ine (F := ℚ) A' := by
  intro Ω _ _ _
  refine ⟨fun p hp => exists_place p hp, fun A n hn => val_lt_one_iff A n hn, ?_⟩
  intro p A A' hp hA hA'
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (isPlaceOver_vQ A hA) (isPlaceOver_vQ A' hA')
  have hL : IsLift (RingEquiv.refl ℚ) (σ⁻¹ : G ℚ Ω).toRingEquiv := fun x =>
    AlgEquiv.commutes _ x
  have hmem : ∀ x : Ω, (σ⁻¹ : G ℚ Ω).toRingEquiv x ∈ A ↔ x ∈ A' := by
    intro x
    rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  have hconj : ∀ g : G ℚ Ω, (σ⁻¹)⁻¹ * g * σ⁻¹ = conjGal hL g := by
    intro g
    ext x
    rfl
  refine ⟨σ⁻¹, ?_, ?_⟩
  · intro g hg
    rw [hconj]
    exact conjGal_mem_Dec hL hmem hg
  · intro g hg
    rw [hconj]
    exact conjGal_mem_Ine hL hmem hg
