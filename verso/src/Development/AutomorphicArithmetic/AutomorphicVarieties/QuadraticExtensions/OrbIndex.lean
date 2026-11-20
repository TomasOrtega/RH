import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

namespace UpperTheory.V.Two.DyadicOrbitIndex

variable (l : ℕ) [hl : Fact l.Prime]

/- English proof (translation)
Establish `h : Prime ((l : ℕ) : ℤ)` using `Nat.prime_iff_prime_int.mp hl.out`. Establish `e : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ)` using `by simp`. Rewrite using `[e]`. Conclude with `(MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h`.
-/
private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  have e : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  rw [e]
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

variable {l} {Ω : Type} [Field Ω]

/- English proof (translation)
Use `show ((n : ℤ) : 𝓞 ℚ) ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _`. Rewrite using `[Ideal.mem_span_singleton]`. Establish `e1 : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ)` using `by simp`. Establish `e2 : ((n : ℤ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm n` using `by simp`. Rewrite using `[e1, e2]`.

Conclude with `map_dvd_iff Rat.ringOfIntegersEquiv.symm`.
-/
private theorem intCast_mem_vQ (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
  show ((n : ℤ) : 𝓞 ℚ) ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _
  rw [Ideal.mem_span_singleton]
  have e1 : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  have e2 : ((n : ℤ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm n := by simp
  rw [e1, e2]
  exact map_dvd_iff Rat.ringOfIntegersEquiv.symm

/- English proof (translation)
The claim follows from `(A.valuation_le_one_iff _).mpr (intCast_mem A n)`.
-/
private theorem val_intCast_le_one (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (intCast_mem A n)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hnd`. Establish `hc : IsCoprime ((l : ℕ) : ℤ) n` using `((Nat.prime_iff_prime_int.mp hl.out).coprime_iff_not_dvd).mpr hnd`. Take `⟨a, b, hab⟩` from `hc`.

Establish `h1 : A.valuation ((a : Ω) * ((l : ℕ) : Ω) + (b : Ω) * (n : Ω)) < 1`. Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) hA`. Rewrite using `[map_mul]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h`. Establish `h2 : (a : Ω) * ((l : ℕ) : Ω) + (b : Ω) * (n : Ω) = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab`. Rewrite `h1` using `[h2, map_one]`. Conclude with `lt_irrefl _ h1`. Introduce and unpack `⟨k, rfl⟩`.

Use `push_cast`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) hA`.
-/
private theorem val_intCast_lt_one_iff (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  constructor
  · intro h
    by_contra hnd
    have hc : IsCoprime ((l : ℕ) : ℤ) n :=
      ((Nat.prime_iff_prime_int.mp hl.out).coprime_iff_not_dvd).mpr hnd
    obtain ⟨a, b, hab⟩ := hc
    have h1 : A.valuation ((a : Ω) * ((l : ℕ) : Ω) + (b : Ω) * (n : Ω)) < 1 := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) hA
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h
    have h2 : (a : Ω) * ((l : ℕ) : Ω) + (b : Ω) * (n : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
    rw [h2, map_one] at h1
    exact lt_irrefl _ h1
  · rintro ⟨k, rfl⟩
    push_cast
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) hA

/- English proof (translation)
Introduce `x`. Take `⟨n, rfl⟩ : ∃ n : ℤ, x = ((n : ℤ) : 𝓞 ℚ)` from `⟨Rat.ringOfIntegersEquiv x, by`. Use `Rat.ringOfIntegersEquiv.symm_apply_apply x` as an intermediate fact. Rewrite using `[← this]`. Use the proof step `simp⟩`.

Rewrite using `[intCast_mem_vQ, ← val_intCast_lt_one_iff A hA]`. Simplify using the standard rewrite rules.
-/
private theorem isPlaceOver_vQ [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = ((n : ℤ) : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, by
      have := Rat.ringOfIntegersEquiv.symm_apply_apply x
      rw [← this]; simp⟩
  rw [intCast_mem_vQ, ← val_intCast_lt_one_iff A hA]
  simp

/- English proof (translation)
Rewrite `hA`, the goal using `[← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]`. Break down `hA with h | h` into its components or cases. Conclude with `Or.inl h`. Use `Or.inr fun h' => h ?_` and prove the remaining obligations. Rewrite `h'` using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`.

Establish `e : g⁻¹ • ((n : Ω))⁻¹ = ((n : Ω))⁻¹` using `by show (g⁻¹ : G ℚ Ω) ((n : Ω))⁻¹ = _`. Rewrite using `[map_inv₀, map_natCast]`. Rewrite `h'` using `[e]`. Then use the resulting hypothesis.
-/
private theorem smul_val_lt [Algebra ℚ Ω] (g : G ℚ Ω) (A : ValuationSubring Ω) (n : ℕ)
    (hA : A.valuation (n : Ω) < 1) : (g • A).valuation (n : Ω) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hA ⊢
  rcases hA with h | h
  · exact Or.inl h
  · refine Or.inr fun h' => h ?_
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at h'
    have e : g⁻¹ • ((n : Ω))⁻¹ = ((n : Ω))⁻¹ := by
      show (g⁻¹ : G ℚ Ω) ((n : Ω))⁻¹ = _
      rw [map_inv₀, map_natCast]
    rwa [e] at h'

end UpperTheory.V.Two.DyadicOrbitIndex

open UpperTheory.V.Two.DyadicOrbitIndex in
/- English proof (translation)
Introduce `Ω _ _ _ p V hV A₀ hp h0 hi`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `haveI : Finite (G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀)) := Nat.finite_of_card_ne_zero hi`. Use `haveI := Fintype.ofFinite (G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀))`. Use `⟨Finset.univ.image fun q : G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀) => q.out • A₀, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `Finset.card_image_le.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]`. Introduce `B hB`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hB`. Conclude with `smul_val_lt _ _ _ h0`.

Introduce `A hA`. Take `⟨g, rfl⟩` from `exists_smul_eq_of_isPlaceOver (F := ℚ) (isPlaceOver_vQ A₀ h0) (isPlaceOver_vQ A hA)`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (V ⊔ Dec (F := ℚ) A₀) g`. Establish `hm : (h⁻¹ : G ℚ Ω) ∈ ((V ⊔ Dec (F` using `ℚ) A₀ : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := inv_mem h.2`. Rewrite `hm` using `[Subgroup.normal_mul]`.

Take `⟨v, hv, d, hd, e⟩` from `hm`. Use `set r := (QuotientGroup.mk g : G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀)).out with hr`. Use `⟨r • A₀, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, r * v * r⁻¹, hV.conj_mem v hv r, ?_⟩` and prove the remaining obligations. Establish `hd' : d • A₀ = A₀` using `(mem_Dec (F := ℚ)).1 hd`. Establish `eg : g = r * v * d`.

Establish `e' : v * d = (h : G ℚ Ω)⁻¹` using `e`. Rewrite using `[mul_assoc, e', hh]`. Use `group`. Rewrite using `[eg, mul_smul (r * v) d, hd', smul_smul]`. Use `congr 1`.

Use `group`.
-/
theorem UpperTheory.V.Two.orbIndex :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) (V : Subgroup (G ℚ Ω)) [V.Normal] (A₀ : ValuationSubring Ω), p.Prime → A₀.valuation (p : Ω) < 1 → (V ⊔ Dec (F := ℚ) A₀).index ≠ 0 → OrbLe V p (V ⊔ Dec (F := ℚ) A₀).index := by
  intro Ω _ _ _ p V hV A₀ hp h0 hi
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀)) := Nat.finite_of_card_ne_zero hi
  haveI := Fintype.ofFinite (G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀))
  refine ⟨Finset.univ.image fun q : G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀) => q.out • A₀, ?_, ?_, ?_⟩
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]
  · intro B hB
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hB
    exact smul_val_lt _ _ _ h0
  · intro A hA
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) (isPlaceOver_vQ A₀ h0) (isPlaceOver_vQ A hA)
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (V ⊔ Dec (F := ℚ) A₀) g
    have hm : (h⁻¹ : G ℚ Ω) ∈ ((V ⊔ Dec (F := ℚ) A₀ : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := inv_mem h.2
    rw [Subgroup.normal_mul] at hm
    obtain ⟨v, hv, d, hd, e⟩ := hm
    set r := (QuotientGroup.mk g : G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀)).out with hr
    refine ⟨r • A₀, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, r * v * r⁻¹, hV.conj_mem v hv r, ?_⟩
    have hd' : d • A₀ = A₀ := (mem_Dec (F := ℚ)).1 hd
    have eg : g = r * v * d := by
      have e' : v * d = (h : G ℚ Ω)⁻¹ := e
      rw [mul_assoc, e', hh]; group
    rw [eg, mul_smul (r * v) d, hd', smul_smul]
    congr 1; group
