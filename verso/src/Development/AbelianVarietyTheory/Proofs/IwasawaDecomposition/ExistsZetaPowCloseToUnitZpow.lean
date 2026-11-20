import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
open NumberField IsDedekindDomain

namespace GlobalTheory.TamePowTeich

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `h : x ^ (k + 1) - y ^ (k + 1) = x * (x ^ k - y ^ k) + (x - y) * y ^ k` using `by ring`.

Rewrite using `[h]`. Apply `Valuation.map_add_lt` to reduce the goal to its premises. Rewrite using `[map_mul, hx, one_mul]`. Conclude with `ih`. Rewrite using `[map_mul, map_pow, hy, one_pow, mul_one]`.

Conclude with `hxy`.
-/
theorem valuation_pow_sub_lt (A : ValuationSubring Ω) {x y : Ω} (hx : A.valuation x = 1) (hy : A.valuation y = 1)
    (hxy : A.valuation (x - y) < 1) : ∀ k : ℕ, A.valuation (x ^ k - y ^ k) < 1 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h : x ^ (k + 1) - y ^ (k + 1) = x * (x ^ k - y ^ k) + (x - y) * y ^ k := by ring
    rw [h]
    apply Valuation.map_add_lt
    · rw [map_mul, hx, one_mul]; exact ih
    · rw [map_mul, map_pow, hy, one_pow, mul_one]; exact hxy

/- English proof (translation)
Consider the cases of `e with`. Consider the case `ofNat k => simpa using valuation_pow_sub_lt A hx hy hxy k`. Consider the case `negSucc k`. Simplify using `only [zpow_negSucc]`. Establish `hxk : A.valuation (x ^ (k + 1)) = 1` using `by rw [map_pow, hx, one_pow]`.

Establish `hyk : A.valuation (y ^ (k + 1)) = 1` using `by rw [map_pow, hy, one_pow]`. Establish `hx0 : x ^ (k + 1) ≠ 0`. Introduce `h0`. Rewrite `hxk` using `[h0, map_zero]`. Conclude with `zero_ne_one hxk`.

Establish `hy0 : y ^ (k + 1) ≠ 0`. Introduce `h0`. Rewrite `hyk` using `[h0, map_zero]`. Conclude with `zero_ne_one hyk`. Rewrite using `[inv_sub_inv hx0 hy0, map_div₀, map_mul, hxk, hyk, mul_one, div_one, Valuation.map_sub_swap]`.

Conclude with `valuation_pow_sub_lt A hx hy hxy (k + 1)`.
-/
theorem valuation_zpow_sub_lt (A : ValuationSubring Ω) {x y : Ω} (hx : A.valuation x = 1) (hy : A.valuation y = 1)
    (hxy : A.valuation (x - y) < 1) (e : ℤ) : A.valuation (x ^ e - y ^ e) < 1 := by
  cases e with
  | ofNat k => simpa using valuation_pow_sub_lt A hx hy hxy k
  | negSucc k =>
    simp only [zpow_negSucc]
    have hxk : A.valuation (x ^ (k + 1)) = 1 := by rw [map_pow, hx, one_pow]
    have hyk : A.valuation (y ^ (k + 1)) = 1 := by rw [map_pow, hy, one_pow]
    have hx0 : x ^ (k + 1) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hxk; exact zero_ne_one hxk
    have hy0 : y ^ (k + 1) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hyk; exact zero_ne_one hyk
    rw [inv_sub_inv hx0 hy0, map_div₀, map_mul, hxk, hyk, mul_one, div_one, Valuation.map_sub_swap]
    exact valuation_pow_sub_lt A hx hy hxy (k + 1)

end GlobalTheory.TamePowTeich

open GlobalTheory.TamePowTeich in
/- English proof (translation)
Introduce `E Ω _ _ _ _ P A ζ hA hζ u e hu`. Use `set n := Formalism.ConjugateSelfDual.normV P - 1 with hn_def`. Use `letI : Field (𝓞 E ⧸ P.asIdeal) := @Ideal.Quotient.field _ _ P.asIdeal P.isMaximal`. Use `haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot`. Use `letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _`.

Establish `hcard : Formalism.ConjugateSelfDual.normV P = Fintype.card (𝓞 E ⧸ P.asIdeal)` using `by show Nat.card _ = _`. Conclude with `Nat.card_eq_fintype_card`. Establish `hn : 0 < n`. Establish `: 1 < Fintype.card (𝓞 E ⧸ P.asIdeal)` using `Fintype.one_lt_card`. Use linear arithmetic over natural numbers and integers.

Establish `hmem : u ^ n - 1 ∈ P.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero, hn_def, hcard]`. Apply `FiniteField.pow_card_sub_one_eq_one` to reduce the goal to its premises. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis. Use `set U : Ω := algebraMap E Ω (u : E) with hU`.

Establish `hUn : A.valuation (U ^ n - 1) < 1`. Use `(hA (u ^ n - 1)).2 hmem` as an intermediate fact. Simplify `this` using `[hU]`. Establish `hUint : U ∈ A`. Apply `ReciprocityTheory.Gal.mem_of_isIntegral_int` to reduce the goal to its premises.

Conclude with `(u.isIntegral_coe).algebraMap`. Establish `hU1 : A.valuation U = 1`. Apply `le_antisymm ((A.valuation_le_one_iff U).2 hUint)` to reduce the goal to its premises. Rewrite using `[← not_lt]`. Introduce `h`.

Conclude with `hu ((hA u).1 h)`. Establish `hζ1 : A.valuation ζ = 1` using `ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A hn.ne' hζ.pow_eq_one`. Establish `hprod : U ^ n - 1 = ∏ μ ∈ Polynomial.nthRootsFinset n (1 : Ω), (U - μ)`. Use `congrArg (Polynomial.eval U) (Polynomial.X_pow_sub_one_eq_prod hn hζ)` as an intermediate fact. Simplify `this` using `[Polynomial.eval_prod]`.

Establish `hex : ∃ μ ∈ Polynomial.nthRootsFinset n (1 : Ω), A.valuation (U - μ) < 1`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `: 1 ≤ A.valuation (U ^ n - 1)`. Rewrite using `[hprod, map_prod]`.

Conclude with `Finset.one_le_prod' hcon`. Conclude with `absurd hUn (not_lt.2 this)`. Take `⟨μ, hμ, hμU⟩` from `hex`. Use `haveI : NeZero n := ⟨hn.ne'⟩`. Take `⟨b, -, hb⟩` from `hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hn 1).1 hμ)`.

Establish `hb1 : A.valuation (ζ ^ b) = 1` using `by rw [map_pow, hζ1, one_pow]`. Establish `hclose : A.valuation (ζ ^ b - U) < 1`. Rewrite using `[Valuation.map_sub_swap, hb]`. Conclude with `hμU`. Establish `key` using `valuation_zpow_sub_lt A hb1 hU1 hclose e`.

Establish `hζ0 : ζ ≠ 0` using `hζ.ne_zero hn.ne'`. Use `⟨((b * e) % (n : ℤ)).toNat, ?_⟩` and prove the remaining obligations. Establish `hnz : (n : ℤ) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `hnonneg : 0 ≤ (b * e) % (n : ℤ)` using `Int.emod_nonneg _ hnz`. Establish `hpow : (ζ ^ b) ^ e = ζ ^ ((b * e) % (n : ℤ)).toNat`.

Establish `h1 : ζ ^ ((b * e) % (n : ℤ)).toNat = ζ ^ ((b * e) % (n : ℤ))`. Rewrite using `[← zpow_natCast, Int.toNat_of_nonneg hnonneg]`. Rewrite using `[h1, ← zpow_natCast ζ b, ← zpow_mul]`. Use `conv_lhs => rw [← Int.emod_add_mul_ediv ((b : ℤ) * e) n]`. Rewrite using `[zpow_add₀ hζ0, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow, mul_one]`.

Rewrite using `[← hpow]`. Conclude with `key`.
-/
theorem GlobalTheory.TamePowTeich.exists_zeta_pow_close : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (ζ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsPrimitiveRoot ζ (Formalism.ConjugateSelfDual.normV P - 1) → ∀ (u : 𝓞 E) (e : ℤ), u ∉ P.asIdeal →
    ∃ a : ℕ, A.valuation (ζ ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ P A ζ hA hζ u e hu
  classical
  set n := Formalism.ConjugateSelfDual.normV P - 1 with hn_def
  letI : Field (𝓞 E ⧸ P.asIdeal) := @Ideal.Quotient.field _ _ P.asIdeal P.isMaximal
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _
  have hcard : Formalism.ConjugateSelfDual.normV P = Fintype.card (𝓞 E ⧸ P.asIdeal) := by
    show Nat.card _ = _
    exact Nat.card_eq_fintype_card
  have hn : 0 < n := by
    have : 1 < Fintype.card (𝓞 E ⧸ P.asIdeal) := Fintype.one_lt_card
    omega

  have hmem : u ^ n - 1 ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero, hn_def, hcard]
    apply FiniteField.pow_card_sub_one_eq_one
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  set U : Ω := algebraMap E Ω (u : E) with hU
  have hUn : A.valuation (U ^ n - 1) < 1 := by
    have := (hA (u ^ n - 1)).2 hmem
    simpa [hU] using this
  have hUint : U ∈ A := by
    apply ReciprocityTheory.Gal.mem_of_isIntegral_int
    exact (u.isIntegral_coe).algebraMap
  have hU1 : A.valuation U = 1 := by
    apply le_antisymm ((A.valuation_le_one_iff U).2 hUint)
    rw [← not_lt]
    intro h
    exact hu ((hA u).1 h)
  have hζ1 : A.valuation ζ = 1 :=
    ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A hn.ne' hζ.pow_eq_one

  have hprod : U ^ n - 1 = ∏ μ ∈ Polynomial.nthRootsFinset n (1 : Ω), (U - μ) := by
    have := congrArg (Polynomial.eval U) (Polynomial.X_pow_sub_one_eq_prod hn hζ)
    simpa [Polynomial.eval_prod] using this
  have hex : ∃ μ ∈ Polynomial.nthRootsFinset n (1 : Ω), A.valuation (U - μ) < 1 := by
    by_contra hcon
    push_neg at hcon
    have : 1 ≤ A.valuation (U ^ n - 1) := by
      rw [hprod, map_prod]
      exact Finset.one_le_prod' hcon
    exact absurd hUn (not_lt.2 this)
  obtain ⟨μ, hμ, hμU⟩ := hex
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨b, -, hb⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hn 1).1 hμ)
  have hb1 : A.valuation (ζ ^ b) = 1 := by rw [map_pow, hζ1, one_pow]
  have hclose : A.valuation (ζ ^ b - U) < 1 := by
    rw [Valuation.map_sub_swap, hb]; exact hμU
  have key := valuation_zpow_sub_lt A hb1 hU1 hclose e

  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn.ne'
  refine ⟨((b * e) % (n : ℤ)).toNat, ?_⟩
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnonneg : 0 ≤ (b * e) % (n : ℤ) := Int.emod_nonneg _ hnz
  have hpow : (ζ ^ b) ^ e = ζ ^ ((b * e) % (n : ℤ)).toNat := by
    have h1 : ζ ^ ((b * e) % (n : ℤ)).toNat = ζ ^ ((b * e) % (n : ℤ)) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hnonneg]
    rw [h1, ← zpow_natCast ζ b, ← zpow_mul]
    conv_lhs => rw [← Int.emod_add_mul_ediv ((b : ℤ) * e) n]
    rw [zpow_add₀ hζ0, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow, mul_one]
  rw [← hpow]
  exact key
