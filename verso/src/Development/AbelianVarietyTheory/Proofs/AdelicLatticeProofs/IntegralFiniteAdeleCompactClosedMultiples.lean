import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.IntegralFinAdele

variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
The claim follows from `inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))`.
-/
theorem t2Space_finiteAdeleRing' : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), FiniteAdeleRing.algebraMap_apply, map_natCast (algebraMap (𝓞 F) F)]`.
-/
theorem natCast_apply (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (M : FiniteAdeleRing (𝓞 F) F) v = ((algebraMap (𝓞 F) F (M : 𝓞 F) : F) : v.adicCompletion F) := by
  rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), FiniteAdeleRing.algebraMap_apply,
    map_natCast (algebraMap (𝓞 F) F)]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mul_apply' (a b : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (a * b) v = a v * b v := rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Both sides reduce to the same expression. Consider the case `succ n ih => rw [pow_succ, pow_succ, mul_apply', ih]`.
-/
theorem pow_apply' (a : FiniteAdeleRing (𝓞 F) F) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (a ^ n) v = a v ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih => rw [pow_succ, pow_succ, mul_apply', ih]

/- English proof (translation)
Use `FiniteAdeleRing.ext F fun v => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `a v = 0`. Assume the negation of the conclusion as `h0`. Use `set N := Ideal.absNorm v.asIdeal with hN`. Establish `hNpos : 0 < N` using `Nat.pos_of_ne_zero (by`.

Rewrite using `[hN, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot)`. Establish `hlt : Valued.v ((N : FiniteAdeleRing (𝓞 F) F) v) < 1`. Rewrite using `[natCast_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_lt_one_iff_mem]`. Conclude with `Ideal.absNorm_mem _`.

Establish `hv0 : Valued.v (a v) ≠ 0` using `by simpa using h0`. Take `⟨n, hn⟩` from `exists_pow_lt₀ hlt (Units.mk0 _ hv0)`. Take `⟨c, hc, hac⟩` from `h (N ^ n) (pow_pos hNpos n)`. Establish `hc' : Valued.v (c v) ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hc v)`. Establish `: Valued.v (a v) ≤ Valued.v ((N : FiniteAdeleRing (𝓞 F) F) v) ^ n` using `by conv_lhs => rw [hac]`.

Rewrite using `[mul_apply', Nat.cast_pow, pow_apply', map_mul, map_pow]`. Conclude with `mul_le_of_le_one_right' hc'`. Conclude with `absurd hn (not_lt.2 this)`.
-/
theorem eq_zero_of_forall_mul (a : FiniteAdeleRing (𝓞 F) F)
    (h : ∀ M : ℕ, 0 < M → ∃ c : FiniteAdeleRing (𝓞 F) F,
      (∀ v, c v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧
        a = (M : FiniteAdeleRing (𝓞 F) F) * c) : a = 0 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  change a v = 0
  by_contra h0
  set N := Ideal.absNorm v.asIdeal with hN
  have hNpos : 0 < N := Nat.pos_of_ne_zero (by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  have hlt : Valued.v ((N : FiniteAdeleRing (𝓞 F) F) v) < 1 := by
    rw [natCast_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact Ideal.absNorm_mem _
  have hv0 : Valued.v (a v) ≠ 0 := by simpa using h0
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hv0)
  obtain ⟨c, hc, hac⟩ := h (N ^ n) (pow_pos hNpos n)
  have hc' : Valued.v (c v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hc v)
  have : Valued.v (a v) ≤ Valued.v ((N : FiniteAdeleRing (𝓞 F) F) v) ^ n := by
    conv_lhs => rw [hac]
    rw [mul_apply', Nat.cast_pow, pow_apply', map_mul, map_pow]
    exact mul_le_of_le_one_right' hc'
  exact absurd hn (not_lt.2 this)

/- English proof (translation)
Take `⟨x, b, hb, hab⟩` from `GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos a`. Use `haveI : Algebra.IsAlgebraic ℤ F := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := F)).2 inferInstance`. Take `⟨m, y, hm, hmx⟩` from `IsAlgebraic.exists_nsmul_eq (𝓞 F) (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x)`. Use `⟨m, Nat.pos_of_ne_zero hm, fun v => ?_⟩` and prove the remaining obligations. Establish `h : (m : FiniteAdeleRing (𝓞 F) F) * a = algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F y) + (m : FiniteAdeleRing (𝓞 F) F) * b`.

Rewrite using `[hab, ← hmx, one_smul, map_nsmul, nsmul_eq_mul, mul_add]`. Rewrite using `[h]`. Use `add_mem (HeightOneSpectrum.coe_mem_adicCompletionIntegers v y) (mul_mem ?_ (hb v))` and prove the remaining obligations. Conclude with `natCast_apply F m v ▸ HeightOneSpectrum.coe_mem_adicCompletionIntegers v (m : 𝓞 F)`.
-/
theorem exists_nat_mul_integral (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ M : ℕ, 0 < M ∧ ∀ v, ((M : FiniteAdeleRing (𝓞 F) F) * a) v ∈
      HeightOneSpectrum.adicCompletionIntegers F v := by
  obtain ⟨x, b, hb, hab⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos a
  haveI : Algebra.IsAlgebraic ℤ F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := F)).2 inferInstance
  obtain ⟨m, y, hm, hmx⟩ := IsAlgebraic.exists_nsmul_eq (𝓞 F)
    (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x)
  refine ⟨m, Nat.pos_of_ne_zero hm, fun v => ?_⟩
  have h : (m : FiniteAdeleRing (𝓞 F) F) * a =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F y) +
        (m : FiniteAdeleRing (𝓞 F) F) * b := by
    rw [hab, ← hmx, one_smul, map_nsmul, nsmul_eq_mul, mul_add]
  rw [h]
  refine add_mem (HeightOneSpectrum.coe_mem_adicCompletionIntegers v y) (mul_mem ?_ (hb v))
  exact natCast_apply F m v ▸ HeightOneSpectrum.coe_mem_adicCompletionIntegers v (m : 𝓞 F)

/- English proof (translation)
Introduce `F _ _`. Use `⟨GlobalTheory.AdeleCocompact.isCompact_integral F, fun M _ => ?_, eq_zero_of_forall_mul F, fun x hx => ?_, exists_nat_mul_integral F, ⟨fun a ⟨n, hn⟩ => ?_⟩⟩` and prove the remaining obligations. Use `haveI := t2Space_finiteAdeleRing' F`. Establish `h` using `((GlobalTheory.AdeleCocompact.isCompact_integral F).image (continuous_const_mul (M : FiniteAdeleRing (𝓞 F) F))).isClosed`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `a`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq, eq_comm]`. Take `⟨y, hy⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => by`. Use `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hx v)` as an intermediate fact. Rewrite `this` using `[FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Then use the resulting hypothesis.

Conclude with `⟨y, hy.symm⟩`. Use `FiniteAdeleRing.ext F fun v => ?_` and prove the remaining obligations. Establish `: a v ^ n = 0` using `by rw [← pow_apply', hn]; rfl`. Conclude with `eq_zero_of_pow_eq_zero this`.
-/
theorem integral_finiteAdele_properties : ∀ (F : Type) [Field F] [NumberField F], IsCompact {a : FiniteAdeleRing (𝓞 F) F | (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)} ∧ (∀ M : ℕ, 0 < M → IsClosed {a : FiniteAdeleRing (𝓞 F) F | ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ a = (M : FiniteAdeleRing (𝓞 F) F) * c}) ∧ (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ M : ℕ, 0 < M → ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ a = (M : FiniteAdeleRing (𝓞 F) F) * c) → a = 0) ∧ (∀ x : F, (∀ v, (algebraMap F (FiniteAdeleRing (𝓞 F) F) x : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) → ∃ y : 𝓞 F, x = y) ∧ (∀ a : FiniteAdeleRing (𝓞 F) F, ∃ M : ℕ, 0 < M ∧ (∀ v, (((M : FiniteAdeleRing (𝓞 F) F) * a) : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ IsReduced (FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _
  refine ⟨GlobalTheory.AdeleCocompact.isCompact_integral F, fun M _ => ?_, eq_zero_of_forall_mul F,
    fun x hx => ?_, exists_nat_mul_integral F, ⟨fun a ⟨n, hn⟩ => ?_⟩⟩
  · haveI := t2Space_finiteAdeleRing' F
    have h := ((GlobalTheory.AdeleCocompact.isCompact_integral F).image
      (continuous_const_mul (M : FiniteAdeleRing (𝓞 F) F))).isClosed
    convert h using 1
    ext a
    simp only [Set.mem_image, Set.mem_setOf_eq, eq_comm]
  · obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => by
      have := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hx v)
      rwa [FiniteAdeleRing.algebraMap_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    exact ⟨y, hy.symm⟩
  · refine FiniteAdeleRing.ext F fun v => ?_
    have : a v ^ n = 0 := by rw [← pow_apply', hn]; rfl
    exact eq_zero_of_pow_eq_zero this

end GlobalTheory.IntegralFinAdele
