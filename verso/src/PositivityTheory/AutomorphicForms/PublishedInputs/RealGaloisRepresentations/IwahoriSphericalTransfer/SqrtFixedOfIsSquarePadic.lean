import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SqFix

/- English proof (translation)
Take `⟨y, hy⟩` from `h`. Establish `hy1 : ‖y‖ ≤ 1`. Establish `h1 : ‖y‖ * ‖y‖ ≤ 1`. Rewrite using `[← norm_mul, ← hy]`. Conclude with `Padic.norm_int_le_one d`.

Use polynomial arithmetic with `[norm_nonneg y]`. Use `set y' : ℤ_[q] := ⟨y, hy1⟩ with hy'`. Use `set x : ℤ := ((PadicInt.toZModPow n y').val : ℤ) with hx`. Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `hmem : y' - (x : ℤ_[q]) ∈ (Ideal.span {(q : ℤ_[q]) ^ n} : Ideal ℤ_[q])`.

Rewrite using `[← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hx]`. Simplify using the standard rewrite rules. Establish `hd : ((d : ℤ) : ℤ_[q]) = y' * y'`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hy', hy]`.

Both sides reduce to the same expression. Establish `hmem2 : (((d - x ^ 2 : ℤ)) : ℤ_[q]) ∈ (Ideal.span {(q : ℤ_[q]) ^ n} : Ideal ℤ_[q])`. Establish `: (((d - x ^ 2 : ℤ)) : ℤ_[q]) = (y' - (x : ℤ_[q])) * (y' + (x : ℤ_[q]))` using `by push_cast; rw [hd]; ring`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ hmem`.

Use `(PadicInt.norm_le_pow_iff_mem_span_pow _ n).mpr hmem2` as an intermediate fact. Conclude with `(PadicInt.norm_int_le_pow_iff_dvd (p := q)).mp this` after adjusting the coercions.
-/
theorem exists_int_sq_approx (q : ℕ) [Fact q.Prime] (d : ℤ) (h : IsSquare (d : ℚ_[q])) (n : ℕ) :
    ∃ x : ℤ, ((q : ℤ) ^ n) ∣ d - x ^ 2 := by
  obtain ⟨y, hy⟩ := h
  have hy1 : ‖y‖ ≤ 1 := by
    have h1 : ‖y‖ * ‖y‖ ≤ 1 := by
      rw [← norm_mul, ← hy]; exact Padic.norm_int_le_one d
    nlinarith [norm_nonneg y]
  set y' : ℤ_[q] := ⟨y, hy1⟩ with hy'
  set x : ℤ := ((PadicInt.toZModPow n y').val : ℤ) with hx
  refine ⟨x, ?_⟩
  have hmem : y' - (x : ℤ_[q]) ∈ (Ideal.span {(q : ℤ_[q]) ^ n} : Ideal ℤ_[q]) := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hx]
    simp
  have hd : ((d : ℤ) : ℤ_[q]) = y' * y' := by
    apply Subtype.ext
    simp [hy', hy]
    rfl
  have hmem2 : (((d - x ^ 2 : ℤ)) : ℤ_[q]) ∈ (Ideal.span {(q : ℤ_[q]) ^ n} : Ideal ℤ_[q]) := by
    have : (((d - x ^ 2 : ℤ)) : ℤ_[q]) = (y' - (x : ℤ_[q])) * (y' + (x : ℤ_[q])) := by
      push_cast; rw [hd]; ring
    rw [this]; exact Ideal.mul_mem_right _ _ hmem
  have := (PadicInt.norm_le_pow_iff_mem_span_pow _ n).mpr hmem2
  exact_mod_cast (PadicInt.norm_int_le_pow_iff_dvd (p := q)).mp this

end GlobalTheory.SqFix

namespace GlobalTheory.SqFix

/- English proof (translation)
Distinguish the cases in `hw : w = 0`. Substitute `hw` using the available equality. Establish `hz : z = 0`. Establish `: A.valuation z = 0` using `le_antisymm (by simpa using h) zero_le'`. Simplify using `using this`.

Substitute `hz` using the available equality. Simplify using the standard rewrite rules. Establish `hsw : s w ≠ 0` using `(map_ne_zero_iff _ s.injective).mpr hw`. Establish `h1 : A.valuation (z / w) ≤ 1`. Rewrite using `[map_div₀]`.

Conclude with `div_le_one_of_le₀ h zero_le'`. Establish `h2 : s (z / w) ∈ A` using `(ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hs _).mpr ((A.valuation_le_one_iff _).mp h1)`. Rewrite `h2` using `[map_div₀]`. Establish `h3` using `(A.valuation_le_one_iff _).mpr h2`. Rewrite `h3` using `[map_div₀]`.

Establish `hv : A.valuation (s w) ≠ 0` using `by simpa using hsw`. Conclude with `(div_le_one₀ (zero_lt_iff.mpr hv)).mp h3`.
-/
theorem valuation_apply_le {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (s : G F Ω) (hs : s ∈ Dec (F := F) A) (z w : Ω)
    (h : A.valuation z ≤ A.valuation w) : A.valuation (s z) ≤ A.valuation (s w) := by
  by_cases hw : w = 0
  · subst hw
    have hz : z = 0 := by
      have : A.valuation z = 0 := le_antisymm (by simpa using h) zero_le'
      simpa using this
    subst hz; simp
  · have hsw : s w ≠ 0 := (map_ne_zero_iff _ s.injective).mpr hw
    have h1 : A.valuation (z / w) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ h zero_le'
    have h2 : s (z / w) ∈ A := (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hs _).mpr ((A.valuation_le_one_iff _).mp h1)
    rw [map_div₀] at h2
    have h3 := (A.valuation_le_one_iff _).mpr h2
    rw [map_div₀] at h3
    have hv : A.valuation (s w) ≠ 0 := by simpa using hsw
    exact (div_le_one₀ (zero_lt_iff.mpr hv)).mp h3

end GlobalTheory.SqFix

namespace GlobalTheory.SqFix

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ v A hA q _ hq d δ hδ hsq s hs`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Establish `hsδ2 : s δ ^ 2 = δ ^ 2` using `by rw [← map_pow, hδ, map_intCast]`. Distinguish the cases in `hd : d = 0`. Substitute `hd` using the available equality.

Establish `: δ = 0` using `by simpa using hδ`. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hsδ2 with h | h` into its components or cases. Conclude with `h`.

It suffices to derive a contradiction. Establish `hqv : A.valuation (q : Ω) < 1`. Use `(hA (q : 𝓞 F)).mpr hq` as an intermediate fact. Simplify using `using this`. Establish `hq0 : (q : Ω) ≠ 0` using `Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero`.

Establish `hN0 : (4 * d).natAbs ≠ 0` using `by simp [hd]`. Take `⟨k, u, hu, hN⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hN0 q (Fact.out : q.Prime).one_lt.ne'`. Establish `hV4d : A.valuation (((4 * d : ℤ)) : Ω) = A.valuation (q : Ω) ^ k * A.valuation (u : Ω)`. Break down `Int.natAbs_eq (4 * d) with e | e` into its components or cases. Rewrite using `[e, hN]`.

Use `push_cast`. Rewrite using `[map_mul, map_pow]`. Rewrite using `[e, hN]`. Use `push_cast`. Rewrite using `[Valuation.map_neg, map_mul, map_pow]`.

Establish `hu1 : 1 ≤ A.valuation (u : Ω)`. Use `not_lt.mp fun hlt => ?_` and prove the remaining obligations. Establish `hu' : ((u : ℕ) : 𝓞 F) ∈ v.asIdeal` using `(hA (u : 𝓞 F)).mp (by simpa using hlt)`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hu)`. Establish `h1 : (1 : 𝓞 F) ∈ v.asIdeal`.

Establish `e` using `congrArg (Int.cast : ℤ → 𝓞 F) hab`. Move the coercions through the operations in `at e`. Rewrite using `[← e]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hu')`. Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)`.

Take `⟨x, m, hm⟩` from `exists_int_sq_approx q d hsq (k + 1)`. Use `set a : Ω := δ - x with ha`. Use `set b : Ω := δ + x with hb`. Establish `hab : a * b = (q : Ω) ^ (k + 1) * (m : Ω)`. Establish `e` using `congrArg (Int.cast : ℤ → Ω) hm`.

Move the coercions through the operations in `at e`. Rewrite using `[ha, hb, ← e, ← hδ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsa : s a = -b` using `by rw [ha, hb, map_sub, map_intCast, h]; ring`. Establish `hsb : s b = -a` using `by rw [ha, hb, map_add, map_intCast, h]; ring`.

Establish `hVab : A.valuation a = A.valuation b`. Break down `le_total (A.valuation a) (A.valuation b) with e | e` into its components or cases. Use `le_antisymm e ?_` and prove the remaining obligations. Use `valuation_apply_le A s hs a b e` as an intermediate fact. Rewrite `this` using `[hsa, hsb, Valuation.map_neg, Valuation.map_neg]`. Then use the resulting hypothesis.

Use `le_antisymm ?_ e` and prove the remaining obligations. Use `valuation_apply_le A s hs b a e` as an intermediate fact. Rewrite `this` using `[hsa, hsb, Valuation.map_neg, Valuation.map_neg]`. Then use the resulting hypothesis. Establish `hm1 : A.valuation (m : Ω) ≤ 1` using `(A.valuation_le_one_iff _).mpr (intCast_mem A m)`. Establish `hVa : A.valuation a * A.valuation a ≤ A.valuation (q : Ω) ^ (k + 1)`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2δ : A.valuation (2 * δ) ≤ A.valuation a`. Establish `e : 2 * δ = a + b` using `by rw [ha, hb]; ring`. Rewrite using `[e]`. Use `(Valuation.map_add _ _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[hVab, max_self]`. Establish `h4d : A.valuation (((4 * d : ℤ)) : Ω) ≤ A.valuation (q : Ω) ^ (k + 1)`. Establish `e : (((4 * d : ℤ)) : Ω) = (2 * δ) * (2 * δ)` using `by push_cast; rw [← hδ]; ring`. Rewrite using `[e, map_mul]`. Conclude with `(mul_le_mul' h2δ h2δ).trans hVa`.

Establish `hqk : A.valuation (q : Ω) ^ k ≠ 0` using `pow_ne_zero _ (by simpa using hq0)`. Establish `key : A.valuation (q : Ω) ^ k * 1 ≤ A.valuation (q : Ω) ^ k * A.valuation (q : Ω)`. Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `mul_le_mul' (le_refl (A.valuation (q : Ω) ^ k)⁻¹) key`. Rewrite `h3` using `[← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hqk, one_mul, one_mul]`.

Use `h3` as an intermediate fact. Conclude with `absurd hqv (not_lt.mpr this)`.
-/
theorem sqrt_fixed_of_isSquare_padic : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (q : ℕ) [Fact q.Prime], ((q : ℕ) : 𝓞 F) ∈ v.asIdeal → ∀ (d : ℤ) (δ : Ω), δ ^ 2 = (d : Ω) → IsSquare (d : ℚ_[q]) → ∀ s ∈ Dec (F := F) A, s δ = δ := by
  intro F Ω _ _ _ _ _ v A hA q _ hq d δ hδ hsq s hs
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hsδ2 : s δ ^ 2 = δ ^ 2 := by rw [← map_pow, hδ, map_intCast]
  by_cases hd : d = 0
  · subst hd
    have : δ = 0 := by simpa using hδ
    subst this; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsδ2 with h | h
  · exact h
  exfalso
  have hqv : A.valuation (q : Ω) < 1 := by
    have := (hA (q : 𝓞 F)).mpr hq
    simpa using this
  have hq0 : (q : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hN0 : (4 * d).natAbs ≠ 0 := by simp [hd]
  obtain ⟨k, u, hu, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 q (Fact.out : q.Prime).one_lt.ne'
  have hV4d : A.valuation (((4 * d : ℤ)) : Ω) = A.valuation (q : Ω) ^ k * A.valuation (u : Ω) := by
    rcases Int.natAbs_eq (4 * d) with e | e
    · rw [e, hN]; push_cast; rw [map_mul, map_pow]
    · rw [e, hN]; push_cast; rw [Valuation.map_neg, map_mul, map_pow]
  have hu1 : 1 ≤ A.valuation (u : Ω) := by
    refine not_lt.mp fun hlt => ?_
    have hu' : ((u : ℕ) : 𝓞 F) ∈ v.asIdeal := (hA (u : 𝓞 F)).mp (by simpa using hlt)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hu)
    have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
      have e := congrArg (Int.cast : ℤ → 𝓞 F) hab
      push_cast at e
      rw [← e]
      exact add_mem (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hu')
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨x, m, hm⟩ := exists_int_sq_approx q d hsq (k + 1)
  set a : Ω := δ - x with ha
  set b : Ω := δ + x with hb
  have hab : a * b = (q : Ω) ^ (k + 1) * (m : Ω) := by
    have e := congrArg (Int.cast : ℤ → Ω) hm
    push_cast at e
    rw [ha, hb, ← e, ← hδ]; ring
  have hsa : s a = -b := by rw [ha, hb, map_sub, map_intCast, h]; ring
  have hsb : s b = -a := by rw [ha, hb, map_add, map_intCast, h]; ring
  have hVab : A.valuation a = A.valuation b := by
    rcases le_total (A.valuation a) (A.valuation b) with e | e
    · refine le_antisymm e ?_
      have := valuation_apply_le A s hs a b e
      rwa [hsa, hsb, Valuation.map_neg, Valuation.map_neg] at this
    · refine le_antisymm ?_ e
      have := valuation_apply_le A s hs b a e
      rwa [hsa, hsb, Valuation.map_neg, Valuation.map_neg] at this
  have hm1 : A.valuation (m : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  have hVa : A.valuation a * A.valuation a ≤ A.valuation (q : Ω) ^ (k + 1) := by
    calc A.valuation a * A.valuation a = A.valuation (a * b) := by rw [map_mul, hVab]
      _ = A.valuation (q : Ω) ^ (k + 1) * A.valuation (m : Ω) := by rw [hab, map_mul, map_pow]
      _ ≤ A.valuation (q : Ω) ^ (k + 1) * 1 := mul_le_mul' le_rfl hm1
      _ = _ := mul_one _
  have h2δ : A.valuation (2 * δ) ≤ A.valuation a := by
    have e : 2 * δ = a + b := by rw [ha, hb]; ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans ?_
    rw [hVab, max_self]
  have h4d : A.valuation (((4 * d : ℤ)) : Ω) ≤ A.valuation (q : Ω) ^ (k + 1) := by
    have e : (((4 * d : ℤ)) : Ω) = (2 * δ) * (2 * δ) := by push_cast; rw [← hδ]; ring
    rw [e, map_mul]
    exact (mul_le_mul' h2δ h2δ).trans hVa
  have hqk : A.valuation (q : Ω) ^ k ≠ 0 := pow_ne_zero _ (by simpa using hq0)
  have key : A.valuation (q : Ω) ^ k * 1 ≤ A.valuation (q : Ω) ^ k * A.valuation (q : Ω) := by
    calc A.valuation (q : Ω) ^ k * 1 ≤ A.valuation (q : Ω) ^ k * A.valuation (u : Ω) := mul_le_mul' le_rfl hu1
      _ = A.valuation (((4 * d : ℤ)) : Ω) := hV4d.symm
      _ ≤ A.valuation (q : Ω) ^ (k + 1) := h4d
      _ = _ := pow_succ _ _
  have h3 := mul_le_mul' (le_refl (A.valuation (q : Ω) ^ k)⁻¹) key
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hqk, one_mul, one_mul] at h3
  have := h3
  exact absurd hqv (not_lt.mpr this)

end GlobalTheory.SqFix
