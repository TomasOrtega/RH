import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.UnifVal

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Establish `h1 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1` using `(u : v.adicCompletionIntegers K).2`. Establish `h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1` using `((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K).2`. Establish `h3 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) * Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) = 1`.

Rewrite using `[← map_mul, ← Subring.coe_mul, Units.mul_inv]`. Simplify using the standard rewrite rules. Assume the negation of the conclusion as `hne`. Establish `hlt` using `lt_of_le_of_ne h1 hne`. Establish `: Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) * Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) < 1` using `mul_lt_one_of_lt_of_le hlt h2`.

Rewrite `this` using `[h3]`. Conclude with `lt_irrefl _ this`. Introduce `h`. Establish `ha0 : (a : v.adicCompletion K) ≠ 0`. Introduce `h0`.

Rewrite `h` using `[h0, map_zero]`. Conclude with `zero_ne_one h`. Establish `hmem : (a : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K` using `by show Valued.v ((a : v.adicCompletion K)⁻¹) ≤ 1`. Rewrite using `[map_inv₀, h, inv_one]`. Use `isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show (a : v.adicCompletion K) * (a : v.adicCompletion K)⁻¹ = 1`. Conclude with `mul_inv_cancel₀ ha0`.
-/
theorem isUnit_iff_v_eq_one (a : v.adicCompletionIntegers K) :
    IsUnit a ↔ Valued.v (a : v.adicCompletion K) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 := (u : v.adicCompletionIntegers K).2
    have h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 :=
      ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K).2
    have h3 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
        Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
      rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
    by_contra hne
    have hlt := lt_of_le_of_ne h1 hne
    have : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
        Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) < 1 :=
      mul_lt_one_of_lt_of_le hlt h2
    rw [h3] at this; exact lt_irrefl _ this
  · intro h
    have ha0 : (a : v.adicCompletion K) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
    have hmem : (a : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
      show Valued.v ((a : v.adicCompletion K)⁻¹) ≤ 1
      rw [map_inv₀, h, inv_one]
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    show (a : v.adicCompletion K) * (a : v.adicCompletion K)⁻¹ = 1
    exact mul_inv_cancel₀ ha0

/- English proof (translation)
Unfold `IsUniformiserAt Formalism.L2.Host.IsUnifAt`. Establish `hx0 : (x : v.adicCompletion K) ≠ 0` using `x.ne_zero`. Establish `hv0 : Valued.v (x : v.adicCompletion K) ≠ 0` using `by simpa using hx0`. Use `set m := WithZero.log (Valued.v (x : v.adicCompletion K)) with hm`. Establish `hx : Valued.v (x : v.adicCompletion K) = WithZero.exp m` using `(WithZero.exp_log hv0).symm`.

Take `⟨π, hπ⟩` from `HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1 : ℤ))`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Conclude with `WithZero.exp_ne_zero (hπ.symm.trans (map_zero _))`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hmem, hirr⟩`. Establish `hle : Valued.v (x : v.adicCompletion K) ≤ 1` using `hmem`. Establish `hnu : Valued.v (x : v.adicCompletion K) ≠ 1` using `fun h => hirr.not_isUnit ((isUnit_iff_v_eq_one v _).2 h)`. Rewrite `hle` using `[hx, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Rewrite `hnu` using `[hx, ← WithZero.exp_zero, Ne, WithZero.exp_inj]`.

Rewrite using `[hx]`. Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[WithZero.exp_inj]`. Establish `hm2 : m ≤ -2` using `by omega`. Establish `ha : π ∈ v.adicCompletionIntegers K` using `by show Valued.v π ≤ 1`.

Rewrite using `[hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Evaluate the numerical expressions. Establish `hbv : Valued.v ((x : v.adicCompletion K) / π) = WithZero.exp (m + 1)`. Rewrite using `[map_div₀, hx, hπ, ← WithZero.exp_sub, sub_neg_eq_add]`. Establish `hb : (x : v.adicCompletion K) / π ∈ v.adicCompletionIntegers K` using `by show Valued.v ((x : v.adicCompletion K) / π) ≤ 1`.

Rewrite using `[hbv, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `hprod : (⟨(x : v.adicCompletion K), hmem⟩ : v.adicCompletionIntegers K) = ⟨π, ha⟩ * ⟨(x : v.adicCompletion K) / π, hb⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (x : v.adicCompletion K) = π * ((x : v.adicCompletion K) / π)`.

Clear the denominators using the available nonvanishing facts. Break down `hirr.isUnit_or_isUnit hprod with h | h` into its components or cases. Rewrite `h` using `[isUnit_iff_v_eq_one]`. Express the relevant statement in the definitionally equal form `Valued.v π = 1 at h`. Rewrite `h` using `[hπ, ← WithZero.exp_zero, WithZero.exp_inj]`.

Evaluate the numerical expressions using `at h`. Rewrite `h` using `[isUnit_iff_v_eq_one]`. Express the relevant statement in the definitionally equal form `Valued.v ((x : v.adicCompletion K) / π) = 1 at h`. Rewrite `h` using `[hbv, ← WithZero.exp_zero, WithZero.exp_inj]`. Use linear arithmetic over natural numbers and integers.

Introduce `h`. Establish `hmem : (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K` using `by show Valued.v (x : v.adicCompletion K) ≤ 1`. Rewrite using `[h, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Evaluate the numerical expressions. Use `⟨hmem, irreducible_iff.2 ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Introduce `hu`. Rewrite `hu` using `[isUnit_iff_v_eq_one]`. Express the relevant statement in the definitionally equal form `Valued.v (x : v.adicCompletion K) = 1 at hu`. Rewrite `hu` using `[h, ← WithZero.exp_zero, WithZero.exp_inj]`. Evaluate the numerical expressions using `at hu`.

Introduce `a b hab`. Establish `hv : Valued.v (a : v.adicCompletion K) * Valued.v (b : v.adicCompletion K) = WithZero.exp (-1 : ℤ)`. Establish `hab' : (x : v.adicCompletion K) = (a : v.adicCompletion K) * (b : v.adicCompletion K)` using `congrArg Subtype.val hab`. Rewrite using `[← map_mul, ← hab', h]`. Establish `ha0 : Valued.v (a : v.adicCompletion K) ≠ 0`.

Introduce `h0`. Rewrite `hv` using `[h0, zero_mul]`. Conclude with `WithZero.exp_ne_zero hv.symm`. Establish `hb0 : Valued.v (b : v.adicCompletion K) ≠ 0`. Introduce `h0`.

Rewrite `hv` using `[h0, mul_zero]`. Conclude with `WithZero.exp_ne_zero hv.symm`. Establish `hale : Valued.v (a : v.adicCompletion K) ≤ 1` using `a.2`. Establish `hble : Valued.v (b : v.adicCompletion K) ≤ 1` using `b.2`. Rewrite `hale` using `[← WithZero.exp_log ha0, ← WithZero.exp_zero, WithZero.exp_le_exp]`.

Rewrite `hble` using `[← WithZero.exp_log hb0, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Rewrite `hv` using `[← WithZero.exp_log ha0, ← WithZero.exp_log hb0, ← WithZero.exp_add, WithZero.exp_inj]`. Distinguish the cases in `hi : WithZero.log (Valued.v (a : v.adicCompletion K)) = 0`. Use `left`. Rewrite using `[isUnit_iff_v_eq_one, ← WithZero.exp_log ha0, hi, WithZero.exp_zero]`.

Use `right`. Establish `hj : WithZero.log (Valued.v (b : v.adicCompletion K)) = 0` using `by omega`. Rewrite using `[isUnit_iff_v_eq_one, ← WithZero.exp_log hb0, hj, WithZero.exp_zero]`.
-/
theorem isUniformiserAt_iff_isUnifAt (x : (v.adicCompletion K)ˣ) :
    IsUniformiserAt K v (x : v.adicCompletion K) ↔ Formalism.L2.Host.IsUnifAt v x := by
  unfold IsUniformiserAt Formalism.L2.Host.IsUnifAt
  have hx0 : (x : v.adicCompletion K) ≠ 0 := x.ne_zero
  have hv0 : Valued.v (x : v.adicCompletion K) ≠ 0 := by simpa using hx0
  set m := WithZero.log (Valued.v (x : v.adicCompletion K)) with hm
  have hx : Valued.v (x : v.adicCompletion K) = WithZero.exp m := (WithZero.exp_log hv0).symm
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hπ.symm.trans (map_zero _))
  constructor
  · rintro ⟨hmem, hirr⟩
    have hle : Valued.v (x : v.adicCompletion K) ≤ 1 := hmem
    have hnu : Valued.v (x : v.adicCompletion K) ≠ 1 := fun h =>
      hirr.not_isUnit ((isUnit_iff_v_eq_one v _).2 h)
    rw [hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
    rw [hx, ← WithZero.exp_zero, Ne, WithZero.exp_inj] at hnu
    rw [hx]
    by_contra hne
    rw [WithZero.exp_inj] at hne
    have hm2 : m ≤ -2 := by omega
    have ha : π ∈ v.adicCompletionIntegers K := by
      show Valued.v π ≤ 1
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
    have hbv : Valued.v ((x : v.adicCompletion K) / π) = WithZero.exp (m + 1) := by
      rw [map_div₀, hx, hπ, ← WithZero.exp_sub, sub_neg_eq_add]
    have hb : (x : v.adicCompletion K) / π ∈ v.adicCompletionIntegers K := by
      show Valued.v ((x : v.adicCompletion K) / π) ≤ 1
      rw [hbv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have hprod : (⟨(x : v.adicCompletion K), hmem⟩ : v.adicCompletionIntegers K) =
        ⟨π, ha⟩ * ⟨(x : v.adicCompletion K) / π, hb⟩ := by
      apply Subtype.ext
      show (x : v.adicCompletion K) = π * ((x : v.adicCompletion K) / π)
      field_simp
    rcases hirr.isUnit_or_isUnit hprod with h | h
    · rw [isUnit_iff_v_eq_one] at h
      change Valued.v π = 1 at h
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_inj] at h
      norm_num at h
    · rw [isUnit_iff_v_eq_one] at h
      change Valued.v ((x : v.adicCompletion K) / π) = 1 at h
      rw [hbv, ← WithZero.exp_zero, WithZero.exp_inj] at h
      omega
  · intro h
    have hmem : (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
      show Valued.v (x : v.adicCompletion K) ≤ 1
      rw [h, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
    refine ⟨hmem, irreducible_iff.2 ⟨?_, ?_⟩⟩
    · intro hu
      rw [isUnit_iff_v_eq_one] at hu
      change Valued.v (x : v.adicCompletion K) = 1 at hu
      rw [h, ← WithZero.exp_zero, WithZero.exp_inj] at hu
      norm_num at hu
    · intro a b hab
      have hv : Valued.v (a : v.adicCompletion K) * Valued.v (b : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
        have hab' : (x : v.adicCompletion K) = (a : v.adicCompletion K) * (b : v.adicCompletion K) :=
          congrArg Subtype.val hab
        rw [← map_mul, ← hab', h]
      have ha0 : Valued.v (a : v.adicCompletion K) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hv; exact WithZero.exp_ne_zero hv.symm
      have hb0 : Valued.v (b : v.adicCompletion K) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hv; exact WithZero.exp_ne_zero hv.symm
      have hale : Valued.v (a : v.adicCompletion K) ≤ 1 := a.2
      have hble : Valued.v (b : v.adicCompletion K) ≤ 1 := b.2
      rw [← WithZero.exp_log ha0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hale
      rw [← WithZero.exp_log hb0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hble
      rw [← WithZero.exp_log ha0, ← WithZero.exp_log hb0, ← WithZero.exp_add, WithZero.exp_inj] at hv
      by_cases hi : WithZero.log (Valued.v (a : v.adicCompletion K)) = 0
      · left
        rw [isUnit_iff_v_eq_one, ← WithZero.exp_log ha0, hi, WithZero.exp_zero]
      · right
        have hj : WithZero.log (Valued.v (b : v.adicCompletion K)) = 0 := by omega
        rw [isUnit_iff_v_eq_one, ← WithZero.exp_log hb0, hj, WithZero.exp_zero]

end GlobalTheory.UnifVal
