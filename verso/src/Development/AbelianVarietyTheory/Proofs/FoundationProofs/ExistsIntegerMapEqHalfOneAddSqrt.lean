import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

/- English proof (translation)
Take `⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m` from `⟨(d + 1) / 4, by omega⟩`. Establish `hm' : (d : L) + 1 = 4 * (m : L)` using `by exact_mod_cast hm`. Use `⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩` and prove the remaining obligations. Use `monicity!`. Rewrite using `[Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, map_natCast]`.

Take the linear combination `(1 / 4 : L) * hb - (1 / 4 : L) * hm'`.
-/
theorem isIntegral_half_one_add {L : Type*} [Field L] [CharZero L] (d : ℕ) (hd : d % 16 = 7) (b : L)
    (hb : b ^ 2 = -(d : L)) : IsIntegral ℤ ((1 + b) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m := ⟨(d + 1) / 4, by omega⟩
  have hm' : (d : L) + 1 = 4 * (m : L) := by exact_mod_cast hm
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩
  · monicity!
  · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_natCast]
    linear_combination (1 / 4 : L) * hb - (1 / 4 : L) * hm'

/- English proof (translation)
Introduce `D`. Establish `hsq` using `D.host.sqd_sq`. Establish `hd16 : D.host.d % 16 = 7` using `D.host.hyp.2.2.2.1`. Establish `hd0 : (0 : ℝ) ≤ D.host.d` using `Nat.cast_nonneg _`. Establish `key : ∀ b : D.host.K, (b : D.host.E) ^ 2 = -(D.host.d : D.host.E) → D.host.φ₀ (b : D.host.E) = Complex.I * (Real.sqrt D.host.d : ℂ) → ∃ a : 𝓞 D.host.K, D.host.φ₀ (((a : D.host.K) : D.host.E)) = w0 D`.

Introduce `b hb hφ`. Establish `hb' : b ^ 2 = -(D.host.d : D.host.K)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hb`. Use `⟨⟨(1 + b) / 2, isIntegral_half_one_add _ hd16 b hb'⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `D.host.φ₀ (algebraMap D.host.K D.host.E ((1 + b) / 2)) = _`. Rewrite using `[map_div₀, map_add, map_one, map_ofNat, map_div₀, map_add, map_one, map_ofNat]`. Express the relevant statement in the definitionally equal form `(1 + D.host.φ₀ (b : D.host.E)) / 2 = _`. Rewrite using `[hφ, w0]`. Set `b : D.host.K` to `⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩`.

Establish `h1 : (D.host.φ₀ (b : D.host.E)) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2`. Express the relevant statement in the definitionally equal form `(D.host.φ₀ (D.host.sqd)) ^ 2 = _`. Rewrite using `[← map_pow, hsq, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hd0]`. Simplify using the standard rewrite rules. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h` into its components or cases.

Conclude with `key b hsq h`. Use `key (-b) ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(-(D.host.sqd)) ^ 2 = _`. Rewrite using `[neg_sq, hsq]`. Express the relevant statement in the definitionally equal form `D.host.φ₀ (-(b : D.host.E)) = _`.

Rewrite using `[map_neg, h, neg_neg]`.
-/
theorem exists_integer_map_eq_w0 :
    ∀ (D : D7), ∃ a : 𝓞 D.host.K, D.host.φ₀ (((a : D.host.K) : D.host.E)) = w0 D := by
  intro D
  have hsq := D.host.sqd_sq
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hd0 : (0 : ℝ) ≤ D.host.d := Nat.cast_nonneg _
  have key : ∀ b : D.host.K, (b : D.host.E) ^ 2 = -(D.host.d : D.host.E) →
      D.host.φ₀ (b : D.host.E) = Complex.I * (Real.sqrt D.host.d : ℂ) →
      ∃ a : 𝓞 D.host.K, D.host.φ₀ (((a : D.host.K) : D.host.E)) = w0 D := by
    intro b hb hφ
    have hb' : b ^ 2 = -(D.host.d : D.host.K) := by
      apply Subtype.ext
      simpa using hb
    refine ⟨⟨(1 + b) / 2, isIntegral_half_one_add _ hd16 b hb'⟩, ?_⟩
    change D.host.φ₀ (algebraMap D.host.K D.host.E ((1 + b) / 2)) = _
    rw [map_div₀, map_add, map_one, map_ofNat, map_div₀, map_add, map_one, map_ofNat]
    change (1 + D.host.φ₀ (b : D.host.E)) / 2 = _
    rw [hφ, w0]
  let b : D.host.K := ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have h1 : (D.host.φ₀ (b : D.host.E)) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
    change (D.host.φ₀ (D.host.sqd)) ^ 2 = _
    rw [← map_pow, hsq, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt hd0]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact key b hsq h
  · refine key (-b) ?_ ?_
    · change (-(D.host.sqd)) ^ 2 = _
      rw [neg_sq, hsq]
    · change D.host.φ₀ (-(b : D.host.E)) = _
      rw [map_neg, h, neg_neg]

end GlobalTheory.NormSum
