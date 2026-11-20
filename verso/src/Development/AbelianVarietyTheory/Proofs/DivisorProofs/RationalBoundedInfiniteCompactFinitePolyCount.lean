import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorCompactFiniteAdelesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAlgebraicIntegersBoundedArchimedeanLeStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `h` using `norm_le_pi_norm (pInf E (algebraMap E (Ad E) ξ)) w`. Rewrite `h` using `[pInf_algebraMap, InfinitePlace.norm_embedding_eq]`. Conclude with `h`.
-/
theorem place_le_norm_pInf {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (ξ : E)
    (w : InfinitePlace E) : w ξ ≤ ‖pInf E (algebraMap E (Ad E) ξ)‖ := by
  have h := norm_le_pi_norm (pInf E (algebraMap E (Ad E) ξ)) w
  rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq] at h
  exact h

/- English proof (translation)
Introduce `E _ _ _`. Take `⟨m, C₀, hC₀, hcount⟩` from `GlobalTheory.T.card_algebraic_integers_bounded_archimedean_le E`. Use `⟨m, fun Kf hKf => ?_⟩` and prove the remaining obligations. Take `⟨n, hn, hint⟩` from `GlobalTheory.T.exists_common_denominator_compact_finiteAdeles E Kf hKf`. Establish `hn' : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`.

Use `⟨C₀ * (n : ℝ) ^ m, by positivity, fun T hT => ?_⟩` and prove the remaining obligations. Establish `hnT : (1 : ℝ) ≤ n * T` using `by nlinarith`. Take `⟨hAfin, hAcard⟩` from `hcount (n * T) hnT`. Use `set A := {x : 𝓞 E | ∀ w : InfinitePlace E, w (x : E) ≤ n * T}`. Use `set S := {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}`.

Establish `hnE : (n : E) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `hsub : S ⊆ (fun x : 𝓞 E => (x : E) / n) '' A`. Introduce `ξ hξ`. Establish `hi : IsIntegral ℤ ((n : E) * ξ)` using `hint ξ hξ.2`. Use `⟨⟨(n : E) * ξ, hi⟩, fun w => ?_, ?_⟩` and prove the remaining obligations.

Use `show w ((n : E) * ξ) ≤ n * T`. Rewrite using `[← InfinitePlace.norm_embedding_eq, map_mul, map_natCast, norm_mul, Complex.norm_natCast, InfinitePlace.norm_embedding_eq]`. Conclude with `mul_le_mul_of_nonneg_left ((place_le_norm_pInf ξ w).trans hξ.1) (Nat.cast_nonneg n)`. Use `show (n : E) * ξ / n = ξ`. Clear the denominators using the available nonvanishing facts.

Establish `hSfin : S.Finite` using `(hAfin.image _).subset hsub`. Use `⟨hSfin, ?_⟩` and prove the remaining obligations. Establish `h1 : S.ncard ≤ A.ncard` using `(Set.ncard_le_ncard hsub (hAfin.image _)).trans (Set.ncard_image_le hAfin)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rat_bounded_compact_polynomial : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], ∃ m : ℕ,
    ∀ Kf : Set (Af E), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.Finite ∧
      ({ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.ncard : ℝ)
        ≤ C * T ^ m := by
  intro E _ _ _
  obtain ⟨m, C₀, hC₀, hcount⟩ := GlobalTheory.T.card_algebraic_integers_bounded_archimedean_le E
  refine ⟨m, fun Kf hKf => ?_⟩
  obtain ⟨n, hn, hint⟩ := GlobalTheory.T.exists_common_denominator_compact_finiteAdeles E Kf hKf
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨C₀ * (n : ℝ) ^ m, by positivity, fun T hT => ?_⟩
  have hnT : (1 : ℝ) ≤ n * T := by nlinarith
  obtain ⟨hAfin, hAcard⟩ := hcount (n * T) hnT
  set A := {x : 𝓞 E | ∀ w : InfinitePlace E, w (x : E) ≤ n * T}
  set S := {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}
  have hnE : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  have hsub : S ⊆ (fun x : 𝓞 E => (x : E) / n) '' A := by
    intro ξ hξ
    have hi : IsIntegral ℤ ((n : E) * ξ) := hint ξ hξ.2
    refine ⟨⟨(n : E) * ξ, hi⟩, fun w => ?_, ?_⟩
    · show w ((n : E) * ξ) ≤ n * T
      rw [← InfinitePlace.norm_embedding_eq, map_mul, map_natCast, norm_mul, Complex.norm_natCast,
        InfinitePlace.norm_embedding_eq]
      exact mul_le_mul_of_nonneg_left ((place_le_norm_pInf ξ w).trans hξ.1) (Nat.cast_nonneg n)
    · show (n : E) * ξ / n = ξ
      field_simp
  have hSfin : S.Finite := (hAfin.image _).subset hsub
  refine ⟨hSfin, ?_⟩
  have h1 : S.ncard ≤ A.ncard :=
    (Set.ncard_le_ncard hsub (hAfin.image _)).trans (Set.ncard_image_le hAfin)
  calc (S.ncard : ℝ) ≤ A.ncard := by exact_mod_cast h1
    _ ≤ C₀ * (n * T) ^ m := hAcard
    _ = C₀ * (n : ℝ) ^ m * T ^ m := by rw [mul_pow]; ring

end GlobalTheory
