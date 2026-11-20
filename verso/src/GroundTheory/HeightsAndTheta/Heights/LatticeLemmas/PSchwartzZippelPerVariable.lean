import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.IsProbabilityMeasureSphereLaw
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `R _ _ _ q d S G hG hdeg`. Establish `key` using `MvPolynomial.schwartz_zippel_sum_degreeOf hG (fun _ : Fin q ↦ S)`. Establish `hsum : ∑ i : Fin q, ((G.degreeOf i : ℚ≥0) / (S.card : ℚ≥0)) ≤ ∑ _i : Fin q, ((d : ℚ≥0) / (S.card : ℚ≥0))` using `Finset.sum_le_sum fun i _ ↦ by gcongr; exact_mod_cast hdeg i`. Establish `key'` using `key.trans hsum`. Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.sum_const, nsmul_eq_mul] at key'`.

Express the relevant statement in the definitionally equal form `((((Fintype.piFinset fun _ : Fin q ↦ S).filter fun c ↦ eval c G = 0).card : ℕ) : ℚ≥0) / (S.card : ℚ≥0) ^ q ≤ (q : ℚ≥0) * ((d : ℚ≥0) / (S.card : ℚ≥0)) at key'`. Break down `Nat.eq_zero_or_pos q with rfl | hq` into its components or cases. Simplify using `only [pow_zero, div_one, Nat.cast_zero, zero_mul, nonpos_iff_eq_zero, Nat.cast_eq_zero] at key'`. Rewrite using `[key']`. Conclude with `Nat.zero_le _`.

Break down `Nat.eq_zero_or_pos S.card with hs | hs` into its components or cases. Establish `: S = ∅` using `Finset.card_eq_zero.mp hs`. Substitute `this` using the available equality. Establish `: Nonempty (Fin q)` using `⟨⟨0, hq⟩⟩`. Simplify using `[Fintype.piFinset_empty]`.

Establish `hs' : (0 : ℚ≥0) < (S.card : ℚ≥0)` using `by exact_mod_cast hs`. Establish `hpow : (S.card : ℚ≥0) ^ q = (S.card : ℚ≥0) * (S.card : ℚ≥0) ^ (q - 1)`. Rewrite using `[← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite `key'` using `[div_le_iff₀ (pow_pos hs' q), hpow]`. Establish `hcalc : (q : ℚ≥0) * ((d : ℚ≥0) / (S.card : ℚ≥0)) * ((S.card : ℚ≥0) * (S.card : ℚ≥0) ^ (q - 1)) = (q : ℚ≥0) * d * (S.card : ℚ≥0) ^ (q - 1)`. Clear the denominators using the available nonvanishing facts. Rewrite `key'` using `[hcalc]`. Conclude with `key'` after adjusting the coercions.
-/
theorem SchwartzZippelPerVariable.proof : SchwartzZippelPerVariable.Statement := by
  intro R _ _ _ q d S G hG hdeg
  have key := MvPolynomial.schwartz_zippel_sum_degreeOf hG (fun _ : Fin q ↦ S)
  have hsum : ∑ i : Fin q, ((G.degreeOf i : ℚ≥0) / (S.card : ℚ≥0)) ≤
      ∑ _i : Fin q, ((d : ℚ≥0) / (S.card : ℚ≥0)) :=
    Finset.sum_le_sum fun i _ ↦ by gcongr; exact_mod_cast hdeg i
  have key' := key.trans hsum
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.sum_const,
    nsmul_eq_mul] at key'
  change ((((Fintype.piFinset fun _ : Fin q ↦ S).filter fun c ↦ eval c G = 0).card : ℕ) : ℚ≥0) /
    (S.card : ℚ≥0) ^ q ≤ (q : ℚ≥0) * ((d : ℚ≥0) / (S.card : ℚ≥0)) at key'
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [pow_zero, div_one, Nat.cast_zero, zero_mul, nonpos_iff_eq_zero,
      Nat.cast_eq_zero] at key'
    rw [key']
    exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos S.card with hs | hs
  · have : S = ∅ := Finset.card_eq_zero.mp hs
    subst this
    have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
    simp [Fintype.piFinset_empty]
  have hs' : (0 : ℚ≥0) < (S.card : ℚ≥0) := by exact_mod_cast hs
  have hpow : (S.card : ℚ≥0) ^ q = (S.card : ℚ≥0) * (S.card : ℚ≥0) ^ (q - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [div_le_iff₀ (pow_pos hs' q), hpow] at key'
  have hcalc : (q : ℚ≥0) * ((d : ℚ≥0) / (S.card : ℚ≥0)) *
      ((S.card : ℚ≥0) * (S.card : ℚ≥0) ^ (q - 1)) =
      (q : ℚ≥0) * d * (S.card : ℚ≥0) ^ (q - 1) := by
    field_simp
  rw [hcalc] at key'
  exact_mod_cast key'

end GroundTheory.Heights₂.Heights
