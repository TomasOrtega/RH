import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassPush
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PGrassHeightE
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFSGeomDegPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

/- English proof (translation)
Introduce `II Ψ _ _ N j cf e hII hN hj1 hjN hJ hZ`. Break down `isEmpty_or_nonempty Ψ with hΨ | hΨ` into its components or cases. Establish `hmu : muPoly Ψ N j = 0`. Unfold `muPoly`. Conclude with `Finset.sum_eq_zero fun p _ => (IsEmpty.false p.1).elim`.

Establish `hFA : FA Ψ N j cf = 0`. Unfold `FA`. Rewrite using `[hmu, zero_pow (Nat.succ_ne_zero _), zero_mul]`. Rewrite using `[hFA, Fintype.card_eq_zero]`. Simplify using `[hFl]`.

Use `set f := Fintype.card Ψ with hfdef`. Establish `hf : 1 ≤ f` using `Fintype.card_pos`. Establish `hP` using `hPush II Ψ N j cf hII hN hj1 hjN`. Establish `hG` using `GrassHeightE.full hZ2 f j (N - j) e hf hZ II hII`. Establish `hD : 0 < geomDeg (grassIdeal f j (N - j)) (GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j))) (f * j * (N - j))` using `hDeg (Fin f) (plBlocks f j (N - j)) (grassIdeal f j (N - j)) (f * j * (N - j)) (GrassArithVar.full f j (N - j) hf)`.

Establish `hJ' : (0 : ℝ) < (Jint Ψ N j cf : ℝ)` using `Rat.cast_pos.mpr hJ`. Express the relevant statement in the definitionally equal form `-hFl Ψ N II (FA Ψ N j cf) * geomDeg (grassIdeal f j (N - j)) (GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j))) (f * j * (N - j)) = (Jint Ψ N j cf : ℝ) * II (Fin f) (plBlocks f j (N - j)) (grassIdeal f j (N - j)) (f * j * (N - j) + 1) (fun _ => GroundTheory.Heights₂.H …`. Express the relevant statement in the definitionally equal form `-hFl Ψ N II (FA Ψ N j cf) ≤ ((f * j * (N - j) + 1 : ℕ) : ℝ) * (Jint Ψ N j cf : ℝ) * (f : ℝ) * e`. Establish `h1` using `mul_le_mul_of_nonneg_left hG hJ'.le`. Use `le_of_mul_le_mul_right ?_ hD` and prove the remaining obligations.

Rewrite using `[hP]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GrassmannianHeightZTwo.proof (hZ2 : SuccessiveMinimaUpperBound) (hPush : FlagGrassPush.Statement)
    (hDeg : HilbertSamuel.FSGeomDegPos.Statement) : GrassmannianHeightZTwo.Statement := by
  intro II Ψ _ _ N j cf e hII hN hj1 hjN hJ hZ
  rcases isEmpty_or_nonempty Ψ with hΨ | hΨ
  · have hmu : muPoly Ψ N j = 0 := by
      unfold muPoly
      exact Finset.sum_eq_zero fun p _ => (IsEmpty.false p.1).elim
    have hFA : FA Ψ N j cf = 0 := by
      unfold FA
      rw [hmu, zero_pow (Nat.succ_ne_zero _), zero_mul]
    rw [hFA, Fintype.card_eq_zero]
    simp [hFl]
  · set f := Fintype.card Ψ with hfdef
    have hf : 1 ≤ f := Fintype.card_pos
    have hP := hPush II Ψ N j cf hII hN hj1 hjN
    have hG := GrassHeightE.full hZ2 f j (N - j) e hf hZ II hII
    have hD : 0 < geomDeg (grassIdeal f j (N - j)) (GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j)))
        (f * j * (N - j)) :=
      hDeg (Fin f) (plBlocks f j (N - j)) (grassIdeal f j (N - j)) (f * j * (N - j))
        (GrassArithVar.full f j (N - j) hf)
    have hJ' : (0 : ℝ) < (Jint Ψ N j cf : ℝ) := Rat.cast_pos.mpr hJ
    change -hFl Ψ N II (FA Ψ N j cf) * geomDeg (grassIdeal f j (N - j))
        (GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j))) (f * j * (N - j)) =
      (Jint Ψ N j cf : ℝ) * II (Fin f) (plBlocks f j (N - j)) (grassIdeal f j (N - j))
        (f * j * (N - j) + 1) (fun _ => GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j))) at hP
    change -hFl Ψ N II (FA Ψ N j cf) ≤ ((f * j * (N - j) + 1 : ℕ) : ℝ) * (Jint Ψ N j cf : ℝ) * (f : ℝ) * e
    have h1 := mul_le_mul_of_nonneg_left hG hJ'.le
    refine le_of_mul_le_mul_right ?_ hD
    rw [hP]
    calc _ ≤ _ := h1
      _ = _ := by ring

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
