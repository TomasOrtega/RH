import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ReConjMulLe

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.FL
open PositivityTheory.Rg.Sw.LVs.II (cE)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `n m e w Z b`. Establish `hX : IsLie (if b = true then dir1 Z else dir2 Z)` using `lie_dir Z b`. Use `haveI := kRCpt n`. Establish `hc1 : Continuous fun k : KR n => rD (if b = true then dir1 Z else dir2 Z) (mR (k : GR n))` using `(continuous_rD _).comp continuous_subtype_val`. Establish `hc2 : Continuous fun k : KR n => rA (if b = true then dir1 Z else dir2 Z) (mR (k : GR n))` using `(continuous_rA _).comp continuous_subtype_val`.

Take `⟨C1, hC1⟩` from `(isCompact_range hc1).isBounded.exists_norm_le`. Take `⟨C2, hC2⟩` from `(isCompact_range hc2).isBounded.exists_norm_le`. Use `⟨|(e : ℝ)| * max C1 0 + ((m : ℝ) + 2 * ‖w‖) * max C2 0, by positivity, fun y => ?_⟩` and prove the remaining obligations. Take `⟨p, k, hp, hk, rfl⟩` from `iwa n y`. Take `⟨R, hR, hRb⟩` from `fz_deriv (x := mR (p * k)) hX (p * k).2 m e w`.

Use `⟨R, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [cE_eq_exp]`. Conclude with `hR`. Use `hRb.trans ?_` and prove the remaining obligations. Establish `e1 : rD (if b = true then dir1 Z else dir2 Z) (mR (p * k)) = rD (if b = true then dir1 Z else dir2 Z) (mR k)`.

Rewrite using `[mR_mul, rD_up]`. Establish `e2 : rA (if b = true then dir1 Z else dir2 Z) (mR (p * k)) = rA (if b = true then dir1 Z else dir2 Z) (mR k)`. Rewrite using `[mR_mul, rA_up _ _ _ hp]`. Establish `b1 : ‖rD (if b = true then dir1 Z else dir2 Z) (mR k)‖ ≤ max C1 0` using `(hC1 _ ⟨⟨k, hk⟩, rfl⟩).trans (le_max_left _ _)`. Establish `b2 : ‖rA (if b = true then dir1 Z else dir2 Z) (mR k)‖ ≤ max C2 0` using `(hC2 _ ⟨⟨k, hk⟩, rfl⟩).trans (le_max_left _ _)`.

Rewrite using `[e1, e2, mul_comm]`. Apply `mul_le_mul_of_nonneg_right _ (norm_nonneg _)` to reduce the goal to its premises. Use `gcongr`.
-/
theorem fzDer : FzDer := by
  intro n m e w Z b
  have hX : IsLie (if b = true then dir1 Z else dir2 Z) := lie_dir Z b
  haveI := kRCpt n
  have hc1 : Continuous fun k : KR n => rD (if b = true then dir1 Z else dir2 Z) (mR (k : GR n)) :=
    (continuous_rD _).comp continuous_subtype_val
  have hc2 : Continuous fun k : KR n => rA (if b = true then dir1 Z else dir2 Z) (mR (k : GR n)) :=
    (continuous_rA _).comp continuous_subtype_val
  obtain ⟨C1, hC1⟩ := (isCompact_range hc1).isBounded.exists_norm_le
  obtain ⟨C2, hC2⟩ := (isCompact_range hc2).isBounded.exists_norm_le
  refine ⟨|(e : ℝ)| * max C1 0 + ((m : ℝ) + 2 * ‖w‖) * max C2 0, by positivity, fun y => ?_⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := iwa n y
  obtain ⟨R, hR, hRb⟩ := fz_deriv (x := mR (p * k)) hX (p * k).2 m e w
  refine ⟨R, ?_, ?_⟩
  · simp only [cE_eq_exp]
    exact hR
  · refine hRb.trans ?_
    have e1 : rD (if b = true then dir1 Z else dir2 Z) (mR (p * k)) =
        rD (if b = true then dir1 Z else dir2 Z) (mR k) := by
      rw [mR_mul, rD_up]
    have e2 : rA (if b = true then dir1 Z else dir2 Z) (mR (p * k)) =
        rA (if b = true then dir1 Z else dir2 Z) (mR k) := by
      rw [mR_mul, rA_up _ _ _ hp]
    have b1 : ‖rD (if b = true then dir1 Z else dir2 Z) (mR k)‖ ≤ max C1 0 :=
      (hC1 _ ⟨⟨k, hk⟩, rfl⟩).trans (le_max_left _ _)
    have b2 : ‖rA (if b = true then dir1 Z else dir2 Z) (mR k)‖ ≤ max C2 0 :=
      (hC2 _ ⟨⟨k, hk⟩, rfl⟩).trans (le_max_left _ _)
    rw [e1, e2, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    gcongr

end PositivityTheory.Rg.Sw.HSt
