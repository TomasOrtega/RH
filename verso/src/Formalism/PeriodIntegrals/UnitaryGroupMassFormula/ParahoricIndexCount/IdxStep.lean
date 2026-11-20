import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ParahoricIndexCount.ParamInjective

noncomputable section

open Matrix Formalism.DoubleCosetMeasures.P.GLRed

namespace PI.ParahoricIdxZ.W

/- English proof (translation)
Introduce `F _ O ϖ hϖ hϖ0 hloc hfin a t J' hKJ hJint J hJ`. Use `hfin` as an intermediate fact. Use `set H := J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t)) with hH`. Establish `hker : (red O (a + t) ϖ hϖ).ker ≤ H`. Rewrite using `[ker_red O ϖ hϖ hϖ0]`.

Introduce `g hg`. Rewrite `hg`, the goal using `[Subgroup.mem_subgroupOf]`. Conclude with `(hJ _).2 (cong_blockCond O hϖ hϖ0 hloc hKJ hg)`. Establish `hidx` using `Subgroup.index_map_eq H (red_surj O (a + t) ϖ hϖ hloc) hker`. Establish `hcm` using `Subgroup.card_mul_index (H.map (red O (a + t) ϖ hϖ))`.

Establish `hcard : Nat.card (H.map (red O (a + t) ϖ hϖ)) = Nat.card (J' ⧸ (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J') * (Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) ^ (a * t) * Nat.card (GL (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)))`. Establish `e1 : Nat.card (H.map (red O (a + t) ϖ hϖ)) = Nat.card ((fun g : GL (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) => (g : Matrix (Fin (a + t)) (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))) '' ((H.map (red O (a + t) ϖ hϖ) : Subgroup _) : Set _))` using `(Nat.card_image_of_injective Units.val_injective _).symm`. Establish `e2 : Nat.card (Matrix (Fin a) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) = Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) ^ (a * t)` using `by show Nat.card (Fin a → Fin t → Formalism.DoubleCosetMeasures.kF O ϖ hϖ) = _`. Rewrite using `[Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, ← pow_mul, mul_comm]`. Rewrite using `[e1, image_eq O hϖ hϖ0 hloc J' hJint J hJ, Nat.card_range_of_injective (param_injective (t := t) O hϖ J' hJint), Nat.card_prod, Nat.card_prod, card_range_redJ O ϖ hϖ hϖ0 J' hJint, e2]`.

Rewrite using `[← hcm, ← hidx, hcard]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem idxStep : IdxStep := by
  intro F _ O ϖ hϖ hϖ0 hloc hfin a t J' hKJ hJint J hJ
  have := hfin
  set H := J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t)) with hH
  have hker : (red O (a + t) ϖ hϖ).ker ≤ H := by
    rw [ker_red O ϖ hϖ hϖ0]
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    exact (hJ _).2 (cong_blockCond O hϖ hϖ0 hloc hKJ hg)
  have hidx := Subgroup.index_map_eq H (red_surj O (a + t) ϖ hϖ hloc) hker
  have hcm := Subgroup.card_mul_index (H.map (red O (a + t) ϖ hϖ))
  have hcard : Nat.card (H.map (red O (a + t) ϖ hϖ)) =
      Nat.card (J' ⧸ (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J') *
        (Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) ^ (a * t) * Nat.card (GL (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))) := by
    have e1 : Nat.card (H.map (red O (a + t) ϖ hϖ)) =
        Nat.card ((fun g : GL (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) =>
          (g : Matrix (Fin (a + t)) (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))) ''
            ((H.map (red O (a + t) ϖ hϖ) : Subgroup _) : Set _)) :=
      (Nat.card_image_of_injective Units.val_injective _).symm
    have e2 : Nat.card (Matrix (Fin a) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) =
        Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) ^ (a * t) := by
      show Nat.card (Fin a → Fin t → Formalism.DoubleCosetMeasures.kF O ϖ hϖ) = _
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, ← pow_mul, mul_comm]
    rw [e1, image_eq O hϖ hϖ0 hloc J' hJint J hJ,
      Nat.card_range_of_injective (param_injective (t := t) O hϖ J' hJint),
      Nat.card_prod, Nat.card_prod, card_range_redJ O ϖ hϖ hϖ0 J' hJint, e2]
  rw [← hcm, ← hidx, hcard]
  ring

end PI.ParahoricIdxZ.W
