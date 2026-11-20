import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantUnitLowerThreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGramDensityInequalityComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUpdateSubShearStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Fin4
noncomputable section

def pw (t : ℂ) : ℝ := (1 + ‖t‖ ^ 2) ^ (-(4 / 3 : ℝ))

/- English proof (translation)
Establish `h` using `integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 8 / 3) (by rw [Complex.finrank_real_complex]; norm_num)`. Use `h.lintegral_lt_top using 4` and compare the differences between its conclusion and the goal. Simplify using `only [pw]`. Evaluate the numerical expressions.
-/
theorem lintegral_pw_lt_top : ∫⁻ t : ℂ, ENNReal.ofReal (pw t) < ⊤ := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 8 / 3)
    (by rw [Complex.finrank_real_complex]; norm_num)
  convert h.lintegral_lt_top using 4
  simp only [pw]; norm_num

/- English proof (translation)
Set `M : Matrix (Fin 3) (Fin 3) ℂ` to `blkW p0 w`. Use `show ∏ k : Fin 3, colGram M k.castSucc ^ (-2:ℤ) = (colGram M 1 ^ 2 * colGram M 2 ^ 2)⁻¹`. Rewrite using `[Fin.prod_univ_three]`. Establish `h0 : colGram M (Fin.castSucc 0) = 1` using `by simp [colGram, lminor]`. Rewrite using `[h0]`.

Simplify using `only [one_zpow, one_mul, zpow_neg, mul_inv, inv_one]`. Both sides reduce to the same expression.
-/
theorem gB_eq (w : Low 4 → ℂ) (p0 : ℕ) : gB p0 w =
    (colGram (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 1 ^ 2 * colGram (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 ^ 2)⁻¹ := by
  let M : Matrix (Fin 3) (Fin 3) ℂ := blkW p0 w
  show ∏ k : Fin 3, colGram M k.castSucc ^ (-2:ℤ) = (colGram M 1 ^ 2 * colGram M 2 ^ 2)⁻¹
  rw [Fin.prod_univ_three]
  have h0 : colGram M (Fin.castSucc 0) = 1 := by simp [colGram, lminor]
  rw [h0]
  simp only [one_zpow, one_mul, zpow_neg, mul_inv, inv_one]
  rfl

/- English proof (translation)
Unfold `pw`. Check the signs of the components of the expression.
-/
theorem pw_nonneg (t : ℂ) : 0 ≤ pw t := by unfold pw; positivity

/- English proof (translation)
Unfold `pw`. Use `fun_prop`.
-/
theorem measurable_pw : Measurable fun t : ℂ => ENNReal.ofReal (pw t) := by
  unfold pw; fun_prop

/- English proof (translation)
Apply the tactic sequence `intro i; fin_cases i <;> simp [blkW, lowMat]`.
-/
theorem blkW_diag (w : Low 4 → ℂ) (p0 : ℕ) : ∀ i, (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) i i = 1 := by
  intro i; fin_cases i <;> simp [blkW, lowMat]

/- English proof (translation)
Apply the tactic sequence `intro i j h; fin_cases i <;> fin_cases j <;> simp_all [blkW, lowMat]`.
-/
theorem blkW_upper (w : Low 4 → ℂ) (p0 : ℕ) :
    ∀ i j : Fin 3, i < j → (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) i j = 0 := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [blkW, lowMat]

/- English proof (translation)
Take `⟨h1, h2⟩` from `GlobalTheory.T.columnGramDeterminant_unitLower_three (blkW (r := 4) p0 w) (blkW_diag w p0) (blkW_upper w p0)`. Rewrite using `[gB_eq, h1, h2, ha, hb, hc]`.
-/
theorem gB_eq_entries (p0 : ℕ) (pa pb pc : Low 4) (w : Low 4 → ℂ)
    (ha : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 1 0 = w pa)
    (hb : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 0 = w pb)
    (hc : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 1 = w pc) :
    gB p0 w = ((1 + ‖w pa‖ ^ 2 + ‖w pb‖ ^ 2) ^ 2 *
      (1 + ‖w pc‖ ^ 2 + ‖w pa * w pc - w pb‖ ^ 2) ^ 2)⁻¹ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.columnGramDeterminant_unitLower_three (blkW (r := 4) p0 w) (blkW_diag w p0) (blkW_upper w p0)
  rw [gB_eq, h1, h2, ha, hb, hc]

/- English proof (translation)
Use `set S : Finset (Low 4) := {pa, pb, pc} with hS`. Set `f : Low 4 → ℂ → ℝ≥0∞` to `fun p x => if p ∈ S then ENNReal.ofReal (pw x) else (Metric.closedBall (0 : ℂ) 1).indicator 1 x`. Establish `hf : ∀ p, Measurable (f p)`. Introduce `p`. Distinguish the cases in `hp : p ∈ S`.

Simplify using `only [f, hp, if_true]`. Conclude with `measurable_pw`. Simplify using `only [f, hp, if_false]`. Conclude with `measurable_one.indicator measurableSet_closedBall`. Set `U : (Low 4 → ℂ) → ℝ≥0∞` to `fun w => ∏ p, f p (w p)`.

Establish `hU : Measurable U` using `Finset.measurable_prod _ fun p _ => (hf p).comp (measurable_pi_apply p)`. Establish `hUfin : ∫⁻ w, U w < ⊤`. Use `GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (μ := fun _ : Low 4 => (volume : Measure ℂ)) (fun p => (hf p).aemeasurable)` as an intermediate fact. Rewrite using `[volume_pi, this]`. Use `ENNReal.prod_lt_top fun p _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hp : p ∈ S`. Simplify using `only [f, hp, if_true]`. Conclude with `lintegral_pw_lt_top`. Simplify using `only [f, hp, if_false]`. Rewrite using `[lintegral_indicator measurableSet_closedBall]`.

Simplify using `using (measure_closedBall_lt_top (μ := (volume : Measure ℂ)) (x := 0) (r := 1))`. Establish `hUeq : ∀ w : Low 4 → ℂ, (∀ p, p ∉ S → ‖w p‖ ≤ 1) → U w = ENNReal.ofReal (pw (w pa)) * ENNReal.ofReal (pw (w pb)) * ENNReal.ofReal (pw (w pc))`. Introduce `w hw`. Simplify using `only [U, f]`. Rewrite using `[Finset.prod_ite, Finset.prod_eq_one (s := Finset.univ.filter (fun p => p ∉ S)) ?_, mul_one]`.

Rewrite using `[Finset.filter_mem_eq_inter, Finset.univ_inter, hS, Finset.prod_insert, Finset.prod_insert, Finset.prod_singleton, mul_assoc]`. Simplify using `using hcb.symm`. Simplify using `[hab, hac]`. Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp`.

Simplify using `[Set.indicator, hw p hp]`. Establish `hpt : ∀ w, hB p0 w ≤ U w + U (Function.update w pb (w pb - w pa * w pc))`. Introduce `w`. Distinguish the cases in `hw : w ∈ {w : Low 4 → ℂ | ∀ p : Low 4, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}`. Establish `hw' : ∀ p, p ∉ S → ‖w p‖ ≤ 1` using `fun p hp => by`.

Establish `h1 : p ≠ pa` using `fun h => hp (by simp [hS, h])`. Establish `h2 : p ≠ pb` using `fun h => hp (by simp [hS, h])`. Establish `h3 : p ≠ pc` using `fun h => hp (by simp [hS, h])`. Take `⟨k1, k2⟩` from `hmix p h1 h2 h3`. Conclude with `hw p k1 k2`.

Establish `hw'' : ∀ p, p ∉ S → ‖Function.update w pb (w pb - w pa * w pc) p‖ ≤ 1` using `fun p hp => by`. Establish `: p ≠ pb` using `fun h => hp (by simp [hS, h])`. Rewrite using `[Function.update_of_ne this]`. Conclude with `hw' p hp`. Rewrite using `[hUeq w hw', hUeq _ hw'']`.

Simplify using `only [Function.update_self, Function.update_of_ne hab, Function.update_of_ne hcb]`. Establish `n1` using `pw_nonneg (w pa)`. Establish `n2` using `pw_nonneg (w pb)`. Establish `n3` using `pw_nonneg (w pc)`. Establish `n4` using `pw_nonneg (w pb - w pa * w pc)`.

Unfold `hB`. Rewrite using `[Set.indicator_of_mem hw, ← ENNReal.ofReal_mul n1, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul n1, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[hg w]`. Establish `key` using `GlobalTheory.T.flagGram_density_inequality_complex (w pa) (w pb) (w pc)`.

Establish `e : pw (w pb - w pa * w pc) = (1 + ‖w pa * w pc - w pb‖ ^ 2) ^ (-(4 / 3 : ℝ))`. Simplify using `only [pw, norm_sub_rev (w pb)]`. Rewrite using `[e]`. Simplify using `only [pw]`. Combine the equalities or inequalities in the displayed calculation.

Unfold `hB`. Rewrite using `[Set.indicator_of_notMem hw]`. Conclude with `zero_le'`. Establish `hgm : Measurable fun w : Low 4 → ℂ => w pa * w pc` using `(measurable_pi_apply pa).mul (measurable_pi_apply pc)`. Establish `hgi : ∀ w v : Low 4 → ℂ, (∀ j, j ≠ pb → w j = v j) → w pa * w pc = v pa * v pc`.

Introduce `w v h`. Rewrite using `[h pa hab, h pc hcb]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[GlobalTheory.T.lintegral_update_sub_shear' pb (fun w => w pa * w pc) hgm hgi U hU]`. Use `_ < ⊤ := ENNReal.add_lt_top.2 ⟨hUfin, hUfin⟩`.
-/
theorem lintegral_hB_lt_top_of_pos (p0 : ℕ) (pa pb pc : Low 4) (hab : pa ≠ pb) (hcb : pc ≠ pb)
    (hac : pa ≠ pc)
    (hg : ∀ w : Low 4 → ℂ, gB p0 w = ((1 + ‖w pa‖ ^ 2 + ‖w pb‖ ^ 2) ^ 2 *
      (1 + ‖w pc‖ ^ 2 + ‖w pa * w pc - w pb‖ ^ 2) ^ 2)⁻¹)
    (hmix : ∀ p : Low 4, p ≠ pa → p ≠ pb → p ≠ pc → (p.1.2 : ℕ) < p0 ∧ p0 ≤ (p.1.1 : ℕ)) :
    ∫⁻ w : Low 4 → ℂ, hB p0 w < ⊤ := by
  set S : Finset (Low 4) := {pa, pb, pc} with hS
  let f : Low 4 → ℂ → ℝ≥0∞ := fun p x =>
    if p ∈ S then ENNReal.ofReal (pw x) else (Metric.closedBall (0 : ℂ) 1).indicator 1 x
  have hf : ∀ p, Measurable (f p) := by
    intro p; by_cases hp : p ∈ S
    · simp only [f, hp, if_true]; exact measurable_pw
    · simp only [f, hp, if_false]; exact measurable_one.indicator measurableSet_closedBall
  let U : (Low 4 → ℂ) → ℝ≥0∞ := fun w => ∏ p, f p (w p)
  have hU : Measurable U := Finset.measurable_prod _ fun p _ => (hf p).comp (measurable_pi_apply p)
  have hUfin : ∫⁻ w, U w < ⊤ := by
    have := GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (μ := fun _ : Low 4 => (volume : Measure ℂ))
      (fun p => (hf p).aemeasurable)
    rw [volume_pi, this]
    refine ENNReal.prod_lt_top fun p _ => ?_
    by_cases hp : p ∈ S
    · simp only [f, hp, if_true]; exact lintegral_pw_lt_top
    · simp only [f, hp, if_false]
      rw [lintegral_indicator measurableSet_closedBall]
      simpa using (measure_closedBall_lt_top (μ := (volume : Measure ℂ)) (x := 0) (r := 1))
  have hUeq : ∀ w : Low 4 → ℂ, (∀ p, p ∉ S → ‖w p‖ ≤ 1) →
      U w = ENNReal.ofReal (pw (w pa)) * ENNReal.ofReal (pw (w pb)) * ENNReal.ofReal (pw (w pc)) := by
    intro w hw
    simp only [U, f]
    rw [Finset.prod_ite, Finset.prod_eq_one (s := Finset.univ.filter (fun p => p ∉ S)) ?_, mul_one]
    · rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hS, Finset.prod_insert, Finset.prod_insert,
        Finset.prod_singleton, mul_assoc]
      · simpa using hcb.symm
      · simp [hab, hac]
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [Set.indicator, hw p hp]
  have hpt : ∀ w, hB p0 w ≤ U w + U (Function.update w pb (w pb - w pa * w pc)) := by
    intro w
    by_cases hw : w ∈ {w : Low 4 → ℂ | ∀ p : Low 4, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
    · have hw' : ∀ p, p ∉ S → ‖w p‖ ≤ 1 := fun p hp => by
        have h1 : p ≠ pa := fun h => hp (by simp [hS, h])
        have h2 : p ≠ pb := fun h => hp (by simp [hS, h])
        have h3 : p ≠ pc := fun h => hp (by simp [hS, h])
        obtain ⟨k1, k2⟩ := hmix p h1 h2 h3
        exact hw p k1 k2
      have hw'' : ∀ p, p ∉ S → ‖Function.update w pb (w pb - w pa * w pc) p‖ ≤ 1 := fun p hp => by
        have : p ≠ pb := fun h => hp (by simp [hS, h])
        rw [Function.update_of_ne this]; exact hw' p hp
      rw [hUeq w hw', hUeq _ hw'']
      simp only [Function.update_self, Function.update_of_ne hab, Function.update_of_ne hcb]
      have n1 := pw_nonneg (w pa)
      have n2 := pw_nonneg (w pb)
      have n3 := pw_nonneg (w pc)
      have n4 := pw_nonneg (w pb - w pa * w pc)
      unfold hB
      rw [Set.indicator_of_mem hw, ← ENNReal.ofReal_mul n1, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul n1, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [hg w]
      have key := GlobalTheory.T.flagGram_density_inequality_complex (w pa) (w pb) (w pc)
      have e : pw (w pb - w pa * w pc) = (1 + ‖w pa * w pc - w pb‖ ^ 2) ^ (-(4 / 3 : ℝ)) := by
        simp only [pw, norm_sub_rev (w pb)]
      rw [e]
      simp only [pw]
      calc _ ≤ _ := key
        _ = _ := by ring
    · unfold hB; rw [Set.indicator_of_notMem hw]; exact zero_le'
  have hgm : Measurable fun w : Low 4 → ℂ => w pa * w pc :=
    (measurable_pi_apply pa).mul (measurable_pi_apply pc)
  have hgi : ∀ w v : Low 4 → ℂ, (∀ j, j ≠ pb → w j = v j) → w pa * w pc = v pa * v pc := by
    intro w v h; rw [h pa hab, h pc hcb]
  calc ∫⁻ w, hB p0 w ≤ ∫⁻ w, (U w + U (Function.update w pb (w pb - w pa * w pc))) :=
        lintegral_mono hpt
    _ = (∫⁻ w, U w) + ∫⁻ w, U (Function.update w pb (w pb - w pa * w pc)) :=
        lintegral_add_left hU _
    _ = (∫⁻ w, U w) + ∫⁻ w, U w := by
        rw [GlobalTheory.T.lintegral_update_sub_shear' pb (fun w => w pa * w pc) hgm hgi U hU]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hUfin, hUfin⟩

/- English proof (translation)
Introduce and unpack `p0 (rfl | rfl)`. Conclude with `lintegral_hB_lt_top_of_pos 1 ⟨(2, 1), by decide⟩ ⟨(3, 1), by decide⟩ ⟨(3, 2), by decide⟩ (by decide) (by decide) (by decide) (fun w => gB_eq_entries 1 _ _ _ w rfl rfl rfl) (by decide)`. Conclude with `lintegral_hB_lt_top_of_pos 3 ⟨(1, 0), by decide⟩ ⟨(2, 0), by decide⟩ ⟨(2, 1), by decide⟩ (by decide) (by decide) (by decide) (fun w => gB_eq_entries 3 _ _ _ w rfl rfl rfl) (by decide)`.
-/
theorem lintegral_hB_four_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 3) → ∫⁻ w : Low 4 → ℂ, hB p0 w < ⊤ := by
  rintro p0 (rfl | rfl)
  · exact lintegral_hB_lt_top_of_pos 1 ⟨(2, 1), by decide⟩ ⟨(3, 1), by decide⟩ ⟨(3, 2), by decide⟩
      (by decide) (by decide) (by decide) (fun w => gB_eq_entries 1 _ _ _ w rfl rfl rfl) (by decide)
  · exact lintegral_hB_lt_top_of_pos 3 ⟨(1, 0), by decide⟩ ⟨(2, 0), by decide⟩ ⟨(2, 1), by decide⟩
      (by decide) (by decide) (by decide) (fun w => gB_eq_entries 3 _ _ _ w rfl rfl rfl) (by decide)
end
end GlobalTheory.IntBall.Fin4
