import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStBA
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyIntegrable
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsHermFormCompare
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartHessCompare
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartDensityIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyIntegrableAlt

/- English proof (translation)
Establish `hx : (Fin.cons 1 y : Fin (e + 1) → ℂ) ≠ 0` using `fun h => by`. Use `congr_fun h 0` as an intermediate fact. Simplify using `at this`. Conclude with `hM.re_dotProduct_pos hx`.
-/
theorem quad_pos {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (y : Fin e → ℂ) :
    0 < (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re := by
  have hx : (Fin.cons 1 y : Fin (e + 1) → ℂ) ≠ 0 := fun h => by
    have := congr_fun h 0
    simp at this
  exact hM.re_dotProduct_pos hx

/- English proof (translation)
Establish `hz : Continuous fun y : Fin e → ℂ => (Fin.cons 1 y : Fin (e + 1) → ℂ)` using `continuous_const.finCons continuous_id`. Establish `hc : Continuous fun y : Fin e → ℂ => star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))` using `hz.star.dotProduct (continuous_const.matrix_mulVec hz)`. Conclude with `Real.measurable_log.comp (Real.continuous_sqrt.measurable.comp (Complex.measurable_re.comp hc.measurable))`.
-/
theorem measurable_hermChartPot {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    Measurable (hermChartPot M) := by
  have hz : Continuous fun y : Fin e → ℂ => (Fin.cons 1 y : Fin (e + 1) → ℂ) :=
    continuous_const.finCons continuous_id
  have hc : Continuous fun y : Fin e → ℂ =>
      star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) :=
    hz.star.dotProduct (continuous_const.matrix_mulVec hz)
  exact Real.measurable_log.comp (Real.continuous_sqrt.measurable.comp (Complex.measurable_re.comp hc.measurable))

/- English proof (translation)
Take `⟨c, hc, h1⟩` from `hCmp _ M N hM hN`. Take `⟨c', hc', h2⟩` from `hCmp _ N M hN hM`. Use `⟨|Real.log c| + |Real.log c'|, fun y => ?_⟩` and prove the remaining obligations. Establish `hqM` using `quad_pos hM y`. Establish `hqN` using `quad_pos hN y`.

Establish `a1` using `Real.log_le_log hqM (h1 (Fin.cons 1 y))`. Establish `a2` using `Real.log_le_log hqN (h2 (Fin.cons 1 y))`. Rewrite `a1` using `[Real.log_mul hc.ne' hqN.ne']`. Rewrite `a2` using `[Real.log_mul hc'.ne' hqM.ne']`. Simplify using `only [hermChartPot, Real.log_sqrt hqM.le, Real.log_sqrt hqN.le, Real.norm_eq_abs]`.

Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith [le_abs_self (Real.log c), le_abs_self (Real.log c'), abs_nonneg (Real.log c), abs_nonneg (Real.log c')]`.
-/
theorem pot_sub_bound (hCmp : HermFormCompare.Statement) {e : ℕ} {M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ}
    (hM : M.PosDef) (hN : N.PosDef) :
    ∃ K : ℝ, ∀ y : Fin e → ℂ, ‖hermChartPot M y - hermChartPot N y‖ ≤ K := by
  obtain ⟨c, hc, h1⟩ := hCmp _ M N hM hN
  obtain ⟨c', hc', h2⟩ := hCmp _ N M hN hM
  refine ⟨|Real.log c| + |Real.log c'|, fun y => ?_⟩
  have hqM := quad_pos hM y
  have hqN := quad_pos hN y
  have a1 := Real.log_le_log hqM (h1 (Fin.cons 1 y))
  have a2 := Real.log_le_log hqN (h2 (Fin.cons 1 y))
  rw [Real.log_mul hc.ne' hqN.ne'] at a1
  rw [Real.log_mul hc'.ne' hqM.ne'] at a2
  simp only [hermChartPot, Real.log_sqrt hqM.le, Real.log_sqrt hqN.le, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log c), le_abs_self (Real.log c'), abs_nonneg (Real.log c),
    abs_nonneg (Real.log c')]

/- English proof (translation)
Use `set HM := cxHessian (hermChartPot M) y`. Use `set HN := cxHessian (hermChartPot N) y`. Use `set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => if (j : ℕ) < k then HM else HN with hAdef`. Establish `hA : (fun j : Fin e => cxHessian (if (j : ℕ) < k then hermChartPot M else hermChartPot N) y) = A`. Use function extensionality and compare the values at `j`.

Simplify using `only [hAdef]`. Apply the tactic sequence `split_ifs <;> rfl`. Use `set B : Fin e → Matrix (Fin e) (Fin e) ℂ := fun _ => ((max C 1 : ℝ) : ℂ) • HN with hBdef`. Establish `hApsd : ∀ j, (A j).PosSemidef` using `fun j => by`. Simplify using `only [hAdef]`.

Use `split_ifs`. Conclude with `hMp`. Conclude with `hNp`. Establish `hsm : ∀ r : ℝ, 0 ≤ r → (((r : ℝ) : ℂ) • HN).PosSemidef` using `fun r hr => hNp.smul (Complex.zero_le_real.2 hr)`. Establish `hAB : ∀ j, (B j - A j).PosSemidef` using `fun j => by`.

Simplify using `only [hBdef, hAdef]`. Use `split_ifs`. Establish `h : ((max C 1 : ℝ) : ℂ) • HN - HM = ((C : ℂ) • HN - HM) + (((max C 1 - C : ℝ)) : ℂ) • HN`. Use `push_cast`. Rewrite using `[sub_smul]`.

Normalize the expressions using the abelian group laws. Rewrite using `[h]`. Conclude with `hle.add (hsm _ (sub_nonneg.2 (le_max_left C 1)))`. Establish `h : ((max C 1 : ℝ) : ℂ) • HN - HN = (((max C 1 - 1 : ℝ)) : ℂ) • HN`. Use `push_cast`.

Rewrite using `[sub_smul, one_smul]`. Rewrite using `[h]`. Conclude with `hsm _ (sub_nonneg.2 (le_max_right C 1))`. Establish `hmono : (mixedDisc A).re ≤ (mixedDisc B).re` using `ReciprocityTheory.AnForm.A.mdisc_re_mono A B hApsd hAB`. Establish `hnn : 0 ≤ (mixedDisc A).re` using `(ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hApsd).2`.

Establish `hB : mixedDisc B = ((max C 1 : ℝ) : ℂ) ^ e * HN.det`. Establish `h` using `ReciprocityTheory.AnForm.A.mdisc_const (((max C 1 : ℝ) : ℂ) • HN)`. Rewrite `h` using `[det_smul, Fintype.card_fin]`. Conclude with `h`. Establish `hN1 : mixedDisc (fun _ : Fin e => HN) = HN.det` using `ReciprocityTheory.AnForm.A.mdisc_const HN`.

Establish `hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e` using `by positivity`. Unfold `maDensity`. Rewrite using `[hA, hN1, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, abs_of_nonneg hnn]`. Rewrite `hmono` using `[hB, ← Complex.ofReal_pow, Complex.re_ofReal_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem abs_maDensity_mix_le {e : ℕ} {M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (k : ℕ) (C : ℝ) (y : Fin e → ℂ)
    (hMp : (cxHessian (hermChartPot M) y).PosSemidef) (hNp : (cxHessian (hermChartPot N) y).PosSemidef)
    (hle : ((C : ℂ) • cxHessian (hermChartPot N) y - cxHessian (hermChartPot M) y).PosSemidef) :
    ‖maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y‖ ≤
      max C 1 ^ e * maDensity (fun _ : Fin e => hermChartPot N) y := by
  set HM := cxHessian (hermChartPot M) y
  set HN := cxHessian (hermChartPot N) y
  set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => if (j : ℕ) < k then HM else HN with hAdef
  have hA : (fun j : Fin e => cxHessian (if (j : ℕ) < k then hermChartPot M else hermChartPot N) y) = A := by
    funext j
    simp only [hAdef]
    split_ifs <;> rfl
  set B : Fin e → Matrix (Fin e) (Fin e) ℂ := fun _ => ((max C 1 : ℝ) : ℂ) • HN with hBdef
  have hApsd : ∀ j, (A j).PosSemidef := fun j => by
    simp only [hAdef]
    split_ifs
    · exact hMp
    · exact hNp
  have hsm : ∀ r : ℝ, 0 ≤ r → (((r : ℝ) : ℂ) • HN).PosSemidef := fun r hr =>
    hNp.smul (Complex.zero_le_real.2 hr)
  have hAB : ∀ j, (B j - A j).PosSemidef := fun j => by
    simp only [hBdef, hAdef]
    split_ifs
    · have h : ((max C 1 : ℝ) : ℂ) • HN - HM = ((C : ℂ) • HN - HM) + (((max C 1 - C : ℝ)) : ℂ) • HN := by
        push_cast
        rw [sub_smul]
        abel
      rw [h]
      exact hle.add (hsm _ (sub_nonneg.2 (le_max_left C 1)))
    · have h : ((max C 1 : ℝ) : ℂ) • HN - HN = (((max C 1 - 1 : ℝ)) : ℂ) • HN := by
        push_cast
        rw [sub_smul, one_smul]
      rw [h]
      exact hsm _ (sub_nonneg.2 (le_max_right C 1))
  have hmono : (mixedDisc A).re ≤ (mixedDisc B).re := ReciprocityTheory.AnForm.A.mdisc_re_mono A B hApsd hAB
  have hnn : 0 ≤ (mixedDisc A).re := (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hApsd).2
  have hB : mixedDisc B = ((max C 1 : ℝ) : ℂ) ^ e * HN.det := by
    have h := ReciprocityTheory.AnForm.A.mdisc_const (((max C 1 : ℝ) : ℂ) • HN)
    rw [det_smul, Fintype.card_fin] at h
    exact h
  have hN1 : mixedDisc (fun _ : Fin e => HN) = HN.det := ReciprocityTheory.AnForm.A.mdisc_const HN
  have hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
  unfold maDensity
  rw [hA, hN1, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, abs_of_nonneg hnn]
  rw [hB, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hmono
  calc (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc A).re
      ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * (max C 1 ^ e * HN.det.re) :=
        mul_le_mul_of_nonneg_left hmono hc
    _ = _ := by ring

end ChartEnergyIntegrableAlt

open ChartEnergyIntegrableAlt in

/- English proof (translation)
Introduce `e M N hM hN k`. Take `⟨C, hC⟩` from `hHess e M N hM hN`. Take `⟨C₀, hC₀⟩` from `hHess e N N hN hN`. Take `⟨K, hK⟩` from `pot_sub_bound hCmp hM hN`. Establish `hmix : Integrable (fun y : Fin e → ℂ => maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y)`.

Use `Integrable.mono' ((ChartDensityIntegrable.proof e N hN).const_mul (max C 1 ^ e)) (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_measurable_maDensity _).aestronglyMeasurable (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Conclude with `abs_maDensity_mix_le k C y (hC y).1.posSemidef (hC₀ y).1.posSemidef (hC y).2`. Conclude with `hmix.bdd_mul ((measurable_hermChartPot M).sub (measurable_hermChartPot N)).aestronglyMeasurable (Eventually.of_forall hK)`.
-/
theorem ChartEnergyIntegrable.proof (hCmp : HermFormCompare.Statement) (hHess : ChartHessCompare.Statement) :
    ChartEnergyIntegrable.Statement := by
  intro e M N hM hN k
  obtain ⟨C, hC⟩ := hHess e M N hM hN
  obtain ⟨C₀, hC₀⟩ := hHess e N N hN hN
  obtain ⟨K, hK⟩ := pot_sub_bound hCmp hM hN
  have hmix : Integrable (fun y : Fin e → ℂ =>
      maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y) := by
    refine Integrable.mono' ((ChartDensityIntegrable.proof e N hN).const_mul (max C 1 ^ e))
      (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_measurable_maDensity _).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    exact abs_maDensity_mix_le k C y (hC y).1.posSemidef (hC₀ y).1.posSemidef (hC y).2
  exact hmix.bdd_mul ((measurable_hermChartPot M).sub (measurable_hermChartPot N)).aestronglyMeasurable
    (Eventually.of_forall hK)

end

end GroundTheory.Heights₂.Heights
