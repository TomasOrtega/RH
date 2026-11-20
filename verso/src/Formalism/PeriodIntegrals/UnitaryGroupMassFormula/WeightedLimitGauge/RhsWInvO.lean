import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsHaar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvR

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

def UnimodK : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), IsHaarOn (UWset k r z) μ → μ Set.univ ≠ ⊤ →
    ∀ b ∈ UWset k r z, μ.map (rmulM b) = μ

def FibTrans : Prop :=
  ∀ (k r : ℕ) (z v v' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r v → inWb k r v' → 0 < Tz k r z →
    herm (Hpk k r) v v = herm (Hpk k r) v' v' → herm (Hpk k r) v z = herm (Hpk k r) v' z →
      ∃ u ∈ UWset k r z, u *ᵥ v = v'

def HypQ : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∃ Q : Measure (Fin (2 * r + k + 1) → ℂ), SigmaFinite Q ∧ (∀ s ∈ UWb k r, Q.map (fun v => s *ᵥ v) = Q) ∧
      Q {v | ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} = 0 ∧
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ v, g (herm (Hpk k r) v z) ∂Q = c * ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * g ζ

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

def Gf (μW : Measure (Mt k r)) (F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞) (v : Fin (2 * r + k + 1) → ℂ) : ℝ≥0∞ :=
  ∫⁻ h, F (Matrix.of h *ᵥ v) ∂μW

/- English proof (translation)
The claim follows from `Continuous.matrix_mulVec (continuous_snd (X := Fin (2 * r + k + 1) → ℂ) (Y := Mat k r)) continuous_fst`.
-/
theorem cont_act : Continuous (fun p : (Fin (2 * r + k + 1) → ℂ) × Mt k r => (Matrix.of p.2 : Mat k r) *ᵥ p.1) :=
  Continuous.matrix_mulVec (continuous_snd (X := Fin (2 * r + k + 1) → ℂ) (Y := Mat k r)) continuous_fst

/- English proof (translation)
The claim follows from `(hF.comp cont_act.measurable).lintegral_prod_right'`.
-/
theorem meas_Gf [SFinite μW] {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) : Measurable (Gf μW F) :=
  (hF.comp cont_act.measurable).lintegral_prod_right'

/- English proof (translation)
The claim follows from `continuous_const.dotProduct (continuous_const.matrix_mulVec continuous_id)`.
-/
theorem cont_herm (w : Fin (2 * r + k + 1) → ℂ) : Continuous (fun v => herm (Hpk k r) v w) :=
  continuous_const.dotProduct (continuous_const.matrix_mulVec continuous_id)

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]`.
-/
theorem herm_both {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) (hg : gᴴ * H * g = H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

/- English proof (translation)
Introduce `i hi`. Simplify using `only [Matrix.mulVec, dotProduct, MB.Em]`. Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg, zero_mul]`. Introduce `h`.

Rewrite `hi` using `[h]`. Use `m.isLt` as an intermediate fact. Simplify using `only [wI] at hi`. Use linear arithmetic over natural numbers and integers.
-/
theorem inWb_Em (u : Fin (k + 1) → ℂ) : inWb k r (MB.Em k r *ᵥ u) := by
  intro i hi
  simp only [Matrix.mulVec, dotProduct, MB.Em]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [if_neg, zero_mul]
  intro h
  rw [h] at hi
  have := m.isLt
  simp only [wI] at hi
  omega

/- English proof (translation)
Rewrite using `[← inWb_eq hz', Matrix.mulVec_mulVec, emb_mul_Em, ← Matrix.mulVec_mulVec]`. Conclude with `inWb_Em _`.
-/
theorem inWb_emb (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hz' : inWb k r z') : inWb k r (embWb k r μ *ᵥ z') := by
  rw [← inWb_eq hz', Matrix.mulVec_mulVec, emb_mul_Em, ← Matrix.mulVec_mulVec]
  exact inWb_Em _

/- English proof (translation)
Unfold `rhsW`. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `lintegral_congr fun ζ => ?_` and prove the remaining obligations. Establish `inner : ∀ h : Mt k r, ∫⁻ h', F (orbV k r z' (fun i j => (Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j)) ∂μW' = ENNReal.ofReal a' * F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z'))`. Introduce `h`.

Establish `hae : ∀ᵐ h' ∂μW', Matrix.of h' ∈ UWset k r z'`. Rewrite using `[ae_iff]`. Conclude with `hd.haarW'.2.2.1`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hae] with h' hh'`. Use `show F ((Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) *ᵥ z') = F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z'))`. Rewrite using `[← Matrix.mulVec_mulVec, inv_fix (HU.isUnit_of_uh hh'.1) hh'.2.2, ← Matrix.mulVec_mulVec]`. Use `_ = F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) * μW' Set.univ := lintegral_const _`. Use `_ = ENNReal.ofReal a' * F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) := by rw [hd.massW', mul_comm]`.

Repeatedly rewrite using `[inner]`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Unfold `Gf`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rhs_orb (hd : WbData k r z z' μW μW' a a' μsec) (F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞) :
    rhsW k r z z' μW μW' μsec (fun x => F (orbV k r z' x)) = ENNReal.ofReal a' *
      ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * Gf μW F (embWb k r (μsec ζ) *ᵥ z') := by
  unfold rhsW
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ζ => ?_
  have inner : ∀ h : Mt k r, ∫⁻ h', F (orbV k r z'
      (fun i j => (Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j)) ∂μW' =
        ENNReal.ofReal a' * F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) := by
    intro h
    have hae : ∀ᵐ h' ∂μW', Matrix.of h' ∈ UWset k r z' := by
      rw [ae_iff]
      exact hd.haarW'.2.2.1
    calc ∫⁻ h', F (orbV k r z' (fun i j => (Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j)) ∂μW'
        = ∫⁻ h', F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) ∂μW' := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with h' hh'
          show F ((Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) *ᵥ z') =
            F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z'))
          rw [← Matrix.mulVec_mulVec, inv_fix (HU.isUnit_of_uh hh'.1) hh'.2.2, ← Matrix.mulVec_mulVec]
      _ = F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) * μW' Set.univ := lintegral_const _
      _ = ENNReal.ofReal a' * F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) := by rw [hd.massW', mul_comm]
  simp_rw [inner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold Gf
  ring

/- English proof (translation)
Use `hW.1` as an intermediate fact. Unfold `Gf`. Rewrite using `[lintegral_lintegral_swap (μ := Q) (ν := μW) (f := fun v (h : Mt k r) => F (Matrix.of h *ᵥ v)) (hF.comp cont_act.measurable).aemeasurable]`. Establish `hae : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z`. Rewrite using `[ae_iff]`.

Conclude with `hW.2.2.1`. Establish `e : ∀ᵐ h ∂μW, ∫⁻ v, F (Matrix.of h *ᵥ v) ∂Q = ∫⁻ v, F v ∂Q` using `by filter_upwards [hae] with h hh`. Establish `hmv : Measurable (fun v : Fin (2 * r + k + 1) → ℂ => (Matrix.of h : Mat k r) *ᵥ v)` using `(continuous_const.matrix_mulVec continuous_id).measurable`. Rewrite using `[← lintegral_map hF hmv, hQ _ ⟨hh.1, hh.2.1⟩]`. Rewrite using `[lintegral_congr_ae e, lintegral_const, mul_comm]`.
-/
theorem avg_Q (Q : Measure (Fin (2 * r + k + 1) → ℂ)) [SigmaFinite Q] (hQ : ∀ s ∈ UWb k r, Q.map (fun v => s *ᵥ v) = Q)
    (hW : IsHaarOn (UWset k r z) μW) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ v, Gf μW F v ∂Q = μW Set.univ * ∫⁻ v, F v ∂Q := by
  have := hW.1
  unfold Gf
  rw [lintegral_lintegral_swap (μ := Q) (ν := μW) (f := fun v (h : Mt k r) => F (Matrix.of h *ᵥ v))
    (hF.comp cont_act.measurable).aemeasurable]
  have hae : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := by
    rw [ae_iff]
    exact hW.2.2.1
  have e : ∀ᵐ h ∂μW, ∫⁻ v, F (Matrix.of h *ᵥ v) ∂Q = ∫⁻ v, F v ∂Q := by
    filter_upwards [hae] with h hh
    have hmv : Measurable (fun v : Fin (2 * r + k + 1) → ℂ => (Matrix.of h : Mat k r) *ᵥ v) :=
      (continuous_const.matrix_mulVec continuous_id).measurable
    rw [← lintegral_map hF hmv, hQ _ ⟨hh.1, hh.2.1⟩]
  rw [lintegral_congr_ae e, lintegral_const, mul_comm]

/- English proof (translation)
Take `⟨u, hu, huv⟩` from `hT k r z v' v hz hv' hv hTz h1.symm h2.symm`. Establish `hm : Measurable (fun y : Mt k r => F (Matrix.of y *ᵥ v'))` using `hF.comp ((cont_act (k := k) (r := r)).comp (Continuous.prodMk continuous_const continuous_id)).measurable`. Unfold `Gf`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun h => ?_` and prove the remaining obligations.

Use `show F (Matrix.of h *ᵥ v) = F ((Matrix.of h * u) *ᵥ v')`. Rewrite using `[← Matrix.mulVec_mulVec, huv]`. Use `_ = ∫⁻ y, F (Matrix.of y *ᵥ v') ∂(μW.map (rmulM u)) := (lintegral_map hm (rmulM_cont u).measurable).symm`. Use `_ = ∫⁻ h, F (Matrix.of h *ᵥ v') ∂μW := by rw [hU k r z μW hW hfin u hu]`.
-/
theorem Gf_fib (hU : UnimodK) (hT : FibTrans) (hW : IsHaarOn (UWset k r z) μW) (hfin : μW Set.univ ≠ ⊤)
    (hz : inWb k r z) (hTz : 0 < Tz k r z) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F)
    {v v' : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hv' : inWb k r v')
    (h1 : herm (Hpk k r) v v = herm (Hpk k r) v' v') (h2 : herm (Hpk k r) v z = herm (Hpk k r) v' z) :
    Gf μW F v = Gf μW F v' := by
  obtain ⟨u, hu, huv⟩ := hT k r z v' v hz hv' hv hTz h1.symm h2.symm
  have hm : Measurable (fun y : Mt k r => F (Matrix.of y *ᵥ v')) :=
    hF.comp ((cont_act (k := k) (r := r)).comp (Continuous.prodMk continuous_const continuous_id)).measurable
  unfold Gf
  calc ∫⁻ h, F (Matrix.of h *ᵥ v) ∂μW = ∫⁻ h, (fun y : Mt k r => F (Matrix.of y *ᵥ v')) (rmulM u h) ∂μW := by
        refine lintegral_congr fun h => ?_
        show F (Matrix.of h *ᵥ v) = F ((Matrix.of h * u) *ᵥ v')
        rw [← Matrix.mulVec_mulVec, huv]
    _ = ∫⁻ y, F (Matrix.of y *ᵥ v') ∂(μW.map (rmulM u)) := (lintegral_map hm (rmulM_cont u).measurable).symm
    _ = ∫⁻ h, F (Matrix.of h *ᵥ v') ∂μW := by rw [hU k r z μW hW hfin u hu]

end PI.RhsWLim.W.RI
