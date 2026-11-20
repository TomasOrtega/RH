import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushI

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def wEquiv (k : ℕ) : ((Fin k → ℂ) × ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ) where
  toFun := toW k
  invFun := ofW k
  map_add' p q := by
    funext j
    unfold toW
    by_cases h : j.val < k
    · simp only [dif_pos h, Prod.fst_add, Pi.add_apply]
    · simp only [dif_neg h, Prod.snd_add, Pi.add_apply]
  map_smul' c p := by
    funext j
    unfold toW
    by_cases h : j.val < k
    · simp only [dif_pos h, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]
    · simp only [dif_neg h, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
  left_inv := ofW_toW
  right_inv := toW_ofW

def blkLin (k : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ((Fin k → ℂ) × ℂ) →ₗ[ℂ] ((Fin k → ℂ) × ℂ) :=
  (((wEquiv k).symm : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] ((Fin k → ℂ) × ℂ)) : (Fin (k + 1) → ℂ) →ₗ[ℂ] ((Fin k → ℂ) × ℂ)) ∘ₗ
    Matrix.toLin' μ ∘ₗ (((wEquiv k).symm.symm : ((Fin k → ℂ) × ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ)) :
      ((Fin k → ℂ) × ℂ) →ₗ[ℂ] (Fin (k + 1) → ℂ))

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem blkLin_apply {k : ℕ} (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : (Fin k → ℂ) × ℂ) :
    blkLin k μ p = blkAct k μ p := by
  simp [blkLin, blkAct, wEquiv, Matrix.toLin'_apply]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem det_blkLin {k : ℕ} (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : LinearMap.det (blkLin k μ) = μ.det := by
  unfold blkLin
  rw [LinearMap.det_conj, LinearMap.det_toLin']

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem normSq_det_hb {k : ℕ} {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μᴴ * Hb k * μ = Hb k) :
    Complex.normSq μ.det = 1 := by
  have h := congrArg Matrix.det hμ
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hb : (Hb k).det ≠ 0 := by
    unfold Hb
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by split_ifs <;> norm_num
  have h2 : star μ.det * μ.det = 1 := by
    have e : (star μ.det * μ.det) * (Hb k).det = 1 * (Hb k).det := by
      rw [show (star μ.det * μ.det) * (Hb k).det = star μ.det * (Hb k).det * μ.det by ring, h, one_mul]
    exact mul_right_cancel₀ hb e
  have h3 : (Complex.normSq μ.det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h2
  exact_mod_cast h3

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem lebInvB : LebInvB := by
  intro k μ hμ
  have h1 : (volume : Measure ℂ).IsAddHaarMeasure := inferInstance
  have h2 : (volume : Measure (Fin k → ℂ)).IsAddHaarMeasure := inferInstance
  have h3 : (volume : Measure ((Fin k → ℂ) × ℂ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set f : ((Fin k → ℂ) × ℂ) →ₗ[ℝ] ((Fin k → ℂ) × ℂ) := (blkLin k μ).restrictScalars ℝ with hfdef
  have hdet : LinearMap.det f = 1 := by
    rw [hfdef, LinearMap.det_restrictScalars, det_blkLin, Algebra.norm_complex_apply, normSq_det_hb hμ]
  have hf : blkAct k μ = ⇑f := by
    funext p
    rw [hfdef, LinearMap.coe_restrictScalars, blkLin_apply]
  rw [hf, Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ((Fin k → ℂ) × ℂ)))
    (by rw [hdet]; norm_num), hdet]
  simp

end PI.RhsWLim.W
