import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CjDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAFTop

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open MeasureTheory Measure
open scoped NNReal

section Gen

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}

def phi (X : GL (Fin k) A) : (Fin k → A) ≃ₜ+ (Fin k → A) where
  toFun v := (X : Matrix (Fin k) (Fin k) A).mulVec v
  invFun v := ((X⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).mulVec v
  left_inv v := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  map_add' v w := Matrix.mulVec_add _ v w
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phi_apply (X : GL (Fin k) A) (v : Fin k → A) :
    phi X v = (X : Matrix (Fin k) (Fin k) A).mulVec v := rfl

def modM (X : GL (Fin k) A) : ℝ≥0 := addEquivAddHaarChar (phi X)

/- English proof (translation)
Apply `ContinuousAddEquiv.ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [ContinuousAddEquiv.trans_apply, phi_apply, Units.val_mul, Matrix.mulVec_mulVec]`.
-/
theorem phi_mul (X Y : GL (Fin k) A) : phi (X * Y) = (phi Y).trans (phi X) := by
  apply ContinuousAddEquiv.ext
  intro v
  simp only [ContinuousAddEquiv.trans_apply, phi_apply, Units.val_mul, Matrix.mulVec_mulVec]

/- English proof (translation)
Simplify using `only [modM, phi_mul, addEquivAddHaarChar_trans, mul_comm]`.
-/
theorem modM_mul (X Y : GL (Fin k) A) : modM (X * Y) = modM X * modM Y := by
  simp only [modM, phi_mul, addEquivAddHaarChar_trans, mul_comm]

/- English proof (translation)
Establish `h : phi (1 : GL (Fin k) A) = ContinuousAddEquiv.refl _`. Apply `ContinuousAddEquiv.ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[phi_apply]`. Simplify using `only [modM, h, addEquivAddHaarChar_refl]`.
-/
theorem modM_one : modM (1 : GL (Fin k) A) = 1 := by
  have h : phi (1 : GL (Fin k) A) = ContinuousAddEquiv.refl _ := by
    apply ContinuousAddEquiv.ext
    intro v
    simp [phi_apply]
  simp only [modM, h, addEquivAddHaarChar_refl]

/- English proof (translation)
Establish `h : modM X⁻¹ * modM X = 1` using `by rw [← modM_mul, inv_mul_cancel, modM_one]`. Conclude with `eq_inv_of_mul_eq_one_left h`.
-/
theorem modM_inv (X : GL (Fin k) A) : modM X⁻¹ = (modM X)⁻¹ := by
  have h : modM X⁻¹ * modM X = 1 := by rw [← modM_mul, inv_mul_cancel, modM_one]
  exact eq_inv_of_mul_eq_one_left h

/- English proof (translation)
Establish `h` using `addEquivAddHaarChar_smul_map μ (phi X)`. Rewrite `h` using `[show addEquivAddHaarChar (phi X) = modM X from rfl, hX, one_smul]`. Then use the resulting hypothesis.
-/
theorem map_phi_of_modM (X : GL (Fin k) A) (hX : modM X = 1) (μ : Measure (Fin k → A))
    [μ.IsAddHaarMeasure] : μ.map (phi X) = μ := by
  have h := addEquivAddHaarChar_smul_map μ (phi X)
  rwa [show addEquivAddHaarChar (phi X) = modM X from rfl, hX, one_smul] at h

/- English proof (translation)
Establish `h1` using `addEquivAddHaarChar_smul_map μ (phi X)`. Rewrite `h1` using `[h]`. Take `⟨K, hK, hKn⟩` from `exists_compact_mem_nhds (0 : Fin k → A)`. Establish `hpos : μ K ≠ 0` using `(measure_pos_of_mem_nhds μ hKn).ne'`. Establish `hfin : μ K ≠ ⊤` using `hK.measure_lt_top.ne`.

Establish `h2` using `congrArg (fun ν : Measure (Fin k → A) => ν K) h1`. Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2`. Establish `h3 : ((modM X : ℝ≥0) : ENNReal) = 1`. Establish `h4 : (modM X : ENNReal) * μ K / μ K = 1 * μ K / μ K` using `by rw [one_mul]; exact congrArg (· / μ K) h2`. Rewrite `h4` using `[ENNReal.mul_div_cancel_right hpos hfin, ENNReal.mul_div_cancel_right hpos hfin]`. Then use the resulting hypothesis.

Conclude with `h3` after adjusting the coercions.
-/
theorem modM_of_map (X : GL (Fin k) A) (μ : Measure (Fin k → A)) [μ.IsAddHaarMeasure]
    (h : μ.map (phi X) = μ) : modM X = 1 := by
  have h1 := addEquivAddHaarChar_smul_map μ (phi X)
  rw [h] at h1
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : Fin k → A)
  have hpos : μ K ≠ 0 := (measure_pos_of_mem_nhds μ hKn).ne'
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h2 := congrArg (fun ν : Measure (Fin k → A) => ν K) h1
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  have h3 : ((modM X : ℝ≥0) : ENNReal) = 1 := by
    have h4 : (modM X : ENNReal) * μ K / μ K = 1 * μ K / μ K := by rw [one_mul]; exact congrArg (· / μ K) h2
    rwa [ENNReal.mul_div_cancel_right hpos hfin, ENNReal.mul_div_cancel_right hpos hfin] at h4
  exact_mod_cast h3

end Gen

end PI.VolSemiDirect.W.Cj
