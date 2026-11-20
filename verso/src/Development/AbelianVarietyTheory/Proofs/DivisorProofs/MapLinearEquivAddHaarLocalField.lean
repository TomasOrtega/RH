import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

noncomputable section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped NNReal ENNReal

namespace GlobalTheory.KSp

/- English proof (translation)
Introduce `F _ _ _ _ _ V _ _ _ _ _ _ _ μ _ T`. Use `letI : MeasurableSpace F := borel F`. Use `haveI : BorelSpace F := ⟨rfl⟩`. Use `haveI := GlobalTheory.SplitWeil.secondCountable F`. Use `haveI := GlobalTheory.SplitWeil.t2Space F`.

Use `set n := Module.finrank F V`. Use `set b := Module.finBasis F V`. Use `set e : V ≃ₗ[F] (Fin n → F) := b.equivFun`. Use `haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V`. Use `haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup F V`.

Establish `hec : Continuous e` using `IsModuleTopology.continuous_of_linearMap e.toLinearMap`. Establish `hes : Continuous e.symm` using `IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap`. Set `E : V ≃L[F] (Fin n → F)` to `{ e with continuous_toFun := hec, continuous_invFun := hes }`. Set `Em : V ≃ᵐ (Fin n → F)` to `E.toHomeomorph.toMeasurableEquiv`. Establish `hEm : (Em : V → Fin n → F) = e` using `rfl`.

Establish `hEms : (Em.symm : (Fin n → F) → V) = e.symm` using `rfl`. Set `P : Measure (Fin n → F)` to `Measure.pi fun _ => (Measure.addHaar : Measure F)`. Use `set X := μ.map Em with hX`. Use `haveI : X.IsAddHaarMeasure := E.isAddHaarMeasure_map μ`. Use `set M := LinearMap.toMatrix b b T.toLinearMap`.

Establish `hM : ∀ y, M.mulVec (e y) = e (T y)` using `fun y => by`. Simplify using `[M, e, LinearMap.toMatrix_mulVec_repr]`. Establish `hdet : ((LinearEquiv.det T : Fˣ) : F) = M.det`. Simplify using `[M, LinearMap.det_toMatrix]`. Use `set d := distribHaarChar F (LinearEquiv.det T)`.

Establish `key : (d : ℝ≥0∞) • P.map M.mulVec = P` using `GlobalTheory.WeilM.smul_map_mulVec_pi (Measure.addHaar : Measure F) M (LinearEquiv.det T) hdet`. Establish `hd0 : (d : ℝ≥0∞) ≠ 0` using `by simpa using (distribHaarChar_pos (A := F) (g := LinearEquiv.det T)).ne'`. Establish `hPM : P.map M.mulVec = ((d⁻¹ : ℝ≥0) : ℝ≥0∞) • P` using `by conv_rhs => rw [← key]`. Rewrite using `[smul_smul, ENNReal.coe_inv (by simpa using hd0), ENNReal.inv_mul_cancel hd0 ENNReal.coe_ne_top, one_smul]`. Establish `hXP : X = (Measure.addHaarScalarFactor X P : ℝ≥0∞) • P` using `Measure.isAddLeftInvariant_eq_smul X P`.

Establish `hmv : Measurable M.mulVec` using `(continuous_const.matrix_mulVec continuous_id).measurable`. Establish `hXM : X.map M.mulVec = ((d⁻¹ : ℝ≥0) : ℝ≥0∞) • X`. Rewrite using `[hXP, Measure.map_smul, hPM, smul_comm]`. Establish `hμ : μ = X.map Em.symm` using `by rw [hX, Measure.map_map Em.symm.measurable Em.measurable]; simp`. Establish `hcomp : (T : V → V) ∘ Em.symm = Em.symm ∘ M.mulVec`.

Use function extensionality and compare the values at `x`. Use `show T (e.symm x) = e.symm (M.mulVec x)`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[← hM, e.apply_symm_apply, e.apply_symm_apply]`. Establish `hTm : Measurable (T : V → V)`.

Establish `: Continuous (T : V → V)` using `IsModuleTopology.continuous_of_linearMap T.toLinearMap`. Conclude with `this.measurable`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem map_linearEquiv_haar : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (T : V ≃ₗ[F] V), μ.map T = (distribHaarChar F (LinearEquiv.det T))⁻¹ • μ := by
  intro F _ _ _ _ _ V _ _ _ _ _ _ _ μ _ T
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable F
  haveI := GlobalTheory.SplitWeil.t2Space F
  set n := Module.finrank F V
  set b := Module.finBasis F V
  set e : V ≃ₗ[F] (Fin n → F) := b.equivFun
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup F V
  have hec : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hes : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

  let E : V ≃L[F] (Fin n → F) := { e with continuous_toFun := hec, continuous_invFun := hes }
  let Em : V ≃ᵐ (Fin n → F) := E.toHomeomorph.toMeasurableEquiv
  have hEm : (Em : V → Fin n → F) = e := rfl
  have hEms : (Em.symm : (Fin n → F) → V) = e.symm := rfl
  let P : Measure (Fin n → F) := Measure.pi fun _ => (Measure.addHaar : Measure F)
  set X := μ.map Em with hX
  haveI : X.IsAddHaarMeasure := E.isAddHaarMeasure_map μ
  set M := LinearMap.toMatrix b b T.toLinearMap
  have hM : ∀ y, M.mulVec (e y) = e (T y) := fun y => by
    simp [M, e, LinearMap.toMatrix_mulVec_repr]
  have hdet : ((LinearEquiv.det T : Fˣ) : F) = M.det := by
    simp [M, LinearMap.det_toMatrix]
  set d := distribHaarChar F (LinearEquiv.det T)
  have key : (d : ℝ≥0∞) • P.map M.mulVec = P :=
    GlobalTheory.WeilM.smul_map_mulVec_pi (Measure.addHaar : Measure F) M (LinearEquiv.det T) hdet
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by simpa using (distribHaarChar_pos (A := F) (g := LinearEquiv.det T)).ne'
  have hPM : P.map M.mulVec = ((d⁻¹ : ℝ≥0) : ℝ≥0∞) • P := by
    conv_rhs => rw [← key]
    rw [smul_smul, ENNReal.coe_inv (by simpa using hd0), ENNReal.inv_mul_cancel hd0 ENNReal.coe_ne_top,
      one_smul]
  have hXP : X = (Measure.addHaarScalarFactor X P : ℝ≥0∞) • P := Measure.isAddLeftInvariant_eq_smul X P
  have hmv : Measurable M.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  have hXM : X.map M.mulVec = ((d⁻¹ : ℝ≥0) : ℝ≥0∞) • X := by
    rw [hXP, Measure.map_smul, hPM, smul_comm]
  have hμ : μ = X.map Em.symm := by rw [hX, Measure.map_map Em.symm.measurable Em.measurable]; simp
  have hcomp : (T : V → V) ∘ Em.symm = Em.symm ∘ M.mulVec := by
    funext x
    show T (e.symm x) = e.symm (M.mulVec x)
    apply e.injective
    rw [← hM, e.apply_symm_apply, e.apply_symm_apply]
  have hTm : Measurable (T : V → V) := by
    have : Continuous (T : V → V) := IsModuleTopology.continuous_of_linearMap T.toLinearMap
    exact this.measurable
  calc μ.map T = (X.map Em.symm).map T := by rw [← hμ]
    _ = X.map ((T : V → V) ∘ Em.symm) := Measure.map_map hTm Em.symm.measurable
    _ = X.map (Em.symm ∘ M.mulVec) := by rw [hcomp]
    _ = (X.map M.mulVec).map Em.symm := (Measure.map_map Em.symm.measurable hmv).symm
    _ = (d⁻¹ : ℝ≥0) • μ := by rw [hXM, Measure.map_smul, ← hμ]; rfl

end GlobalTheory.KSp
