import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMuP

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

def BetaSym : Prop := ∀ {D : D7} (X : HidaSetting D) (x y : EuclideanSpace ℝ (KapI X)), betaI X x y = betaI X y x

open Classical in

def MatND : Prop := ∀ {D : D7} (X : HidaSetting D), (matI X).det ≠ 0

section
variable {D : D7} (X : HidaSetting D)

open Classical in

def Alin : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) :=
  ((EuclideanSpace.equiv (KapI X) ℝ).toLinearEquiv.symm : (KapI X → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) ∘ₗ
    Matrix.toLin' (matI X) ∘ₗ
    ((EuclideanSpace.equiv (KapI X) ℝ).toLinearEquiv.symm.symm : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] (KapI X → ℝ))

open Classical in
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem det_Alin : LinearMap.det (Alin X) = (matI X).det := by
  rw [Alin, LinearMap.det_conj, LinearMap.det_toLin']

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_Alin (x y : EuclideanSpace ℝ (KapI X)) : ⟪x, Alin X y⟫ = betaI X x y := by
  classical
  rw [betaI_expand]
  simp only [Alin, PiLp.inner_apply, LinearMap.coe_comp, Function.comp_apply, Matrix.toLin'_apply,
    LinearEquiv.coe_coe]
  simp
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct]
  have hy : ∀ j, (EuclideanSpace.equiv (KapI X) ℝ) y j = y j := fun j => rfl
  simp only [hy]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end

open Classical in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Put the polynomial expressions in normal form.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem densMu_of (hS : BetaSym) (hN : MatND) : DensMu := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hdet : IsUnit (LinearMap.det (Alin X)) := by rw [det_Alin]; exact isUnit_iff_ne_zero.2 (hN X)
  let A : EuclideanSpace ℝ (KapI X) ≃L[ℝ] EuclideanSpace ℝ (KapI X) := (LinearMap.equivOfIsUnitDet hdet).toContinuousLinearEquiv
  have hAapp : ∀ y, A y = Alin X y := fun y => by simp [A, LinearMap.equivOfIsUnitDet_apply]
  have hAl : (A : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) = Alin X := LinearMap.ext hAapp
  have hAd : LinearMap.det (A : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) = (matI X).det := by
    rw [hAl, det_Alin]
  have hsym : ∀ x y, ⟪x, A y⟫ = ⟪A x, y⟫ := by
    intro x y
    rw [hAapp, hAapp, inner_Alin, real_inner_comm, inner_Alin, hS]
  have hν := FSD.selfDual_lin A hsym
  rw [hAd] at hν

  have hμ : SelfDual μinf (fun x y : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y)) :=
    hP.2.2.2.2.1
  have hμ' := selfDual_transport μinf _ (tupCoord X) (tupCoord_add X) hμ
  have hχ : (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
      ((tupCoord X).symm x) ((tupCoord X).symm y))) = fun x y => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) := by
    funext x y
    rw [hAapp, inner_Alin, psiInf_eq ψ hP.2.2.1, Real.fourierChar_apply]
    simp only [betaI]
    push_cast
    ring_nf
  rw [hχ] at hμ'
  haveI := hν.1
  have hB : ST.IsBichar (fun x y : EuclideanSpace ℝ (KapI X) => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ)) :=
    { addL := fun x x' y => by simp only [inner_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]
      addR := fun x y y' => by simp only [map_add, inner_add_right, AddChar.map_add_eq_mul, Circle.coe_mul]
      norm1 := fun x y => Circle.norm_coe _
      contL := fun y => (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_id.inner continuous_const)
      contR := fun x => (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_const.inner A.continuous) }
  obtain ⟨Φ, hc, hs, hI, z, hz⟩ := ST.testEx_bichar (ENNReal.ofReal (Real.sqrt |(matI X).det|) • (volume : Measure (EuclideanSpace ℝ (KapI X)))) hB
  exact SelfDual.eq_of_test hν hμ' Φ hc hs hI z hz

end PI.AprimeInfW
