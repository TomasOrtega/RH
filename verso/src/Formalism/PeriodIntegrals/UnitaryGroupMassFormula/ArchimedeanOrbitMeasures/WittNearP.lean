import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacOneOfCharts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WittInfHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.RmulFactsHolds

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

/- English proof (translation)
Introduce `D X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T hTm hU`. Take `⟨-, hmul, hsm, hgr, hcT, hc1, -, -⟩` from `rmulFacts_holds X`. Take `⟨u, hu⟩` from `hU`. Use `set w : TupI X := rmulT X (↑u⁻¹ : MfI X) (rmulT X (a T) (Y0 X u')) with hw`. Establish `hgT : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a T) (Y0 X u')) = (T : Matrix _ _ _)` using `hC.2.2.2 T hTm.1`.

Establish `hgT₂ : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a₂ T) (Y0 X u')) = (T : Matrix _ _ _)` using `hC₂.2.2.2 T hTm.2`. Establish `hY0 : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (Y0 X u') = (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F))` using `gramR_ratTup (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))`. Establish `hinv1 : cTI X (↑u⁻¹ : MfI X) * cTI X (↑u : MfI X) = 1`. Rewrite using `[← hcT, Units.mul_inv, hc1]`. Establish `hgw : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J w = (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F))`.

Rewrite using `[hw, hgr, hgT, ← hgT₂, ← hu, hgr, hY0]`. Rewrite using `[show cTI X (↑u⁻¹ : MfI X) * (cTI X (↑u : MfI X) * (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) * (↑u : MfI X)) * (↑u⁻¹ : MfI X) = (cTI X (↑u⁻¹ : MfI X) * cTI X (↑u : MfI X)) * (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X. …`. Establish `h2 : Module.finrank X.B.I.F X.B.I.E = 2` using `X.B.I.cm.deg2`. Establish `hfix : ∀ b : X.B.I.E, X.B.I.cm.sig b = b ↔ b ∈ (algebraMap X.B.I.F X.B.I.E).range` using `fun b => X.B.I.cm.fixed b`. Establish `hinv : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x` using `fun x => star_star x`.

Establish `hJ : IsHermND X.B.I.cm.sig X.B.I.J`. Use `⟨fun i j => ?_, X.B.I.J_det⟩` and prove the remaining obligations. Use `congrFun (congrFun X.B.I.J_herm i) j` as an intermediate fact. Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this`. Conclude with `this`.

Establish `hdet` using `detNZ_holds X u' ψ hT μinf νinf fibInf hP`. Establish `hUC : PIW.AdelicOrbitU.UnitChoice (Ainf X.B.I.F)` using `PIW.AdelicOrbitU.uc_pi (fun v : NumberField.InfinitePlace X.B.I.F => v.Completion)`. Take `⟨g, hg⟩` from `PI.AprimeInfWitt.witt_R X.B.I.cm.sig h2 hfix hinv X.B.I.J hJ (tupH (frameOf X u')) hT hdet (Ainf X.B.I.F) hUC w hgw`. Use `⟨g, ?_⟩` and prove the remaining obligations. Establish `hback : rmulT X (↑u : MfI X) w = rmulT X (a T) (Y0 X u')`.

Rewrite using `[hw, hmul, Units.inv_mul, rmulT_one]`. Rewrite using `[← hback, ← hu, hsm]`. Use `congr 1`. Conclude with `hg.symm`.
-/
theorem wittNear_holds : WittNear := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T hTm hU
  obtain ⟨-, hmul, hsm, hgr, hcT, hc1, -, -⟩ := rmulFacts_holds X
  obtain ⟨u, hu⟩ := hU
  set w : TupI X := rmulT X (↑u⁻¹ : MfI X) (rmulT X (a T) (Y0 X u')) with hw
  have hgT : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a T) (Y0 X u')) = (T : Matrix _ _ _) :=
    hC.2.2.2 T hTm.1
  have hgT₂ : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a₂ T) (Y0 X u')) = (T : Matrix _ _ _) :=
    hC₂.2.2.2 T hTm.2
  have hY0 : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (Y0 X u') =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) :=
    gramR_ratTup (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))
  have hinv1 : cTI X (↑u⁻¹ : MfI X) * cTI X (↑u : MfI X) = 1 := by
    rw [← hcT, Units.mul_inv, hc1]
  have hgw : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J w =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) := by
    rw [hw, hgr, hgT, ← hgT₂, ← hu, hgr, hY0]
    rw [show cTI X (↑u⁻¹ : MfI X) * (cTI X (↑u : MfI X) *
        (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) * (↑u : MfI X)) *
        (↑u⁻¹ : MfI X) = (cTI X (↑u⁻¹ : MfI X) * cTI X (↑u : MfI X)) *
        (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) *
        ((↑u : MfI X) * (↑u⁻¹ : MfI X)) by simp only [Matrix.mul_assoc],
      hinv1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  have h2 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have hfix : ∀ b : X.B.I.E, X.B.I.cm.sig b = b ↔ b ∈ (algebraMap X.B.I.F X.B.I.E).range :=
    fun b => X.B.I.cm.fixed b
  have hinv : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hJ : IsHermND X.B.I.cm.sig X.B.I.J := by
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hUC : PIW.AdelicOrbitU.UnitChoice (Ainf X.B.I.F) :=
    PIW.AdelicOrbitU.uc_pi (fun v : NumberField.InfinitePlace X.B.I.F => v.Completion)
  obtain ⟨g, hg⟩ := PI.AprimeInfWitt.witt_R X.B.I.cm.sig h2 hfix hinv X.B.I.J hJ (tupH (frameOf X u')) hT hdet
    (Ainf X.B.I.F) hUC w hgw
  refine ⟨g, ?_⟩
  have hback : rmulT X (↑u : MfI X) w = rmulT X (a T) (Y0 X u') := by
    rw [hw, hmul, Units.inv_mul, rmulT_one]
  rw [← hback, ← hu, hsm]
  congr 1
  exact hg.symm

end PI.AprimeInfW
