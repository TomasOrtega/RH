import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OneLetterGaussEveryIntProof
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OneLetterGaussEveryOrthOf
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThmBGaussOrthOf
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThmBGaussIntOf
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.StructureTheoremCMOfUniformGaussModelsOfHypShape
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.GaussFormCMOfUniformGaussModelsOfHypShape
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NeZeroOfNorm
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KappaIntegralOfCalculation
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.IntegralOperatorTwoOrthogonal
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OneLetterGaussEveryPh
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThetaAdditiveHomogeneousHomothety
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.EvenDegreeWeightBounds
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThetaKappaShapeOfTransferIntegrality
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OneLetterGaussTranslateOfCmCase
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OfClosedInt
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OrthogonalShapeOneLetter
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormLeOneOfQuad
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KJoint
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormTwelveCubedEqOneOfFiveLePrime

namespace Formalism.L2.Th1.Top

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phMap : PhMap := PhMap_proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem calcC : CalcC := CalcC_proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem orthShape : OrthShape := OrthShape_of calcC
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem orthShapeOne : OrthShapeOne := orthogonal_shape_one_letter
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem goodModelAll : GoodModelAll := good_model_exists_all_primes
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem goodModelUniform : GoodModelUniform := good_model_uniform_homothety
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thetaZScale : ThetaZScale := theta_additive_homogeneous_homothety
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cmDatum : CMDatum := CMDatum_proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem shapeCM : ShapeCM := ShapeCM_of cmDatum
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetsCM : JetsCM := JetsCM_of cmDatum
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelJoint : KernelJoint := kernel_bounds_joint
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem calcP : CalcP := CalcP_of cmDatum
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kappa_integral : uniformGaussModelConditionReformulated := kappa_integral_of_calculation calcC
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hypShape : HypShape := HypShape_of calcC

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryInt : ThmAEntryInt := ThmAEntryInt_proof
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussInt : ThmAGaussInt := ThmAGaussInt_proof
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussInt : OneLetterGaussInt := OneLetterGaussInt_proof
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelInt : KernelInt := KernelInt_proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryEveryInt : ThmAEntryEveryInt := ThmAEntryEveryInt_proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussEveryInt : ThmAGaussEveryInt := ThmAGaussEveryInt_proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussEveryInt : OneLetterGaussEveryInt := OneLetterGaussEveryInt_proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelEveryInt : KernelEveryInt := KernelEveryInt_proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmSEveryInt : ThmSEveryInt := ThmSEveryInt_proof

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem modelInert (dK : ℕ) (L : PeriodPair) (hsq : Squarefree dK) (hmod : dK % 4 = 3)
    (hcm : Formalism.L2.Th1.CM.HasCMBy dK L) (l : ℕ) [Fact l.Prime] (h5 : 5 ≤ l) (hd : ¬ l ∣ dK)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) (ι : ℂ ≃+* ℂ_[l]) :
    ∃ g2 g3 ε : Formalism.L2.Th1.CM.MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 ∧ ‖ε‖ = 1 ∧
      ∀ n, ‖PowerSeries.coeff n (Formalism.L2.Th1.D.thetaS l g2 g3 ε)‖ ≤ 1 :=
  Formalism.L2.Th1.D.FAux.model l Formalism.L2.Th1.CM.cm2 Formalism.L2.Th1.CM.cm3 dK L hsq hmod hcm h5 hd hin ι

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryEveryPh : ThmAEntryEveryPh := ThmAEntryEveryPh_of hypShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussEveryPh : ThmAGaussEveryPh := ThmAGaussEveryPh_of hypShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussEveryPh : OneLetterGaussEveryPh := one_letter_gauss_every_ph
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelEveryPh : KernelEveryPh := KernelEveryPh_of hypShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmSEveryPh : ThmSEveryPh := ThmSEveryPh_of hypShape

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matrix_entries_cm_holds : MatrixEntriesCM := matrixEntriesCM_of_uniformGaussModels_of_hypShape kappa_integral hypShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gauss_form_cm_holds : GaussFormCM := gaussFormCM_of_uniformGaussModels_of_hypShape kappa_integral hypShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem one_letter_gauss_cm_holds : OneLetterGaussCMReformulated := oneLetterGaussCMReformulated_of_uniformGaussModels kappa_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem three_bounds_cm_holds : ThreeBoundsCM := threeBoundsCM_of_uniformGaussModels_of_hypShape kappa_integral hypShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem structure_theorem_cm_holds : StructureTheoremCM := structureTheoremCM_of_uniformGaussModels_of_hypShape kappa_integral hypShape

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryEveryOrth : ThmAEntryEveryOrth := ThmAEntryEveryOrth_of orthShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussEveryOrth : ThmAGaussEveryOrth := ThmAGaussEveryOrth_of orthShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussEveryOrth : OneLetterGaussEveryOrth := OneLetterGaussEveryOrth_of orthShapeOne
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelEveryOrth : KernelEveryOrth := KernelEveryOrth_of orthShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmSEveryOrth : ThmSEveryOrth := ThmSEveryOrth_of orthShape
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryOrth : ThmAEntryOrth := ThmAEntryOrth_of thmAEntryEveryOrth
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussOrth : ThmAGaussOrth := ThmAGaussOrth_of thmAGaussEveryOrth
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussOrth : OneLetterGaussOrth := OneLetterGaussOrth_of oneLetterGaussEveryOrth
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelOrth : KernelOrth := KernelOrth_of kernelEveryOrth

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryAll7 : ThmAEntryAll7 := matrix_entries_all_disc_seven
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussAll7 : ThmAGaussAll7 := gauss_form_all_disc_seven
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussAll7 : OneLetterGaussAll7 := one_letter_gauss_all_disc_seven
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryInt7 : ThmAEntryInt7 := matrix_entries_integral_disc_seven
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussInt7 : ThmAGaussInt7 := gauss_form_integral_disc_seven
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussInt7 : OneLetterGaussInt7 := one_letter_gauss_integral_disc_seven
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryEveryInt7 : ThmAEntryEveryInt7 := matrix_entries_every_integral_disc_seven
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussEveryInt7 : ThmAGaussEveryInt7 := gauss_form_every_integral_disc_seven
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussEveryInt7 : OneLetterGaussEveryInt7 := one_letter_gauss_every_integral_disc_seven
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryEveryPh7 : ThmAEntryEveryPh7 := ThmAEntryEveryPh7_of hypShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussEveryPh7 : ThmAGaussEveryPh7 := ThmAGaussEveryPh7_of hypShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussEveryPh7 : OneLetterGaussEveryPh7 := one_letter_gauss_every_principal_seven
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matrix_entries_sharp_cm_holds : MatrixEntriesSharpCM := matrix_entries_sharp_of_kappa_integral kappa_integral hypShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gauss_form_sharp_cm_holds : GaussFormSharpCM := gauss_form_sharp_of_kappa_integral kappa_integral hypShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem one_letter_gauss_sharp_cm_holds : OneLetterGaussSharpCM := one_letter_gauss_sharp_of_kappa_integral kappa_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryEveryOrth7 : ThmAEntryEveryOrth7 := ThmAEntryEveryOrth7_of orthShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussEveryOrth7 : ThmAGaussEveryOrth7 := ThmAGaussEveryOrth7_of orthShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussEveryOrth7 : OneLetterGaussEveryOrth7 := OneLetterGaussEveryOrth7_of orthShapeOne
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryOrth7 : ThmAEntryOrth7 := ThmAEntryOrth7_of thmAEntryEveryOrth7
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussOrth7 : ThmAGaussOrth7 := ThmAGaussOrth7_of thmAGaussEveryOrth7
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussOrth7 : OneLetterGaussOrth7 := OneLetterGaussOrth7_of oneLetterGaussEveryOrth7

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ltNormExists : LTNormExists := lubin_tate_norm_exists
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem transIntLT : TransIntLT := lubin_tate_transfer_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem local_kappa_shape_holds : uniformGaussModelConditionReformulated₂ := local_kappa_shape_of_transfer_integrality transIntLT
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem theta_kappa_shape_holds : uniformGaussModelConditionEquivalent := theta_kappa_shape_of_transfer_integrality transIntLT
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryEveryH : ThmAEntryEveryH := ThmAEntryEveryH_of matrix_entries_cm_holds ltNormExists theta_kappa_shape_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussEveryH : ThmAGaussEveryH := ThmAGaussEveryH_of gauss_form_cm_holds ltNormExists theta_kappa_shape_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussEveryH : OneLetterGaussEveryH :=
  OneLetterGaussEveryH_of one_letter_gauss_cm_holds ltNormExists theta_kappa_shape_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelEveryH : CMThetaKernelEveryInertPrime := KernelEveryH_of three_bounds_cm_holds ltNormExists theta_kappa_shape_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmSEveryH : ThmSEveryH := ThmSEveryH_of structure_theorem_cm_holds ltNormExists theta_kappa_shape_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem matrix_entries_sharp_translate_holds : MatrixEntriesSharpTranslate := matrix_entries_translate_of_cm_case matrix_entries_sharp_cm_holds ltNormExists theta_kappa_shape_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gauss_form_sharp_translate_holds : GaussFormSharpTranslate := gauss_form_translate_of_cm_case gauss_form_sharp_cm_holds ltNormExists theta_kappa_shape_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem one_letter_gauss_sharp_translate_holds : OneLetterGaussSharpTranslate :=
  one_letter_gauss_translate_of_cm_case one_letter_gauss_sharp_cm_holds ltNormExists theta_kappa_shape_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem shapeOrthD : ShapeOrthD := ShapeOrthD_of shapeCM kernelJoint
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmBOrth : ThmBOrth := ThmBOrth_of shapeCM kernelJoint
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmBGaussOrth : ThmBGaussOrth := ThmBGaussOrth_of shapeCM kernelJoint
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intOpOrth : IntOpOrth := IntOpOrth_of jetsCM kernelJoint
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intOpTwoOrth : IntOpTwoOrth := integral_operator_two_orthogonal

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmBInt : ThmBInt := ThmBInt_of calcP shapeCM
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmBGaussInt : ThmBGaussInt := ThmBGaussInt_of calcP shapeCM
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intOpInt : IntOpInt := IntOpInt_of calcP jetsCM

end Formalism.L2.Th1.Top
