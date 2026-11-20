import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.DividedPowerZeroOfGlActionZero
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ComponentsInFiltrationContractionSingle
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.AntitoneOfAppend
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.EqEmptyIffSplit
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.JointTypeLatticeSaturated
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.IntegralJointTypeSum
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftSubstitutionCoeffDivisible
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.CanonicalTranslateJetIdentity

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma adm_fourteen_of_adm {D : Formalism.BasicNotions.D7} (h : AdmB D) : JointComponentsPaths D := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
/- English proof (translation)
A detailed English derivation is pending.
-/
lemma adm_sixteen_of_adm {D : Formalism.BasicNotions.D7} (h : AdmB D) : PairedPathIndependence D := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
/- English proof (translation)
A detailed English derivation is pending.
-/
lemma adm_seventeen_of_adm {D : Formalism.BasicNotions.D7} (h : AdmB D) : PathBasisOverRing D := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nested_sets_lemma_of_admitted (D : Formalism.BasicNotions.D7) (h14 : JointComponentsPaths D) (h16 : PairedPathIndependence D) : ConclusionB3 D :=
  lemma_B3 D h16 (lemma_B2 D) (integral_joint_type_sum D h14 h16)

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem aux_of_valuationField_of_admB (D : Formalism.BasicNotions.D7) (hV : ValuationLemmaField D) (hB : AdmB D) : Conclusion2 D :=
  ⟨automorphicSideConclusion_of_pathBasis D (adm_seventeen_of_adm hB), prvA3_of_valuationField_of_admB D hV hB, prvB1_of_D7 D, lemma_B2 D,
    nested_sets_lemma_of_admitted D (adm_fourteen_of_adm hB) (adm_sixteen_of_adm hB), coefficientDependence D, canonical_translate_jet_identity D⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem hodgeTateFromSandwich (D : Formalism.BasicNotions.D7) : HodgeTateFromSandwich D := fun _ hV hB => aux_of_valuationField_of_admB D hV hB

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem part_two_closed_form (D : Formalism.BasicNotions.D7) : SecondPartClosed D := hodgeTateFromSandwich D

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem part_two_along_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : SecondPartFamily Fm := by
  intro _ hV hB
  obtain ⟨x0, h⟩ := hV
  exact ⟨x0, fun x hx i => aux_of_valuationField_of_admB _ (h x hx i) (hB x i)⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem part_two_closed_form_along_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : SecondPartFamilyClosed Fm := part_two_along_family Fm

end Formalism.MainNotions.LemmaBAlt
