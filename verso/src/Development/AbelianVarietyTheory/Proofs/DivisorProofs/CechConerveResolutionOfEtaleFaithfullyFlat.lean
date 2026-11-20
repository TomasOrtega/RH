import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatRingHomBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveEtaleSectionBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveChainsQuasiIsoOfLocallySurjectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem preservesColimitsOfShape_spec_yoneda (J : Type) [SmallCategory J] :
    PreservesColimitsOfShape J (Scheme.Spec.{0}.rightOp ⋙ (yoneda (C := Scheme.{0})).op) := by
  have h1 : PreservesColimitsOfShape J Scheme.Spec.{0}.rightOp := preservesColimitsOfShape_rightOp J _
  have h2 : PreservesColimitsOfShape J (yoneda (C := Scheme.{0})).op := preservesColimitsOfShape_op J _
  infer_instance

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem hyp_spec_coAug_of_etFF : ∀ (R : Type) [CommRing R] (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Hyp R (Scheme.Spec.rightOp ⋙ sch.op) (coAug g) := by
  intro R _ A B g hg k
  obtain ⟨h1, h2⟩ := (etFF_basic.2.1 A B g).1 hg
  exact GlobalTheory.T.cechConerve_chains_quasiIso_of_locallySurjective R CommRingCat.{0} (Scheme.Spec.{0}.rightOp ⋙ (yoneda (C := Scheme.{0})).op)
    (fun n => preservesColimitsOfShape_spec_yoneda _) A B g
    (locallySurjective_etale_section_baseChange.1 _ _ (Spec.map g) h1 h2)

end GlobalTheory.EtC
