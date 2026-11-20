import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfStalkwiseBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtC.LocGlobSp.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEquivOfStalkwiseBaseChange.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.equiv_of_stalkwise_base_change : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → Eqv R α F := by
  first
  | exact @GlobalTheory.EtC.LocGlobSp.main
  | exact GlobalTheory.EtC.LocGlobSp.main
  | (intros; apply GlobalTheory.EtC.LocGlobSp.main <;> assumption)
