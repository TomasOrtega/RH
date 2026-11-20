import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleJOfParams
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAdmissibleJOfParams.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.admissible_J_of_params : ∀ (D : D7) (L : SizeData₂ D), SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → WeightParam D → BlockCharParam D → AdmissibleParameterJ.AdmPar L → AdmissibleParameterJ.AdmJ L := by
  first | exact @GlobalTheory.AdmJointAssembly.main | exact GlobalTheory.AdmJointAssembly.main | (intros; apply GlobalTheory.AdmJointAssembly.main <;> assumption)
