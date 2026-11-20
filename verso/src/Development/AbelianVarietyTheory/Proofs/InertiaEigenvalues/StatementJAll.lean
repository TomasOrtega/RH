import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.JumpStatement

/- English proof (translation)
The claim follows from `GlobalTheory.JumpSets.stmtJ_holds`.
-/
theorem holds_all : ∀ D : D7, AdmissibleParameterJ.JumpBoundClosedForm D := GlobalTheory.JumpSets.stmtJ_holds

end GlobalTheory.JumpStatement
