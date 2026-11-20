import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

noncomputable section

namespace GlobalTheory.EigenProjector

/- English proof (translation)
Assemble the required witnesses or components as `⟨π, (D.Zgood_tie i π).1 hπ⟩`.
-/
theorem HG_of_mem_Zgood (D : D7) (i : D.nd.Loc) (π : D.nd.X i) (hπ : π ∈ D.nd.Zgood i) :
    HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩

end GlobalTheory.EigenProjector
