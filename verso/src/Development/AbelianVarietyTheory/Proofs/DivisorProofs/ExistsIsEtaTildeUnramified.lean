import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.WeilParts

/- English proof (translation)
Take `⟨χ, h1, h2, h3, h4⟩` from `GlobalTheory.Mem.EtaTilde.exists_etaTilde D`. Conclude with `⟨χ, h1, h4, h3, h2⟩`.
-/
theorem exists_isEtaTilde_unramified (D : D7) : ∃ η, IsEtaTilde D η := by
  obtain ⟨χ, h1, h2, h3, h4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  exact ⟨χ, h1, h4, h3, h2⟩

end GlobalTheory.WeilParts
