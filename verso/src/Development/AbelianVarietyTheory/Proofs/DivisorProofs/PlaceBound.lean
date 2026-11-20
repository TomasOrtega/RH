import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultSharpOfPlaceBound
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ResidueLevelMultiplicity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNumBlockSetsMulGammaTwoSidedBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityParabolicInductStatement

namespace GlobalTheory.FinGL.MultSharpObj

open GlobalTheory.FinGL Formalism.L2.DIV

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem placeBound : MultSharpPf.PlaceBound := by
  intro F _ _ ψ hψ r V _ _ _ b σ hσ ρ k hk hr hq
  rw [GlobalTheory.T.symmetricPositionCharMultiplicity_parabolicInduction F ψ hψ r V b σ hσ ρ k hr]
  exact sum_numBlockSets_mul_gamma_two_sided_bounds r k (Fintype.card F) b hk (by omega) hq Fintype.one_lt_card

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem multSharp : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.MultSharp := MultSharpPf.multSharp_of_placeBound placeBound

end GlobalTheory.FinGL.MultSharpObj
