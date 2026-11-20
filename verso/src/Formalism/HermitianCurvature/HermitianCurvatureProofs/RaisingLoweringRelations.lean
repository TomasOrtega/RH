import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolyTopOf

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem raising_lowering_relations : KrAA := by
  intro k r Wp Wq _ _ _ _ _ _ Bs F hF u x hx
  obtain ⟨hs, ⟨R, hR⟩, -⟩ := hF
  exact (PBG.kr_AA_cpt Bs hs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R)
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne)) r le_rfl u 0 hx).1

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem polynomial_top : PBN.PolyTop := VandermondePolynomialIntegral.polyTop_of VandermondePolynomialIntegral.raising_lowering_relations

end Formalism.FourierDecayAlt.P
