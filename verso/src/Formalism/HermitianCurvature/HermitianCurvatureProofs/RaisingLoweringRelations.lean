import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolyTopOf

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ Bs F hF u x hx`. Take `⟨hs, ⟨R, hR⟩, -⟩` from `hF`. Conclude with `(PBG.kr_AA_cpt Bs hs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R) (fun g hg hgC => by`. Assume the negation of the conclusion as `hne`. Conclude with `hgC (hR g hg hne)) r le_rfl u 0 hx).1`.
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
The claim follows from `VandermondePolynomialIntegral.polyTop_of VandermondePolynomialIntegral.raising_lowering_relations`.
-/
theorem polynomial_top : PBN.PolyTop := VandermondePolynomialIntegral.polyTop_of VandermondePolynomialIntegral.raising_lowering_relations

end Formalism.FourierDecayAlt.P
