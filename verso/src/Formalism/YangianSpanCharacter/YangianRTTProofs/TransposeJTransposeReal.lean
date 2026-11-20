import Formalism.YangianSpanCharacter.StatementB
import Formalism.YangianSpanCharacter.YangianRTTProofs.TransposeJReversed
import Formalism.YangianSpanCharacter.YangianRTTProofs.TransposeSymplecticShift
import Formalism.YangianSpanCharacter.YangianRTTProofs.RttRelation

namespace Formalism.YangianSpanCharacter.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.QuantumDeterminants

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem transpose_j_transpose_real : Formalism.YangianSpanCharacter.B.TJTReal := by
  intro m E _ _ l Y
  exact transposeSymplecticShift ℂ (Module.End ℂ (WSm m E)) _ _ _ Y (weylRel_end (E := E) l)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

A detailed English derivation is pending.
-/
theorem twisted_j_transpose_real : Formalism.YangianSpanCharacter.B.TvJTsReal := by
  intro m E _ _ l Y
  obtain ⟨h1, h2, h3⟩ := weylRel_end_bar (E := E) l
  have h3' : cbEnd (E := E) l * -pbEnd l = -pbEnd l * cbEnd l + cbEnd l := by
    rw [mul_neg, neg_mul, h3]; abel
  exact transpose_j_reversed ℂ (Module.End ℂ (WSm m E)) _ _ _ Y h1 h2 h3'

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem rtt_real : Formalism.YangianSpanCharacter.B.RTTReal := by
  intro m E _ _ l Y Y'
  exact rttRelation ℂ (Module.End ℂ (WSm m E)) _ _ _ Y Y' (weylRel_end (E := E) l)

end Formalism.YangianSpanCharacter.P
