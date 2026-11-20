import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem CechTop.idx_isEmpty (N i : ℕ) (hi : N < i) :
    IsEmpty (Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) := by
  refine ⟨fun I => ?_⟩
  have h1 : I.1.1.card ≤ N + 1 := by
    simpa using Finset.card_le_univ I.1.1
  have h2 := I.2
  omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Express the relevant assertion in an equivalent form by its definition. Proceed by induction. Treat this case separately. Proceed by induction. Treat this case separately.

Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem CechTop.proof : CechTop.Statement := by
  intro S _ _ N M _ _ _ _ 𝓜 i c hi
  have := CechTop.idx_isEmpty N i hi
  have hC : Subsingleton (Cech.Cochain (locSys S N M) i) := inferInstance
  constructor
  intro a b
  change (a : Cech.Hdeg _ _ _ i) = b
  induction a using Submodule.Quotient.induction_on with
  | H x =>
    induction b using Submodule.Quotient.induction_on with
    | H y =>
      congr 1
      exact Subtype.ext (hC.elim _ _)

end GroundTheory.Heights₂.Heights.Kleiman
