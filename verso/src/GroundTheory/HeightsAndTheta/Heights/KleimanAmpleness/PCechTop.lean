import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

/- English proof (translation)
Use `⟨fun I => ?_⟩` and prove the remaining obligations. Establish `h1 : I.1.1.card ≤ N + 1`. Simplify using `using Finset.card_le_univ I.1.1`. Establish `h2` using `I.2`. Use linear arithmetic over natural numbers and integers.
-/
theorem CechTop.idx_isEmpty (N i : ℕ) (hi : N < i) :
    IsEmpty (Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) := by
  refine ⟨fun I => ?_⟩
  have h1 : I.1.1.card ≤ N + 1 := by
    simpa using Finset.card_le_univ I.1.1
  have h2 := I.2
  omega

/- English proof (translation)
Introduce `S _ _ N M _ _ _ _ 𝓜 i c hi`. Use `CechTop.idx_isEmpty N i hi` as an intermediate fact. Establish `hC : Subsingleton (Cech.Cochain (locSys S N M) i)` using `inferInstance`. Prove the components needed by the constructor for the conclusion. Introduce `a b`.

Express the relevant statement in the definitionally equal form `(a : Cech.Hdeg _ _ _ i) = b`. Proceed by induction on `a using Submodule.Quotient.induction_on with`. Consider the case `H x`. Proceed by induction on `b using Submodule.Quotient.induction_on with`. Consider the case `H y`.

Use `congr 1`. Conclude with `Subtype.ext (hC.elim _ _)`.
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
