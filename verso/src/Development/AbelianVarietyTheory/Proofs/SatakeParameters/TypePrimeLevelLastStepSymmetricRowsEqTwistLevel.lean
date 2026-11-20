import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.KernelLattices.TopPin
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem levGTop_rPsymF_eq_twLt : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m), X.Ok → Pr.Ok → Ch.Ok →
    levGTop Ch (rPsymF Ch) = twLt Ch R.m := by
  intro X Pr R Ch _ _ _
  funext w
  rw [levGTop_PsymF]
  show _ = colLevSym Ch R.m w
  unfold colLevSym
  rw [if_neg (by have := R.two_le_m; omega), dif_neg (by omega), dif_neg (by omega)]
  rfl

end GlobalTheory
