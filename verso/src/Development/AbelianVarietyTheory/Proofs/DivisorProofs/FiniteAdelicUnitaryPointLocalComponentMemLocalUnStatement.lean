import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointLocalComponentMemLocalUn
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteAdelicUnitaryPointLocalComponentMemLocalUn.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (w : Pl E) (x : finU E n), cLoc w (x : UA E n) ∈ UL n w := by
  first | exact @GlobalTheory.BCT.cLoc_mem_UL | exact GlobalTheory.BCT.cLoc_mem_UL | (intros; apply GlobalTheory.BCT.cLoc_mem_UL <;> assumption)
