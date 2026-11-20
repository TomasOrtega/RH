import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjZpowersEntriesValuedBoundedOfCompactClosure
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConjZpowersEntriesValuedBoundedOfCompactClosure.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.conj_zpowers_entries_valued_bounded_of_compact_closure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t g : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℤ) (i j : Fin n),
      Valued.v ((((g⁻¹ * t ^ k * g : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ B := by
  first | exact @GlobalTheory.BCT.powers_entries_bdd | exact GlobalTheory.BCT.powers_entries_bdd | (intros; apply GlobalTheory.BCT.powers_entries_bdd <;> assumption)
