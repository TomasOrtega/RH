import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.LocCpt.loc_cpt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsCompactDefiniteUnitaryRestrictedProduct.lean&line=117#L117)
-/
theorem _root_.GlobalTheory.T.isCompact_definiteUnitary_restricted_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ C : ∀ w : Pl E, Set (UL n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w = KL n w) → IsCompact {x : finU E n | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
  first | exact @GlobalTheory.BCT.LocCpt.loc_cpt | exact GlobalTheory.BCT.LocCpt.loc_cpt | (intros; apply GlobalTheory.BCT.LocCpt.loc_cpt <;> assumption)
