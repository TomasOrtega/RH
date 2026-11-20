import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOneOfFiniteOrderUnipotentReductionLargePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnipRed.eq_one_of_unipotent_reduction` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FEqOneOfFiniteOrderUnipotentReductionLargePrime.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.eq_one_of_finiteOrder_unipotentReduction_largePrime : ∀ (E R k : Type) [Field E] [NumberField E] [CommRing R] [CommRing k] (S : Subring R) (ι : E →+* R) (φ : S →+* k) (p n : ℕ), p.Prime → CharP k p → Module.finrank ℚ E * n + 1 < p → ∀ (u : GL (Fin n) E) (x : GL (Fin n) R) (y : GL (Fin n) S), IsOfFinOrder u → Formalism.UG.bc S.subtype y = x⁻¹ * Formalism.UG.bc ι u * x → IsNilpotent ((Formalism.UG.bc φ y : GL (Fin n) k).val - 1) → u = 1 := by
  first | exact @GlobalTheory.UnipRed.eq_one_of_unipotent_reduction | exact GlobalTheory.UnipRed.eq_one_of_unipotent_reduction | (intros; apply GlobalTheory.UnipRed.eq_one_of_unipotent_reduction <;> assumption)
