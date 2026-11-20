import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerSubConjNotMemSelfConjugatePlace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConjMovesResidue.exists_sub_star_notMem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsIntegerSubConjNotMemSelfConjugatePlace.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_integer_sub_conj_notMem_self_conjugate_place : ∀ (D : D7) (Q : Pl D.host.E), IsConjPl (D := D) Q Q → ∃ δ δ' : 𝓞 D.host.E, (δ' : D.host.E) = star (δ : D.host.E) ∧ δ - δ' ∉ Q.asIdeal := by
  first | exact @GlobalTheory.ConjMovesResidue.exists_sub_star_notMem | exact GlobalTheory.ConjMovesResidue.exists_sub_star_notMem | (intros; apply GlobalTheory.ConjMovesResidue.exists_sub_star_notMem <;> assumption)
