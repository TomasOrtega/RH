import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvTateDual
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TateDualInv.noInv_tateDual` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNoInvTateDual.lean&line=133#L133)
-/
theorem _root_.GlobalTheory.T.noInv_tateDual_of_hodge_of_noJump : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) → HodgeL bkP i s → NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tdual i s) v := by
  first | exact @GlobalTheory.TateDualInv.noInv_tateDual | exact GlobalTheory.TateDualInv.noInv_tateDual | (intros; apply GlobalTheory.TateDualInv.noInv_tateDual <;> assumption)
