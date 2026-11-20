import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoHodgeJumpOfGoodJumpMultiset
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NoJumpMult.noJump_of_jumps` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNoHodgeJumpOfGoodJumpMultiset.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.noHodgeJump_of_goodJumpMultiset : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NoJump bkP i s := by
  first | exact @GlobalTheory.NoJumpMult.noJump_of_jumps | exact GlobalTheory.NoJumpMult.noJump_of_jumps | (intros; apply GlobalTheory.NoJumpMult.noJump_of_jumps <;> assumption)
