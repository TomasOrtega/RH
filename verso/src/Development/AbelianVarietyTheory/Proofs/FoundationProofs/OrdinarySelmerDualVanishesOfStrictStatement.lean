import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerDualVanishesOfStrict
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FOrdinarySelmerDualVanishesOfStrict.lean&line=161#L161)
-/
theorem _root_.GlobalTheory.T.ordinarySelmer_dual_vanishes_of_strict : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → StrZero (dual1 W) A → GrZero (dual1 W) A := by
  first | exact @GlobalTheory.Ord2.Upgrade.upgrade | exact GlobalTheory.Ord2.Upgrade.upgrade | (intros; apply GlobalTheory.Ord2.Upgrade.upgrade <;> assumption)
