import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.TraceHeckeCongruenceVanish

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Kato.Nb.sLiftOk :
    UpperTheory.V.Z.Kato.Nb.SLiftOk := by
  intro Ω _ _ _ ε X l _ N w _ hl hc hw
  have h : ∃ c, LiftsWith X l N w c :=
    UpperTheory.Kd.K4.liftH ε X l N w hl (Nat.pos_of_ne_zero (NeZero.ne N)) hc hw
  exact Classical.epsilon_spec h
