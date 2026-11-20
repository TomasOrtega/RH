import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MaxUnramifiedResidueAlgClosedAndFrobeniusLift
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FMaxUnramifiedResidueAlgClosedAndFrobeniusLift.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.maxUnramified_residueAlgClosed_and_frobeniusLift : ∀ (l : ℕ) [Fact l.Prime], 2 < l → ResAlg (MaximalUnramifiedExtension l) ∧ ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension l) l σ → Unr (MaximalUnramifiedExtension l) l σ := by
  first | exact @GlobalTheory.Honda.kur_resAlg_unr | exact GlobalTheory.Honda.kur_resAlg_unr | (intros; apply GlobalTheory.Honda.kur_resAlg_unr <;> assumption)
