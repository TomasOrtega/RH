import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumScalarSmulMemCompletedModulus
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIdempotentSumScalarSmulMemCompletedModulus.lean&line=111#L111)
-/
theorem _root_.GlobalTheory.T.idempotentSum_scalar_smul_mem_completedModulus : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)) (e : AE D), IsIdemSum e G.pl.W0 → ∀ α ∈ intAf D.host.F, ∀ b : D.host.E, (∀ w ∈ G.pl.W0, Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ))) → ∀ g ∈ M, e • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n) ∈ hatMx (G.modul • M) := by
  first | exact @GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx | exact GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx | (intros; apply GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx <;> assumption)
