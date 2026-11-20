import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlaceRelativeNormLeLocalSizePow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix NumberField IsDedekindDomain
open scoped NNReal TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFinitePlaceRelativeNormLeLocalSizePow.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.finitePlace_relativeNorm_le_localSize_pow : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (y : D.host.E), ‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F y)‖₊ ≤ GlobalTheory.AdelicU.absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] y) ^ Module.finrank D.host.F D.host.E := by
  first | exact @GlobalTheory.NormFin.normFin_le | exact GlobalTheory.NormFin.normFin_le | (intros; apply GlobalTheory.NormFin.normFin_le <;> assumption)
