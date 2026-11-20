import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenvalueSystemSetFinite
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EigFinite.eigSet_finite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHeckeEigenvalueSystemSetFinite.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.heckeEigenvalueSystemSet_finite : HeckeStdPlain → ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (X : MtReal D μ j) (l : ℕ) (Q : Finset (PlE D.host)) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.HypOutside X.J X.χ B → (∀ v k (s : SplitPlace D.host.E), GenAt D l Q v k → IsConjPl D.host v s.w → s.v ∉ B) → (EigSet X l Q).Finite := by
  first | exact @GlobalTheory.EigFinite.eigSet_finite | exact GlobalTheory.EigFinite.eigSet_finite | (intros; apply GlobalTheory.EigFinite.eigSet_finite <;> assumption)
