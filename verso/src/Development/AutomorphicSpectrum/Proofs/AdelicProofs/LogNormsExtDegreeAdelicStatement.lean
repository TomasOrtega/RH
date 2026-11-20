import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsExtDegreeAdelic
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAdelicProofs%2FLogNormsExtDegreeAdelic.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.logNorms_ext_degree_adelic : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') (N : LogNorms k), (N.ext f).deg = N.deg ∧ ((N.ext f).IsAdelic ↔ N.IsAdelic) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic | exact GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic <;> assumption)
