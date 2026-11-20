import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeGaussSumLocalTerm
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FHeckeGaussSumLocalTerm.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.hecke_gauss_sum_local_term : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (m : ℕ), m ≠ 0 → ExpAt χ v m → ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) * psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ * algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) = gaussSumAt χ v m (unif v ^ (m + diffExp v)) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt | exact GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt <;> assumption)
