import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeLFunctionEulerProduct
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FHeckeLFunctionEulerProduct.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.hecke_L_function_euler_product : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (s : ℂ), 1 < s.re → HasProd (eulerFactor χ s) ((toHecke χ hu).LFunction s) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.hasProd_eulerFactor_toHecke | exact GlobalTheory.CompanionTheory.HeckeBridge.hasProd_eulerFactor_toHecke | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.hasProd_eulerFactor_toHecke <;> assumption)
