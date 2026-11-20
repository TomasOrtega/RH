import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeCharacterConductorExponent
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
Apply `GlobalTheory.CompanionTheory.HeckeBridge.multiplicity_conductor_toHecke` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FHeckeCharacterConductorExponent.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.hecke_character_conductor_exponent : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (m : ℕ), ExpAt χ v m → multiplicity v.asIdeal (toHecke χ hu).conductor = m := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.multiplicity_conductor_toHecke | exact GlobalTheory.CompanionTheory.HeckeBridge.multiplicity_conductor_toHecke | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.multiplicity_conductor_toHecke <;> assumption)
