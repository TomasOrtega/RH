import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalAdditiveCharacterEqAdelic
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
Apply `GlobalTheory.CompanionTheory.PsiStd.psiAt_eq_localAdelicChar` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FLocalAdditiveCharacterEqAdelic.lean&line=290#L290)
-/
theorem _root_.GlobalTheory.T.local_additive_character_eq_adelic : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E), psiAt w x = (localAdelicChar E w x : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.PsiStd.psiAt_eq_localAdelicChar | exact GlobalTheory.CompanionTheory.PsiStd.psiAt_eq_localAdelicChar | (intros; apply GlobalTheory.CompanionTheory.PsiStd.psiAt_eq_localAdelicChar <;> assumption)
