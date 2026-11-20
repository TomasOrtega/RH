import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostCompletionLeMaxUnramifiedPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHostCompletionLeMaxUnramifiedPadic.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.hostCompletion_le_maxUnramified_padic : ∀ (D : D7) (i : D.nd.Loc), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (D.nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (D.nd.l i) := by
  first | exact @GlobalTheory.HubLoc.kw_le_Kur_all | exact GlobalTheory.HubLoc.kw_le_Kur_all | (intros; apply GlobalTheory.HubLoc.kw_le_Kur_all <;> assumption)
