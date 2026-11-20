import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerOrderEqOne
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAlgHomMulEquivDec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.GlobalFields.LocalFieldAtPlace
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUniformizerOrderEqOne.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.uniformizer_order_eq_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ord (algebraMap F (v.adicCompletion F) (ϖ : F)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one | exact GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one | (intros; apply GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one <;> assumption)
