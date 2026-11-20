import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentExtensionSurjectionOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCoherentExtensionSurjectionOpen.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.coherent_extension_surjection_open : ∀ {X : Scheme.{0}} [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ (O : X.Opens) (E : (O : Scheme.{0}).Modules), IsCoherent E → ∃ P : X.Modules, IsCoherent P ∧ ∃ f : P.restrict O.ι ⟶ E, Epi f := by
  first | exact @GlobalTheory.CompanionTheory.GE.Present.exists_coherent_epi_restrict | exact GlobalTheory.CompanionTheory.GE.Present.exists_coherent_epi_restrict | (intros; apply GlobalTheory.CompanionTheory.GE.Present.exists_coherent_epi_restrict <;> assumption)
