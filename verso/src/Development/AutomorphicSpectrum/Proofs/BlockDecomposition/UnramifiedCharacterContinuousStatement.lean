import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterContinuous
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
Apply `GlobalTheory.CompanionTheory.LocalUnram.continuous_of_additive_of_frobenius_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnramifiedCharacterContinuous.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.unramified_character_continuous : ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (n : ℕ) [NeZero n] (χ : Gal(Ω/K) → ZMod n), (∀ g h, χ (g * h) = χ g + χ h) → (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → Continuous χ := by
  first | exact @GlobalTheory.CompanionTheory.LocalUnram.continuous_of_additive_of_frobenius_eq_one | exact GlobalTheory.CompanionTheory.LocalUnram.continuous_of_additive_of_frobenius_eq_one | (intros; apply GlobalTheory.CompanionTheory.LocalUnram.continuous_of_additive_of_frobenius_eq_one <;> assumption)
