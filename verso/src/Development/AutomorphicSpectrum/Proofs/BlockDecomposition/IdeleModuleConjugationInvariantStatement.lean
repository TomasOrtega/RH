import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleConjugationInvariant
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIdeleModuleConjugationInvariant.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.idele_module_conjugation_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ x : (AF F ⊗[F] E)ˣ, (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (Units.map (sigR (AF F) σ).toMonoidHom x)) : ℝ) = (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ModConj.ideleModule_conj | exact GlobalTheory.CompanionTheory.SW.ModConj.ideleModule_conj | (intros; apply GlobalTheory.CompanionTheory.SW.ModConj.ideleModule_conj <;> assumption)
