import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SenUnramifiedCharacterPeriod
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSenUnramifiedCharacterPeriod.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.sen_unramified_character_period : ∀ {l : ℕ} [Fact l.Prime], ∀ (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E] (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ), Continuous ψ →
      (∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) →
      ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
        σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units | exact GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units | (intros; apply GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units <;> assumption)
