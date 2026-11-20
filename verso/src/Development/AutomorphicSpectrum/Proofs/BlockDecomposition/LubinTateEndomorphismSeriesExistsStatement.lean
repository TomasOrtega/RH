import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateEndomorphismSeriesExists
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LTPer.exists_series_comm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLubinTateEndomorphismSeriesExists.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.lubin_tate_endomorphism_series_exists : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ a : ↥(OL K),
    ∃ φ : PowerSeries ↥(OL K), PowerSeries.constantCoeff φ = 0 ∧ PowerSeries.coeff 1 φ = a ∧
      PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.exists_series_comm | exact GlobalTheory.CompanionTheory.LTPer.exists_series_comm | (intros; apply GlobalTheory.CompanionTheory.LTPer.exists_series_comm <;> assumption)
