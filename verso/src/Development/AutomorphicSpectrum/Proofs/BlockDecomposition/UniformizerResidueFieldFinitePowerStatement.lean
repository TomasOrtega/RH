import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerResidueFieldFinitePower
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUniformizerResidueFieldFinitePower.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.uniformizer_residue_field_finite_power : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π →
    (Ideal.span {π}).IsMaximal ∧ Finite (↥(OL K) ⧸ Ideal.span {π}) ∧ ∃ f : ℕ, 0 < f ∧ qOf π = l ^ f := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.resfield_of_irreducible | exact GlobalTheory.CompanionTheory.LTPer.Tilt.resfield_of_irreducible | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.resfield_of_irreducible <;> assumption)
