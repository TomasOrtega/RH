import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameBlockPermSign
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FWeylAntisymmetrizationRenameBlockPermSign.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.weylAntisymmetrization_rename_block_perm_sign : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (w : ∀ τ, Equiv.Perm (Fin (m τ))), rename (Equiv.sigmaCongrRight w) (antisymm Q) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • antisymm Q := by
  first | exact @GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight | exact GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight | (intros; apply GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight <;> assumption)
