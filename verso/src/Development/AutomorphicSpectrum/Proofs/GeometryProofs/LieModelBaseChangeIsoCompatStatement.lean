import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeIsoCompat
import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.GMove.gramAt_move` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLieModelBaseChangeIsoCompat.lean&line=158#L158)
-/
theorem _root_.GlobalTheory.T.lie_model_base_change_iso_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X)
    (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (k : SABMap t' t e.hom)
    (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V),
    ξ' ≫ e.hom = ξ → (∀ v, (M'.pt v).left ≫ k.φ = (M.pt v).left) →
    ∀ (z : Sp ℂ ⟶ X') (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ),
      M'.GramAt t'.PP.L z b Γ ↔ M.GramAt t.PP.L (z ≫ e.hom) b Γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GMove.gramAt_move | exact GlobalTheory.CompanionTheory.Ar.GMove.gramAt_move | (intros; apply GlobalTheory.CompanionTheory.Ar.GMove.gramAt_move <;> assumption)
