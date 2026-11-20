import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProjectiveOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GE.statement_open_projective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFormalExistenceProjectiveOpen.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.formal_existence_projective_open : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {N : ℕ} {Y : Scheme.{0}} (i : Y ⟶ projectiveSpace A N), IsClosedImmersion i → ∀ (O : Y.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ i ≫ ProjSpace.toSpecBase A N⟩; Statement I (⊥ : (O : Scheme.{0}).IdealSheafData) := by
  first | exact @GlobalTheory.CompanionTheory.GE.statement_open_projective | exact GlobalTheory.CompanionTheory.GE.statement_open_projective | (intros; apply GlobalTheory.CompanionTheory.GE.statement_open_projective <;> assumption)
