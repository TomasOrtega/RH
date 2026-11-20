import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GE.Comb.restrict_alg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FArtinReesClosedSystem.lean&line=334#L334)
-/
theorem _root_.GlobalTheory.T.artin_rees_closed_system : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → PropSupp A (S 0) → ∀ (D : Subobject E), (D : X.Modules).IsQuasicoherent → ∀ c : ℕ, (∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1)) → ∃ c' : ℕ, ClosedSys I (D : X.Modules) (restrictSys I D S c') ∧ PropSupp A (restrictSys I D S c' 0) ∧ (Alg I (D : X.Modules) (restrictSys I D S c') → PropSupp A D → Alg I E S) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Comb.restrict_alg | exact GlobalTheory.CompanionTheory.GE.Comb.restrict_alg | (intros; apply GlobalTheory.CompanionTheory.GE.Comb.restrict_alg <;> assumption)
