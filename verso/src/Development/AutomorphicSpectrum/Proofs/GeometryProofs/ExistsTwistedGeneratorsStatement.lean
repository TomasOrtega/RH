import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTwistedGenerators
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FExistsTwistedGenerators.lean&line=448#L448)
-/
theorem _root_.GlobalTheory.T.exists_twisted_generators : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → L.IsVB r V → ∃ (m n : ℕ) (φ : Fin n → Module.Dual Ω E), IsTwistGen ξ x L m φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Twist.exists_twistGen | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Twist.exists_twistGen | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Twist.exists_twistGen <;> assumption)
