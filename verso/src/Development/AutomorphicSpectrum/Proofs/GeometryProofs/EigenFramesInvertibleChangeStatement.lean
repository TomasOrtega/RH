import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesInvertibleChange
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FEigenFramesInvertibleChange.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.eigen_frames_invertible_change : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] [Nontrivial R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (O : Type) [CommRing O] (act : OAct O G) (σ : O →+* R) (n r : ℕ) (u : Fin n → (epsAt x ⟶ G)) (V : Fin r → (epsAt x ⟶ G)), IsEigFrame act x σ u → IsEigFrame act x σ V → r = n ∧ ∃ C : Matrix (Fin r) (Fin n) R, (∀ i, IsComb (C i) u (V i)) ∧ ∃ C' : Matrix (Fin n) (Fin r) R, C * C' = 1 ∧ C' * C = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change | exact GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change <;> assumption)
