import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFramePullbackMumfordFrameGaloisTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsSymmetricFramePullbackMumfordFrameGaloisTwist.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.isSymmetricFrame_pullbackMumfordFrameGaloisTwist : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀) (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b), GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p₀ (frTw D τ h w) := by
  first | exact @GlobalTheory.Mum.Conj.txFrame_frTw | exact GlobalTheory.Mum.Conj.txFrame_frTw | (intros; apply GlobalTheory.Mum.Conj.txFrame_frTw <;> assumption)
