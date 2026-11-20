import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorRelationPullbackGaloisAutomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOperatorRelationPullbackGaloisAutomorphism.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.operator_relation_pullback_galois_automorphism : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀) (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) (s s' : Fam D (Kb R) N), PhiRel D (Kb R) N p w s s' → PhiRel D (Kb R) N p₀ (frTw D τ h w) (famTw D N τ s) (famTw D N τ s') := by
  first | exact @GlobalTheory.Mum.Conj.PhiTw.phiRel_famTw | exact GlobalTheory.Mum.Conj.PhiTw.phiRel_famTw | (intros; apply GlobalTheory.Mum.Conj.PhiTw.phiRel_famTw <;> assumption)
