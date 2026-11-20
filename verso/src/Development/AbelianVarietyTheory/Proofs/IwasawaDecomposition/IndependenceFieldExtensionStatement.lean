import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndependenceFieldExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN GlobalTheory.TorRef
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FieldAscent.indepAlong_ascent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIndependenceFieldExtension.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.independence_field_extension : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (L : LB G.left) (N n : ℕ)
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk (𝟙 (Sp R))))) (k K : Type) [Field k] [Field K] (ψ : R →+* k)
    (ι : k →+* K), L.IsLB → IndepAlong G L N (toBase ψ) b → IndepAlong G L N (toBase (ι.comp ψ)) b := by
  first | exact @GlobalTheory.FieldAscent.indepAlong_ascent | exact GlobalTheory.FieldAscent.indepAlong_ascent | (intros; apply GlobalTheory.FieldAscent.indepAlong_ascent <;> assumption)
