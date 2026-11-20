import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPowFlatLocallyQuasiFinite.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.pow_flat_locallyQuasiFinite : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ q : ℕ, q ≠ 0 → Flat ((𝟙 G) ^ q : G ⟶ G).left ∧ LocallyQuasiFinite ((𝟙 G) ^ q : G ⟶ G).left := by
  first | exact @GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow | exact GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow | (intros; apply GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow <;> assumption)
