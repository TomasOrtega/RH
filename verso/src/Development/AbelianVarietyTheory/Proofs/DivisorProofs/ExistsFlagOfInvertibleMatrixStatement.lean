import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagOfInvertibleMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFlagOfInvertibleMatrix.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.exists_flag_of_invertible_matrix : ∀ (B : Scheme.{0}) (M : B.Modules) (r : ℕ) (hM : IsVB M r) (V : B.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (K : Type) [Field K] (x : Sp K ⟶ B), ⊤ ≤ x ⁻¹ᵁ V → ∀ A : Matrix (Fin r) (Fin r) K, IsUnit A.det → ∃ fl' : Vert.Flag ((Scheme.Modules.pullback x).obj M) r, FlagMat hM x fl' hf (𝟙 (Sp K)) A := by
  first | exact @GlobalTheory.FlagCls.exists_flag_flagMat | exact GlobalTheory.FlagCls.exists_flag_flagMat | (intros; apply GlobalTheory.FlagCls.exists_flag_flagMat <;> assumption)
