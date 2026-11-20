import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ConjTransposeBoostMulSignatureMulBoost
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.PosDefSwap

open scoped Matrix.Norms.L2Operator in

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem one_sub_mul_conjTranspose_posDef {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ)
    (h : (1 - zᴴ * z).PosDef) : (1 - z * zᴴ).PosDef := by
  have h1 : ‖z‖ < 1 := (GlobalTheory.MatrixBall.posDef_iff_norm_lt_one z).mp h
  have h2 : ‖zᴴ‖ < 1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  have h3 := (GlobalTheory.MatrixBall.posDef_iff_norm_lt_one zᴴ).mpr h2
  rwa [Matrix.conjTranspose_conjTranspose] at h3

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem main : ∀ {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ), (1 - zᴴ * z).PosDef → (1 - z * zᴴ).PosDef :=
  fun z h => one_sub_mul_conjTranspose_posDef z h

end GlobalTheory.PosDefSwap
