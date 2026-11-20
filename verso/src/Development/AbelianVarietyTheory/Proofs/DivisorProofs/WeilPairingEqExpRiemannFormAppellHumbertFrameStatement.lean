import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqExpRiemannFormAppellHumbertFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeilPairingEqExpRiemannFormAppellHumbertFrame.lean&line=186#L186)
-/
theorem _root_.GlobalTheory.T.weilPairing_eq_exp_riemannForm_appellHumbert_frame : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left), L.IsLB →
    ∀ (n : ℕ) (u : HolUnif A L n) (Hm : Matrix (Fin n) (Fin n) ℂ) (χ : u.Λ → ℂ), GlobalTheory.TorusRM.IsFactorAH u Hm χ →
      ∀ (k : ℕ) (a b : Fin n → ℂ) (c : ℂˣ), 0 < k → a ∈ u.Λ → b ∈ u.Λ →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((a ⬝ᵥ Hm.mulVec (star b)).im : ℝ) : ℂ) / k) →
        Out.WeilIs A L k (u.ex ((k : ℂ)⁻¹ • a)) (u.ex ((k : ℂ)⁻¹ • b)) (unitOn c) := by
  first | exact @GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm | exact GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm | (intros; apply GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm <;> assumption)
