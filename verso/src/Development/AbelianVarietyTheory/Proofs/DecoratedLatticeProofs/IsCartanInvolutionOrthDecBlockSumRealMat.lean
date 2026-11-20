import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumMatApply
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox

noncomputable section

namespace GlobalTheory.Core.Rk.SumBox

open Matrix ComplexOrder in

/- English proof (translation)
Establish `hWH : iWᴴ * G * iH = 0`. Use `congrArg Matrix.conjTranspose hHW` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hGh, conjTranspose_zero, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Establish `c1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), pW * (iW * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, h1, Matrix.one_mul]`.

Establish `c2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), pW * (iH * X) = 0` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, h2, Matrix.zero_mul]`. Establish `c3 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), pH * (iH * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, h3, Matrix.one_mul]`. Establish `c4 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), pH * (iW * X) = 0` using `fun X => by`.

Rewrite using `[← Matrix.mul_assoc, h4, Matrix.zero_mul]`. Establish `g1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iWᴴ * (G * (iW * X)) = GW * X` using `fun X => by`. Simplify using `only [← Matrix.mul_assoc, hWW]`. Establish `g2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iWᴴ * (G * (iH * X)) = 0` using `fun X => by`. Simplify using `only [← Matrix.mul_assoc, hWH, Matrix.zero_mul]`.

Establish `g3 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iHᴴ * (G * (iH * X)) = GH * X` using `fun X => by`. Simplify using `only [← Matrix.mul_assoc, hHH]`. Establish `g4 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iHᴴ * (G * (iW * X)) = 0` using `fun X => by`. Simplify using `only [← Matrix.mul_assoc, hHW, Matrix.zero_mul]`. Establish `hG : G = pWᴴ * GW * pW + pHᴴ * GH * pH`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsum, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Use `_ = _ := by`. Simplify using `only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, g1, g2, g3, g4, Matrix.mul_zero, add_zero, zero_add]`. Establish `hGs : G * (iW * sW * pW + iH * sH * pH) = pWᴴ * (GW * sW) * pW + pHᴴ * (GH * sH) * pH`.

Rewrite using `[hG]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, c1, c2, c3, c4, Matrix.mul_zero, add_zero, zero_add]`. Establish `d1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iWᴴ * (pWᴴ * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_one, Matrix.one_mul]`. Establish `d2 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iHᴴ * (pWᴴ * X) = 0` using `fun X => by`.

Rewrite using `[← Matrix.mul_assoc, ← conjTranspose_mul, h2, conjTranspose_zero, Matrix.zero_mul]`. Establish `d3 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iHᴴ * (pHᴴ * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, ← conjTranspose_mul, h3, conjTranspose_one, Matrix.one_mul]`. Establish `d4 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iWᴴ * (pHᴴ * X) = 0` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, ← conjTranspose_mul, h4, conjTranspose_zero, Matrix.zero_mul]`.

Establish `e1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), sWᴴ * (GW * (sW * X)) = GW * X` using `fun X => by`. Simplify using `only [← Matrix.mul_assoc, hW.2.1]`. Establish `e2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), sHᴴ * (GH * (sH * X)) = GH * X` using `fun X => by`. Simplify using `only [← Matrix.mul_assoc, hH.2.1]`. Establish `f1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), sW * (sW * X) = X` using `fun X => by`.

Rewrite using `[← Matrix.mul_assoc, hW.1, Matrix.one_mul]`. Establish `f2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), sH * (sH * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hH.1, Matrix.one_mul]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, c1, c2, c3, c4, f1, f2, Matrix.mul_zero, add_zero, zero_add]`.

Simplify `hsum` using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_assoc, hGs] conv_rhs => rw [hG]`. Simplify using `only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, d1, d2, d3, d4, e1, e2, Matrix.mul_zero, add_zero, zero_add]`. Rewrite using `[hGs]`. Establish `hPW` using `hW.2.2`.

Establish `hPH` using `hH.2.2`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos ((hPW.posSemidef.conjTranspose_mul_mul_same pW).add (hPH.posSemidef.conjTranspose_mul_mul_same pH)).1 fun x hx => ?_` and prove the remaining obligations. Establish `key : ∀ {n} (P : Matrix (Fin n) (Fin k) ℂ) (M : Matrix (Fin n) (Fin n) ℂ), star x ⬝ᵥ ((Pᴴ * M * P) *ᵥ x) = star (P *ᵥ x) ⬝ᵥ (M *ᵥ (P *ᵥ x))` using `fun P M => by`. Simplify using `only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]`. Rewrite using `[Matrix.add_mulVec, dotProduct_add, key, key]`.

Establish `hx' : iW *ᵥ (pW *ᵥ x) + iH *ᵥ (pH *ᵥ x) = x`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hsum, Matrix.one_mulVec]`. Distinguish the cases in `hw : pW *ᵥ x = 0`. Establish `hh : pH *ᵥ x ≠ 0` using `fun hh => hx (by rw [← hx', hw, hh, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero])`. Rewrite using `[hw]`.

Simplify using `using hPH.dotProduct_mulVec_pos hh`. Conclude with `add_pos_of_pos_of_nonneg (hPW.dotProduct_mulVec_pos hw) (hPH.posSemidef.dotProduct_mulVec_nonneg _)`.
-/
theorem isCartanInv_blockSum {k k₁ k₂ : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (GW : Matrix (Fin k₁) (Fin k₁) ℂ)
    (GH : Matrix (Fin k₂) (Fin k₂) ℂ) (iW : Matrix (Fin k) (Fin k₁) ℂ) (iH : Matrix (Fin k) (Fin k₂) ℂ)
    (pW : Matrix (Fin k₁) (Fin k) ℂ) (pH : Matrix (Fin k₂) (Fin k) ℂ) (sW : Matrix (Fin k₁) (Fin k₁) ℂ)
    (sH : Matrix (Fin k₂) (Fin k₂) ℂ) (hGh : Gᴴ = G) (hWW : iWᴴ * G * iW = GW) (hHH : iHᴴ * G * iH = GH)
    (hHW : iHᴴ * G * iW = 0) (h1 : pW * iW = 1) (h2 : pW * iH = 0) (h3 : pH * iH = 1) (h4 : pH * iW = 0)
    (hsum : iW * pW + iH * pH = 1) (hW : IsCartanInv GW sW) (hH : IsCartanInv GH sH) :
    IsCartanInv G (iW * sW * pW + iH * sH * pH) := by
  have hWH : iWᴴ * G * iH = 0 := by
    have := congrArg Matrix.conjTranspose hHW
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hGh, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have c1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), pW * (iW * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have c2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), pW * (iH * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.zero_mul]
  have c3 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), pH * (iH * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  have c4 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), pH * (iW * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, h4, Matrix.zero_mul]
  have g1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iWᴴ * (G * (iW * X)) = GW * X := fun X => by
    simp only [← Matrix.mul_assoc, hWW]
  have g2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iWᴴ * (G * (iH * X)) = 0 := fun X => by
    simp only [← Matrix.mul_assoc, hWH, Matrix.zero_mul]
  have g3 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iHᴴ * (G * (iH * X)) = GH * X := fun X => by
    simp only [← Matrix.mul_assoc, hHH]
  have g4 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iHᴴ * (G * (iW * X)) = 0 := fun X => by
    simp only [← Matrix.mul_assoc, hHW, Matrix.zero_mul]

  have hG : G = pWᴴ * GW * pW + pHᴴ * GH * pH := by
    calc G = (iW * pW + iH * pH)ᴴ * G * (iW * pW + iH * pH) := by
            rw [hsum, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by
        simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, g1, g2,
          g3, g4, Matrix.mul_zero, add_zero, zero_add]
  have hGs : G * (iW * sW * pW + iH * sH * pH) = pWᴴ * (GW * sW) * pW + pHᴴ * (GH * sH) * pH := by
    rw [hG]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, c1, c2, c3, c4, Matrix.mul_zero, add_zero, zero_add]
  have d1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iWᴴ * (pWᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_one, Matrix.one_mul]
  have d2 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), iHᴴ * (pWᴴ * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, h2, conjTranspose_zero, Matrix.zero_mul]
  have d3 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iHᴴ * (pHᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, h3, conjTranspose_one, Matrix.one_mul]
  have d4 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), iWᴴ * (pHᴴ * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, h4, conjTranspose_zero, Matrix.zero_mul]
  have e1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), sWᴴ * (GW * (sW * X)) = GW * X := fun X => by
    simp only [← Matrix.mul_assoc, hW.2.1]
  have e2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), sHᴴ * (GH * (sH * X)) = GH * X := fun X => by
    simp only [← Matrix.mul_assoc, hH.2.1]
  have f1 : ∀ {n} (X : Matrix (Fin k₁) (Fin n) ℂ), sW * (sW * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hW.1, Matrix.one_mul]
  have f2 : ∀ {n} (X : Matrix (Fin k₂) (Fin n) ℂ), sH * (sH * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hH.1, Matrix.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, c1, c2, c3, c4, f1, f2, Matrix.mul_zero, add_zero,
      zero_add]
    simpa only [Matrix.mul_assoc] using hsum
  · rw [Matrix.mul_assoc, hGs]
    conv_rhs => rw [hG]
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, d1, d2, d3, d4,
      e1, e2, Matrix.mul_zero, add_zero, zero_add]
  · rw [hGs]
    have hPW := hW.2.2
    have hPH := hH.2.2
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      ((hPW.posSemidef.conjTranspose_mul_mul_same pW).add (hPH.posSemidef.conjTranspose_mul_mul_same pH)).1
      fun x hx => ?_
    have key : ∀ {n} (P : Matrix (Fin n) (Fin k) ℂ) (M : Matrix (Fin n) (Fin n) ℂ),
        star x ⬝ᵥ ((Pᴴ * M * P) *ᵥ x) = star (P *ᵥ x) ⬝ᵥ (M *ᵥ (P *ᵥ x)) := fun P M => by
      simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
    rw [Matrix.add_mulVec, dotProduct_add, key, key]
    have hx' : iW *ᵥ (pW *ᵥ x) + iH *ᵥ (pH *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hsum, Matrix.one_mulVec]
    by_cases hw : pW *ᵥ x = 0
    · have hh : pH *ᵥ x ≠ 0 := fun hh => hx (by rw [← hx', hw, hh, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero])
      rw [hw]
      simpa using hPH.dotProduct_mulVec_pos hh
    · exact add_pos_of_pos_of_nonneg (hPW.dotProduct_mulVec_pos hw)
        (hPH.posSemidef.dotProduct_mulVec_nonneg _)

open Matrix in

/- English proof (translation)
Introduce `D B W H o sW sH hW hH τ`. Establish `hc : Function.Semiconj (tauE D τ) star star` using `fun x => GlobalTheory.FockCompare.tauE_star τ x`. Establish `mm : ∀ {a b d : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) (N : Matrix (Fin b) (Fin d) D.host.E), (M * N).map (tauE D τ) = M.map (tauE D τ) * N.map (tauE D τ)` using `fun M N => Matrix.map_mul`. Establish `ct : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), Mᴴ.map (tauE D τ) = (M.map (tauE D τ))ᴴ` using `fun M => Matrix.conjTranspose_map _ hc`. Establish `m1 : ∀ {a : ℕ}, (1 : Matrix (Fin a) (Fin a) D.host.E).map (tauE D τ) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`.

Establish `m0 : ∀ {a b : ℕ}, (0 : Matrix (Fin a) (Fin b) D.host.E).map (tauE D τ) = 0` using `Matrix.map_zero _ (map_zero _)`. Rewrite using `[sumMat_apply]`. Use `isCartanInv_blockSum (gramAt D B τ) (gramAt D W τ) (gramAt D H τ) (o.iA.map (tauE D τ)) (o.iB.map (tauE D τ)) (o.qA.map (tauE D τ)) (o.qB.map (tauE D τ)) (sW τ) (sH τ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hW τ) (hH τ)` and prove the remaining obligations. Use `show ((HSpace.gram B).map (tauE D τ))ᴴ = (HSpace.gram B).map (tauE D τ)`. Rewrite using `[← ct, gram_conjTranspose]`.

Use `show (o.iA.map (tauE D τ))ᴴ * (HSpace.gram B).map (tauE D τ) * o.iA.map (tauE D τ) = (HSpace.gram W).map (tauE D τ)`. Rewrite using `[← ct, ← mm, ← mm, o.isoA]`. Use `show (o.iB.map (tauE D τ))ᴴ * (HSpace.gram B).map (tauE D τ) * o.iB.map (tauE D τ) = (HSpace.gram H).map (tauE D τ)`. Rewrite using `[← ct, ← mm, ← mm, o.isoB]`. Use `show (o.iB.map (tauE D τ))ᴴ * (HSpace.gram B).map (tauE D τ) * o.iA.map (tauE D τ) = 0`.

Rewrite using `[← ct, ← mm, ← mm, o.orth, m0]`. Rewrite using `[← mm, o.qA_iA, m1]`. Rewrite using `[← mm, o.qA_iB, m0]`. Rewrite using `[← mm, o.qB_iB, m1]`. Rewrite using `[← mm, o.qB_iA, m0]`.

Rewrite using `[← mm, ← mm, ← Matrix.map_add _ (map_add _), o.iA_qA_add, m1]`.
-/
theorem isCartanInv_sumMat : ∀ (D : D7) (B W H : HSp D) (o : OrthDec B W H) (sW : RealMat W) (sH : RealMat H), (∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → ∀ τ, IsCartanInv (gramAt D B τ) (sumMat o sW sH τ) := by
  intro D B W H o sW sH hW hH τ
  have hc : Function.Semiconj (tauE D τ) star star := fun x => GlobalTheory.FockCompare.tauE_star τ x
  have mm : ∀ {a b d : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) (N : Matrix (Fin b) (Fin d) D.host.E),
      (M * N).map (tauE D τ) = M.map (tauE D τ) * N.map (tauE D τ) := fun M N => Matrix.map_mul
  have ct : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), Mᴴ.map (tauE D τ) = (M.map (tauE D τ))ᴴ :=
    fun M => Matrix.conjTranspose_map _ hc
  have m1 : ∀ {a : ℕ}, (1 : Matrix (Fin a) (Fin a) D.host.E).map (tauE D τ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have m0 : ∀ {a b : ℕ}, (0 : Matrix (Fin a) (Fin b) D.host.E).map (tauE D τ) = 0 := Matrix.map_zero _ (map_zero _)
  rw [sumMat_apply]
  refine isCartanInv_blockSum (gramAt D B τ) (gramAt D W τ) (gramAt D H τ) (o.iA.map (tauE D τ))
    (o.iB.map (tauE D τ)) (o.qA.map (tauE D τ)) (o.qB.map (tauE D τ)) (sW τ) (sH τ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (hW τ) (hH τ)
  · show ((HSpace.gram B).map (tauE D τ))ᴴ = (HSpace.gram B).map (tauE D τ)
    rw [← ct, gram_conjTranspose]
  · show (o.iA.map (tauE D τ))ᴴ * (HSpace.gram B).map (tauE D τ) * o.iA.map (tauE D τ) = (HSpace.gram W).map (tauE D τ)
    rw [← ct, ← mm, ← mm, o.isoA]
  · show (o.iB.map (tauE D τ))ᴴ * (HSpace.gram B).map (tauE D τ) * o.iB.map (tauE D τ) = (HSpace.gram H).map (tauE D τ)
    rw [← ct, ← mm, ← mm, o.isoB]
  · show (o.iB.map (tauE D τ))ᴴ * (HSpace.gram B).map (tauE D τ) * o.iA.map (tauE D τ) = 0
    rw [← ct, ← mm, ← mm, o.orth, m0]
  · rw [← mm, o.qA_iA, m1]
  · rw [← mm, o.qA_iB, m0]
  · rw [← mm, o.qB_iB, m1]
  · rw [← mm, o.qB_iA, m0]
  · rw [← mm, ← mm, ← Matrix.map_add _ (map_add _), o.iA_qA_add, m1]

end GlobalTheory.Core.Rk.SumBox
end
