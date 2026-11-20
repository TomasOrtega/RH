import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMixedBridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

/- English proof (translation)
Introduce `D K _ _ ι _ Ω _ _ d L A₁ hL hdeg hA₁`. Establish `hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ), IsGoodProj (mCoordIdeal d.y) Ψ` using `goodProjExists K ι (mCoordIdeal d.y) D d.arith`. Use `set B : HermLine ι := A₁.tensor d.A.inv with hBdef`. Establish `hB0 : B.a = 0`. Use function extensionality and compare the values at `k`.

Simplify using `[B, HermLine.tensor, HermLine.inv, hdeg, d.deg]`. Establish `hgl : (fun z => Real.log (A₁.h z / d.A.h z)) = logNorm B.inv 1`. Use function extensionality and compare the values at `z`. Rewrite using `[logNorm_inv_one]`. Simplify using `only [B, HermLine.tensor, HermLine.inv, div_eq_mul_inv]`.

Establish `hBs : IsSmoothHerm B.inv` using `isSmoothHerm_inv (isSmoothHerm_tensor hA₁ (isSmoothHerm_inv d.semipos.1))`. Establish `hsec : IsSectionOn (mCoordIdeal d.y) B.inv 1` using `isSectionOn_inv_one d.arith.2.1.1 hB0`. Establish `key` using `AnResBridge.bridge d.R hex.choose L B.inv 1 d.arith hex.choose_spec hL hBs hsec`. Establish `hgr : (fun x => Real.log (A₁.h (blockPt d x) / d.A.h (blockPt d x))) = fun x => logNorm B.inv 1 (d.R.lift x x)`. Use function extensionality and compare the values at `fun x => congrFun hgl (d.R.lift x x)`.

Unfold `ptsIntegral`. Rewrite using `[dif_pos hex, hgl, hgr]`. Conclude with `key`.
-/
theorem BlockResolutionMixedBridge.proof : BlockResolutionMixedBridge.Statement := by
  intro D K _ _ ι _ Ω _ _ d L A₁ hL hdeg hA₁
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (mCoordIdeal d.y) Ψ :=
    goodProjExists K ι (mCoordIdeal d.y) D d.arith
  set B : HermLine ι := A₁.tensor d.A.inv with hBdef
  have hB0 : B.a = 0 := by
    funext k
    simp [B, HermLine.tensor, HermLine.inv, hdeg, d.deg]
  have hgl : (fun z => Real.log (A₁.h z / d.A.h z)) = logNorm B.inv 1 := by
    funext z
    rw [logNorm_inv_one]
    simp only [B, HermLine.tensor, HermLine.inv, div_eq_mul_inv]
  have hBs : IsSmoothHerm B.inv :=
    isSmoothHerm_inv (isSmoothHerm_tensor hA₁ (isSmoothHerm_inv d.semipos.1))
  have hsec : IsSectionOn (mCoordIdeal d.y) B.inv 1 := isSectionOn_inv_one d.arith.2.1.1 hB0
  have key := AnResBridge.bridge d.R hex.choose L B.inv 1 d.arith hex.choose_spec hL hBs hsec
  have hgr : (fun x => Real.log (A₁.h (blockPt d x) / d.A.h (blockPt d x))) =
      fun x => logNorm B.inv 1 (d.R.lift x x) :=
    funext fun x => congrFun hgl (d.R.lift x x)
  unfold ptsIntegral
  rw [dif_pos hex, hgl, hgr]
  exact key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
