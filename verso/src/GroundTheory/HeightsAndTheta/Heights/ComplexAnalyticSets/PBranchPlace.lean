import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInComponent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMinimalPrimePlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeBranchPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

/- English proof (translation)
Introduce `n I q c hrad hdim`. Take `⟨J, hJ, hmaps⟩` from `h₁ n I 1 q c`. Establish `hJp : J.IsPrime` using `hJ.1.1`. Establish `hIJ : I ≤ J` using `hJ.1.2`. Set `c' : VarBranch J 1 q` to `{ radius := c.radius, radius_pos := c.radius_pos, toFun := c.toFun, differentiableOn := c.differentiableOn, injOn := c.injOn, map_zero := c.map_zero, mapsTo := hmaps }`.

Establish `hJq : J ≤ RingHom.ker (eval q)`. Introduce `g hg`. Establish `h0` using `hmaps (Metric.mem_ball_self c.radius_pos) g hg`. Rewrite `h0` using `[c.map_zero]`. Conclude with `RingHom.mem_ker.2 h0`.

Establish `hdimJ : ringKrullDim (curveLocalRing J q) ≤ 1`. Establish `hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) ≤ J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))` using `Ideal.map_mono hIJ`. Rewrite using `[← hdim]`. Conclude with `ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle : curveLocalRing I q →+* curveLocalRing J q) (Ideal.Quotient.factor_surjective hle)`. Take `⟨P', hP'⟩` from `h₂ n J q c' hJp hdimJ`.

Take `⟨P, hP⟩` from `h₃ n I J q hrad hJ hJq P'`. Conclude with `⟨P, fun f ↦ (hP f).trans (hP' f)⟩`.
-/
theorem BranchPlace.proof (h₁ : BranchInComponent.Statement) (h₂ : PrimeBranchPlace.Statement)
    (h₃ : MinimalPrimePlace.Statement) : BranchPlace.Statement := by
  intro n I q c hrad hdim
  obtain ⟨J, hJ, hmaps⟩ := h₁ n I 1 q c
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : I ≤ J := hJ.1.2

  let c' : VarBranch J 1 q :=
    { radius := c.radius, radius_pos := c.radius_pos, toFun := c.toFun, differentiableOn := c.differentiableOn,
      injOn := c.injOn, map_zero := c.map_zero, mapsTo := hmaps }

  have hJq : J ≤ RingHom.ker (eval q) := by
    intro g hg
    have h0 := hmaps (Metric.mem_ball_self c.radius_pos) g hg
    rw [c.map_zero] at h0
    exact RingHom.mem_ker.2 h0

  have hdimJ : ringKrullDim (curveLocalRing J q) ≤ 1 := by
    have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) ≤
        J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) :=
      Ideal.map_mono hIJ
    rw [← hdim]
    exact ringKrullDim_le_of_surjective
      (Ideal.Quotient.factor hle : curveLocalRing I q →+* curveLocalRing J q) (Ideal.Quotient.factor_surjective hle)
  obtain ⟨P', hP'⟩ := h₂ n J q c' hJp hdimJ
  obtain ⟨P, hP⟩ := h₃ n I J q hrad hJ hJq P'
  exact ⟨P, fun f ↦ (hP f).trans (hP' f)⟩

end GroundTheory.Heights₂.Heights
