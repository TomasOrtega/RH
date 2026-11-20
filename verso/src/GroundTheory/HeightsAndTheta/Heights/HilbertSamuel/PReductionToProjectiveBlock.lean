import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsReductionToProjectiveBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageGenDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

/- English proof (translation)
Introduce `D K _ _ ι _ Ω _ _ I d hI`. Take `⟨d₀, r, M, N, d', hy, hk, hB, hmet, hchi⟩` from `hIm D K ι Ω d`. Establish `h1` using `hMC D K ι Ω I d d₀ hI hy hk`. Establish `h2` using `(hRP D Ω (Fin r) I d' hI).2`. Establish `hdeg : d₀.A.a = unitDeg d.k₀` using `hk ▸ d₀.deg`.

Establish `htop : I K ι (mCoordIdeal d₀.y) (D + 1) (fun _ => d₀.A) = top I d'.x d'.m D`. Rewrite using `[hy]`. Conclude with `hTop D K ι Ω (Fin r) I d.y d.k₀ d₀.A M N d'.x d'.m hI d.arith d.birat d'.arith hB hdeg d₀.semipos.1 d'.smooth hmet`. Establish `hg : genDeg (ι` using `GlobalTheory (Fin r)) (coordIdeal ℤ d'.x) D 1 = genDeg (mCoordIdeal d.y) D d.A.a := by`. Rewrite using `[d.deg]`.

Conclude with `hGD D K ι Ω (Fin r) d.y d.k₀ M N d'.x d.arith d.birat hB`. Rewrite `h2` using `[hg]`. Use `(h2.sub h1).congr_left fun n => ?_` and prove the remaining obligations. Simplify using `only [hsDefect, hchi n, htop]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ReductionToProjectiveBlock.proof (hRP : ReductionToProjective.Statement)
    (hMC : BlockMetricChange.Statement) (hIm : BlockImageDatum.Statement) (hTop : BlockImageTop.Statement)
    (hGD : BlockImageGenDeg.Statement) : ReductionToProjectiveBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ I d hI
  obtain ⟨d₀, r, M, N, d', hy, hk, hB, hmet, hchi⟩ := hIm D K ι Ω d

  have h1 := hMC D K ι Ω I d d₀ hI hy hk

  have h2 := (hRP D Ω (Fin r) I d' hI).2

  have hdeg : d₀.A.a = unitDeg d.k₀ := hk ▸ d₀.deg
  have htop : I K ι (mCoordIdeal d₀.y) (D + 1) (fun _ => d₀.A) = top I d'.x d'.m D := by
    rw [hy]
    exact hTop D K ι Ω (Fin r) I d.y d.k₀ d₀.A M N d'.x d'.m hI d.arith d.birat d'.arith hB hdeg
      d₀.semipos.1 d'.smooth hmet

  have hg : genDeg (ι := GlobalTheory (Fin r)) (coordIdeal ℤ d'.x) D 1 = genDeg (mCoordIdeal d.y) D d.A.a := by
    rw [d.deg]
    exact hGD D K ι Ω (Fin r) d.y d.k₀ M N d'.x d.arith d.birat hB
  rw [hg] at h2
  refine (h2.sub h1).congr_left fun n => ?_
  simp only [hsDefect, hchi n, htop]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
