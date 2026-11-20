import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsBilinear
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegrePartition
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem StokesStatement.of_found (hBil : PtsBilinear.Statement) (hPart : SegrePartition.Statement)
    (hChart : SegreChart.Statement) (hSV : StokesOnVariety.Statement) :
    ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement := by
  classical
  intro K _ ι _ P n L B B' hP hL hB hB' hB0 hB'0
  have hw := isDegZeroSmooth_log hB hB0
  have hw' := isDegZeroSmooth_log hB' hB'0
  have hne : ∀ k, Nonempty (ι k) := fun k => by
    obtain ⟨i, -⟩ := hP.2.1.2.2 k
    exact ⟨i⟩
  obtain ⟨δ, hδ, ρ, hρs, hρ1, hρ0⟩ := hPart K ι hne

  have hpiece : ∀ i, IsDegZeroSmooth (fun z => ρ i z * Real.log (B.h z)) := fun i => (hρs i).mul hw

  have key : ∀ i, ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
        (fun z => ρ i z * Real.log (B.h z)) =
      ptsIntegral P (Fin.cons (fun z => ρ i z * Real.log (B.h z)) (pot L))
        (fun z => Real.log (B'.h z)) := by
    intro i
    obtain ⟨m, Js, U, V, Φ, hJ, hU, h1, h2⟩ := hChart K ι P n L (fun z => ρ i z * Real.log (B.h z))
      (fun z => Real.log (B'.h z)) i δ hP hL (hpiece i) hw' hδ
      (fun z hz => by simp only [hρ0 i z hz, zero_mul])
    rw [h1, h2]
    refine Finset.sum_congr rfl fun J hJs => ?_
    obtain ⟨hJp, hJd, hUs, hVs, hΦs⟩ := hJ J hJs
    exact hSV m n J U V Φ hJp hJd hUs hVs hΦs (Or.inl hU)
  have hsum : (fun z => Real.log (B.h z)) = fun z => ∑ i, ρ i z * Real.log (B.h z) := by
    funext z
    rw [← Finset.sum_mul, hρ1 z, one_mul]
  obtain ⟨hA, hC⟩ := hBil K ι P n L _ (fun i z => ρ i z * Real.log (B.h z))
    (fun z => Real.log (B'.h z)) hP hL hpiece hw'
  calc ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L)) (fun z => Real.log (B.h z))
      = ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
          (fun z => ∑ i, ρ i z * Real.log (B.h z)) := by rw [← hsum]
    _ = ∑ i, ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
          (fun z => ρ i z * Real.log (B.h z)) := hA
    _ = ∑ i, ptsIntegral P (Fin.cons (fun z => ρ i z * Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := Finset.sum_congr rfl fun i _ => key i
    _ = ptsIntegral P (Fin.cons (fun z => ∑ i, ρ i z * Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := hC.symm
    _ = ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := by rw [← hsum]

end GroundTheory.Heights₂.Heights
