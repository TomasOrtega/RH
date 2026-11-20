import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PoincareLelongRegularised
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PoincareLelongLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

/- English proof (translation)
Introduce `K _ ι _ P n L A B s hP hL hA hB hBa hs`. Take `⟨a, ha, hsa, -⟩` from `id hs`. Establish `hS : ∀ ε ∈ Set.Ioi (0 : ℝ), ptsIntegral P (Fin.cons (regLog A s ε) (pot L)) (fun z => Real.log (B.h z)) = ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (regLog A s ε)`. Introduce `ε hε`. Establish `h` using `hSt K ι P n L (regLine A s ε ha hsa) B hP hL (isSmoothHerm_regLine hA hε ha hsa) hB (regLine_a A s ε ha hsa) hBa`.

Rewrite `h` using `[log_regLine]`. Conclude with `h.symm`. Conclude with `tendsto_nhds_unique (hReg K ι P n L A B s hP hL hA hB hBa hs) ((hLim K ι P n L A B s hP hL hA hB hBa hs).congr' (eventually_nhdsWithin_of_forall hS))`.
-/
theorem PoincareLelongAlt.of_found (hSt : StokesStatement) (hReg : PoincareLelongRegularised.Statement)
    (hLim : PoincareLelongLimit.Statement) : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticPoincareLelongFormula := by
  intro K _ ι _ P n L A B s hP hL hA hB hBa hs
  obtain ⟨a, ha, hsa, -⟩ := id hs
  have hS : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ptsIntegral P (Fin.cons (regLog A s ε) (pot L)) (fun z => Real.log (B.h z)) =
        ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (regLog A s ε) := by
    intro ε hε
    have h := hSt K ι P n L (regLine A s ε ha hsa) B hP hL (isSmoothHerm_regLine hA hε ha hsa) hB
      (regLine_a A s ε ha hsa) hBa
    rw [log_regLine] at h
    exact h.symm
  exact tendsto_nhds_unique (hReg K ι P n L A B s hP hL hA hB hBa hs)
    ((hLim K ι P n L A B s hP hL hA hB hBa hs).congr' (eventually_nhdsWithin_of_forall hS))

end GroundTheory.Heights₂.Heights.Targets
