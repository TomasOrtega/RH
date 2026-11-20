import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitLocalSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartRing
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartMax
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartResidue
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartMult
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalLengthPlaces
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterChart
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightPlaceCentredSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartTerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

/- English proof (translation)
Introduce `ι _ _ _ n A x s hx hs V hV`. Take `⟨hVmin, hVrel⟩` from `id hV`. Use `choose c hc using hVrel`. Establish `hWV : orbitIdeal x ≤ V` using `le_sup_left.trans hVmin.1.2`. Establish `hxc : ∀ k, x k (c k) ≠ 0` using `fun k h ↦ hc k (hWV (by`.

Rewrite using `[orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]`. Simplify using `[flatCone, h]))`. Take `⟨hft, hfr⟩` from `hR ι n x c hxc`. Use `hM ι n A x s hx hs V hV c hc` as an intermediate fact. Take `⟨hf0, hterm⟩` from `hT ι n A x s hs c hxc`.

Set `_ : Algebra (ratioField x) (coordField x)` to `(IntermediateField.inclusion (ratioField_le_coordField x)).toRingHom.toAlgebra`. Establish `hset : {v : FinitePlace (coordField x) | orbitCenter x v = V} = {v : FinitePlace (coordField x) | AbsCentredAt (chartRing x c) (chartPoint x c V) fun u ↦ v (algebraMap (ratioField x) (coordField x) u)}` using `Set.ext fun v ↦ hC ι n A x s hx hs V hV c hc v`. Establish `hsum : ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V}, (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) = ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V}, -Real.log (v (algebraMap (ratioField x) (coordField x) (chartEval x c s)))` using `finsum_mem_congr rfl fun v hv ↦ hterm v fun k hk ↦ hc k (by`. Rewrite using `[← (show orbitCenter x v = V from hv)]`. Conclude with `hk)`.

Establish `hdeg` using `Module.finrank_mul_finrank ℚ (ratioField x) (coordField x)`. Rewrite using `[hsum, hset, hS (ratioField x) (coordField x) (chartRing x c) (chartPoint x c V), hU ι n A x s hx hs V hV c hc, hF ι n A x s hx hs V hV c hc, ← hP (ratioField x) (chartRing x c) hft hfr (chartPoint x c V) (chartEval x c s) hf0, ← hdeg]`. Use `push_cast`. Put the polynomial expressions in normal form. Both sides reduce to the same expression.
-/
theorem OrbitLocalSum.proof (hR : OrbitChartRing.Statement) (hM : OrbitChartMax.Statement)
    (hF : OrbitChartResidue.Statement) (hU : OrbitChartMult.Statement)
    (hP : LocalLengthPlaces.Statement) (hC : OrbitCenterChart.Statement)
    (hS : PlaceCentredSum.Statement) (hT : OrbitChartTerm.Statement) :
    OrbitLocalSum.Statement := by
  intro ι _ _ _ n A x s hx hs V hV
  obtain ⟨hVmin, hVrel⟩ := id hV
  choose c hc using hVrel
  have hWV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  have hxc : ∀ k, x k (c k) ≠ 0 := fun k h ↦ hc k (hWV (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [flatCone, h]))
  obtain ⟨hft, hfr⟩ := hR ι n x c hxc
  have := hM ι n A x s hx hs V hV c hc
  obtain ⟨hf0, hterm⟩ := hT ι n A x s hs c hxc
  let _ : Algebra (ratioField x) (coordField x) :=
    (IntermediateField.inclusion (ratioField_le_coordField x)).toRingHom.toAlgebra
  have hset : {v : FinitePlace (coordField x) | orbitCenter x v = V} =
      {v : FinitePlace (coordField x) | AbsCentredAt (chartRing x c) (chartPoint x c V)
        fun u ↦ v (algebraMap (ratioField x) (coordField x) u)} :=
    Set.ext fun v ↦ hC ι n A x s hx hs V hV c hc v
  have hsum : ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
      (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) =
      ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
        -Real.log (v (algebraMap (ratioField x) (coordField x) (chartEval x c s))) :=
    finsum_mem_congr rfl fun v hv ↦ hterm v fun k hk ↦ hc k (by
      rw [← (show orbitCenter x v = V from hv)]
      exact hk)
  have hdeg := Module.finrank_mul_finrank ℚ (ratioField x) (coordField x)
  rw [hsum, hset, hS (ratioField x) (coordField x) (chartRing x c) (chartPoint x c V),
    hU ι n A x s hx hs V hV c hc, hF ι n A x s hx hs V hV c hc,
    ← hP (ratioField x) (chartRing x c) hft hfr (chartPoint x c V) (chartEval x c s) hf0, ← hdeg]
  push_cast
  ring_nf
  rfl

end GroundTheory.Heights₂.Heights
