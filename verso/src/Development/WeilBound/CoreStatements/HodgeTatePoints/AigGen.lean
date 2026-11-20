import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordFibreDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreMultiHomog
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGenFibreChartDeg
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordRatioDeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartScalingIndep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PAdjoinIndepRelfinrank

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PositivityTheory.HtPt.Aig

/- English proof (translation)
The claim follows from `GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.proof GroundTheory.Heights₂.Heights.Targets.FibreMultiHomog.proof (GroundTheory.Heights₂.Heights.Targets.GenFibreChartDeg.proof GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.proof GroundTheory.Heights₂.Heights.Inter.Adjo …`.
-/
theorem coordFibreDeg : GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.Statement :=
  GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.proof GroundTheory.Heights₂.Heights.Targets.FibreMultiHomog.proof
    (GroundTheory.Heights₂.Heights.Targets.GenFibreChartDeg.proof GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.proof
      GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.proof)
    GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg.proof

/- English proof (translation)
Introduce `I hI K _ ι _ K' _ ι' _ κ v P' d G J L L' hv hP' hP hJ hL hLL'`. Take `⟨Ω, _, y, hy, -⟩` from `GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalModelExists.proof K' ι' P' d hP'`. Substitute `hy` using the available equality. Establish `: CharZero Ω`. Use `charZero_of_inj_zero fun n hn => ?_` and prove the remaining obligations.

Establish `hz : ((n : ℤ) : Ω) = 0` using `by exact_mod_cast hn`. Establish `hmem : (C (n : ℤ) : MRing ι') ∈ mCoordIdeal y`. Simplify using `only [mCoordIdeal, RingHom.mem_ker, mConeMap, eq_intCast]`. Rewrite using `[map_intCast, ← map_intCast (C : Ω →+* MvPolynomial K' Ω), hz, map_zero]`. Establish `h2 : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι')` using `hmem`.

Rewrite `h2` using `[hP'.2.2.1]`. Conclude with `(Ideal.mem_bot).1 h2` after adjusting the coercions. Establish `hV : IsProjVarF (fibreIdeal κ G) 0` using `hFD K ι K' ι' κ v (mCoordIdeal y) d 0 G hv hP' hP`. Use `choose i hi using hV.1.2.2`. Establish `h0` using `hJ.1 (fibreIdeal κ G) Fin.elim0 i hV hi`.

Rewrite using `[hPF I hI K ι K' ι' κ v Ω y d L L' hv hP' hP hL hLL', h0, coordFibreDeg K ι K' ι' κ v Ω y d G i hv hP' hP hi, Int.cast_natCast]`.
-/
theorem genDeg_of_coord (hPF : PFCoordStatement) (hFD : FibreDimStatement) : GenDegStatement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d G J L L' hv hP' hP hJ hL hLL'
  obtain ⟨Ω, _, y, hy, -⟩ :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalModelExists.proof K' ι' P' d hP'
  subst hy
  have : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hz : ((n : ℤ) : Ω) = 0 := by exact_mod_cast hn
    have hmem : (C (n : ℤ) : MRing ι') ∈ mCoordIdeal y := by
      simp only [mCoordIdeal, RingHom.mem_ker, mConeMap, eq_intCast]
      rw [map_intCast, ← map_intCast (C : Ω →+* MvPolynomial K' Ω), hz, map_zero]
    have h2 : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι') := hmem
    rw [hP'.2.2.1] at h2
    exact_mod_cast (Ideal.mem_bot).1 h2
  have hV : IsProjVarF (fibreIdeal κ G) 0 := hFD K ι K' ι' κ v (mCoordIdeal y) d 0 G hv hP' hP
  choose i hi using hV.1.2.2
  have h0 := hJ.1 (fibreIdeal κ G) Fin.elim0 i hV hi
  rw [hPF I hI K ι K' ι' κ v Ω y d L L' hv hP' hP hL hLL', h0,
    coordFibreDeg K ι K' ι' κ v Ω y d G i hv hP' hP hi, Int.cast_natCast]

/- English proof (translation)
The claim follows from `genDeg_of_coord`.
-/
theorem genDeg : PFCoordStatement → FibreDimStatement → GenDegStatement :=
  genDeg_of_coord

end PositivityTheory.HtPt.Aig
