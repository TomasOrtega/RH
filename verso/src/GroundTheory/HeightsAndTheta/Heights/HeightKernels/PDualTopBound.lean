import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace TopDualBound

/- English proof (translation)
Establish `h : (1 : ℝ) + ((i - 1 : ℕ) : ℝ) = i`. Rewrite using `[Nat.cast_sub hi]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [grassConst, h]`.

Evaluate the numerical expressions.
-/
theorem grassConst_lines {i : ℕ} (hi : 1 ≤ i) : grassConst 1 1 (i - 1) = 1 / 2 * Real.log i := by
  have h : (1 : ℝ) + ((i - 1 : ℕ) : ℝ) = i := by
    rw [Nat.cast_sub hi]; push_cast; ring
  simp only [grassConst, h]
  norm_num

/- English proof (translation)
Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem dim_lines {i : ℕ} (hi : 1 ≤ i) : ((1 * 1 * (i - 1) + 1 : ℕ) : ℝ) = i := by
  congr 1; omega

end TopDualBound

/- English proof (translation)
Introduce `hZ2 K _ _ i F T _ _ b hb II hi hII`. Take `⟨T', _, _, ⟨b'⟩⟩` from `hBasis K i (HermLattice.standard K i)`. Establish `hb'` using `hBij K i (HermLattice.standard K i) T' b'`. Use `set g := geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))`. Use `set d : ℝ := (Module.finrank ℚ K : ℝ) with hd`.

Establish `hA` using `hMetric K i F T b hb II hi hII`. Establish `hB` using `hLattice K i F T T' b hb b' hb' II hi hII`. Establish `hC` using `hStd K i T' b' hb' II hi hII`. Establish `hG` using `hDeg K i F T b hb hi`. Establish `hH` using `hGrass hZ2 1 1 (i - 1) le_rfl II hII`.

Rewrite `hH` using `[TopDualBound.dim_lines hi, TopDualBound.grassConst_lines hi]`. Rewrite using `[hA, hB, hC, hG]`. Establish `hd0 : 0 < d` using `by rw [hd]; exact_mod_cast Module.finrank_pos`. Establish `hi0 : (0 : ℝ) < i` using `by exact_mod_cast hi`. Establish `hslope : (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) * (d * g) = -F.degree * g + d * ((i : ℝ) * (1 / 2 * Real.log i) * g)`.

Simplify using `only [HermLattice.slope, normalise]`. Rewrite using `[← hd]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hslope]`. Use `mul_le_mul_of_nonneg_left hH hd0.le` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem DualTopBound.proof (hBasis : DualLatticeBasisExists.Statement)
    (hBij : DualEmbBijective.Statement) (hMetric : DualTopMetricChange.Statement)
    (hLattice : DualTopLatticeChange.Statement) (hStd : DualTopStandard.Statement)
    (hDeg : DualGeomDegStandard.Statement) (hGrass : GrassHeightBound.Statement) :
    DualTopBound.Statement := by
  intro hZ2 K _ _ i F T _ _ b hb II hi hII
  obtain ⟨T', _, _, ⟨b'⟩⟩ := hBasis K i (HermLattice.standard K i)
  have hb' := hBij K i (HermLattice.standard K i) T' b'
  set g := geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hd
  have hA := hMetric K i F T b hb II hi hII
  have hB := hLattice K i F T T' b hb b' hb' II hi hII
  have hC := hStd K i T' b' hb' II hi hII
  have hG := hDeg K i F T b hb hi
  have hH := hGrass hZ2 1 1 (i - 1) le_rfl II hII
  rw [TopDualBound.dim_lines hi, TopDualBound.grassConst_lines hi] at hH
  rw [hA, hB, hC, hG]
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast Module.finrank_pos
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  have hslope : (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) * (d * g) =
      -F.degree * g + d * ((i : ℝ) * (1 / 2 * Real.log i) * g) := by
    simp only [HermLattice.slope, normalise]
    rw [← hd]
    field_simp
  rw [hslope]
  have := mul_le_mul_of_nonneg_left hH hd0.le
  linarith

end GroundTheory.Heights₂.Heights
