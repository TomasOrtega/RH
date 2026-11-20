import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace TopDualBound

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Evaluate the numerical expressions.
-/
theorem grassConst_lines {i : ℕ} (hi : 1 ≤ i) : grassConst 1 1 (i - 1) = 1 / 2 * Real.log i := by
  have h : (1 : ℝ) + ((i - 1 : ℕ) : ℝ) = i := by
    rw [Nat.cast_sub hi]; push_cast; ring
  simp only [grassConst, h]
  norm_num

/- English proof (translation)
Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers.
-/
theorem dim_lines {i : ℕ} (hi : 1 ≤ i) : ((1 * 1 * (i - 1) + 1 : ℕ) : ℝ) = i := by
  congr 1; omega

end TopDualBound

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
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
