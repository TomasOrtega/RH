import Formalism.LatticeTheta.LatticeSummableDecay

open MeasureTheory Filter Asymptotics Topology

noncomputable section

namespace Formalism.H

/- English proof (translation)
Introduce `L _ _ g b hb hg`. Take `⟨C, hC⟩` from `hg.bound`. Establish `hrank : Module.finrank ℤ L = Module.finrank ℝ V` using `ZLattice.rank ℝ L`. Establish `hsum : Summable fun z : L => ‖z‖ ^ (-b)` using `ZLattice.summable_norm_rpow L (-b) (by rw [hrank]; linarith)`. Establish `ht : Tendsto (Subtype.val : L → V) cofinite (cocompact V)` using `(AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)).tendsto_coe_cofinite_of_isDiscrete (isDiscrete_iff_discreteTopology.mpr inferInstance)`.

Use `Summable.of_norm_bounded_eventually (hsum.mul_left C) ?_` and prove the remaining obligations. Use `filter_upwards [ht.eventually hC] with z hz`. Rewrite `hz` using `[Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]`. Conclude with `hz`.
-/
theorem lattice_summable_decay (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : LatticeSummableDecay V := by
  intro L _ _ g b hb hg
  obtain ⟨C, hC⟩ := hg.bound
  have hrank : Module.finrank ℤ L = Module.finrank ℝ V := ZLattice.rank ℝ L
  have hsum : Summable fun z : L => ‖z‖ ^ (-b) :=
    ZLattice.summable_norm_rpow L (-b) (by rw [hrank]; linarith)
  have ht : Tendsto (Subtype.val : L → V) cofinite (cocompact V) :=
    (AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)).tendsto_coe_cofinite_of_isDiscrete
      (isDiscrete_iff_discreteTopology.mpr inferInstance)
  refine Summable.of_norm_bounded_eventually (hsum.mul_left C) ?_
  filter_upwards [ht.eventually hC] with z hz
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] at hz
  exact hz

end Formalism.H
