import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveClosedPointChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def segre (y : (Σ k, ι k) → Ω) : (Σ _ : Unit, ∀ k, ι k) → Ω :=
  fun q ↦ ∏ k, y ⟨k, q.2 k⟩

omit [∀ k, Fintype (ι k)] in
/- English proof (translation)
Simplify using `[segre, Finset.prod_ne_zero_iff]`.
-/
theorem segre_ne_zero_iff (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) :
    segre y ⟨(), f⟩ ≠ 0 ↔ ∀ k, y ⟨k, f k⟩ ≠ 0 := by
  simp [segre, Finset.prod_ne_zero_iff]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Simplify using `[segre, Finset.prod_div_distrib]`.
-/
theorem segre_ratio (y : (Σ k, ι k) → Ω) (f g : ∀ k, ι k) :
    segre y ⟨(), g⟩ / segre y ⟨(), f⟩ = ∏ k, y ⟨k, g k⟩ / y ⟨k, f k⟩ := by
  simp [segre, Finset.prod_div_distrib]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[Finset.prod_eq_single p.1]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Rewrite using `[Function.update_of_ne hk, div_self (hf k)]`. Simplify using the standard rewrite rules.
-/
theorem prod_ratio_update [DecidableEq K] (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0)
    (p : Σ k, ι k) :
    ∏ k, y ⟨k, Function.update f p.1 p.2 k⟩ / y ⟨k, f k⟩ = y p / y ⟨p.1, f p.1⟩ := by
  rw [Finset.prod_eq_single p.1]
  · simp
  · intro k _ hk
    rw [Function.update_of_ne hk, div_self (hf k)]
  · simp

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[chartRingZ, Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨⟨⟨⟩, g⟩, rfl⟩`. Express the relevant statement in the definitionally equal form `segre y ⟨(), g⟩ / segre y ⟨(), f⟩ ∈ chartRingZ y f`. Rewrite using `[segre_ratio]`.

Conclude with `prod_mem fun k _ ↦ Algebra.subset_adjoin ⟨⟨k, g k⟩, rfl⟩`. Rewrite using `[chartRingZ, Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨p, rfl⟩`. Express the relevant statement in the definitionally equal form `y p / y ⟨p.1, f p.1⟩ ∈ chartRingZ (segre y) (fun _ ↦ f)`. Rewrite using `[← prod_ratio_update y f hf p, ← segre_ratio]`.

Conclude with `Algebra.subset_adjoin ⟨⟨(), Function.update f p.1 p.2⟩, rfl⟩`.
-/
theorem chartRingZ_segre (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) :
    chartRingZ (segre y) (fun _ ↦ f) = chartRingZ y f := by
  classical
  apply le_antisymm
  · rw [chartRingZ, Algebra.adjoin_le_iff]
    rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
    change segre y ⟨(), g⟩ / segre y ⟨(), f⟩ ∈ chartRingZ y f
    rw [segre_ratio]
    exact prod_mem fun k _ ↦ Algebra.subset_adjoin ⟨⟨k, g k⟩, rfl⟩
  · rw [chartRingZ, Algebra.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    change y p / y ⟨p.1, f p.1⟩ ∈ chartRingZ (segre y) (fun _ ↦ f)
    rw [← prod_ratio_update y f hf p, ← segre_ratio]
    exact Algebra.subset_adjoin ⟨⟨(), Function.update f p.1 p.2⟩, rfl⟩

/- English proof (translation)
Use `charZero_of_inj_zero fun n hn ↦ ?_` and prove the remaining obligations. Establish `hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι)`. Rewrite using `[Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_C]`. Rewrite using `[eq_intCast, Int.cast_natCast, ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]`. Rewrite `hmem` using `[show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1, Ideal.mem_bot]`.

Conclude with `hmem` after adjusting the coercions.
-/
theorem charZero_of_isArithVar {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn ↦ ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_C]
    rw [eq_intCast, Int.cast_natCast, ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1, Ideal.mem_bot] at hmem
  exact_mod_cast hmem

/- English proof (translation)
Establish `h : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0` using `fun k ↦ by`. Take `⟨i, hi⟩` from `hP.2.1.2.2 k`. Use `⟨i, fun h0 ↦ hi ?_⟩` and prove the remaining obligations. Rewrite using `[mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]`. Use `choose f hf using h`.

Conclude with `⟨f, hf⟩`.
-/
theorem exists_chart {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) :
    ∃ f : ∀ k, ι k, ∀ k, y ⟨k, f k⟩ ≠ 0 := by
  have h : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k ↦ by
    obtain ⟨i, hi⟩ := hP.2.1.2.2 k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]
  choose f hf using h
  exact ⟨f, hf⟩

/- English proof (translation)
Rewrite using `[segre_ratio]`. Use `(IsIntegral.prod _ fun k _ ↦ ?_).isAlgebraic` and prove the remaining obligations. Conclude with `(IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_ratio hP f hf ⟨k, g k⟩).isIntegral`.
-/
theorem isAlgebraic_segre_ratio [CharZero Ω] {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1)
    (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) :
    IsAlgebraic ℚ (segre y ⟨(), g⟩ / segre y ⟨(), f⟩) := by
  rw [segre_ratio]
  refine (IsIntegral.prod _ fun k _ ↦ ?_).isAlgebraic
  exact (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_ratio hP f hf ⟨k, g k⟩).isIntegral

/- English proof (translation)
Use `CoordConeArithVar.full Unit (fun _ ↦ ∀ k, ι k) Ω (segre y) (fun _ ↦ f) 0 Fin.elim0 ⟨()⟩ (fun _ ↦ (segre_ne_zero_iff y f).mpr hf) algebraicIndependent_empty_type (fun i ↦ i.elim0) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨⟨⟩, g⟩, rfl⟩`. Conclude with `IsAlgebraic.extendScalars (RingHom.injective _) (isAlgebraic_segre_ratio hP f hf g)`.
-/
theorem isArithVar_segre [DecidableEq K] [CharZero Ω] {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1)
    (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) : IsArithVar (mCoordIdeal (segre y)) 1 := by
  refine CoordConeArithVar.full Unit (fun _ ↦ ∀ k, ι k) Ω (segre y) (fun _ ↦ f) 0 Fin.elim0 ⟨()⟩
    (fun _ ↦ (segre_ne_zero_iff y f).mpr hf) algebraicIndependent_empty_type (fun i ↦ i.elim0) ?_
  rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
  exact IsAlgebraic.extendScalars (RingHom.injective _) (isAlgebraic_segre_ratio hP f hf g)

end SegreChart

end

end GroundTheory.Heights₂.Heights.Targets
