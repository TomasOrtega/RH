import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryComplementOpenDenseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothContinuousLimsupExtEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySmoothBoundPotentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperSemicontinuousLimsupExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPotentialContinuousOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPshOfLocallyIsPshStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPshCongrOnStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

namespace GlobalTheory.ExtLogGrowth
open Filter Topology

open ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic in

/- English proof (translation)
Introduce `D Y _ _ _ A L s m W hB Θ u C₁ hΘ hu hpos hgr`. Take `⟨hop, hde⟩` from `GlobalTheory.T.boundary_complement_open_dense D Y A L s m W hB`. Take `⟨hcont, heq⟩` from `GlobalTheory.T.smooth_continuous_limsup_ext_eq D Y A (opn s) u hop hu`. Establish `hloc : ∀ y : Y, ∃ O : Set Y, IsOpen O ∧ y ∈ O ∧ ∃ M : ℝ, ∀ y' ∈ O ∩ opn s, u y' ≤ M`. Introduce `y`.

Distinguish the cases in `hy : y ∈ opn s`. Establish `hca : ContinuousAt u y` using `hcont.continuousAt (hop.mem_nhds hy)`. Take `⟨O, hO, hOo, hyO⟩` from `mem_nhds_iff.1 (hca.preimage_mem_nhds (Iio_mem_nhds (lt_add_one (u y))))`. Conclude with `⟨O, hOo, hyO, u y + 1, fun y' hy' => (hO hy'.1).le⟩`. Take `⟨j, hj⟩` from `A.cover y`.

Establish `hz0 : A.chart j y ∈ chartPart A j (Θ.U y)` using `⟨(A.chart j).map_source hj, by show (A.chart j).symm (A.chart j y) ∈ Θ.U y`. Rewrite using `[(A.chart j).left_inv hj]`. Conclude with `Θ.mem_U y⟩`. Take `⟨V, hVo, hz0V, ⟨M, hM⟩, -⟩` from `GlobalTheory.T.boundary_smooth_bound_potential D Y A L s m W hB Θ u C₁ hΘ hu hpos hgr y j _ hz0 (by rwa [(A.chart j).left_inv hj])`. Use `⟨(A.chart j).source ∩ A.chart j ⁻¹' V, (A.chart j).isOpen_inter_preimage hVo, ⟨hj, hz0V⟩, M, ?_⟩` and prove the remaining obligations.

Introduce and unpack `y' ⟨⟨hy's, hy'V⟩, hy'o⟩`. Use `hM _ hy'V (by rwa [(A.chart j).left_inv hy's])` as an intermediate fact. Rewrite `this` using `[(A.chart j).left_inv hy's]`. Then use the resulting hypothesis. Use `choose O hOo hyO M hM using hloc`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover O hOo (fun y _ => Set.mem_iUnion.2 ⟨y, hyO y⟩)`.

Establish `hbd : ∀ y ∈ opn s, u y ≤ ∑ y' ∈ t, |M y'|`. Introduce `y hy`. Take `⟨y', hy't, hyO'⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ y))`. Conclude with `(hM y' y ⟨hyO', hy⟩).trans ((le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (M i)) hy't))`. Use `⟨⟨_, hbd⟩, heq, ?_⟩` and prove the remaining obligations.

Introduce `x j`. Establish `hvle : ∀ y, limsupExt (opn s) u y ≤ ((∑ y' ∈ t, |M y'| : ℝ) : EReal)`. Introduce `y`. Apply `Filter.limsup_le_of_le (by isBoundedDefault)` to reduce the goal to its premises. Conclude with `eventually_nhdsWithin_of_forall fun y' hy' => EReal.coe_le_coe_iff.2 (hbd y' hy')`.

Establish `hUo : IsOpen (chartPart A j (Θ.U x))` using `(A.chart j).isOpen_inter_preimage_symm (Θ.isOpen_U x)`. Establish `hcompat : IsCompatChart A (A.chart j)` using `fun k => ⟨A.holo k j, A.holo j k⟩`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z _`. Conclude with `(EReal.add_lt_top (EReal.coe_ne_top _) ((hvle _).trans_lt (EReal.coe_lt_top _)).ne).ne`.

Introduce `z hz`. Establish `hc : ContinuousWithinAt (fun z => ((2 * Θ.φ x ((A.chart j).symm z) : ℝ) : EReal)) (chartPart A j (Θ.U x)) z` using `continuous_coe_real_ereal.continuousAt.comp_continuousWithinAt ((continuousWithinAt_const.mul ((hΘ.1 x j).continuousOn z hz)))`. Establish `hv : UpperSemicontinuousWithinAt (fun z => limsupExt (opn s) u ((A.chart j).symm z)) (chartPart A j (Θ.U x)) z`. Introduce `b hb`. Establish `h1` using `GlobalTheory.T.upperSemicontinuous_limsupExt Y (opn s) u ((A.chart j).symm z) b hb`.

Establish `h2 : Tendsto (A.chart j).symm (𝓝[chartPart A j (Θ.U x)] z) (𝓝 ((A.chart j).symm z))` using `((A.chart j).continuousOn_symm z hz.1).mono_left (nhdsWithin_mono _ fun w hw => hw.1)`. Conclude with `h2.eventually h1`. Use `hc.upperSemicontinuousWithinAt.add' hv ?_` and prove the remaining obligations. Conclude with `EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))`. Introduce `z hz`.

Rewrite using `[mem_closure_iff_nhds]`. Introduce `T hT`. Establish `hTU : T ∩ chartPart A j (Θ.U x) ∈ 𝓝 z` using `Filter.inter_mem hT (hUo.mem_nhds hz)`. Establish `himg : (A.chart j).symm '' (T ∩ chartPart A j (Θ.U x)) ∈ 𝓝 ((A.chart j).symm z)` using `(A.chart j).symm.image_mem_nhds hz.1 hTU`. Take `⟨y, ⟨z', hz', rfl⟩, hyo⟩` from `mem_closure_iff_nhds.1 (hde ((A.chart j).symm z)) _ himg`.

Use `⟨z', hz'.1, hz'.2, ?_⟩` and prove the remaining obligations. Use `show ((2 * Θ.φ x ((A.chart j).symm z') : ℝ) : EReal) + limsupExt (opn s) u ((A.chart j).symm z') ≠ ⊥`. Rewrite using `[heq _ hyo, ← EReal.coe_add]`. Conclude with `EReal.coe_ne_bot _`. Introduce `κ`.

Apply `GlobalTheory.T.isPsh_of_locally_isPsh D _ _ hUo` to reduce the goal to its premises. Introduce `z₀ hz₀`. Distinguish the cases in `hy : (A.chart j).symm z₀ ∈ opn s`. Take `⟨hVo, -, -, hVpsh⟩` from `GlobalTheory.T.chart_potential_continuous_on D Y A Θ u (opn s) x (A.chart j) hop hΘ hu hpos hcompat`. Use `⟨_, hVo, ⟨hz₀.1, hz₀.2, hy⟩, GlobalTheory.T.isPsh_congr_divisor D _ _ _ (hVpsh κ) ?_⟩` and prove the remaining obligations.

Introduce `w hw`. Use `show _ = (max (((2 * Θ.φ x ((A.chart j).symm w) : ℝ) : EReal) + limsupExt (opn s) u ((A.chart j).symm w)) ((-κ : ℝ) : EReal)).toReal`. Rewrite using `[heq _ hw.2.2, ← EReal.coe_add, ← (EReal.coe_strictMono.monotone).map_max, EReal.toReal_coe]`. Take `⟨V, hVo, hz₀V, -, hV⟩` from `GlobalTheory.T.boundary_smooth_bound_potential D Y A L s m W hB Θ u C₁ hΘ hu hpos hgr x j z₀ hz₀ hy`. Conclude with `⟨V, hVo, hz₀V, hV κ⟩`.
-/
theorem extension_of_log_growth : GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.Extension := by
  intro D Y _ _ _ A L s m W hB Θ u C₁ hΘ hu hpos hgr
  obtain ⟨hop, hde⟩ := GlobalTheory.T.boundary_complement_open_dense D Y A L s m W hB
  obtain ⟨hcont, heq⟩ := GlobalTheory.T.smooth_continuous_limsup_ext_eq D Y A (opn s) u hop hu
  have hloc : ∀ y : Y, ∃ O : Set Y, IsOpen O ∧ y ∈ O ∧ ∃ M : ℝ, ∀ y' ∈ O ∩ opn s, u y' ≤ M := by
    intro y
    by_cases hy : y ∈ opn s
    · have hca : ContinuousAt u y := hcont.continuousAt (hop.mem_nhds hy)
      obtain ⟨O, hO, hOo, hyO⟩ :=
        mem_nhds_iff.1 (hca.preimage_mem_nhds (Iio_mem_nhds (lt_add_one (u y))))
      exact ⟨O, hOo, hyO, u y + 1, fun y' hy' => (hO hy'.1).le⟩
    · obtain ⟨j, hj⟩ := A.cover y
      have hz0 : A.chart j y ∈ chartPart A j (Θ.U y) :=
        ⟨(A.chart j).map_source hj, by
          show (A.chart j).symm (A.chart j y) ∈ Θ.U y
          rw [(A.chart j).left_inv hj]; exact Θ.mem_U y⟩
      obtain ⟨V, hVo, hz0V, ⟨M, hM⟩, -⟩ := GlobalTheory.T.boundary_smooth_bound_potential D Y A L s m W hB Θ u C₁ hΘ hu hpos hgr y j _ hz0
        (by rwa [(A.chart j).left_inv hj])
      refine ⟨(A.chart j).source ∩ A.chart j ⁻¹' V, (A.chart j).isOpen_inter_preimage hVo,
        ⟨hj, hz0V⟩, M, ?_⟩
      rintro y' ⟨⟨hy's, hy'V⟩, hy'o⟩
      have := hM _ hy'V (by rwa [(A.chart j).left_inv hy's])
      rwa [(A.chart j).left_inv hy's] at this
  choose O hOo hyO M hM using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hOo
    (fun y _ => Set.mem_iUnion.2 ⟨y, hyO y⟩)
  have hbd : ∀ y ∈ opn s, u y ≤ ∑ y' ∈ t, |M y'| := by
    intro y hy
    obtain ⟨y', hy't, hyO'⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact (hM y' y ⟨hyO', hy⟩).trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun i _ => abs_nonneg (M i)) hy't))
  refine ⟨⟨_, hbd⟩, heq, ?_⟩
  intro x j
  have hvle : ∀ y, limsupExt (opn s) u y ≤ ((∑ y' ∈ t, |M y'| : ℝ) : EReal) := by
    intro y
    apply Filter.limsup_le_of_le (by isBoundedDefault)
    exact eventually_nhdsWithin_of_forall fun y' hy' => EReal.coe_le_coe_iff.2 (hbd y' hy')
  have hUo : IsOpen (chartPart A j (Θ.U x)) :=
    (A.chart j).isOpen_inter_preimage_symm (Θ.isOpen_U x)
  have hcompat : IsCompatChart A (A.chart j) := fun k => ⟨A.holo k j, A.holo j k⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z _
    exact (EReal.add_lt_top (EReal.coe_ne_top _) ((hvle _).trans_lt (EReal.coe_lt_top _)).ne).ne
  · intro z hz
    have hc : ContinuousWithinAt (fun z => ((2 * Θ.φ x ((A.chart j).symm z) : ℝ) : EReal))
        (chartPart A j (Θ.U x)) z :=
      continuous_coe_real_ereal.continuousAt.comp_continuousWithinAt
        ((continuousWithinAt_const.mul ((hΘ.1 x j).continuousOn z hz)))
    have hv : UpperSemicontinuousWithinAt (fun z => limsupExt (opn s) u ((A.chart j).symm z))
        (chartPart A j (Θ.U x)) z := by
      intro b hb
      have h1 := GlobalTheory.T.upperSemicontinuous_limsupExt Y (opn s) u ((A.chart j).symm z) b hb
      have h2 : Tendsto (A.chart j).symm (𝓝[chartPart A j (Θ.U x)] z) (𝓝 ((A.chart j).symm z)) :=
        ((A.chart j).continuousOn_symm z hz.1).mono_left (nhdsWithin_mono _ fun w hw => hw.1)
      exact h2.eventually h1
    refine hc.upperSemicontinuousWithinAt.add' hv ?_
    exact EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))
  · intro z hz
    rw [mem_closure_iff_nhds]
    intro T hT
    have hTU : T ∩ chartPart A j (Θ.U x) ∈ 𝓝 z := Filter.inter_mem hT (hUo.mem_nhds hz)
    have himg : (A.chart j).symm '' (T ∩ chartPart A j (Θ.U x)) ∈ 𝓝 ((A.chart j).symm z) :=
      (A.chart j).symm.image_mem_nhds hz.1 hTU
    obtain ⟨y, ⟨z', hz', rfl⟩, hyo⟩ := mem_closure_iff_nhds.1 (hde ((A.chart j).symm z)) _ himg
    refine ⟨z', hz'.1, hz'.2, ?_⟩
    show ((2 * Θ.φ x ((A.chart j).symm z') : ℝ) : EReal) + limsupExt (opn s) u ((A.chart j).symm z') ≠ ⊥
    rw [heq _ hyo, ← EReal.coe_add]
    exact EReal.coe_ne_bot _
  · intro κ
    apply GlobalTheory.T.isPsh_of_locally_isPsh D _ _ hUo
    intro z₀ hz₀
    by_cases hy : (A.chart j).symm z₀ ∈ opn s
    · obtain ⟨hVo, -, -, hVpsh⟩ := GlobalTheory.T.chart_potential_continuous_on D Y A Θ u (opn s) x (A.chart j) hop hΘ hu hpos hcompat
      refine ⟨_, hVo, ⟨hz₀.1, hz₀.2, hy⟩, GlobalTheory.T.isPsh_congr_divisor D _ _ _ (hVpsh κ) ?_⟩
      intro w hw
      show _ = (max (((2 * Θ.φ x ((A.chart j).symm w) : ℝ) : EReal) + limsupExt (opn s) u ((A.chart j).symm w)) ((-κ : ℝ) : EReal)).toReal
      rw [heq _ hw.2.2, ← EReal.coe_add, ← (EReal.coe_strictMono.monotone).map_max, EReal.toReal_coe]
    · obtain ⟨V, hVo, hz₀V, -, hV⟩ := GlobalTheory.T.boundary_smooth_bound_potential D Y A L s m W hB Θ u C₁ hΘ hu hpos hgr x j z₀ hz₀ hy
      exact ⟨V, hVo, hz₀V, hV κ⟩

end GlobalTheory.ExtLogGrowth
