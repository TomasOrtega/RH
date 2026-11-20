import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertIndexSteps
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveCountObjects
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCurveCharts
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFnFieldTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.CoordinateConeArithVar

noncomputable section

namespace CurveSectionQuotientFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use `charZero_of_inj_zero fun n hn => ?_` and prove the remaining obligations. Establish `h : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι)`. Rewrite using `[Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]`. Establish `e : (C (n : ℤ) : MRing ι) = (n : MRing ι)` using `by simp`. Rewrite using `[e, map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]`.

Rewrite `h` using `[hP, Ideal.mem_bot]`. Conclude with `h` after adjusting the coercions.
-/
theorem charZero (y : (Σ k, ι k) → Ω) (hP : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have h : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    have e : (C (n : ℤ) : MRing ι) = (n : MRing ι) := by simp
    rw [e, map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [hP, Ideal.mem_bot] at h
  exact_mod_cast h

/- English proof (translation)
Introduce `h0`. Apply `hsP` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `s ∈ RingHom.ker (mConeMap y)`. Rewrite using `[RingHom.mem_ker]`. Use `erw [HilbertSamuel.SectionBounded.mConeMap_homog y hs]`.

Rewrite using `[h0, map_zero, zero_mul]`.
-/
theorem aeval_ne_zero (y : (Σ k, ι k) → Ω) {s : MRing ι} {d : K → ℕ} (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d)
    (hsP : s ∉ mCoordIdeal y) : aeval y s ≠ 0 := by
  intro h0
  apply hsP
  change s ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [HilbertSamuel.SectionBounded.mConeMap_homog y hs]
  rw [h0, map_zero, zero_mul]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact IntermediateField.subset_adjoin _ _ hx`. Consider the case `algebraMap r => rw [eq_intCast]`. Conclude with `intCast_mem _ r`. Consider the case `add x z _ _ hx hz => exact add_mem hx hz`.

Consider the case `mul x z _ _ hx hz => exact mul_mem hx hz`.
-/
theorem mem_ratioField [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {b : Ω}
    (hb : b ∈ chartRingZ y c) : b ∈ ratioField y c := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact IntermediateField.subset_adjoin _ _ hx
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

/- English proof (translation)
Establish `htr` using `LowerBoundFree.FnFieldTrdeg.full K ι (ratioField y c) (ratioPtL y c) 0 (birational y c hc) (by rw [mCoordIdeal_ratioPtL y c hc]; exact hP)`. Establish `halg : Algebra.IsAlgebraic ℤ (ratioField y c)` using `trdeg_eq_zero_iff.mp htr`. Establish `h1 : IsAlgebraic ℚ (⟨x, hx⟩ : ratioField y c)` using `(halg.isAlgebraic _).extendScalars (algebraMap ℤ ℚ).injective_int`. Conclude with `IntermediateField.isAlgebraic_iff.mp h1`.
-/
theorem isAlgebraic_of_mem [CharZero Ω] (y : (Σ k, ι k) → Ω) (hP : IsArithVar (mCoordIdeal y) 1)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω} (hx : x ∈ ratioField y c) : IsAlgebraic ℚ x := by
  have htr := LowerBoundFree.FnFieldTrdeg.full K ι (ratioField y c) (ratioPtL y c) 0 (birational y c hc)
    (by rw [mCoordIdeal_ratioPtL y c hc]; exact hP)
  have halg : Algebra.IsAlgebraic ℤ (ratioField y c) := trdeg_eq_zero_iff.mp htr
  have h1 : IsAlgebraic ℚ (⟨x, hx⟩ : ratioField y c) :=
    (halg.isAlgebraic _).extendScalars (algebraMap ℤ ℚ).injective_int
  exact IntermediateField.isAlgebraic_iff.mp h1

/- English proof (translation)
Establish `hq' : q ∈ Algebra.adjoin ℚ (coneRatios y c)`. Rewrite using `[← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun x hx => isAlgebraic_of_mem y hP c hc (IntermediateField.subset_adjoin _ _ hx))]`. Conclude with `hq`. Conclude with `CurveAffineCharts.exists_nat_mul_mem_adjoin hq'`.
-/
theorem exists_nat_mul_mem_chartRingZ [CharZero Ω] (y : (Σ k, ι k) → Ω) (hP : IsArithVar (mCoordIdeal y) 1)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {q : Ω} (hq : q ∈ ratioField y c) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : Ω) * q ∈ chartRingZ y c := by
  have hq' : q ∈ Algebra.adjoin ℚ (coneRatios y c) := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x hx => isAlgebraic_of_mem y hP c hc (IntermediateField.subset_adjoin _ _ hx))]
    exact hq
  exact CurveAffineCharts.exists_nat_mul_mem_adjoin hq'

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `key : ∀ p : Ω, p ≠ 0 → m * p ∈ ratioField y c → x * p ∈ ratioField y c → m / x ∈ ratioField y c` using `fun p hp h1 h2 => by rw [← mul_div_mul_right m x hp]; exact div_mem h1 h2`. Conclude with `key _ (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)) (mem_ratioField y c (hm c hc)) (mem_ratioField y c (hx c hc))`.
-/
theorem div_mem_ratioField [CharZero Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {m x : Ω} (hm : m ∈ chartLat y a 1) (hx : x ∈ chartLat y a 1) :
    m / x ∈ ratioField y c := by
  have key : ∀ p : Ω, p ≠ 0 → m * p ∈ ratioField y c → x * p ∈ ratioField y c → m / x ∈ ratioField y c :=
    fun p hp h1 h2 => by rw [← mul_div_mul_right m x hp]; exact div_mem h1 h2
  exact key _ (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k))
    (mem_ratioField y c (hm c hc)) (mem_ratioField y c (hx c hc))

/- English proof (translation)
Use `charZero y hP.2.2.1` as an intermediate fact. Establish `key : ∀ c : ∀ k, ι k, ∃ n : ℕ, n ≠ 0 ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) → (n : Ω) * (m / x) ∈ chartRingZ y c)`. Introduce `c`. Distinguish the cases in `hc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Take `⟨n, hn, h⟩` from `exists_nat_mul_mem_chartRingZ y hP c hc (div_mem_ratioField y a c hc hm hx)`.

Conclude with `⟨n, hn, fun _ => h⟩`. Conclude with `⟨1, one_ne_zero, fun h => (hc h).elim⟩`. Use `choose N hN0 hN using key`. Establish `hb : ((∏ c, N c : ℕ) : Ω) * (m / x) ∈ curveRing y`. Rewrite using `[mem_curveRing]`.

Introduce `c hc`. Establish `e : ((∏ c', N c' : ℕ) : Ω) * (m / x) = ((∏ c' ∈ Finset.univ.erase c, N c' : ℕ) : Ω) * ((N c : Ω) * (m / x))`. Rewrite using `[← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ c)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `mul_mem (natCast_mem _ _) (hN c hc)`. Use `⟨∏ c, N c, Finset.prod_ne_zero_iff.mpr fun c _ => hN0 c, Submodule.mem_span_singleton.mpr ⟨⟨_, hb⟩, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Subring.smul_def, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_nat_mul_mem_span (y : (Σ k, ι k) → Ω) (hP : IsArithVar (mCoordIdeal y) 1) {a : K → ℤ}
    {m x : Ω} (hm : m ∈ chartLat y a 1) (hx : x ∈ chartLat y a 1) (hx0 : x ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : Ω) * m ∈ Submodule.span (curveRing y) {x} := by
  classical
  have := charZero y hP.2.2.1
  have key : ∀ c : ∀ k, ι k, ∃ n : ℕ, n ≠ 0 ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → (n : Ω) * (m / x) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_chartRingZ y hP c hc (div_mem_ratioField y a c hc hm hx)
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, one_ne_zero, fun h => (hc h).elim⟩
  choose N hN0 hN using key
  have hb : ((∏ c, N c : ℕ) : Ω) * (m / x) ∈ curveRing y := by
    rw [mem_curveRing]
    intro c hc
    have e : ((∏ c', N c' : ℕ) : Ω) * (m / x) =
        ((∏ c' ∈ Finset.univ.erase c, N c' : ℕ) : Ω) * ((N c : Ω) * (m / x)) := by
      rw [← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ c)]
      push_cast; ring
    rw [e]
    exact mul_mem (natCast_mem _ _) (hN c hc)
  refine ⟨∏ c, N c, Finset.prod_ne_zero_iff.mpr fun c _ => hN0 c,
    Submodule.mem_span_singleton.mpr ⟨⟨_, hb⟩, ?_⟩⟩
  rw [Subring.smul_def, smul_eq_mul]
  field_simp

/- English proof (translation)
Take `⟨c, -, hc⟩` from `exists_chart hP`. Establish `hfg : (chartLat y a 1).FG` using `HilbertSamuel.SectionLatticeFinite.proof HilbertSamuel.Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond K ι Ω y a 1 (fun k => ⟨c k, hc k⟩)`. Establish `: Module.Finite ℤ (chartLat y a 1)` using `Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg _).mpr hfg)`. Set `f : curveSectionMod y a →+ chartLat y a 1` to `{ toFun := fun m => ⟨m, m.2⟩ map_zero' := rfl map_add' := fun _ _ => rfl }`. Conclude with `Module.Finite.of_injective f.toIntLinearMap fun u v h => Subtype.ext (congrArg (fun z : chartLat y a 1 => (z : Ω)) h)`.
-/
theorem finite_curveSectionMod (y : (Σ k, ι k) → Ω) (hP : IsArithVar (mCoordIdeal y) 1) (a : K → ℤ) :
    Module.Finite ℤ (curveSectionMod y a) := by
  obtain ⟨c, -, hc⟩ := exists_chart hP
  have hfg : (chartLat y a 1).FG :=
    HilbertSamuel.SectionLatticeFinite.proof HilbertSamuel.Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond K ι Ω y a 1
      (fun k => ⟨c k, hc k⟩)
  have : Module.Finite ℤ (chartLat y a 1) :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg _).mpr hfg)
  let f : curveSectionMod y a →+ chartLat y a 1 :=
    { toFun := fun m => ⟨m, m.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact Module.Finite.of_injective f.toIntLinearMap fun u v h =>
    Subtype.ext (congrArg (fun z : chartLat y a 1 => (z : Ω)) h)

end CurveSectionQuotientFinite

open CurveSectionQuotientFinite in

/- English proof (translation)
Introduce `K _ ι _ Ω _ y s d hP hs hsP`. Establish `hxM : aeval y s ∈ chartLat y (fun k => (d k : ℤ)) 1` using `HilbertSamuel.LiftBirationalAmple.chartLat_form hs`. Establish `hx0` using `aeval_ne_zero y hs hsP`. Establish `hfM` using `finite_curveSectionMod y hP (fun k => (d k : ℤ))`. Establish `hfg : AddGroup.FG (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s))` using `AddGroup.fg_of_surjective (f := (Submodule.mkQ _).toAddMonoidHom) (Submodule.mkQ_surjective _) (hG := Module.Finite.iff_addGroup_fg.mp hfM)`.

Set `_ : Module ℤ (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s))` to `AddCommGroup.toIntModule _`. Establish `hfin : Module.Finite ℤ (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s))` using `Module.Finite.iff_addGroup_fg.mpr hfg`. Use `Module.finite_of_fg_torsion _ fun q => ?_` and prove the remaining obligations. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨n, hn, hnm⟩` from `exists_nat_mul_mem_span y hP m.2 hxM hx0`.

Use `⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.mpr hn)⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((n : ℤ)) • (Submodule.Quotient.mk m : curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) = 0`. Rewrite using `[natCast_zsmul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]`. Simplify `hnm` using `[nsmul_eq_mul]`.
-/
theorem CurveSectionQuotFinite.proof : CurveSectionQuotFinite.Statement := by
  intro K _ ι _ Ω _ y s d hP hs hsP
  have hxM : aeval y s ∈ chartLat y (fun k => (d k : ℤ)) 1 := HilbertSamuel.LiftBirationalAmple.chartLat_form hs
  have hx0 := aeval_ne_zero y hs hsP
  have hfM := finite_curveSectionMod y hP (fun k => (d k : ℤ))
  have hfg : AddGroup.FG (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) :=
    AddGroup.fg_of_surjective (f := (Submodule.mkQ _).toAddMonoidHom) (Submodule.mkQ_surjective _)
      (hG := Module.Finite.iff_addGroup_fg.mp hfM)
  let _ : Module ℤ (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) := AddCommGroup.toIntModule _
  have hfin : Module.Finite ℤ (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) :=
    Module.Finite.iff_addGroup_fg.mpr hfg
  refine Module.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨n, hn, hnm⟩ := exists_nat_mul_mem_span y hP m.2 hxM hx0
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.mpr hn)⟩, ?_⟩
  change ((n : ℤ)) • (Submodule.Quotient.mk m : curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) = 0
  rw [natCast_zsmul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.subtype_apply]
  simpa [nsmul_eq_mul] using hnm

end

end GroundTheory.Heights₂.Heights.Targets
