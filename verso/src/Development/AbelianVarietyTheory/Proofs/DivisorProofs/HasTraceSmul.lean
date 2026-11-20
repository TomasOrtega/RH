import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryLieAlgebraMemIffEntriesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousExpGAndToMInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRinvUJ

noncomputable section

open MeasureTheory Filter Topology Set GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK expG inG)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3

/- English proof (translation)
The claim follows from `Submodule.span_mono fun _ ⟨H, P, hH, hP, e⟩ => ⟨H, P, hH, hP.trans h, e⟩`.
-/
theorem shapeM_mono {n : ℕ} (ε : Fin n → Bool) {d d' : ℕ} (h : d ≤ d') : ShapeM ε d ≤ ShapeM ε d' :=
  Submodule.span_mono fun _ ⟨H, P, hH, hP, e⟩ => ⟨H, P, hH, hP.trans h, e⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hS.1.add hT.1, by rw [trace_add hS.1 hT.1, hS.2, hT.2]⟩`.
-/
theorem hasTrace_add' {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    {S T : U →L[ℂ] U} {a b : ℂ} (hS : HasTrace S a) (hT : HasTrace T b) : HasTrace (S + T) (a + b) :=
  ⟨hS.1.add hT.1, by rw [trace_add hS.1 hT.1, hS.2, hT.2]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hT.1.smul c, by rw [trace_smul, hT.2]⟩`.
-/
theorem hasTrace_smul' {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    {T : U →L[ℂ] U} {a : ℂ} (c : ℂ) (hT : HasTrace T a) : HasTrace (c • T) (c * a) :=
  ⟨hT.1.smul c, by rw [trace_smul, hT.2]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toM_mul' {n : ℕ} {ε : Fin n → Bool} (a b : UJ ε) : toM (a * b) = toM a * toM b := rfl

/- English proof (translation)
Use `GlobalTheory.CompanionTheory.HaarUJ.haar_rinv_UJ n ε μ` as an intermediate fact. Establish `hZG : inG ε Z` using `(GlobalTheory.T.indefiniteUnitaryLieAlgebra_mem_iff_entries n ε Z).2 hZ`. Take `⟨hxc, hxinv⟩` from `GlobalTheory.CompanionTheory.ExpOneParam.continuous_expG_and_toM_inv n ε Z hZG`. Take `⟨hadS, hder⟩` from `hBD n ε Z H P hZ hH`. Establish `hbS : bas ε H P ∈ ShapeM ε (P.totalDegree + 2)` using `Submodule.subset_span ⟨H, P, hH, by omega, rfl⟩`.

Take `⟨-, -, hac, hacs⟩` from `hSh n ε _ _ hadS`. Take `⟨-, -, hbc, hbcs⟩` from `hSh n ε _ _ hbS`. Take `⟨L, hLf, hLmem, hLd⟩` from `hUF n ε U π hπ hirr (P.totalDegree + 2)`. Use `hLf` as an intermediate fact. Take `⟨-, hTr⟩` from `hRS n ε μ U π hπ _ _ hadS`.

Take `⟨-, hAr⟩` from `hRS n ε μ U π hπ _ _ hbS`. Use `set fad : UJ ε → ℂ := fun g => adBas ε Z H P (toM g) with hfad`. Use `set fb : UJ ε → ℂ := fun g => bas ε H P (toM g) with hfb`. Use `set T := repOp π μ fad with hT`. Use `set A := repOp π μ fb with hA`.

Use `set e := stdOrthonormalBasis ℂ L with he`. Use `set x : ℝ → UJ ε := fun t => expG ε Z t with hx`. Establish `hx0 : x 0 = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Use `Formalism.REAL.toM_expG ε Z 0 hZG` as an intermediate fact. Simplify using `only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero] at this`. Conclude with `this`. Establish `hconj : ∀ (s : ℝ) (g : UJ ε), toM ((x s)⁻¹ * g * x s) = NormedSpace.exp (-((s : ℂ) • Z)) * toM g * NormedSpace.exp ((s : ℂ) • Z)` using `fun s g => by`. Rewrite using `[toM_mul', toM_mul', hxinv s, Formalism.REAL.toM_expG ε Z s hZG]`.

Establish `key : ∀ (y : UJ ε) (v u : U), ⟪v, π y u⟫_ℂ = ⟪π y⁻¹ v, u⟫_ℂ` using `fun y v u => by`. Rewrite using `[hπ.inner_apply_left, inv_inv]`. Use `set w : UJ ε → ℂ := fun g => ∑ j, ⟪(e j : U), π g (e j : U)⟫_ℂ with hw`. Establish `hwc : Continuous w` using `continuous_finsetSum _ fun j _ => continuous_const.inner (hπ.continuous_apply _)`. Establish `hsum : ∑ j, ⟪(e j : U), T (e j : U)⟫_ℂ = ∫ g, fad g * w g ∂μ`.

Establish `hint : ∀ j ∈ Finset.univ, Integrable (fun g => fad g * ⟪(e j : U), π g (e j : U)⟫_ℂ) μ` using `fun j _ => (hac.mul (continuous_const.inner (hπ.continuous_apply _))).integrable_of_hasCompactSupport hacs.mul_right`. Simplify using `only [hT, hπ.inner_repOp hac hacs, hw, Finset.mul_sum]`. Rewrite using `[integral_finsetSum _ hint]`. Establish `hid : ∀ t : ℝ, ∑ j, ⟪(e j : U), π (x t) (A (π (x t)⁻¹ (e j : U)))⟫_ℂ = ∫ g, fb ((x t)⁻¹ * g * x t) * w g ∂μ`. Introduce `t`.

Use `set y := x t`. Establish `h1 : ∀ j, ⟪(e j : U), π y (A (π y⁻¹ (e j : U)))⟫_ℂ = ∫ g, fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ ∂μ`. Introduce `j`. Rewrite using `[key y, hA, hπ.inner_repOp hbc hbcs]`. Use `integral_congr_ae (Eventually.of_forall fun g => ?_)` and prove the remaining obligations.

Simplify using `only`. Use `congr 1`. Rewrite using `[map_mul, map_mul]`. Use `show _ = ⟪(e j : U), π y (π g (π y⁻¹ (e j : U)))⟫_ℂ`. Rewrite using `[key y]`.

Establish `hint : ∀ j ∈ Finset.univ, Integrable (fun g => fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ) μ` using `fun j _ => (hbc.mul (continuous_const.inner ((hπ.continuous_apply _).comp (by fun_prop)))).integrable_of_hasCompactSupport hbcs.mul_right`. Rewrite using `[Finset.sum_congr rfl fun j _ => h1 j, ← integral_finsetSum _ hint]`. Establish `e2 : (fun g => ∑ j, fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ) = fun g => fb g * w (y * g * y⁻¹)` using `funext fun g => by simp only [hw, Finset.mul_sum]`. Rewrite using `[e2]`. Establish `e3` using `integral_mul_right_eq_self (μ := μ) (fun g => fb (y⁻¹ * g) * w (y * (y⁻¹ * g) * y⁻¹)) y`.

Establish `e4` using `integral_mul_left_eq_self (μ := μ) (fun g => fb g * w (y * g * y⁻¹)) y⁻¹`. Rewrite using `[← e4, ← e3]`. Use `integral_congr_ae (Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only`. Use `congr 2`.

Use `group`. Use `group`. Establish `h0 : π (x 0) = 1` using `by rw [hx0, map_one]`. Establish `hCD'` using `hCD U L (fun t => π (x t)) (fun t => π (x t)⁻¹) A h0 (fun t v u => by`. Rewrite using `[hπ.inner_apply_left, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply])`.

Use the proof step `(fun t v u => (hπ.inner_apply_left _ v u).symm) (fun v hv => hLd v hv Z hZG)`. Use the proof step `(fun u => hLmem _ (hAr u).1) (fun u => hLmem _ (hAr u).2)`. Establish `hfun : (fun t => ∑ j, ⟪(stdOrthonormalBasis ℂ L j : U), π (x t) (A (π (x t)⁻¹ (stdOrthonormalBasis ℂ L j : U)))⟫_ℂ) = fun t => ∫ g, fb ((x t)⁻¹ * g * x t) * w g ∂μ`. Use function extensionality and compare the values at `hid`. Rewrite `hCD'` using `[hfun]`.

Establish `hC : IsCompact ((fun p : ℝ × UJ ε => x p.1 * p.2 * (x p.1)⁻¹) '' (Icc (-1 : ℝ) 1 ×ˢ tsupport fad))` using `(isCompact_Icc.prod hacs.isCompact).image (by fun_prop)`. Take `⟨χ, h1, -, hcs, -⟩` from `exists_continuous_one_zero_of_isCompact hC isClosed_empty (disjoint_empty _)`. Take `⟨M, hM⟩` from `hacs.exists_bound_of_continuous hac`. Establish `hM0 : 0 ≤ M` using `(norm_nonneg _).trans (hM 1)`. Establish `keyb : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ g, ‖fad ((x u)⁻¹ * g * x u) * w g‖ ≤ M * ‖(χ g : ℂ)‖ * ‖w g‖`.

Introduce `u hu g`. Rewrite using `[norm_mul]`. Distinguish the cases in `h : fad ((x u)⁻¹ * g * x u) = 0`. Rewrite using `[h, norm_zero, zero_mul]`. Check the signs of the components of the expression.

Establish `hg : g ∈ (fun p : ℝ × UJ ε => x p.1 * p.2 * (x p.1)⁻¹) '' (Icc (-1 : ℝ) 1 ×ˢ tsupport fad)` using `⟨(u, (x u)⁻¹ * g * x u), ⟨hu, subset_tsupport fad h⟩, by simp only; group⟩`. Establish `h2 : (χ g : ℂ) = 1` using `by simp [h1 hg]`. Rewrite using `[h2, norm_one, mul_one]`. Conclude with `mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)`. Establish `hχc : Continuous fun g => (χ g : ℂ)` using `Complex.continuous_ofReal.comp χ.continuous`.

Establish `hbint : Integrable (fun g => M * ‖(χ g : ℂ)‖ * ‖w g‖) μ`. Use `(((hχc.norm.const_mul M).mul hwc.norm)).integrable_of_hasCompactSupport ?_` and prove the remaining obligations. Use `HasCompactSupport.mul_right ?_` and prove the remaining obligations. Use `HasCompactSupport.mul_left ?_` and prove the remaining obligations. Conclude with `(hcs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).norm`.

Establish `hcontF : ∀ (f : UJ ε → ℂ), Continuous f → ∀ u, Continuous fun g => f ((x u)⁻¹ * g * x u) * w g` using `fun f hf u => (hf.comp (by fun_prop)).mul hwc`. Establish `hint` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun u g => fb ((x u)⁻¹ * g * x u) * w g) (F' := fun u g => fad ((x u)⁻¹ * g * x u) * w g) (x₀ := (0 : ℝ)) (s := Ioo (-1 : ℝ) 1) (bound := fun g => M * ‖(χ g : ℂ)‖ * ‖w g‖) (Ioo_mem_nhds (by norm_num) (by norm_num)) ( …`. Simplify using `only [hx0, inv_one, one_mul, mul_one]`. Conclude with `(hbc.mul hwc).integrable_of_hasCompactSupport hbcs.mul_right)`. Use the proof step `(hcontF fad hac 0).aestronglyMeasurable`.

Use the proof step `(.of_forall fun g u hu => keyb u (Ioo_subset_Icc_self hu) g) hbint`. Use the proof step `(.of_forall fun g u _ => by`. Establish `e5 : (fun v : ℝ => fb ((x v)⁻¹ * g * x v) * w g) = fun v : ℝ => bas ε H P (NormedSpace.exp (-((v : ℂ) • Z)) * toM g * NormedSpace.exp ((v : ℂ) • Z)) * w g`. Use function extensionality and compare the values at `fun v => by simp only [hfb, hconj]`. Rewrite using `[e5]`.

Establish `e6 : fad ((x u)⁻¹ * g * x u) = adBas ε Z H P (NormedSpace.exp (-((u : ℂ) • Z)) * toM g * NormedSpace.exp ((u : ℂ) • Z))`. Simplify using `only [hfad, hconj]`. Rewrite using `[e6]`. Conclude with `(hder (toM g) u).mul_const (w g))`. Establish `hzero : ∫ g, fad ((x 0)⁻¹ * g * x 0) * w g ∂μ = 0` using `hint.2.unique hCD'`.

Simplify using `only [hx0, inv_one, one_mul, mul_one] at hzero`. Establish `hTL : ∀ u, T u ∈ L` using `fun u => hLmem _ (hTr u).1`. Use `hTS U L T hTL` as an intermediate fact. Rewrite `this` using `[hsum, hzero]`. Then use the resulting hypothesis.
-/
theorem trace_adBas (hSh : StShape) (hBD : StBasDeriv) (hUF : UFin) (hRS : RangeShape) (hTS : TraceSum)
    (hCD : ConjDeriv) {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type)
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U))
    (hπ : IsUnitaryRep π) (hirr : IsTopIrreducible π) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n)
    (hZ : LieU ε Z) (hH : IsCutFn H) :
    HasTrace (repOp π μ fun g => adBas ε Z H P (toM g)) 0 := by
  have := GlobalTheory.CompanionTheory.HaarUJ.haar_rinv_UJ n ε μ
  have hZG : inG ε Z := (GlobalTheory.T.indefiniteUnitaryLieAlgebra_mem_iff_entries n ε Z).2 hZ
  obtain ⟨hxc, hxinv⟩ := GlobalTheory.CompanionTheory.ExpOneParam.continuous_expG_and_toM_inv n ε Z hZG
  obtain ⟨hadS, hder⟩ := hBD n ε Z H P hZ hH
  have hbS : bas ε H P ∈ ShapeM ε (P.totalDegree + 2) := Submodule.subset_span ⟨H, P, hH, by omega, rfl⟩
  obtain ⟨-, -, hac, hacs⟩ := hSh n ε _ _ hadS
  obtain ⟨-, -, hbc, hbcs⟩ := hSh n ε _ _ hbS
  obtain ⟨L, hLf, hLmem, hLd⟩ := hUF n ε U π hπ hirr (P.totalDegree + 2)
  have := hLf
  obtain ⟨-, hTr⟩ := hRS n ε μ U π hπ _ _ hadS
  obtain ⟨-, hAr⟩ := hRS n ε μ U π hπ _ _ hbS
  set fad : UJ ε → ℂ := fun g => adBas ε Z H P (toM g) with hfad
  set fb : UJ ε → ℂ := fun g => bas ε H P (toM g) with hfb
  set T := repOp π μ fad with hT
  set A := repOp π μ fb with hA
  set e := stdOrthonormalBasis ℂ L with he
  set x : ℝ → UJ ε := fun t => expG ε Z t with hx
  have hx0 : x 0 = 1 := by
    apply Subtype.ext
    apply Units.ext
    have := Formalism.REAL.toM_expG ε Z 0 hZG
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero] at this
    exact this
  have hconj : ∀ (s : ℝ) (g : UJ ε), toM ((x s)⁻¹ * g * x s) =
      NormedSpace.exp (-((s : ℂ) • Z)) * toM g * NormedSpace.exp ((s : ℂ) • Z) := fun s g => by
    rw [toM_mul', toM_mul', hxinv s, Formalism.REAL.toM_expG ε Z s hZG]
  have key : ∀ (y : UJ ε) (v u : U), ⟪v, π y u⟫_ℂ = ⟪π y⁻¹ v, u⟫_ℂ := fun y v u => by
    rw [hπ.inner_apply_left, inv_inv]
  set w : UJ ε → ℂ := fun g => ∑ j, ⟪(e j : U), π g (e j : U)⟫_ℂ with hw
  have hwc : Continuous w := continuous_finsetSum _ fun j _ => continuous_const.inner (hπ.continuous_apply _)

  have hsum : ∑ j, ⟪(e j : U), T (e j : U)⟫_ℂ = ∫ g, fad g * w g ∂μ := by
    have hint : ∀ j ∈ Finset.univ, Integrable (fun g => fad g * ⟪(e j : U), π g (e j : U)⟫_ℂ) μ := fun j _ =>
      (hac.mul (continuous_const.inner (hπ.continuous_apply _))).integrable_of_hasCompactSupport hacs.mul_right
    simp only [hT, hπ.inner_repOp hac hacs, hw, Finset.mul_sum]
    rw [integral_finsetSum _ hint]

  have hid : ∀ t : ℝ, ∑ j, ⟪(e j : U), π (x t) (A (π (x t)⁻¹ (e j : U)))⟫_ℂ =
      ∫ g, fb ((x t)⁻¹ * g * x t) * w g ∂μ := by
    intro t
    set y := x t
    have h1 : ∀ j, ⟪(e j : U), π y (A (π y⁻¹ (e j : U)))⟫_ℂ =
        ∫ g, fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ ∂μ := by
      intro j
      rw [key y, hA, hπ.inner_repOp hbc hbcs]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only
      congr 1
      rw [map_mul, map_mul]
      show _ = ⟪(e j : U), π y (π g (π y⁻¹ (e j : U)))⟫_ℂ
      rw [key y]
    have hint : ∀ j ∈ Finset.univ, Integrable (fun g => fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ) μ :=
      fun j _ => (hbc.mul (continuous_const.inner ((hπ.continuous_apply _).comp (by fun_prop)))).integrable_of_hasCompactSupport
        hbcs.mul_right
    rw [Finset.sum_congr rfl fun j _ => h1 j, ← integral_finsetSum _ hint]
    have e2 : (fun g => ∑ j, fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ) =
        fun g => fb g * w (y * g * y⁻¹) := funext fun g => by simp only [hw, Finset.mul_sum]
    rw [e2]
    have e3 := integral_mul_right_eq_self (μ := μ) (fun g => fb (y⁻¹ * g) * w (y * (y⁻¹ * g) * y⁻¹)) y
    have e4 := integral_mul_left_eq_self (μ := μ) (fun g => fb g * w (y * g * y⁻¹)) y⁻¹
    rw [← e4, ← e3]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only
    congr 2
    · group
    · group

  have h0 : π (x 0) = 1 := by rw [hx0, map_one]
  have hCD' := hCD U L (fun t => π (x t)) (fun t => π (x t)⁻¹) A h0
    (fun t v u => by
      rw [hπ.inner_apply_left, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        ContinuousLinearMap.one_apply])
    (fun t v u => (hπ.inner_apply_left _ v u).symm) (fun v hv => hLd v hv Z hZG)
    (fun u => hLmem _ (hAr u).1) (fun u => hLmem _ (hAr u).2)
  have hfun : (fun t => ∑ j, ⟪(stdOrthonormalBasis ℂ L j : U), π (x t) (A (π (x t)⁻¹
      (stdOrthonormalBasis ℂ L j : U)))⟫_ℂ) = fun t => ∫ g, fb ((x t)⁻¹ * g * x t) * w g ∂μ :=
    funext hid
  rw [hfun] at hCD'

  have hC : IsCompact ((fun p : ℝ × UJ ε => x p.1 * p.2 * (x p.1)⁻¹) '' (Icc (-1 : ℝ) 1 ×ˢ tsupport fad)) :=
    (isCompact_Icc.prod hacs.isCompact).image (by fun_prop)
  obtain ⟨χ, h1, -, hcs, -⟩ := exists_continuous_one_zero_of_isCompact hC isClosed_empty (disjoint_empty _)
  obtain ⟨M, hM⟩ := hacs.exists_bound_of_continuous hac
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have keyb : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ g, ‖fad ((x u)⁻¹ * g * x u) * w g‖ ≤ M * ‖(χ g : ℂ)‖ * ‖w g‖ := by
    intro u hu g
    rw [norm_mul]
    by_cases h : fad ((x u)⁻¹ * g * x u) = 0
    · rw [h, norm_zero, zero_mul]
      positivity
    · have hg : g ∈ (fun p : ℝ × UJ ε => x p.1 * p.2 * (x p.1)⁻¹) '' (Icc (-1 : ℝ) 1 ×ˢ tsupport fad) :=
        ⟨(u, (x u)⁻¹ * g * x u), ⟨hu, subset_tsupport fad h⟩, by simp only; group⟩
      have h2 : (χ g : ℂ) = 1 := by simp [h1 hg]
      rw [h2, norm_one, mul_one]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have hχc : Continuous fun g => (χ g : ℂ) := Complex.continuous_ofReal.comp χ.continuous
  have hbint : Integrable (fun g => M * ‖(χ g : ℂ)‖ * ‖w g‖) μ := by
    refine (((hχc.norm.const_mul M).mul hwc.norm)).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.mul_right ?_
    refine HasCompactSupport.mul_left ?_
    exact (hcs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).norm
  have hcontF : ∀ (f : UJ ε → ℂ), Continuous f → ∀ u, Continuous fun g => f ((x u)⁻¹ * g * x u) * w g :=
    fun f hf u => (hf.comp (by fun_prop)).mul hwc
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun u g => fb ((x u)⁻¹ * g * x u) * w g) (F' := fun u g => fad ((x u)⁻¹ * g * x u) * w g)
    (x₀ := (0 : ℝ)) (s := Ioo (-1 : ℝ) 1) (bound := fun g => M * ‖(χ g : ℂ)‖ * ‖w g‖)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun u => (hcontF fb hbc u).aestronglyMeasurable)
    (by
      simp only [hx0, inv_one, one_mul, mul_one]
      exact (hbc.mul hwc).integrable_of_hasCompactSupport hbcs.mul_right)
    (hcontF fad hac 0).aestronglyMeasurable
    (.of_forall fun g u hu => keyb u (Ioo_subset_Icc_self hu) g) hbint
    (.of_forall fun g u _ => by
      have e5 : (fun v : ℝ => fb ((x v)⁻¹ * g * x v) * w g) =
          fun v : ℝ => bas ε H P (NormedSpace.exp (-((v : ℂ) • Z)) * toM g * NormedSpace.exp ((v : ℂ) • Z)) * w g :=
        funext fun v => by simp only [hfb, hconj]
      rw [e5]
      have e6 : fad ((x u)⁻¹ * g * x u) =
          adBas ε Z H P (NormedSpace.exp (-((u : ℂ) • Z)) * toM g * NormedSpace.exp ((u : ℂ) • Z)) := by
        simp only [hfad, hconj]
      rw [e6]
      exact (hder (toM g) u).mul_const (w g))
  have hzero : ∫ g, fad ((x 0)⁻¹ * g * x 0) * w g ∂μ = 0 := hint.2.unique hCD'
  simp only [hx0, inv_one, one_mul, mul_one] at hzero
  have hTL : ∀ u, T u ∈ L := fun u => hLmem _ (hTr u).1
  have := hTS U L T hTL
  rwa [hsum, hzero] at this

/- English proof (translation)
Introduce `hSh hBD hUF hRS hTS hCD n ε μ _ U _ _ _ π hπ hirr φ hφ`. It suffices to establish `h : (∃ d, φ ∈ ShapeM ε d) ∧ HasTrace (repOp π μ fun g => φ (toM g)) 0 from h.2`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem φ hmem`. Take `⟨Z, H, P, hZ, hH, rfl⟩` from `hmem`.

Conclude with `⟨⟨_, (hBD n ε Z H P hZ hH).1⟩, trace_adBas hSh hBD hUF hRS hTS hCD ε μ U π hπ hirr Z H P hZ hH⟩`. Consider the case `zero`. Use `⟨⟨0, zero_mem _⟩, ?_⟩` and prove the remaining obligations. Establish `h0 : IsRepOp π μ (fun g => (0 : Mat n → ℂ) (toM g)) 0` using `fun v => by`. Simplify using `only [Pi.zero_apply, zero_smul, integral_zero, ContinuousLinearMap.zero_apply]`.

Conclude with `⟨integrable_zero _ _ _, trivial⟩`. Rewrite using `[h0.repOp_eq]`. Conclude with `⟨isTraceClass_zero, trace_zero⟩`. Consider the case `add φ₁ φ₂ _ _ h₁ h₂`. Take `⟨⟨d₁, hd₁⟩, ht₁⟩` from `h₁`.

Take `⟨⟨d₂, hd₂⟩, ht₂⟩` from `h₂`. Use `⟨⟨max d₁ d₂, add_mem (shapeM_mono ε (le_max_left _ _) hd₁) (shapeM_mono ε (le_max_right _ _) hd₂)⟩, ?_⟩` and prove the remaining obligations. Establish `o₁` using `(hRS n ε μ U π hπ d₁ φ₁ hd₁).1`. Establish `o₂` using `(hRS n ε μ U π hπ d₂ φ₂ hd₂).1`. Establish `hs : IsRepOp π μ (fun g => (φ₁ + φ₂) (toM g)) (repOp π μ (fun g => φ₁ (toM g)) + repOp π μ (fun g => φ₂ (toM g)))` using `fun v => by`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `((o₁ v).1.add (o₂ v).1).congr (Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only [Pi.add_apply, add_smul]`. Rewrite using `[ContinuousLinearMap.add_apply, (o₁ v).2, (o₂ v).2, ← integral_add (o₁ v).1 (o₂ v).1]`. Simplify using `only [Pi.add_apply, add_smul]`.

Rewrite using `[hs.repOp_eq]`. Simplify using `using hasTrace_add' ht₁ ht₂`. Consider the case `smul c φ _ h`. Take `⟨⟨d, hd⟩, ht⟩` from `h`. Use `⟨⟨d, Submodule.smul_mem _ c hd⟩, ?_⟩` and prove the remaining obligations.

Establish `o` using `(hRS n ε μ U π hπ d φ hd).1`. Establish `hs : IsRepOp π μ (fun g => (c • φ) (toM g)) (c • repOp π μ (fun g => φ (toM g)))` using `fun v => by`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `((o v).1.smul c).congr (Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_smul]`.

Rewrite using `[ContinuousLinearMap.smul_apply, (o v).2, ← integral_smul]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_smul]`. Rewrite using `[hs.repOp_eq]`. Simplify using `using hasTrace_smul' c ht`.
-/
theorem stTrAd_of : StShape → StBasDeriv → UFin → RangeShape → TraceSum → ConjDeriv → StTrAd := by
  intro hSh hBD hUF hRS hTS hCD n ε μ _ U _ _ _ π hπ hirr φ hφ
  suffices h : (∃ d, φ ∈ ShapeM ε d) ∧ HasTrace (repOp π μ fun g => φ (toM g)) 0 from h.2
  induction hφ using Submodule.span_induction with
  | mem φ hmem =>
    obtain ⟨Z, H, P, hZ, hH, rfl⟩ := hmem
    exact ⟨⟨_, (hBD n ε Z H P hZ hH).1⟩, trace_adBas hSh hBD hUF hRS hTS hCD ε μ U π hπ hirr Z H P hZ hH⟩
  | zero =>
    refine ⟨⟨0, zero_mem _⟩, ?_⟩
    have h0 : IsRepOp π μ (fun g => (0 : Mat n → ℂ) (toM g)) 0 := fun v => by
      simp only [Pi.zero_apply, zero_smul, integral_zero, ContinuousLinearMap.zero_apply]
      exact ⟨integrable_zero _ _ _, trivial⟩
    rw [h0.repOp_eq]
    exact ⟨isTraceClass_zero, trace_zero⟩
  | add φ₁ φ₂ _ _ h₁ h₂ =>
    obtain ⟨⟨d₁, hd₁⟩, ht₁⟩ := h₁
    obtain ⟨⟨d₂, hd₂⟩, ht₂⟩ := h₂
    refine ⟨⟨max d₁ d₂, add_mem (shapeM_mono ε (le_max_left _ _) hd₁) (shapeM_mono ε (le_max_right _ _) hd₂)⟩, ?_⟩
    have o₁ := (hRS n ε μ U π hπ d₁ φ₁ hd₁).1
    have o₂ := (hRS n ε μ U π hπ d₂ φ₂ hd₂).1
    have hs : IsRepOp π μ (fun g => (φ₁ + φ₂) (toM g))
        (repOp π μ (fun g => φ₁ (toM g)) + repOp π μ (fun g => φ₂ (toM g))) := fun v => by
      refine ⟨?_, ?_⟩
      · refine ((o₁ v).1.add (o₂ v).1).congr (Eventually.of_forall fun g => ?_)
        simp only [Pi.add_apply, add_smul]
      · rw [ContinuousLinearMap.add_apply, (o₁ v).2, (o₂ v).2, ← integral_add (o₁ v).1 (o₂ v).1]
        simp only [Pi.add_apply, add_smul]
    rw [hs.repOp_eq]
    simpa using hasTrace_add' ht₁ ht₂
  | smul c φ _ h =>
    obtain ⟨⟨d, hd⟩, ht⟩ := h
    refine ⟨⟨d, Submodule.smul_mem _ c hd⟩, ?_⟩
    have o := (hRS n ε μ U π hπ d φ hd).1
    have hs : IsRepOp π μ (fun g => (c • φ) (toM g)) (c • repOp π μ (fun g => φ (toM g))) := fun v => by
      refine ⟨?_, ?_⟩
      · refine ((o v).1.smul c).congr (Eventually.of_forall fun g => ?_)
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
      · rw [ContinuousLinearMap.smul_apply, (o v).2, ← integral_smul]
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [hs.repOp_eq]
    simpa using hasTrace_smul' c ht

end GlobalTheory.PsCo.Pc3
