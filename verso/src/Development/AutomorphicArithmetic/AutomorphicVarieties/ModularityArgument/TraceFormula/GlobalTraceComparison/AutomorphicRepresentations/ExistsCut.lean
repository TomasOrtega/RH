import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwtrContOfMem

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

open NumberField MeasureTheory Filter GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
private theorem borelSp : BorelSpace (H E n 0) := ⟨rfl⟩

attribute [local instance] borelSp

/- English proof (translation)
Take `⟨c, h1, -, h3, -⟩` from `exists_continuous_one_zero_of_isCompact (isCompact_closedBall (0 : ℝ) A) (Metric.isOpen_ball (x := (0 : ℝ)) (ε := A + 1)).isClosed_compl (Set.disjoint_compl_right_iff_subset.2 (Metric.closedBall_subset_ball (by linarith)))`. Use `⟨fun s => (c s : ℂ), Complex.continuous_ofReal.comp c.continuous, h3.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero, fun s hs => ?_⟩` and prove the remaining obligations. Establish `: c s = 1` using `h1 (by simpa [Real.norm_eq_abs] using hs)`. Simplify using `[this]`.
-/
private theorem exists_cut (A : ℝ) : ∃ χ : ℝ → ℂ, Continuous χ ∧ HasCompactSupport χ ∧ ∀ s, |s| ≤ A → χ s = 1 := by
  obtain ⟨c, h1, -, h3, -⟩ := exists_continuous_one_zero_of_isCompact (isCompact_closedBall (0 : ℝ) A)
    (Metric.isOpen_ball (x := (0 : ℝ)) (ε := A + 1)).isClosed_compl
    (Set.disjoint_compl_right_iff_subset.2 (Metric.closedBall_subset_ball (by linarith)))
  refine ⟨fun s => (c s : ℂ), Complex.continuous_ofReal.comp c.continuous,
    h3.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero, fun s hs => ?_⟩
  have : c s = 1 := h1 (by simpa [Real.norm_eq_abs] using hs)
  simp [this]

private def mulL (D : Dom E n 0) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ} (hC : ∀ s, ‖w s‖ ≤ C) :
    Lp ℂ 2 D.ν →L[ℂ] Lp ℂ 2 D.ν :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL D.ν ∞ 2 2
    (memLp_top_of_bound (hw.comp DiscreteGroups.T1.G.continuous_ldet).aestronglyMeasurable C
      (Eventually.of_forall fun x => hC (ldet x)) : MemLp (fun x : H E n 0 => w (ldet x)) ∞ D.ν).toLp

/- English proof (translation)
Establish `hm : MemLp (fun x : H E n 0 => w (ldet x)) ∞ D.ν` using `memLp_top_of_bound (hw.comp DiscreteGroups.T1.G.continuous_ldet).aestronglyMeasurable C (Eventually.of_forall fun x => hC (ldet x))`. Use `filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) hm.toLp v, hm.coeFn_toLp] with x h1 h2`. Use `Eq.trans h1 ?_` and prove the remaining obligations. Simplify using `only [ContinuousLinearMap.mul_apply']`. Rewrite using `[h2]`.
-/
private theorem mulL_ae (D : Dom E n 0) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ} (hC : ∀ s, ‖w s‖ ≤ C)
    (v : Lp ℂ 2 D.ν) : (mulL D hw hC v : H E n 0 → ℂ) =ᵐ[D.ν] fun x => w (ldet x) * (v : H E n 0 → ℂ) x := by
  have hm : MemLp (fun x : H E n 0 => w (ldet x)) ∞ D.ν :=
    memLp_top_of_bound (hw.comp DiscreteGroups.T1.G.continuous_ldet).aestronglyMeasurable C
      (Eventually.of_forall fun x => hC (ldet x))
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) hm.toLp v, hm.coeFn_toLp] with x h1 h2
  refine Eq.trans h1 ?_
  simp only [ContinuousLinearMap.mul_apply']
  rw [h2]

private def mulV (D : Dom E n 0) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ} (hC : ∀ s, ‖w s‖ ≤ C) (ι : Type) [Fintype ι] :
    Hs (ι := ι) D →ₗ[ℂ] Hs (ι := ι) D where
  toFun f := WithLp.toLp 2 fun i => mulL D hw hC (f i)
  map_add' a b := PiLp.ext fun i => map_add (mulL D hw hC) (a i) (b i)
  map_smul' c a := PiLp.ext fun i => map_smul (mulL D hw hC) c (a i)

/- English proof (translation)
The claim follows from `(PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => (mulL D hw hC).continuous.comp (PiLp.continuous_apply 2 _ i))`.
-/
private theorem mulV_cont (D : Dom E n 0) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ} (hC : ∀ s, ‖w s‖ ≤ C)
    (ι : Type) [Fintype ι] : Continuous (mulV D hw hC ι) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    (mulL D hw hC).continuous.comp (PiLp.continuous_apply 2 _ i))

/- English proof (translation)
Establish `hle : Submodule.span ℂ {f | IsPiVec D π f} ≤ (piSp D π ι).comap (mulV D hw hC ι)`. Use `Submodule.span_le.2 fun g hg => ?_` and prove the remaining obligations. Use `choose ψ hψ u hu hu' hgu using hg`. Use `Submodule.le_topologicalClosure _ (Submodule.subset_span fun j => ?_)` and prove the remaining obligations. Use `⟨ψ j, hψ j, fun s => u j s * w s, (hu j).mul hw, (hu' j).mul_right, ?_⟩` and prove the remaining obligations.

Use `filter_upwards [mulL_ae D hw hC (g j), hgu j] with x h1 h2`. Use `Eq.trans h1 ?_` and prove the remaining obligations. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcl : IsClosed (((piSp D π ι).comap (mulV D hw hC ι)) : Set (Hs (ι` using `ι) D)) := (show IsClosed (piSp D π ι : Set (Hs (ι := ι) D)) from Submodule.isClosed_topologicalClosure _).preimage (mulV_cont D hw hC ι)`.

Conclude with `Submodule.topologicalClosure_minimal _ hle hcl hf`.
-/
private theorem mul_keep (D : Dom E n 0) (π : CuspSub E n) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ}
    (hC : ∀ s, ‖w s‖ ≤ C) (ι : Type) [Fintype ι] {f : Hs (ι := ι) D} (hf : f ∈ piSp D π ι) :
    mulV D hw hC ι f ∈ piSp D π ι := by
  have hle : Submodule.span ℂ {f | IsPiVec D π f} ≤ (piSp D π ι).comap (mulV D hw hC ι) := by
    refine Submodule.span_le.2 fun g hg => ?_
    choose ψ hψ u hu hu' hgu using hg
    refine Submodule.le_topologicalClosure _ (Submodule.subset_span fun j => ?_)
    refine ⟨ψ j, hψ j, fun s => u j s * w s, (hu j).mul hw, (hu' j).mul_right, ?_⟩
    filter_upwards [mulL_ae D hw hC (g j), hgu j] with x h1 h2
    refine Eq.trans h1 ?_
    rw [h2]
    ring
  have hcl : IsClosed (((piSp D π ι).comap (mulV D hw hC ι)) : Set (Hs (ι := ι) D)) :=
    (show IsClosed (piSp D π ι : Set (Hs (ι := ι) D)) from Submodule.isClosed_topologicalClosure _).preimage
      (mulV_cont D hw hC ι)
  exact Submodule.topologicalClosure_minimal _ hle hcl hf

/- English proof (translation)
Establish `hl : Continuous (ldet : H E n 0 → ℝ)` using `DiscreteGroups.T1.G.continuous_ldet`. Use `haveI : SecondCountableTopology (H E n 0) := inferInstance`. Use `haveI : FirstCountableTopology (H E n 0) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _`. Establish `h1 : Continuous fun x : H E n 0 => ∫ y in tsupport φ, φ y * u (ldet y) * f (x.1 * y.1) ∂μ` using `continuous_parametric_integral_of_continuous (f := fun (x y : H E n 0) => φ y * u (ldet y) * f (x.1 * y.1)) (((hφ.1.comp continuous_snd).mul (hu.comp (hl.comp continuous_snd))).mul (hf.comp ((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)))) hφ.2.isC …`. Establish `h2 : cvF μ φ u f = fun g : GA E n => ∫ y in tsupport φ, φ y * u (ldet y) * f ((g, (1 : GA E 0)).1 * y.1) ∂μ`.

Use function extensionality and compare the values at `g`. Use `(setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm` and prove the remaining obligations. Simplify using `[image_eq_zero_of_notMem_tsupport hy]`. Rewrite using `[h2]`. Conclude with `h1.comp (continuous_id.prodMk continuous_const)`.
-/
private theorem cv_cont (μ : Measure (H E n 0)) [IsLocallyFiniteMeasure μ] {φ : H E n 0 → ℂ} (hφ : IsTestH φ)
    {u : ℝ → ℂ} (hu : Continuous u) {f : GA E n → ℂ} (hf : Continuous f) : Continuous (cvF μ φ u f) := by
  have hl : Continuous (ldet : H E n 0 → ℝ) := DiscreteGroups.T1.G.continuous_ldet
  haveI : SecondCountableTopology (H E n 0) := inferInstance
  haveI : FirstCountableTopology (H E n 0) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have h1 : Continuous fun x : H E n 0 => ∫ y in tsupport φ, φ y * u (ldet y) * f (x.1 * y.1) ∂μ :=
    continuous_parametric_integral_of_continuous
      (f := fun (x y : H E n 0) => φ y * u (ldet y) * f (x.1 * y.1))
      (((hφ.1.comp continuous_snd).mul (hu.comp (hl.comp continuous_snd))).mul
        (hf.comp ((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd))))
      hφ.2.isCompact
  have h2 : cvF μ φ u f = fun g : GA E n => ∫ y in tsupport φ, φ y * u (ldet y) * f ((g, (1 : GA E 0)).1 * y.1) ∂μ := by
    funext g
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    simp [image_eq_zero_of_notMem_tsupport hy]
  rw [h2]
  exact h1.comp (continuous_id.prodMk continuous_const)

/- English proof (translation)
Take `⟨⟨a, b⟩, hγ⟩` from `γ.2`. Establish `e : (γ : H E n 0).1 = ratGL E n a` using `by rw [← hγ]; rfl`. Rewrite using `[Prod.fst_mul, e]`. Conclude with `(π.cusp ψ hψ).1.left a y.1`.
-/
private theorem form_rat (π : CuspSub E n) {ψ : Sm E n} (hψ : ψ ∈ π.V) (γ : ratH E n 0) (y : H E n 0) :
    ψ.1 ((γ : H E n 0) * y).1 = ψ.1 y.1 := by
  obtain ⟨⟨a, b⟩, hγ⟩ := γ.2
  have e : (γ : H E n 0).1 = ratGL E n a := by rw [← hγ]; rfl
  rw [Prod.fst_mul, e]
  exact (π.cusp ψ hψ).1.left a y.1

/- English proof (translation)
Take `⟨-, hmul, -, -, -, -, -, -, -, hrat, hl, -⟩` from `hB E n hn`. Use `set φ' : H E n 0 → ℂ := fun y => φ y * u (ldet y) with hφ'`. Establish `ht : IsTestH φ'` using `⟨hφ.1.mul (hu.comp hl), hφ.2.mul_right⟩`. Take `⟨A, hA⟩` from `(hφ.2.isCompact.image hl).isBounded.subset_closedBall (0 : ℝ)`. Establish `hA' : ∀ y, φ y ≠ 0 → |ldet y| ≤ A` using `fun y hy => by`.

Use `hA (Set.mem_image_of_mem _ (subset_tsupport φ hy))` as an intermediate fact. Rewrite `this` using `[Metric.mem_closedBall, Real.dist_eq, sub_zero]`. Then use the resulting hypothesis. Take `⟨χ, hχ, hχs, hχ1⟩` from `exists_cut (R + A)`. Use `set f : H E n 0 → ℂ := fun x => ψ.1 x.1 * χ (ldet x) with hf`. Establish `hfL : MemLp f 2 D.ν` using `(DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ χ hχ hχs).1`.

Set `g : Hs (ι` to `Unit) D := WithLp.toLp 2 fun _ => hfL.toLp f`. Establish `hg : g ∈ piSp D π Unit` using `Submodule.le_topologicalClosure _ (Submodule.subset_span fun _ => ⟨ψ, hψ, χ, hχ, hχs, hfL.coeFn_toLp⟩)`. Take `⟨T, hT, -, -⟩` from `PositivityTheory.Rg.BcB.E1.kernel_operator_exists_holds E n 0 D Unit (fun _ _ => φ') (fun _ _ => ht)`. Use `⟨T g, DiscreteGroups.T1.G.piInv E n hn D π hθ Unit _ T (fun _ _ => ht) hT g hg, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hT g ()] with x hx hxR`.

Set `X` to `PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D`. Establish `hinv : ∀ (δ : ratH E n 0) (y : H E n 0), f ((δ : H E n 0) * y) = f y` using `fun δ y => by show ψ.1 ((δ : H E n 0) * y).1 * χ (ldet ((δ : H E n 0) * y)) = ψ.1 y.1 * χ (ldet y)`. Rewrite using `[form_rat π hψ δ y, hmul, (hrat δ).1, zero_add]`. Establish `e1 : ∫ y, kerH φ' x y * (g () : H E n 0 → ℂ) y ∂D.ν = ∫ y, kerH φ' x y * f y ∂D.ν` using `integral_congr_ae (hfL.coeFn_toLp.mono fun y hy => by show kerH φ' x y * (hfL.toLp f : H E n 0 → ℂ) y = _`. Rewrite using `[hy])`.

Establish `e2 : ∫ y, kerH φ' x y * f y ∂D.ν = ∫ y, φ' (x⁻¹ * y) * f y ∂D.μ` using `(DiscreteGroups.T1.G.unfold X PositivityTheory.Rg.BcB.E1.kerBasic PositivityTheory.Rg.BcB.E1.kernel_rows_columns_square_integrable ht hinv hfL x).2`. Establish `e3 : ∫ y, φ' (x⁻¹ * y) * f y ∂D.μ = ∫ y, φ' y * f (x * y) ∂D.μ` using `by haveI : D.μ.IsMulLeftInvariant := D.haar.1`. Establish `h` using `integral_mul_left_eq_self (μ := D.μ) (fun y => φ' y * f (x * y)) x⁻¹`. Simplify `h` using `only [mul_inv_cancel_left]`. Establish `e4 : ∫ y, φ' y * f (x * y) ∂D.μ = cvF D.μ φ u ψ.1 x.1`.

Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Distinguish the cases in `h0 : φ y = 0`. Simplify using `[hφ', h0]`. Establish `hy` using `hA' y h0`. Establish `hc : χ (ldet (x * y)) = 1` using `hχ1 _ (by`.

Rewrite using `[hmul]`. Conclude with `(abs_add_le _ _).trans (add_le_add hxR hy))`. Simplify using `only [hφ', hf, hc, mul_one, Prod.fst_mul]`. Rewrite using `[hx]`. Simplify using `only [Finset.univ_unique, Finset.sum_singleton]`.

Conclude with `e1.trans (e2.trans (e3.trans e4))`.
-/
private theorem cut_value (hB : Basic) (hn : 1 ≤ n) (D : Dom E n 0) (π : CuspSub E n) (hθ : ThetaFix π)
    {ψ : Sm E n} (hψ : ψ ∈ π.V) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {u : ℝ → ℂ} (hu : Continuous u) (R : ℝ) :
    ∃ v ∈ piSp D π Unit, ∀ᵐ x ∂D.ν, |ldet x| ≤ R → (v () : H E n 0 → ℂ) x = cvF D.μ φ u ψ.1 x.1 := by
  obtain ⟨-, hmul, -, -, -, -, -, -, -, hrat, hl, -⟩ := hB E n hn
  set φ' : H E n 0 → ℂ := fun y => φ y * u (ldet y) with hφ'
  have ht : IsTestH φ' := ⟨hφ.1.mul (hu.comp hl), hφ.2.mul_right⟩
  obtain ⟨A, hA⟩ := (hφ.2.isCompact.image hl).isBounded.subset_closedBall (0 : ℝ)
  have hA' : ∀ y, φ y ≠ 0 → |ldet y| ≤ A := fun y hy => by
    have := hA (Set.mem_image_of_mem _ (subset_tsupport φ hy))
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  obtain ⟨χ, hχ, hχs, hχ1⟩ := exists_cut (R + A)
  set f : H E n 0 → ℂ := fun x => ψ.1 x.1 * χ (ldet x) with hf
  have hfL : MemLp f 2 D.ν := (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ χ hχ hχs).1
  let g : Hs (ι := Unit) D := WithLp.toLp 2 fun _ => hfL.toLp f
  have hg : g ∈ piSp D π Unit :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span fun _ => ⟨ψ, hψ, χ, hχ, hχs, hfL.coeFn_toLp⟩)
  obtain ⟨T, hT, -, -⟩ := PositivityTheory.Rg.BcB.E1.kernel_operator_exists_holds E n 0 D Unit (fun _ _ => φ') (fun _ _ => ht)
  refine ⟨T g, DiscreteGroups.T1.G.piInv E n hn D π hθ Unit _ T (fun _ _ => ht) hT g hg, ?_⟩
  filter_upwards [hT g ()] with x hx hxR
  let X := PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D
  have hinv : ∀ (δ : ratH E n 0) (y : H E n 0), f ((δ : H E n 0) * y) = f y := fun δ y => by
    show ψ.1 ((δ : H E n 0) * y).1 * χ (ldet ((δ : H E n 0) * y)) = ψ.1 y.1 * χ (ldet y)
    rw [form_rat π hψ δ y, hmul, (hrat δ).1, zero_add]
  have e1 : ∫ y, kerH φ' x y * (g () : H E n 0 → ℂ) y ∂D.ν = ∫ y, kerH φ' x y * f y ∂D.ν :=
    integral_congr_ae (hfL.coeFn_toLp.mono fun y hy => by
      show kerH φ' x y * (hfL.toLp f : H E n 0 → ℂ) y = _
      rw [hy])
  have e2 : ∫ y, kerH φ' x y * f y ∂D.ν = ∫ y, φ' (x⁻¹ * y) * f y ∂D.μ :=
    (DiscreteGroups.T1.G.unfold X PositivityTheory.Rg.BcB.E1.kerBasic PositivityTheory.Rg.BcB.E1.kernel_rows_columns_square_integrable ht hinv hfL x).2
  have e3 : ∫ y, φ' (x⁻¹ * y) * f y ∂D.μ = ∫ y, φ' y * f (x * y) ∂D.μ := by
    haveI : D.μ.IsMulLeftInvariant := D.haar.1
    have h := integral_mul_left_eq_self (μ := D.μ) (fun y => φ' y * f (x * y)) x⁻¹
    simpa only [mul_inv_cancel_left] using h
  have e4 : ∫ y, φ' y * f (x * y) ∂D.μ = cvF D.μ φ u ψ.1 x.1 := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases h0 : φ y = 0
    · simp [hφ', h0]
    · have hy := hA' y h0
      have hc : χ (ldet (x * y)) = 1 := hχ1 _ (by
        rw [hmul]
        exact (abs_add_le _ _).trans (add_le_add hxR hy))
      simp only [hφ', hf, hc, mul_one, Prod.fst_mul]
  rw [hx]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  exact e1.trans (e2.trans (e3.trans e4))

/- English proof (translation)
Introduce `w hw hws`. Take `⟨R, hR⟩` from `hws.isCompact.isBounded.subset_closedBall (0 : ℝ)`. Take `⟨C, hC⟩` from `hw.bounded_above_of_compact_support hws`. Take `⟨v, hv, hva⟩` from `cut_value hB hn D π hθ hψ hφ hu R`. Use `⟨mulV D hw hC Unit v, mul_keep D π hw hC Unit hv, ?_⟩` and prove the remaining obligations.

Use `filter_upwards [mulL_ae D hw hC (v ()), hva] with x h1 h2`. Use `Eq.trans h1 ?_` and prove the remaining obligations. Distinguish the cases in `h0 : w (ldet x) = 0`. Simplify using `[h0]`. Establish `hx` using `hR (subset_tsupport w h0)`.

Rewrite `hx` using `[Metric.mem_closedBall, Real.dist_eq, sub_zero]`. Rewrite using `[h2 hx, mul_comm]`.
-/
private theorem cv_inS (hB : Basic) (hn : 1 ≤ n) (D : Dom E n 0) (π : CuspSub E n) (hθ : ThetaFix π)
    {ψ : Sm E n} (hψ : ψ ∈ π.V) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {u : ℝ → ℂ} (hu : Continuous u) :
    InS D π (cvF D.μ φ u ψ.1) := by
  intro w hw hws
  obtain ⟨R, hR⟩ := hws.isCompact.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨C, hC⟩ := hw.bounded_above_of_compact_support hws
  obtain ⟨v, hv, hva⟩ := cut_value hB hn D π hθ hψ hφ hu R
  refine ⟨mulV D hw hC Unit v, mul_keep D π hw hC Unit hv, ?_⟩
  filter_upwards [mulL_ae D hw hC (v ()), hva] with x h1 h2
  refine Eq.trans h1 ?_
  by_cases h0 : w (ldet x) = 0
  · simp [h0]
  · have hx := hR (subset_tsupport w h0)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx
    rw [h2 hx, mul_comm]

/- English proof (translation)
Introduce `w hw hws`. Establish `hL` using `(DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ w hw hws).1`. Conclude with `⟨WithLp.toLp 2 fun _ => hL.toLp _, Submodule.le_topologicalClosure _ (Submodule.subset_span fun _ => ⟨ψ, hψ, w, hw, hws, hL.coeFn_toLp⟩), hL.coeFn_toLp⟩`.
-/
private theorem form_inS (hn : 1 ≤ n) (D : Dom E n 0) (π : CuspSub E n) (hθ : ThetaFix π)
    {ψ : Sm E n} (hψ : ψ ∈ π.V) : InS D π ψ.1 := by
  intro w hw hws
  have hL := (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ w hw hws).1
  exact ⟨WithLp.toLp 2 fun _ => hL.toLp _,
    Submodule.le_topologicalClosure _ (Submodule.subset_span fun _ => ⟨ψ, hψ, w, hw, hws, hL.coeFn_toLp⟩),
    hL.coeFn_toLp⟩

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

/- English proof (translation)
Introduce `hB _ E _ _ _ n hn D π hθ ψ hψ`. Establish `hc` using `DiscreteGroups.T1.G.continuous_of_mem π hψ`. Establish `hμ : MeasureTheory.IsLocallyFiniteMeasure D.μ` using `D.haar.2.2.2`. Use `⟨⟨hc, (π.cusp ψ hψ).1.left, hθ.1 ψ hψ, fun w hw hws => (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ w hw hws).1⟩, fun φ u hφ hu => ?_⟩` and prove the remaining obligations. Establish `hin` using `cv_inS hB hn D π hθ hψ hφ hu`.

Use `⟨⟨cv_cont D.μ hφ hu hc, fun γ g => ?_, fun t g => ?_, fun w hw hws => ?_⟩, hin, form_inS hn D π hθ hψ⟩` and prove the remaining obligations. Use `MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_) show _ * ψ.1 (_ * g * y.1) = _ * ψ.1 (g * y.1)` and prove the remaining obligations. Rewrite using `[mul_assoc (GlobalTheory.CuspRep.ratGL E n γ) g y.1, (π.cusp ψ hψ).1.left]`. Use `MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_) show _ * ψ.1 (_ * g * y.1) = _ * ψ.1 (g * y.1)` and prove the remaining obligations. Rewrite using `[mul_assoc (GlobalTheory.UnitaryBC.splitCentre E n t) g y.1, hθ.1 ψ hψ]`.

Take `⟨v, -, hv⟩` from `hin w hw hws`. Conclude with `(MeasureTheory.Lp.memLp (v ())).ae_eq hv`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.cvIn_pf :
    Basic → AeEq → CvIn := by
  intro hB _ E _ _ _ n hn D π hθ ψ hψ
  have hc := DiscreteGroups.T1.G.continuous_of_mem π hψ
  have hμ : MeasureTheory.IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  refine ⟨⟨hc, (π.cusp ψ hψ).1.left, hθ.1 ψ hψ, fun w hw hws =>
    (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ w hw hws).1⟩, fun φ u hφ hu => ?_⟩
  have hin := cv_inS hB hn D π hθ hψ hφ hu
  refine ⟨⟨cv_cont D.μ hφ hu hc, fun γ g => ?_, fun t g => ?_, fun w hw hws => ?_⟩, hin, form_inS hn D π hθ hψ⟩
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show _ * ψ.1 (_ * g * y.1) = _ * ψ.1 (g * y.1)
    rw [mul_assoc (GlobalTheory.CuspRep.ratGL E n γ) g y.1, (π.cusp ψ hψ).1.left]
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show _ * ψ.1 (_ * g * y.1) = _ * ψ.1 (g * y.1)
    rw [mul_assoc (GlobalTheory.UnitaryBC.splitCentre E n t) g y.1, hθ.1 ψ hψ]
  · obtain ⟨v, -, hv⟩ := hin w hw hws
    exact (MeasureTheory.Lp.memLp (v ())).ae_eq hv
