import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothin
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact

noncomputable section
open NumberField MeasureTheory Matrix Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutGrowth.ApproxId GlobalTheory.GLFin
open scoped ContDiff

namespace GlobalTheory.GLFin.Inhab
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
omit [IsTotallyComplex E] in

/- English proof (translation)
Use `haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _`. Set `T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a` to `LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)`. Set `S : Lie E a →L[ℝ] Matrix (Fin a) (Fin a) (Cinf E)` to `LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)`. Introduce `x hx`. Establish `hu : IsUnit (S x)` using `hx`.

Establish `h1 : ContDiffAt ℝ ∞ Ring.inverse (S x)` using `by simpa using contDiffAt_ringInverse ℝ (n := ∞) hu.unit`. Establish `h2` using `(T.contDiff.contDiffAt.comp x (h1.comp x S.contDiff.contDiffAt)).contDiffWithinAt (s := invSet E a)`. Apply the tactic sequence `refine h2.congr (fun y _ => ?_) ?_ <;> exact congrArg toL (Matrix.nonsing_inv_eq_ringInverse _)`.
-/
theorem contDiffOn_invL : ContDiffOn ℝ ∞ (fun x : Lie E a => toL (Matrix.of x)⁻¹) (invSet E a) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  let S : Lie E a →L[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  intro x hx
  have hu : IsUnit (S x) := hx
  have h1 : ContDiffAt ℝ ∞ Ring.inverse (S x) := by simpa using contDiffAt_ringInverse ℝ (n := ∞) hu.unit
  have h2 := (T.contDiff.contDiffAt.comp x (h1.comp x S.contDiff.contDiffAt)).contDiffWithinAt (s := invSet E a)
  refine h2.congr (fun y _ => ?_) ?_ <;> exact congrArg toL (Matrix.nonsing_inv_eq_ringInverse _)
end

/- English proof (translation)
Establish `h : Continuous (pInf E)`. Use `continuous_pi fun w => ?_` and prove the remaining obligations. Conclude with `(InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp ((continuous_apply w).comp continuous_fst)`. Conclude with `Continuous.units_map _ (continuous_id.matrix_map h)`.
-/
theorem cP : Continuous (fun g : GA E a => GeneralLinearGroup.map (pInf E) g) := by
  have h : Continuous (pInf E) := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)
  exact Continuous.units_map _ (continuous_id.matrix_map h)

omit [IsTotallyComplex E] in

/- English proof (translation)
The claim follows from `Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))`.
-/
theorem cQ : Continuous (fun g : GA E a => GeneralLinearGroup.map (pFin E) g) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

omit [IsTotallyComplex E] in

/- English proof (translation)
Use `Continuous.units_map _ ?_` and prove the remaining obligations. Establish `hs : Continuous (sFin E : Af E → Ad E)` using `continuous_const.prodMk continuous_id`. Conclude with `continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)`.
-/
theorem cF : Continuous (finGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) := continuous_const.prodMk continuous_id
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

omit [IsTotallyComplex E] in

/- English proof (translation)
The claim follows from `(contDiff_bumpR m).comp L.contDiff`.
-/
theorem cd1 (m : ℝ) (L : Lie E a →L[ℝ] Lie E a) : ContDiff ℝ ∞ fun x => bumpR E a m (L x) :=
  (contDiff_bumpR m).comp L.contDiff

/- English proof (translation)
Establish `: ProperSpace (Lie E a)` using `FiniteDimensional.proper ℝ _`. Establish `hv : (fun y : GL (Fin a) (Cinf E) => toL y.val) '' N ∈ 𝓝 (oneL E a)` using `isOpenEmbedding_val.isOpenMap.image_mem_nhds hN`. Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.1 hv`. Take `⟨n, hn⟩` from `exists_nat_one_div_lt hε`. Use `set m : ℝ := (n : ℝ) + 1 with hmd`.

Establish `hm : 0 < m` using `by positivity`. Establish `hsub : Metric.closedBall (oneL E a) (1 / m) ⊆ (fun y : GL (Fin a) (Cinf E) => toL y.val) '' N` using `(Metric.closedBall_subset_ball hn).trans hball`. Set `b : GL (Fin a) (Cinf E) → ℝ` to `fun y => bumpR E a m (toL y.val)`. Establish `hb : Continuous b` using `(contDiff_bumpR m).continuous.comp isOpenEmbedding_val.continuous`. Establish `hbc : ∀ (k : Kinf E a) y, b (Unitary.toUnits k * y * (Unitary.toUnits k)⁻¹) = b y` using `fun k y => bumpR_conj m k _`.

Set `P` to `GeneralLinearGroup.map (n := Fin a) (pInf E)`. Set `Q` to `GeneralLinearGroup.map (n := Fin a) (pFin E)`. Set `χ : GL (Fin a) (Af E) → ℝ` to `(U : Set _).indicator 1`. Establish `hχ : Continuous χ` using `IsClopen.continuous_indicator ⟨U.isClosed_of_isOpen hUo, hUo⟩ continuous_const`. Establish `hχl : ∀ u ∈ U, ∀ k, χ (u * k) = χ k` using `fun u hu k => by`.

Simplify using `only [χ, Set.indicator, SetLike.mem_coe, U.mul_mem_cancel_left hu]`. Both sides reduce to the same expression. Establish `hχi : ∀ k, χ k⁻¹ = χ k` using `fun k => by`. Simplify using `only [χ, Set.indicator, SetLike.mem_coe, inv_mem_iff]`. Both sides reduce to the same expression.

Establish `hχ0 : ∀ k, 0 ≤ χ k` using `fun k => Set.indicator_nonneg (fun _ _ => zero_le_one) k`. Set `f₀ : GA E a → ℝ` to `fun g => b (P g) * b (P g)⁻¹ * χ (Q g)`. Establish `hc : Continuous f₀` using `((hb.comp cP).mul (hb.comp cP.inv)).mul (hχ.comp cQ)`. Establish `h0 : ∀ g, 0 ≤ f₀ g` using `fun g => mul_nonneg (mul_nonneg (bumpR_nonneg _ _) (bumpR_nonneg _ _)) (hχ0 _)`. Establish `hsm : ∀ g, f₀ g ≠ 0 → toL (P g).val ∈ Metric.closedBall (oneL E a) (1 / m) ∧ Q g ∈ U` using `fun g h => ⟨(dist_lt_of_bumpR_ne_zero hm (left_ne_zero_of_mul (left_ne_zero_of_mul h))).le, Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h)⟩`.

Establish `hK : IsCompact ((fun y : GL (Fin a) (Cinf E) => toL y.val) ⁻¹' Metric.closedBall (oneL E a) (1 / m))` using `isOpenEmbedding_val.isInducing.isCompact_preimage' (isCompact_closedBall (oneL E a) (1 / m)) (hsub.trans (Set.image_subset_range _ _))`. Establish `hcs : HasCompactSupport f₀`. Use `HasCompactSupport.intro ((hK.prod hUc).image ((continuous_infGL.comp continuous_fst).mul (cF.comp continuous_snd))) fun g hg => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hg ⟨(P g, Q g), hsm g h, infGL_mul_finGL g⟩`.

Establish `h1 : f₀ 1 = 1`. Establish `: b 1 = 1` using `bumpR_one m`. Simplify using `[f₀, this, χ]`. Establish `hpos : 0 < ∫ g, f₀ g ∂μ` using `hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs h0 (x := 1) (by rw [h1]; norm_num)`. Use `set c := (∫ g, f₀ g ∂μ)⁻¹`.

Establish `hsym : ∀ g, f₀ g⁻¹ = f₀ g` using `fun g => by`. Simplify using `only [f₀, map_inv, inv_inv, hχi, mul_comm (b (P g))]`. Establish `hleft : ∀ u ∈ U, ∀ g, f₀ (finGL E a u * g) = f₀ g` using `fun u hu g => by`. Simplify using `only [f₀, P, Q, map_mul, pInf_finGL, pFin_finGL, one_mul, hχl u hu]`. Use `⟨fun g => ((c * f₀ g : ℝ) : ℂ), ⟨Complex.continuous_ofReal.comp (continuous_const.mul hc), ?_, ?_, ?_⟩, fun g => ⟨?_, Complex.ofReal_im _⟩, ?_, fun g => by rw [hsym], fun k g => ?_, fun u hu g => by rw [hleft u hu], fun g hg => ?_⟩` and prove the remaining obligations.

Conclude with `hcs.comp_left (g := fun x : ℝ => ((c * x : ℝ) : ℂ)) (by simp)`. Introduce `g`. Establish `e1 : ContDiffOn ℝ ∞ (fun x : Lie E a => bumpR E a m (lmul (toL (P g).val) x)) (invSet E a)` using `(cd1 m (lmul (toL (P g).val))).contDiffOn`. Establish `e2 : ContDiffOn ℝ ∞ (fun x : Lie E a => bumpR E a m (rmul (toL ((P g)⁻¹).val) (toL (Matrix.of x)⁻¹))) (invSet E a)` using `(cd1 m (rmul (toL ((P g)⁻¹ : GL (Fin a) (Cinf E)).val))).comp_contDiffOn contDiffOn_invL`. Use `(Complex.ofRealCLM.contDiff.comp_contDiffOn (((e1.mul e2).mul (contDiffOn_const (c := χ (Q g)))).const_smul c)).congr ?_` and prove the remaining obligations.

Introduce and unpack `x ⟨u, hu⟩`. Take `rfl : x = toL u.val` from `hu.symm`. Rewrite using `[chart_val, hsym]`. Simplify using `only [f₀, P, Q, map_mul, pInf_infGL, pFin_infGL, mul_one, _root_.mul_inv_rev]`. Establish `: (Matrix.of (toL u.val))⁻¹ = (u⁻¹).val` using `(Matrix.coe_units_inv u).symm`.

Simplify using `only [Function.comp_apply, this]`. Both sides reduce to the same expression. Set `S : Subgroup (GL (Fin a) (Af E))` to `{ carrier := {k | ∀ g, ((c * f₀ (finGL E a k * g) : ℝ) : ℂ) = ((c * f₀ g : ℝ) : ℂ)} one_mem' := fun g => by rw [map_one, one_mul] mul_mem' := fun {x y} hx hy g => by rw [map_mul, mul_assoc, hx, hy] inv_mem' := fun {x} hx g => (hx (finGL E a x⁻¹ * g)).symm.trans (by rw [← mul_asso …`. Conclude with `Subgroup.isOpen_mono (H₁ := U) (H₂ := S) (fun u hu g => by rw [hleft u hu]) hUo`. Conclude with `mul_nonneg (inv_nonneg.2 hpos.le) (h0 g)`.

Rewrite using `[integral_complex_ofReal, integral_const_mul, inv_mul_cancel₀ hpos.ne']`. Simplify using the standard rewrite rules. Use `congrArg (fun t : ℝ => ((c * t : ℝ) : ℂ)) (?_ : f₀ _ = f₀ _)` and prove the remaining obligations. Simplify using `only [f₀, P, Q, map_mul, pInf_infGL, pFin_infGL, mul_one, one_mul, _root_.mul_inv_rev]`. Rewrite using `[← hbc k (GeneralLinearGroup.map (pInf E) g * _), ← hbc k ((Unitary.toUnits k)⁻¹ * _)]`.

Simplify using `only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]`. Establish `h : f₀ g ≠ 0` using `fun e => hg (by simp [e])`. Take `⟨y, hy, e⟩` from `hsub (hsm g h).1`. Take `rfl : y = P g` from `Units.ext e`. Conclude with `⟨_, hy, _, (hsm g h).2, (infGL_mul_finGL g).symm⟩`.
-/
theorem exists_isDirac (μ : Measure (GA E a)) [μ.IsHaarMeasure] (U : Subgroup (GL (Fin a) (Af E)))
    (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    (N : Set (GL (Fin a) (Cinf E))) (hN : N ∈ 𝓝 1) : ∃ f, IsDirac μ U N f := by
  classical
  have : ProperSpace (Lie E a) := FiniteDimensional.proper ℝ _
  have hv : (fun y : GL (Fin a) (Cinf E) => toL y.val) '' N ∈ 𝓝 (oneL E a) := isOpenEmbedding_val.isOpenMap.image_mem_nhds hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hv
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  set m : ℝ := (n : ℝ) + 1 with hmd
  have hm : 0 < m := by positivity
  have hsub : Metric.closedBall (oneL E a) (1 / m) ⊆ (fun y : GL (Fin a) (Cinf E) => toL y.val) '' N :=
    (Metric.closedBall_subset_ball hn).trans hball
  let b : GL (Fin a) (Cinf E) → ℝ := fun y => bumpR E a m (toL y.val)
  have hb : Continuous b := (contDiff_bumpR m).continuous.comp isOpenEmbedding_val.continuous
  have hbc : ∀ (k : Kinf E a) y, b (Unitary.toUnits k * y * (Unitary.toUnits k)⁻¹) = b y := fun k y => bumpR_conj m k _
  let P := GeneralLinearGroup.map (n := Fin a) (pInf E)
  let Q := GeneralLinearGroup.map (n := Fin a) (pFin E)
  let χ : GL (Fin a) (Af E) → ℝ := (U : Set _).indicator 1
  have hχ : Continuous χ := IsClopen.continuous_indicator ⟨U.isClosed_of_isOpen hUo, hUo⟩ continuous_const
  have hχl : ∀ u ∈ U, ∀ k, χ (u * k) = χ k := fun u hu k => by
    simp only [χ, Set.indicator, SetLike.mem_coe, U.mul_mem_cancel_left hu]; rfl
  have hχi : ∀ k, χ k⁻¹ = χ k := fun k => by
    simp only [χ, Set.indicator, SetLike.mem_coe, inv_mem_iff]; rfl
  have hχ0 : ∀ k, 0 ≤ χ k := fun k => Set.indicator_nonneg (fun _ _ => zero_le_one) k
  let f₀ : GA E a → ℝ := fun g => b (P g) * b (P g)⁻¹ * χ (Q g)
  have hc : Continuous f₀ := ((hb.comp cP).mul (hb.comp cP.inv)).mul (hχ.comp cQ)
  have h0 : ∀ g, 0 ≤ f₀ g := fun g => mul_nonneg (mul_nonneg (bumpR_nonneg _ _) (bumpR_nonneg _ _)) (hχ0 _)
  have hsm : ∀ g, f₀ g ≠ 0 → toL (P g).val ∈ Metric.closedBall (oneL E a) (1 / m) ∧ Q g ∈ U := fun g h =>
    ⟨(dist_lt_of_bumpR_ne_zero hm (left_ne_zero_of_mul (left_ne_zero_of_mul h))).le,
      Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h)⟩
  have hK : IsCompact ((fun y : GL (Fin a) (Cinf E) => toL y.val) ⁻¹' Metric.closedBall (oneL E a) (1 / m)) :=
    isOpenEmbedding_val.isInducing.isCompact_preimage' (isCompact_closedBall (oneL E a) (1 / m))
      (hsub.trans (Set.image_subset_range _ _))
  have hcs : HasCompactSupport f₀ := by
    refine HasCompactSupport.intro ((hK.prod hUc).image
      ((continuous_infGL.comp continuous_fst).mul (cF.comp continuous_snd))) fun g hg => ?_
    by_contra h
    exact hg ⟨(P g, Q g), hsm g h, infGL_mul_finGL g⟩
  have h1 : f₀ 1 = 1 := by
    have : b 1 = 1 := bumpR_one m
    simp [f₀, this, χ]
  have hpos : 0 < ∫ g, f₀ g ∂μ := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs h0 (x := 1) (by rw [h1]; norm_num)
  set c := (∫ g, f₀ g ∂μ)⁻¹
  have hsym : ∀ g, f₀ g⁻¹ = f₀ g := fun g => by
    simp only [f₀, map_inv, inv_inv, hχi, mul_comm (b (P g))]
  have hleft : ∀ u ∈ U, ∀ g, f₀ (finGL E a u * g) = f₀ g := fun u hu g => by
    simp only [f₀, P, Q, map_mul, pInf_finGL, pFin_finGL, one_mul, hχl u hu]
  refine ⟨fun g => ((c * f₀ g : ℝ) : ℂ), ⟨Complex.continuous_ofReal.comp (continuous_const.mul hc), ?_, ?_, ?_⟩,
    fun g => ⟨?_, Complex.ofReal_im _⟩, ?_, fun g => by rw [hsym], fun k g => ?_, fun u hu g => by rw [hleft u hu],
    fun g hg => ?_⟩
  · exact hcs.comp_left (g := fun x : ℝ => ((c * x : ℝ) : ℂ)) (by simp)
  · intro g
    have e1 : ContDiffOn ℝ ∞ (fun x : Lie E a => bumpR E a m (lmul (toL (P g).val) x)) (invSet E a) :=
      (cd1 m (lmul (toL (P g).val))).contDiffOn
    have e2 : ContDiffOn ℝ ∞ (fun x : Lie E a => bumpR E a m (rmul (toL ((P g)⁻¹).val) (toL (Matrix.of x)⁻¹))) (invSet E a) :=
      (cd1 m (rmul (toL ((P g)⁻¹ : GL (Fin a) (Cinf E)).val))).comp_contDiffOn contDiffOn_invL
    refine (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (((e1.mul e2).mul (contDiffOn_const (c := χ (Q g)))).const_smul c)).congr ?_
    rintro x ⟨u, hu⟩
    obtain rfl : x = toL u.val := hu.symm
    rw [chart_val, hsym]
    simp only [f₀, P, Q, map_mul, pInf_infGL, pFin_infGL, mul_one, _root_.mul_inv_rev]
    have : (Matrix.of (toL u.val))⁻¹ = (u⁻¹).val := (Matrix.coe_units_inv u).symm
    simp only [Function.comp_apply, this]
    rfl
  · let S : Subgroup (GL (Fin a) (Af E)) :=
      { carrier := {k | ∀ g, ((c * f₀ (finGL E a k * g) : ℝ) : ℂ) = ((c * f₀ g : ℝ) : ℂ)}
        one_mem' := fun g => by rw [map_one, one_mul]
        mul_mem' := fun {x y} hx hy g => by rw [map_mul, mul_assoc, hx, hy]
        inv_mem' := fun {x} hx g => (hx (finGL E a x⁻¹ * g)).symm.trans (by rw [← mul_assoc (finGL E a x), ← map_mul, mul_inv_cancel, map_one, one_mul]) }
    exact Subgroup.isOpen_mono (H₁ := U) (H₂ := S) (fun u hu g => by rw [hleft u hu]) hUo
  · exact mul_nonneg (inv_nonneg.2 hpos.le) (h0 g)
  · rw [integral_complex_ofReal, integral_const_mul, inv_mul_cancel₀ hpos.ne']; simp
  · refine congrArg (fun t : ℝ => ((c * t : ℝ) : ℂ)) (?_ : f₀ _ = f₀ _)
    simp only [f₀, P, Q, map_mul, pInf_infGL, pFin_infGL, mul_one, one_mul, _root_.mul_inv_rev]
    rw [← hbc k (GeneralLinearGroup.map (pInf E) g * _), ← hbc k ((Unitary.toUnits k)⁻¹ * _)]
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
  · have h : f₀ g ≠ 0 := fun e => hg (by simp [e])
    obtain ⟨y, hy, e⟩ := hsub (hsm g h).1
    obtain rfl : y = P g := Units.ext e
    exact ⟨_, hy, _, (hsm g h).2, (infGL_mul_finGL g).symm⟩

/- English proof (translation)
Establish `h : MemL2Quotient (latticeGL E 1) μ (oneFn E 1).1` using `memL2_of_rank_one continuous_const fun _ _ _ => rfl`. Use `mem_smv.2 fun l => ?_` and prove the remaining obligations. Proceed by induction on `l using List.reverseRecOn with`. Consider the case `nil`. Establish `e : word ([] : List (Lie E 1)) (oneFn E 1) = oneFn E 1` using `by simp [word]`.

Rewrite using `[e]`. Use `⟨one_mem_cuspCont_iff.2 le_rfl, ?_, ⟨1, fun g => by simp [oneFn]⟩, h.toL2, trivial, h.lift_toL2_ae_eq⟩` and prove the remaining obligations. Establish `: {k | finRep E 1 k (oneFn E 1) = oneFn E 1} = Set.univ` using `Set.eq_univ_of_forall fun k => rfl`. Rewrite using `[this]`. Conclude with `isOpen_univ`.

Consider the case `append_singleton l X _`. Establish `e : word (l ++ [X]) (oneFn E 1) = 0` using `by simp [word, List.map_append, List.prod_append, lie_oneFn]`. Rewrite using `[e]`. Conclude with `zero_mem _`.
-/
theorem one_mem_smv (μ : Measure (GA E 1)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : oneFn E 1 ∈ smv μ ⊤ := by
  have h : MemL2Quotient (latticeGL E 1) μ (oneFn E 1).1 := memL2_of_rank_one continuous_const fun _ _ _ => rfl
  refine mem_smv.2 fun l => ?_
  induction l using List.reverseRecOn with
  | nil =>
    have e : word ([] : List (Lie E 1)) (oneFn E 1) = oneFn E 1 := by simp [word]
    rw [e]
    refine ⟨one_mem_cuspCont_iff.2 le_rfl, ?_, ⟨1, fun g => by simp [oneFn]⟩, h.toL2, trivial, h.lift_toL2_ae_eq⟩
    have : {k | finRep E 1 k (oneFn E 1) = oneFn E 1} = Set.univ := Set.eq_univ_of_forall fun k => rfl
    rw [this]; exact isOpen_univ
  | append_singleton l X _ =>
    have e : word (l ++ [X]) (oneFn E 1) = 0 := by simp [word, List.map_append, List.prod_append, lie_oneFn]
    rw [e]; exact zero_mem _

/- English proof (translation)
Introduce `h`. Establish `h1` using `one_mem_smv μ`. Rewrite `h1` using `[h, Submodule.mem_bot]`. Establish `h2` using `congrFun (congrArg Subtype.val h1) 1`. Simplify using `[oneFn] at h2`.
-/
theorem smv_top_ne_bot (μ : Measure (GA E 1)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    smv μ (⊤ : Submodule ℂ (L2 (latticeGL E 1) μ)) ≠ ⊥ := by
  intro h
  have h1 := one_mem_smv μ
  rw [h, Submodule.mem_bot] at h1
  have h2 := congrFun (congrArg Subtype.val h1) 1
  simp [oneFn] at h2

/- English proof (translation)
Establish `h` using `GlobalTheory.GLIntegral.exists_isOpen_isCompact E a`. Take `⟨U, hU⟩` from `h`. Apply the tactic sequence `obtain ⟨f, hf⟩ := exists_isDirac μ U hU.1 (by first | exact hU.2 | exact hU.2.1) N hN`. Use `⟨U, f, hf, hf.test, fun e => ?_⟩` and prove the remaining obligations. Use `hf.mass` as an intermediate fact.

Simplify using `[e] at this`.
-/
theorem exists_isDirac' (μ : Measure (GA E a)) [μ.IsHaarMeasure] (N : Set (GL (Fin a) (Cinf E))) (hN : N ∈ 𝓝 1) :
    ∃ U f, IsDirac μ U N f ∧ IsTestGL f ∧ f ≠ 0 := by
  have h := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a
  obtain ⟨U, hU⟩ := h
  obtain ⟨f, hf⟩ := exists_isDirac μ U hU.1 (by first | exact hU.2 | exact hU.2.1) N hN
  refine ⟨U, f, hf, hf.test, fun e => ?_⟩
  have := hf.mass
  simp [e] at this
end GlobalTheory.GLFin.Inhab
end
