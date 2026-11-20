import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Counterexample.StatementsMuMetric
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPtsIntegralPoints
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegree
import GroundTheory.HeightsAndTheta.Heights.Intersections.ConservationDegreeFormOfExistence
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo Line

section Curve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_chartMon_notMem hW`. Rewrite using `[inter_eq_recR I hI hW (isSmoothHerm_constLine M hM) (d := 0) (fun k ↦ rfl) (isMultiHomog_chartMon c 0) (hc 0), chartMon_zero, recR_one]`. Establish `h : logNorm (constLine (ι` using `ι) M hM) 1 = fun _ ↦ -Real.log M := by`. Use function extensionality and compare the values at `z`. Simplify using `[logNorm, constLine, Real.log_inv]`.

Establish `hfin : Finite (projPts W)`. Rewrite `hdeg` using `[degC_eq_card_projPts]`. Conclude with `(Nat.card_pos_iff.mp hdeg).2`. Establish `key : ∀ φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ, ptsIntegral W φ (fun _ ↦ (1 : ℝ)) = degC W`. Introduce `φ`.

Take `rfl : φ = Fin.elim0` from `funext fun j ↦ j.elim0`. Rewrite using `[PtsIntegralPoints.homogProof K ι W (fun _ ↦ 1) hH hfin (fun _ _ _ _ ↦ rfl), degC_eq_card_projPts]`. Use `Fintype.ofFinite (projPts W)` as an intermediate fact. Rewrite using `[finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]`. Unfold `arInt`.

Rewrite using `[h, Inter.Conservation.ptsIntegral_const, key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inter_constLine_eq [Nonempty K] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    (hH : IsMultiHomogIdeal W) (hdeg : 0 < degC W) (M : ℝ) (hM : 0 < M) :
    I W 1 ![constLine M hM] = Real.log M * degC W := by
  obtain ⟨c, hc⟩ := exists_chartMon_notMem hW
  rw [inter_eq_recR I hI hW (isSmoothHerm_constLine M hM) (d := 0) (fun k ↦ rfl)
    (isMultiHomog_chartMon c 0) (hc 0), chartMon_zero, recR_one]
  have h : logNorm (constLine (ι := ι) M hM) 1 = fun _ ↦ -Real.log M := by
    funext z
    simp [logNorm, constLine, Real.log_inv]
  have hfin : Finite (projPts W) := by
    rw [degC_eq_card_projPts] at hdeg
    exact (Nat.card_pos_iff.mp hdeg).2
  have key : ∀ φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ, ptsIntegral W φ (fun _ ↦ (1 : ℝ)) = degC W := by
    intro φ
    obtain rfl : φ = Fin.elim0 := funext fun j ↦ j.elim0
    rw [PtsIntegralPoints.homogProof K ι W (fun _ ↦ 1) hH hfin (fun _ _ _ _ ↦ rfl),
      degC_eq_card_projPts]
    have := Fintype.ofFinite (projPts W)
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  unfold arInt
  rw [h, Inter.Conservation.ptsIntegral_const, key]
  ring

end Curve

section Point

def ptIdeal : Ideal (MRing (PBlk 2)) := orbitIdeal samplePoint

/- English proof (translation)
The claim follows from `OrbitCurve.full Unit (fun _ ↦ 1) samplePoint samplePoint_blockNonzero`.
-/
theorem isArithVar_ptIdeal : IsArithVar ptIdeal 1 :=
  OrbitCurve.full Unit (fun _ ↦ 1) samplePoint samplePoint_blockNonzero

/- English proof (translation)
The claim follows from `OrbitCurve.isMultiHomogIdeal_orbitIdeal samplePoint`.
-/
theorem isMultiHomogIdeal_ptIdeal : IsMultiHomogIdeal ptIdeal :=
  OrbitCurve.isMultiHomogIdeal_orbitIdeal samplePoint

/- English proof (translation)
The claim follows from `OrbitDegree.full Unit (fun _ ↦ 1) samplePoint samplePoint_blockNonzero`.
-/
theorem degC_ptIdeal_pos : 0 < degC ptIdeal :=
  OrbitDegree.full Unit (fun _ ↦ 1) samplePoint samplePoint_blockNonzero

end Point

section Shift

/- English proof (translation)
Take `⟨a, ha, hza⟩` from `exists_eq_smul_orbitRep z`. Establish `hw : ∀ k, ∃ i, orbitRep z ⟨k, i⟩ ≠ 0`. Introduce `k`. Take `⟨i, hi⟩` from `hz k`. Use `⟨i, fun h0 ↦ hi ?_⟩` and prove the remaining obligations.

Rewrite using `[hza]`. Simplify using `[torusSmul, h0]`. Use `show refNorm 0 z * Real.exp (Real.log (muMetric (lineHodgeScaled II hII c hc) (orbitRep z) / refNorm 0 (orbitRep z))) = Real.sqrt c`. Rewrite using `[hMu II hII c hc _ hw]`. Simplify using `only [refNorm, Pi.zero_apply, Int.cast_zero, zero_div, Real.rpow_zero, Finset.prod_const_one, div_one, one_mul]`.

Conclude with `Real.exp_log (Real.sqrt_pos.mpr hc)`.
-/
theorem muLine_scaled_h (hMu : MuMetricLine.Statement) (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
    (c : ℝ) (hc : 0 < c) (z : (Σ _ : Unit, Fin 2) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (muLine (lineHodgeScaled II hII c hc)).h z = Real.sqrt c := by
  obtain ⟨a, ha, hza⟩ := exists_eq_smul_orbitRep z
  have hw : ∀ k, ∃ i, orbitRep z ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hz k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    rw [hza]
    simp [torusSmul, h0]
  show refNorm 0 z * Real.exp (Real.log (muMetric (lineHodgeScaled II hII c hc) (orbitRep z) /
    refNorm 0 (orbitRep z))) = Real.sqrt c
  rw [hMu II hII c hc _ hw]
  simp only [refNorm, Pi.zero_apply, Int.cast_zero, zero_div, Real.rpow_zero, Finset.prod_const_one,
    div_one, one_mul]
  exact Real.exp_log (Real.sqrt_pos.mpr hc)

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet in

/- English proof (translation)
Use `set h1 := fsHeight_nonneg II hII`. Use `set μc := muLine (lineHodgeScaled II h1 c hc)`. Use `set μ1 := muLine (lineHodgeScaled II h1 1 one_pos)`. Establish `hsc : 0 < Real.sqrt c` using `Real.sqrt_pos.mpr hc`. Establish `hμc : ∀ z : (Σ _ : Unit, Fin 2) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → μc.h z = Real.sqrt c` using `muLine_scaled_h hMu II h1 c hc`.

Establish `hμ1 : ∀ z : (Σ _ : Unit, Fin 2) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → μ1.h z = 1` using `fun z hz ↦ by`. Rewrite using `[muLine_scaled_h hMu II h1 1 one_pos z hz, Real.sqrt_one]`. Establish `hsm : ∀ (μ : Geo.HermLine (PBlk 2)) (v : ℝ), (∀ z : (Σ _ : Unit, Fin 2) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → μ.h z = v) → IsSmoothHerm μ` using `fun μ v h ↦ contDiffOn_const.congr fun z hz ↦ h z hz`. Establish `hshift` using `R.shift t' μ1 μc (Real.sqrt c) hsc rfl fun z hz ↦ by rw [hμc z hz, hμ1 z hz, mul_one]`. Establish `hrc` using `R.smooth t' μc (hsm μc _ hμc)`.

Establish `hr1` using `R.smooth t' μ1 (hsm μ1 _ hμ1)`. Establish `hI` using `hII Unit (PBlk 2)`. Establish `hcongr : II Unit (PBlk 2) W 1 ![R.reg t' μc] = II Unit (PBlk 2) W 1 ![(R.reg t' μ1).tensor (constLine (Real.sqrt c) hsc)]` using `inter_congr (II Unit (PBlk 2)) hI hW hrc (IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_tensor hr1 (isSmoothHerm_constLine _ _)) (d := 0) (fun k ↦ by rw [R.deg]; rfl) (fun k ↦ by show (R.reg t' μ1).a k + (0 : Unit → ℤ) k = _`. Rewrite using `[R.deg]`. Use the proof step `rfl)`.

Use the proof step `(fun z hz ↦ by`. Rewrite using `[hshift z hz.1]`. Use `show _ = (R.reg t' μ1).h z * Real.sqrt c`. Use the proof step `ring)`. Establish `hA : ∀ (c' : ℝ) (hc' : 0 < c'), (lineDataScaled II h1 c' hc').A' = fsLine 2` using `fun _ _ ↦ rfl`.

Establish `hd : (degC W : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr hdeg.ne'`. Simplify using `only [heightMU, hA]`. Rewrite using `[hcongr, inter_tensor (II Unit (PBlk 2)) hI hW hr1 (isSmoothHerm_constLine _ _), inter_constLine_eq (II Unit (PBlk 2)) hI hW hH hdeg]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heightMU_scaled (hMu : MuMetricLine.Statement) (II : IntersectionSystem)
    (hII : IsIntersectionSystem II) (R : WeightReg (PBlk 2)) (eps t' : ℝ) {W : Ideal (MRing (PBlk 2))}
    (hW : IsArithVar W 1) (hH : IsMultiHomogIdeal W) (hdeg : 0 < degC W) (c : ℝ) (hc : 0 < c) :
    heightMU (lineDataScaled II (fsHeight_nonneg II hII) c hc)
        (lineHodgeScaled II (fsHeight_nonneg II hII) c hc) R eps t' W =
      heightMU (lineDataScaled II (fsHeight_nonneg II hII) 1 one_pos)
        (lineHodgeScaled II (fsHeight_nonneg II hII) 1 one_pos) R eps t' W + Real.log (Real.sqrt c) := by
  set h1 := fsHeight_nonneg II hII
  set μc := muLine (lineHodgeScaled II h1 c hc)
  set μ1 := muLine (lineHodgeScaled II h1 1 one_pos)
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hμc : ∀ z : (Σ _ : Unit, Fin 2) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → μc.h z = Real.sqrt c :=
    muLine_scaled_h hMu II h1 c hc
  have hμ1 : ∀ z : (Σ _ : Unit, Fin 2) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → μ1.h z = 1 := fun z hz ↦ by
    rw [muLine_scaled_h hMu II h1 1 one_pos z hz, Real.sqrt_one]
  have hsm : ∀ (μ : Geo.HermLine (PBlk 2)) (v : ℝ),
      (∀ z : (Σ _ : Unit, Fin 2) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → μ.h z = v) → IsSmoothHerm μ :=
    fun μ v h ↦ contDiffOn_const.congr fun z hz ↦ h z hz
  have hshift := R.shift t' μ1 μc (Real.sqrt c) hsc rfl fun z hz ↦ by rw [hμc z hz, hμ1 z hz, mul_one]
  have hrc := R.smooth t' μc (hsm μc _ hμc)
  have hr1 := R.smooth t' μ1 (hsm μ1 _ hμ1)
  have hI := hII Unit (PBlk 2)
  have hcongr : II Unit (PBlk 2) W 1 ![R.reg t' μc] =
      II Unit (PBlk 2) W 1 ![(R.reg t' μ1).tensor (constLine (Real.sqrt c) hsc)] :=
    inter_congr (II Unit (PBlk 2)) hI hW hrc (IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_tensor hr1 (isSmoothHerm_constLine _ _))
      (d := 0) (fun k ↦ by rw [R.deg]; rfl)
      (fun k ↦ by
        show (R.reg t' μ1).a k + (0 : Unit → ℤ) k = _
        rw [R.deg]
        rfl)
      (fun z hz ↦ by
        rw [hshift z hz.1]
        show _ = (R.reg t' μ1).h z * Real.sqrt c
        ring)
  have hA : ∀ (c' : ℝ) (hc' : 0 < c'), (lineDataScaled II h1 c' hc').A' = fsLine 2 := fun _ _ ↦ rfl
  have hd : (degC W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdeg.ne'
  simp only [heightMU, hA]
  rw [hcongr, inter_tensor (II Unit (PBlk 2)) hI hW hr1 (isSmoothHerm_constLine _ _),
    inter_constLine_eq (II Unit (PBlk 2)) hI hW hH hdeg]
  field_simp
  ring

end Shift

section Main

def HtInteriorNotUniversal.Statement : Prop :=
  ∀ (II : IntersectionSystem) (hII : IsIntersectionSystem II) (R : WeightReg (PBlk 2)) (Ch rd Lval : ℝ),
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (c : ℝ) (hc : 0 < c), c ≤ c₀ →
      ¬ HtInteriorArch (lineDataScaled II (fsHeight_nonneg II hII) c hc)
        (lineHodgeScaled II (fsHeight_nonneg II hII) c hc) R Ch rd Lval

/- English proof (translation)
The claim follows from `weightRegRef`.
-/
example : WeightReg (PBlk 2) := weightRegRef

/- English proof (translation)
Introduce `II hII R Ch rd Lval`. Use `set h1 := fsHeight_nonneg II hII`. Use `set X := heightMU (lineDataScaled II h1 1 one_pos) (lineHodgeScaled II h1 1 one_pos) R 1 1 ptIdeal`. Use `set β := -Ch * abelian₂ 16 rd Lval`. Use `⟨Real.exp (2 * (β - X - 1)), Real.exp_pos _, fun c hc hcle hN ↦ ?_⟩` and prove the remaining obligations.

Establish `hPX : (lineDataScaled II h1 c hc).PX ≤ ptIdeal` using `by show mCoordIdeal yLine ≤ _`. Rewrite using `[mCoordIdeal_yLine]`. Conclude with `bot_le`. Establish `h` using `hN 16 (by rw [lineDataScaled_f, lineDataScaled_N]; norm_num) 1 1 one_pos le_rfl one_pos le_rfl ptIdeal isArithVar_ptIdeal hPX (fun z _ hz ↦ Set.notMem_empty z hz)`. Rewrite `h` using `[heightMU_scaled hMu II hII R 1 1 isArithVar_ptIdeal isMultiHomogIdeal_ptIdeal degC_ptIdeal_pos c hc, Real.log_sqrt hc.le]`.

Establish `hK : (lineDataScaled II h1 c hc).KA = 0` using `rfl`. Rewrite `h` using `[lineDataScaled_f, lineDataScaled_j', hK]`. Establish `hlog : Real.log c ≤ 2 * (β - X - 1)`. Rewrite using `[← Real.log_exp (2 * (β - X - 1))]`. Conclude with `Real.log_le_log hc hcle`.

Move the coercions through the operations in `at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem HtInteriorNotUniversal.proof (hMu : MuMetricLine.Statement) : HtInteriorNotUniversal.Statement := by
  intro II hII R Ch rd Lval
  set h1 := fsHeight_nonneg II hII
  set X := heightMU (lineDataScaled II h1 1 one_pos) (lineHodgeScaled II h1 1 one_pos) R 1 1 ptIdeal
  set β := -Ch * abelian₂ 16 rd Lval
  refine ⟨Real.exp (2 * (β - X - 1)), Real.exp_pos _, fun c hc hcle hN ↦ ?_⟩
  have hPX : (lineDataScaled II h1 c hc).PX ≤ ptIdeal := by
    show mCoordIdeal yLine ≤ _
    rw [mCoordIdeal_yLine]
    exact bot_le
  have h := hN 16 (by rw [lineDataScaled_f, lineDataScaled_N]; norm_num) 1 1 one_pos le_rfl one_pos le_rfl
    ptIdeal isArithVar_ptIdeal hPX (fun z _ hz ↦ Set.notMem_empty z hz)
  rw [heightMU_scaled hMu II hII R 1 1 isArithVar_ptIdeal isMultiHomogIdeal_ptIdeal degC_ptIdeal_pos c hc,
    Real.log_sqrt hc.le] at h
  have hK : (lineDataScaled II h1 c hc).KA = 0 := rfl
  rw [lineDataScaled_f, lineDataScaled_j', hK] at h
  have hlog : Real.log c ≤ 2 * (β - X - 1) := by
    rw [← Real.log_exp (2 * (β - X - 1))]
    exact Real.log_le_log hc hcle
  push_cast at h
  linarith

end Main

end GroundTheory.Heights₂.Heights.LowerBoundFree
