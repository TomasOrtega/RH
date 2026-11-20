import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

noncomputable section

def zeroExt (m k : ℕ) : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin (m + k)) where
  toFun x := WithLp.toLp 2 (Fin.append (fun i => x i) 0)
  map_add' x y := by
    ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
  map_smul' c x := by
    ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, zeroExt, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_add]`. Simplify using the standard rewrite rules.
-/
theorem norm_zeroExt (m k : ℕ) (x : EuclideanSpace ℂ (Fin m)) : ‖zeroExt m k x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, zeroExt, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_add]
  simp

/- English proof (translation)
The claim follows from `AddMonoidHomClass.isometry_of_norm (zeroExt m k) (norm_zeroExt m k)`.
-/
theorem isometry_zeroExt (m k : ℕ) : Isometry (zeroExt m k) :=
  AddMonoidHomClass.isometry_of_norm (zeroExt m k) (norm_zeroExt m k)

/- English proof (translation)
Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Establish `hset : {y : EuclideanSpace ℂ (Fin (m + k)) | ‖y‖ < 1 ∧ ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0} = zeroExt m k '' Metric.ball 0 1`. Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_image, Metric.mem_ball, dist_zero_right]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hy, hz⟩`. Use `⟨WithLp.toLp 2 fun i => y (Fin.castAdd k i), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← norm_zeroExt m k]`. Use `hy using 2` and compare the differences between its conclusion and the goal. Use extensionality with `j`.

Use `Fin.addCases (fun i => ?_) (fun i => ?_) j` and prove the remaining obligations. Simplify using `[zeroExt]`. Simplify using `[zeroExt, hz (Fin.natAdd m i) (by simp)]`. Use extensionality with `j`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) j` and prove the remaining obligations.

Simplify using `[zeroExt]`. Simplify using `[zeroExt, hz (Fin.natAdd m i) (by simp)]`. Introduce and unpack `⟨x, hx, rfl⟩`. Use `⟨by rwa [norm_zeroExt], fun j hj => ?_⟩` and prove the remaining obligations. Use `revert hj`.

Use `Fin.addCases (fun i => ?_) (fun i => ?_) j` and prove the remaining obligations. Introduce `hi`. Simplify using `at hi`. Use linear arithmetic over natural numbers and integers. Introduce `_`.

Simplify using `[zeroExt]`. Rewrite using `[hset, (isometry_zeroExt m k).hausdorffMeasure_image (Or.inl (by positivity))]`. Establish `hd : ((2 * m : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ)`. Rewrite using `[finrank_real_of_complex, finrank_euclideanSpace_fin]`. Rewrite using `[hd]`.

Conclude with `⟨Metric.measure_ball_pos _ _ one_pos, measure_ball_lt_top⟩`.
-/
theorem coordBall_mass {n m : ℕ} (hmn : m ≤ n) :
    0 < Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0} ∧
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0} < ⊤ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hset : {y : EuclideanSpace ℂ (Fin (m + k)) | ‖y‖ < 1 ∧ ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0} =
      zeroExt m k '' Metric.ball 0 1 := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨hy, hz⟩
      refine ⟨WithLp.toLp 2 fun i => y (Fin.castAdd k i), ?_, ?_⟩
      · rw [← norm_zeroExt m k]
        convert hy using 2
        ext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [zeroExt]
        · simp [zeroExt, hz (Fin.natAdd m i) (by simp)]
      · ext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [zeroExt]
        · simp [zeroExt, hz (Fin.natAdd m i) (by simp)]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨by rwa [norm_zeroExt], fun j hj => ?_⟩
      revert hj
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · intro hi
        simp at hi
        omega
      · intro _
        simp [zeroExt]
  rw [hset, (isometry_zeroExt m k).hausdorffMeasure_image (Or.inl (by positivity))]
  have hd : ((2 * m : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  rw [hd]
  exact ⟨Metric.measure_ball_pos _ _ one_pos, measure_ball_lt_top⟩

def linProjₗ {m n : ℕ} (π : Fin m → Fin n → ℂ) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) where
  toFun := linProj π
  map_add' x y := by
    ext i
    simp [linProj, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    simp [linProj, Finset.mul_sum, mul_left_comm]

/- English proof (translation)
Use `set R := (LinearMap.range (linProjₗ π)).restrictScalars ℝ`. Establish `hR : R ≠ ⊤`. Introduce `hT`. Rewrite `hT` using `[Submodule.restrictScalars_eq_top_iff]`. Establish `h1` using `LinearMap.finrank_range_le (linProjₗ π)`.

Rewrite `h1` using `[hT, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]`. Use linear arithmetic over natural numbers and integers. Establish `h0 : volume (R : Set (EuclideanSpace ℂ (Fin m))) = 0` using `Measure.addHaar_submodule _ R hR`. Use `filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with w hw`. Rewrite using `[fibreCount, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]`.

Introduce and unpack `y ⟨-, rfl⟩`. Conclude with `hw ⟨y, rfl⟩`.
-/
theorem ae_fibreCount_eq_zero {n m : ℕ} (hnm : n < m) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (π : Fin m → Fin n → ℂ) :
    ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w = 0 := by
  set R := (LinearMap.range (linProjₗ π)).restrictScalars ℝ
  have hR : R ≠ ⊤ := by
    intro hT
    rw [Submodule.restrictScalars_eq_top_iff] at hT
    have h1 := LinearMap.finrank_range_le (linProjₗ π)
    rw [hT, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h1
    omega
  have h0 : volume (R : Set (EuclideanSpace ℂ (Fin m))) = 0 := Measure.addHaar_submodule _ R hR
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with w hw
  rw [fibreCount, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro y ⟨-, rfl⟩
  exact hw ⟨y, rfl⟩

/- English proof (translation)
Introduce `n e δ h W f hW hf hδ`. Establish `hfib` using `hF n e δ h W f hW hf hδ`. Establish `hmass` using `hM n (e + 1) δ h W hW hfib`. Unfold `coneIntegral`. Simplify using `only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]`.

Rewrite using `[hmass]`. Distinguish the cases in `hn : e + 1 ≤ n`. Take `⟨hpos, hfin⟩` from `coordBall_mass hn`. Rewrite using `[ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_div_assoc, div_self (ENNReal.toReal_pos hpos.ne' hfin.ne).ne', mul_one]`. Establish `hδ0 : δ = 0`.

Establish `: (volume : Measure (Fin (e + 1) → Fin n → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `: (ae (volume : Measure (Fin (e + 1) → Fin n → ℂ))).NeBot` using `ae_neBot.2 (NeZero.ne _)`. Establish `: (ae (volume : Measure (EuclideanSpace ℂ (Fin (e + 1))))).NeBot` using `ae_neBot.2 (NeZero.ne _)`. Take `⟨π, hπ⟩` from `hfib.exists`. Take `⟨w, hw1, hw2⟩` from `(hπ.and (ae_fibreCount_eq_zero (by omega) h W π)).exists`.

Rewrite `hw2` using `[hw1]`. Conclude with `hw2` after adjusting the coercions. Simplify using `[hδ0]`.
-/
theorem ConeIntegralMass.proof (hF : ConeFibreDegree.Statement) (hM : ConeMassOfFibre.Statement) :
    ConeIntegralMass.Statement := by
  intro n e δ h W f hW hf hδ
  have hfib := hF n e δ h W f hW hf hδ
  have hmass := hM n (e + 1) δ h W hW hfib
  unfold coneIntegral
  simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  rw [hmass]
  by_cases hn : e + 1 ≤ n
  · obtain ⟨hpos, hfin⟩ := coordBall_mass hn
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_div_assoc,
      div_self (ENNReal.toReal_pos hpos.ne' hfin.ne).ne', mul_one]
  · have hδ0 : δ = 0 := by
      have : (volume : Measure (Fin (e + 1) → Fin n → ℂ)).IsAddHaarMeasure :=
        Measure.pi.isAddHaarMeasure _
      have : (ae (volume : Measure (Fin (e + 1) → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
      have : (ae (volume : Measure (EuclideanSpace ℂ (Fin (e + 1))))).NeBot :=
        ae_neBot.2 (NeZero.ne _)
      obtain ⟨π, hπ⟩ := hfib.exists
      obtain ⟨w, hw1, hw2⟩ := (hπ.and (ae_fibreCount_eq_zero (by omega) h W π)).exists
      rw [hw1] at hw2
      exact_mod_cast hw2
    simp [hδ0]

end

end GroundTheory.Heights₂.Heights
