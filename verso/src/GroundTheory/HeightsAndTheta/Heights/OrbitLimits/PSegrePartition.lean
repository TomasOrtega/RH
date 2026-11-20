import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegrePartition
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (segre)

namespace SegrePartition

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def segreSq (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) : ℝ := ‖segre z i‖ ^ 2

def segreSqSum (z : (Σ k, ι k) → ℂ) : ℝ := ∑ i, segreSq z i

def numIdx (ι : K → Type*) [∀ k, Fintype (ι k)] : ℝ := Fintype.card ((k : K) → ι k)

def bump (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) : ℝ :=
  Real.smoothTransition (2 * numIdx ι * (segreSq z i / segreSqSum z) - 1)

open Classical in

def rho (i : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if 0 < segreSqSum z then bump z i / ∑ j, bump z j else 1 / numIdx ι

omit [DecidableEq K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
The claim follows from `sq_nonneg _`.
-/
theorem segreSq_nonneg (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) : 0 ≤ segreSq z i :=
  sq_nonneg _

omit [DecidableEq K] in
/- English proof (translation)
Establish `h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => segre z i)` using `contDiff_prod fun k _ => contDiff_apply ℝ ℂ (⟨k, i k⟩ : Σ k, ι k)`. Conclude with `(contDiff_norm_sq ℝ).comp h`.
-/
theorem contDiff_segreSq (i : (k : K) → ι k) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => segreSq z i) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => segre z i) :=
    contDiff_prod fun k _ => contDiff_apply ℝ ℂ (⟨k, i k⟩ : Σ k, ι k)
  exact (contDiff_norm_sq ℝ).comp h

/- English proof (translation)
The claim follows from `ContDiff.sum fun i _ => contDiff_segreSq i`.
-/
theorem contDiff_segreSqSum :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => segreSqSum z) :=
  ContDiff.sum fun i _ => contDiff_segreSq i

/- English proof (translation)
Use `choose i hi using hz`. Establish `h : segre z i ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hi k`. Conclude with `Finset.sum_pos' (fun j _ => segreSq_nonneg z j) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr h) 2⟩`.
-/
theorem segreSqSum_pos {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : 0 < segreSqSum z := by
  choose i hi using hz
  have h : segre z i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hi k
  exact Finset.sum_pos' (fun j _ => segreSq_nonneg z j)
    ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr h) 2⟩

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
The claim follows from `Finset.prod_mul_distrib`.
-/
theorem segre_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) :
    segre (fun p => c p.1 * z p) i = (∏ k, c k) * segre z i :=
  Finset.prod_mul_distrib

omit [DecidableEq K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Simplify using `only [segreSq, segre_smul, norm_mul, mul_pow]`.
-/
theorem segreSq_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) :
    segreSq (fun p => c p.1 * z p) i = ‖∏ k, c k‖ ^ 2 * segreSq z i := by
  simp only [segreSq, segre_smul, norm_mul, mul_pow]

/- English proof (translation)
Simplify using `only [segreSqSum, segreSq_smul, Finset.mul_sum]`.
-/
theorem segreSqSum_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segreSqSum (fun p => c p.1 * z p) = ‖∏ k, c k‖ ^ 2 * segreSqSum z := by
  simp only [segreSqSum, segreSq_smul, Finset.mul_sum]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hle : ∀ j, segreSq z j ≤ segreSqSum z / (2 * numIdx ι)`. Introduce `j`. Establish `h1 : 2 * numIdx ι * (segreSq z j / segreSqSum z) - 1 ≤ 0`.

Assume the negation of the conclusion as `h2`. Conclude with `absurd (Real.smoothTransition.pos_of_pos (lt_of_not_ge h2)) (not_lt.mpr (h j))`. Rewrite using `[le_div_iff₀ (by positivity)]`. Establish `h3 : 2 * numIdx ι * segreSq z j / segreSqSum z ≤ 1`. Rewrite using `[mul_div_assoc]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h3` using `[div_le_one hS]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum : segreSqSum z ≤ numIdx ι * (segreSqSum z / (2 * numIdx ι))`. Use `Finset.sum_le_card_nsmul Finset.univ (fun j => segreSq z j) _ fun j _ => hle j` as an intermediate fact.

Rewrite `this` using `[Finset.card_univ, nsmul_eq_mul]`. Conclude with `this`. Establish `h4 : numIdx ι * (segreSqSum z / (2 * numIdx ι)) = segreSqSum z / 2`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_bump_pos (hN : 0 < numIdx ι) {z : (Σ k, ι k) → ℂ} (hS : 0 < segreSqSum z) :
    ∃ j, 0 < bump z j := by
  by_contra h
  push Not at h
  have hle : ∀ j, segreSq z j ≤ segreSqSum z / (2 * numIdx ι) := by
    intro j
    have h1 : 2 * numIdx ι * (segreSq z j / segreSqSum z) - 1 ≤ 0 := by
      by_contra h2
      exact absurd (Real.smoothTransition.pos_of_pos (lt_of_not_ge h2)) (not_lt.mpr (h j))
    rw [le_div_iff₀ (by positivity)]
    have h3 : 2 * numIdx ι * segreSq z j / segreSqSum z ≤ 1 := by
      rw [mul_div_assoc]; linarith
    rw [div_le_one hS] at h3
    linarith
  have hsum : segreSqSum z ≤ numIdx ι * (segreSqSum z / (2 * numIdx ι)) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun j => segreSq z j) _ fun j _ => hle j
    rw [Finset.card_univ, nsmul_eq_mul] at this
    exact this
  have h4 : numIdx ι * (segreSqSum z / (2 * numIdx ι)) = segreSqSum z / 2 := by
    field_simp
  linarith

/- English proof (translation)
Take `⟨j, hj⟩` from `exists_bump_pos hN hS`. Conclude with `Finset.sum_pos' (fun i _ => Real.smoothTransition.nonneg _) ⟨j, Finset.mem_univ _, hj⟩`.
-/
theorem bump_sum_pos (hN : 0 < numIdx ι) {z : (Σ k, ι k) → ℂ} (hS : 0 < segreSqSum z) :
    0 < ∑ j, bump z j := by
  obtain ⟨j, hj⟩ := exists_bump_pos hN hS
  exact Finset.sum_pos' (fun i _ => Real.smoothTransition.nonneg _) ⟨j, Finset.mem_univ _, hj⟩

/- English proof (translation)
Use `(Real.smoothTransition.contDiff (n := ⊤)).comp_contDiffOn ?_` and prove the remaining obligations. Use `ContDiffOn.sub (contDiffOn_const.mul ?_) contDiffOn_const` and prove the remaining obligations. Conclude with `ContDiffOn.div (contDiff_segreSq i).contDiffOn contDiff_segreSqSum.contDiffOn fun z hz => (segreSqSum_pos hz).ne'`.
-/
theorem contDiffOn_bump (i : (k : K) → ι k) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => bump z i)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  refine (Real.smoothTransition.contDiff (n := ⊤)).comp_contDiffOn ?_
  refine ContDiffOn.sub (contDiffOn_const.mul ?_) contDiffOn_const
  exact ContDiffOn.div (contDiff_segreSq i).contDiffOn contDiff_segreSqSum.contDiffOn
    fun z hz => (segreSqSum_pos hz).ne'

/- English proof (translation)
Establish `ha : ‖∏ k, c k‖ ^ 2 ≠ 0` using `pow_ne_zero 2 (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => hc k))`. Simplify using `only [bump, segreSq_smul, segreSqSum_smul, mul_div_mul_left _ _ ha]`.
-/
theorem bump_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) (i : (k : K) → ι k) :
    bump (fun p => c p.1 * z p) i = bump z i := by
  have ha : ‖∏ k, c k‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => hc k))
  simp only [bump, segreSq_smul, segreSqSum_smul, mul_div_mul_left _ _ ha]

/- English proof (translation)
Use `⟨?_, fun c z hc => ?_⟩` and prove the remaining obligations. Establish `hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => bump z i / ∑ j, bump z j) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}` using `ContDiffOn.div (contDiffOn_bump i) (ContDiffOn.sum fun j _ => contDiffOn_bump j) fun z hz => (bump_sum_pos hN (segreSqSum_pos hz)).ne'`. Use `hf.congr fun z hz => ?_` and prove the remaining obligations. Simplify using `only [rho, if_pos (segreSqSum_pos hz)]`. Establish `ha : 0 < ‖∏ k, c k‖ ^ 2` using `pow_pos (norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => hc k)) 2`.

Establish `hS : 0 < segreSqSum (fun p => c p.1 * z p) ↔ 0 < segreSqSum z`. Rewrite using `[segreSqSum_smul]`. Conclude with `mul_pos_iff_of_pos_left ha`. Simplify using `only [rho, hS, bump_smul c z hc]`.
-/
theorem isDegZeroSmooth_rho (hN : 0 < numIdx ι) (i : (k : K) → ι k) :
    IsDegZeroSmooth (rho (ι := ι) i) := by
  refine ⟨?_, fun c z hc => ?_⟩
  · have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : (Σ k, ι k) → ℂ => bump z i / ∑ j, bump z j) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
      ContDiffOn.div (contDiffOn_bump i) (ContDiffOn.sum fun j _ => contDiffOn_bump j)
        fun z hz => (bump_sum_pos hN (segreSqSum_pos hz)).ne'
    refine hf.congr fun z hz => ?_
    simp only [rho, if_pos (segreSqSum_pos hz)]
  · have ha : 0 < ‖∏ k, c k‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => hc k)) 2
    have hS : 0 < segreSqSum (fun p => c p.1 * z p) ↔ 0 < segreSqSum z := by
      rw [segreSqSum_smul]; exact mul_pos_iff_of_pos_left ha
    simp only [rho, hS, bump_smul c z hc]

/- English proof (translation)
Distinguish the cases in `hS : 0 < segreSqSum z`. Simplify using `only [rho, if_pos hS]`. Rewrite using `[← Finset.sum_div, div_self (bump_sum_pos hN hS).ne']`. Simplify using `only [rho, if_neg hS, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite `hN`, the goal using `[numIdx]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem sum_rho (hN : 0 < numIdx ι) (z : (Σ k, ι k) → ℂ) : ∑ i, rho (ι := ι) i z = 1 := by
  by_cases hS : 0 < segreSqSum z
  · simp only [rho, if_pos hS]
    rw [← Finset.sum_div, div_self (bump_sum_pos hN hS).ne']
  · simp only [rho, if_neg hS, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [numIdx] at hN ⊢
    field_simp

/- English proof (translation)
Establish `hδ : 0 < (Real.sqrt (2 * numIdx ι))⁻¹` using `inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))`. Establish `hw : 0 < ‖segre z‖`. Assume the negation of the conclusion as `h0`. Establish `: ‖segre z‖ = 0` using `le_antisymm (not_lt.mp h0) (norm_nonneg _)`. Rewrite `h` using `[this, mul_zero]`.

Conclude with `absurd h (not_lt.mpr (norm_nonneg _))`. Establish `hle : ‖segre z‖ ≤ Real.sqrt (segreSqSum z)`. Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_` and prove the remaining obligations. Use `Real.le_sqrt_of_sq_le ?_` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun j => segreSq z j) (fun j _ => segreSq_nonneg z j) (Finset.mem_univ j)`.

Establish `hS : 0 < segreSqSum z` using `Real.sqrt_pos.mp (lt_of_lt_of_le hw hle)`. Establish `h1 : ‖segre z i‖ < (Real.sqrt (2 * numIdx ι))⁻¹ * Real.sqrt (segreSqSum z)` using `lt_of_lt_of_le h (mul_le_mul_of_nonneg_left hle hδ.le)`. Establish `h2 : segreSq z i < segreSqSum z / (2 * numIdx ι)`. Establish `h3` using `pow_lt_pow_left₀ h1 (norm_nonneg _) two_ne_zero`. Rewrite `h3` using `[mul_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hS.le]`.

Rewrite using `[segreSq]`. Combine the equalities or inequalities in the displayed calculation. Establish `hb : bump z i = 0`. Use `Real.smoothTransition.zero_of_nonpos ?_` and prove the remaining obligations. Rewrite `h2` using `[lt_div_iff₀ (by positivity)]`.

Establish `h4 : 2 * numIdx ι * (segreSq z i / segreSqSum z) ≤ 1`. Rewrite using `[← mul_div_assoc, div_le_one hS]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [rho, if_pos hS, hb, zero_div]`.
-/
theorem rho_eq_zero (hN : 0 < numIdx ι) (i : (k : K) → ι k) (z : (Σ k, ι k) → ℂ)
    (h : ‖segre z i‖ < (Real.sqrt (2 * numIdx ι))⁻¹ * ‖segre z‖) : rho i z = 0 := by
  have hδ : 0 < (Real.sqrt (2 * numIdx ι))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hw : 0 < ‖segre z‖ := by
    by_contra h0
    have : ‖segre z‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
    rw [this, mul_zero] at h
    exact absurd h (not_lt.mpr (norm_nonneg _))
  have hle : ‖segre z‖ ≤ Real.sqrt (segreSqSum z) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun j => segreSq z j) (fun j _ => segreSq_nonneg z j)
      (Finset.mem_univ j)
  have hS : 0 < segreSqSum z := Real.sqrt_pos.mp (lt_of_lt_of_le hw hle)
  have h1 : ‖segre z i‖ < (Real.sqrt (2 * numIdx ι))⁻¹ * Real.sqrt (segreSqSum z) :=
    lt_of_lt_of_le h (mul_le_mul_of_nonneg_left hle hδ.le)
  have h2 : segreSq z i < segreSqSum z / (2 * numIdx ι) := by
    have h3 := pow_lt_pow_left₀ h1 (norm_nonneg _) two_ne_zero
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hS.le] at h3
    rw [segreSq]
    calc ‖segre z i‖ ^ 2 < (2 * numIdx ι)⁻¹ * segreSqSum z := h3
      _ = segreSqSum z / (2 * numIdx ι) := by rw [inv_mul_eq_div]
  have hb : bump z i = 0 := by
    refine Real.smoothTransition.zero_of_nonpos ?_
    rw [lt_div_iff₀ (by positivity)] at h2
    have h4 : 2 * numIdx ι * (segreSq z i / segreSqSum z) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one hS]
      linarith
    linarith
  simp only [rho, if_pos hS, hb, zero_div]

end SegrePartition

/- English proof (translation)
Introduce `K _ _ ι _ hne`. Establish `hN : 0 < SegrePartition.numIdx ι`. Rewrite using `[SegrePartition.numIdx, Nat.cast_pos]`. Conclude with `Fintype.card_pos`. Conclude with `⟨(Real.sqrt (2 * SegrePartition.numIdx ι))⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)), SegrePartition.rho, SegrePartition.isDegZeroSmooth_rho hN, SegrePartition.sum_rho hN, SegrePartition.rho_eq_zero hN⟩`.
-/
theorem SegrePartition.proof : SegrePartition.Statement := by
  intro K _ _ ι _ hne
  have hN : 0 < SegrePartition.numIdx ι := by
    rw [SegrePartition.numIdx, Nat.cast_pos]
    exact Fintype.card_pos
  exact ⟨(Real.sqrt (2 * SegrePartition.numIdx ι))⁻¹,
    inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)), SegrePartition.rho,
    SegrePartition.isDegZeroSmooth_rho hN, SegrePartition.sum_rho hN,
    SegrePartition.rho_eq_zero hN⟩

end GroundTheory.Heights₂.Heights
