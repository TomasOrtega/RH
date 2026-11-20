import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPlace

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix
open scoped ENNReal NNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyCV

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
  Formalism.L2.SG.Pf.Carrier.EnergyPlace

section Weight

variable {r : ℕ}

/- English proof (translation)
The claim follows from `| 0 => by simp | n + 1 => by rw [Finset.prod_Icc_succ_top (by omega), prod_Icc_range x n, Finset.prod_range_succ (fun i => x i ^ (n + 1 - i)), Finset.prod_range_succ x n] have h : ∏ i ∈ Finset.range n, x i ^ (n + 1 - i) = (∏ i ∈ Finset.range n, x i ^ (n - i)) * ∏ i ∈ Finset.range …`.
-/
theorem prod_Icc_range (x : ℕ → ℝ) : ∀ n : ℕ,
    ∏ l ∈ Finset.Icc 1 n, ∏ i ∈ Finset.range l, x i = ∏ i ∈ Finset.range n, x i ^ (n - i)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.prod_Icc_succ_top (by omega), prod_Icc_range x n, Finset.prod_range_succ (fun i => x i ^ (n + 1 - i)),
      Finset.prod_range_succ x n]
    have h : ∏ i ∈ Finset.range n, x i ^ (n + 1 - i) =
        (∏ i ∈ Finset.range n, x i ^ (n - i)) * ∏ i ∈ Finset.range n, x i := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
    rw [h, show n + 1 - n = 1 by omega, pow_one]
    ring

def xN (c : Fin (r + 1) → ℂ) (i : ℕ) : ℝ := if h : i < r + 1 then ‖c ⟨i, h⟩‖ else 1

/- English proof (translation)
Unfold `Formalism.L2.SG.RealObj.Dl`. Rewrite using `[dif_pos hl, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hl), Matrix.det_diagonal, norm_prod, ← Fin.prod_univ_eq_prod_range]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hi : (i : ℕ) < r + 1` using `lt_of_lt_of_le i.2 hl`. Simplify using `only [xN, dif_pos hi, Function.comp_apply]`.

Both sides reduce to the same expression.
-/
theorem norm_dl_diag (c : Fin (r + 1) → ℂ) (l : ℕ) (hl : l ≤ r + 1) :
    ‖Formalism.L2.SG.RealObj.Dl (Matrix.diagonal c) l‖ = ∏ i ∈ Finset.range l, xN c i := by
  unfold Formalism.L2.SG.RealObj.Dl
  rw [dif_pos hl, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hl), Matrix.det_diagonal, norm_prod,
    ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : (i : ℕ) < r + 1 := lt_of_lt_of_le i.2 hl
  simp only [xN, dif_pos hi, Function.comp_apply]
  rfl

/- English proof (translation)
Unfold `xN`. Rewrite using `[dif_pos (by omega)]`. Both sides reduce to the same expression.
-/
theorem xN_last (c : Fin (r + 1) → ℂ) : xN c r = ‖c (Fin.last r)‖ := by
  unfold xN
  rw [dif_pos (by omega)]
  rfl

/- English proof (translation)
Unfold `Gv`. Rewrite using `[norm_dl_diag c (r + 1) le_rfl, norm_dl_diag c r (by omega), Finset.prod_range_succ, xN_last]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gv_diag (T T' : ℝ) (c : Fin (r + 1) → ℂ) :
    Gv T T' (Matrix.diagonal c) = (∏ i ∈ Finset.range r, xN c i) ^ 2 * (‖c (Fin.last r)‖ ^ 2 - T * T') := by
  unfold Gv
  rw [norm_dl_diag c (r + 1) le_rfl, norm_dl_diag c r (by omega), Finset.prod_range_succ, xN_last]
  ring

/- English proof (translation)
Unfold `JacV modC`. Rewrite using `[← prod_Icc_range (fun i => xN c i ^ 4) r]`. Use `Finset.prod_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite `hl` using `[Finset.mem_Icc]`. Rewrite using `[norm_dl_diag c l (by omega), Finset.prod_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem jac_diag (c : Fin (r + 1) → ℂ) :
    JacV (Matrix.diagonal c) = ∏ i ∈ Finset.range r, (xN c i ^ 4) ^ (r - i) := by
  unfold JacV modC
  rw [← prod_Icc_range (fun i => xN c i ^ 4) r]
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Finset.mem_Icc] at hl
  rw [norm_dl_diag c l (by omega), Finset.prod_pow]
  ring

def phiC (lam : Fin r → ℝ) (c : Fin (r + 1) → ℂ) : (Fin r → ℂ) × ℂ :=
  (fun a => ((lam a : ℝ) : ℂ) * c ⟨a.val, by have := a.2; omega⟩, c ⟨r, by omega⟩)

/- English proof (translation)
Establish `h1 : ∀ a : Fin r, ‖(phiC lam c).1 a‖ = lam a * xN c a` using `fun a => by`. Establish `ha : (a : ℕ) < r + 1` using `by have := a.2; omega`. Simplify using `only [phiC, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hlam a), xN, dif_pos ha]`. Simplify using `only [h1, mul_pow, Finset.prod_mul_distrib]`. Use `congr 1`.

Use `show ∏ a : Fin r, (fun i : ℕ => xN c i ^ (2 * (2 * (r - i) + k + 1 - 2))) a = _`. Rewrite using `[Fin.prod_univ_eq_prod_range (fun i : ℕ => xN c i ^ (2 * (2 * (r - i) + k + 1 - 2))) r, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[← pow_mul, ← pow_mul, ← pow_add]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem bc_prod (k : ℕ) (hk : 1 ≤ k) (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) (c : Fin (r + 1) → ℂ) :
    ∏ a : Fin r, ‖(phiC lam c).1 a‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)) =
      (∏ a : Fin r, lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2))) *
        (((∏ i ∈ Finset.range r, xN c i) ^ 2) ^ (k - 1) * ∏ i ∈ Finset.range r, (xN c i ^ 4) ^ (r - i)) := by
  have h1 : ∀ a : Fin r, ‖(phiC lam c).1 a‖ = lam a * xN c a := fun a => by
    have ha : (a : ℕ) < r + 1 := by have := a.2; omega
    simp only [phiC, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hlam a), xN, dif_pos ha]
  simp only [h1, mul_pow, Finset.prod_mul_distrib]
  congr 1
  show ∏ a : Fin r, (fun i : ℕ => xN c i ^ (2 * (2 * (r - i) + k + 1 - 2))) a = _
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => xN c i ^ (2 * (2 * (r - i) + k + 1 - 2))) r,
    ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  omega

end Weight

section AE

instance sf2 : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by
  have h : ((2 : ℝ≥0∞) • (volume : Measure ℂ)) = ((2 : ℝ≥0) • (volume : Measure ℂ)) := by
    rw [ENNReal.smul_def]; simp
  rw [h]; infer_instance

variable {r : ℕ}

def GoodC (T T' : ℝ) : Set (Fin (r + 1) → ℂ) :=
  {c | (∀ l, c l ≠ 0) ∧ 0 < Gv T T' (Matrix.diagonal c)}

def dcC : Measure (Fin (r + 1) → ℂ) := Measure.pi fun _ => (2 : ℝ≥0∞) • (volume : Measure ℂ)

def kapC (k : ℕ) (lam : Fin r → ℝ) : ℝ := ∏ a : Fin r, (lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)))⁻¹

/- English proof (translation)
The claim follows from `Finset.prod_nonneg fun a _ => inv_nonneg.2 (pow_nonneg (hlam a).le _)`.
-/
theorem kapC_nonneg (k : ℕ) (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) : 0 ≤ kapC k lam := Finset.prod_nonneg fun a _ => inv_nonneg.2 (pow_nonneg (hlam a).le _)

/- English proof (translation)
Establish `hsub : {c : Fin (r + 1) → ℂ | ¬ ((∀ i, c i ≠ 0) ∧ ‖c (Fin.last r)‖ ^ 2 ≠ T * T')} ⊆ (⋃ i, Function.eval i ⁻¹' ({0} : Set ℂ)) ∪ Function.eval (Fin.last r) ⁻¹' {z : ℂ | ‖z‖ ^ 2 = T * T'}`. Introduce `c hc`. Simplify using `only [Set.mem_setOf_eq, not_and_or, not_forall, not_not] at hc`. Break down `hc with ⟨i, hi⟩ | h` into its components or cases. Conclude with `Or.inl (Set.mem_iUnion.2 ⟨i, hi⟩)`.

Conclude with `Or.inr h`. Use `measure_mono_null hsub (measure_union_null (measure_iUnion_null fun i => ?_) ?_)` and prove the remaining obligations. Use `Measure.pi_eval_preimage_null _ ?_` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, measure_singleton, smul_zero]`. Use `Measure.pi_eval_preimage_null _ ?_` and prove the remaining obligations.

Rewrite using `[Measure.smul_apply]`. Establish `hs : {z : ℂ | ‖z‖ ^ 2 = T * T'} ⊆ Metric.sphere 0 (Real.sqrt (T * T'))`. Introduce `z hz`. Simplify using `only [Set.mem_setOf_eq] at hz`. Simplify using `only [mem_sphere_iff_norm, sub_zero]`.

Rewrite using `[← hz, Real.sqrt_sq (norm_nonneg z)]`. Rewrite using `[measure_mono_null hs (Measure.addHaar_sphere volume 0 _), smul_zero]`.
-/
theorem null_set (T T' : ℝ) :
    dcC (r := r) {c | ¬ ((∀ i, c i ≠ 0) ∧ ‖c (Fin.last r)‖ ^ 2 ≠ T * T')} = 0 := by
  have hsub : {c : Fin (r + 1) → ℂ | ¬ ((∀ i, c i ≠ 0) ∧ ‖c (Fin.last r)‖ ^ 2 ≠ T * T')} ⊆
      (⋃ i, Function.eval i ⁻¹' ({0} : Set ℂ)) ∪
        Function.eval (Fin.last r) ⁻¹' {z : ℂ | ‖z‖ ^ 2 = T * T'} := by
    intro c hc
    simp only [Set.mem_setOf_eq, not_and_or, not_forall, not_not] at hc
    rcases hc with ⟨i, hi⟩ | h
    · exact Or.inl (Set.mem_iUnion.2 ⟨i, hi⟩)
    · exact Or.inr h
  refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun i => ?_) ?_)
  · refine Measure.pi_eval_preimage_null _ ?_
    rw [Measure.smul_apply, measure_singleton, smul_zero]
  · refine Measure.pi_eval_preimage_null _ ?_
    rw [Measure.smul_apply]
    have hs : {z : ℂ | ‖z‖ ^ 2 = T * T'} ⊆ Metric.sphere 0 (Real.sqrt (T * T')) := by
      intro z hz
      simp only [Set.mem_setOf_eq] at hz
      simp only [mem_sphere_iff_norm, sub_zero]
      rw [← hz, Real.sqrt_sq (norm_nonneg z)]
    rw [measure_mono_null hs (Measure.addHaar_sphere volume 0 _), smul_zero]

/- English proof (translation)
Establish `hmem : {c : Fin (r + 1) → ℂ | (∀ i, c i ≠ 0) ∧ ‖c (Fin.last r)‖ ^ 2 ≠ T * T'} ∈ ae (dcC (r` using `r)) := by`. Rewrite using `[mem_ae_iff]`. Use `null_set (r := r) T T'` as an intermediate fact. Simplify `this` using `[Set.compl_setOf]`. Use `filter_upwards [hmem] with c hc`.

Take `⟨hc0, hcT⟩` from `hc`. Establish `hP : 0 < ∏ i ∈ Finset.range r, xN c i`. Use `Finset.prod_pos fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_range]`. Unfold `xN`.

Rewrite using `[dif_pos (by omega)]`. Conclude with `norm_pos_iff.2 (hc0 _)`. Establish `hP2 : 0 < (∏ i ∈ Finset.range r, xN c i) ^ 2` using `by positivity`. Establish `hns : Complex.normSq (phiC lam c).2 = ‖c (Fin.last r)‖ ^ 2`. Rewrite using `[Complex.normSq_eq_norm_sq]`.

Both sides reduce to the same expression. Establish `hlamne : (∏ a : Fin r, lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2))) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (hlam a).ne'`. Establish `hkap : kapC k lam * (∏ a : Fin r, lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2))) = 1`. Unfold `kapC`. Rewrite using `[← Finset.prod_mul_distrib]`.

Conclude with `Finset.prod_eq_one fun a _ => inv_mul_cancel₀ (pow_ne_zero _ (hlam a).ne')`. Distinguish the cases in `hg : c ∈ GoodC T T'`. Rewrite using `[Set.indicator_of_mem hg]`. Establish `hG` using `hg.2`. Rewrite `hG` using `[gv_diag]`.

Establish `hpos : 0 < ‖c (Fin.last r)‖ ^ 2 - T * T'` using `pos_of_mul_pos_right hG hP2.le`. Unfold `Formalism.QuantumDeterminants.bcWeight`. Rewrite using `[if_pos (by rw [hns]; linarith), bc_prod k hk lam hlam c, hns, gv_diag, jac_diag]`. Use `congr 1`. Rewrite using `[mul_pow]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Set.indicator_of_notMem hg]`. Establish `hng : ¬ 0 < Gv T T' (Matrix.diagonal c)` using `fun h => hg ⟨hc0, h⟩`. Rewrite `hng` using `[gv_diag]`. Establish `hle : ‖c (Fin.last r)‖ ^ 2 - T * T' ≤ 0`.

Assume the negation of the conclusion as `h`. Conclude with `hng (mul_pos hP2 (lt_of_not_ge h))`. Establish `hlt : ‖c (Fin.last r)‖ ^ 2 < T * T'` using `lt_of_le_of_ne (by linarith) hcT`. Unfold `Formalism.QuantumDeterminants.bcWeight`. Rewrite using `[if_neg (by rw [hns]; linarith)]`.

Simplify using the standard rewrite rules.
-/
theorem ae_weight (k : ℕ) (hk : 1 ≤ k) (T T' : ℝ) (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a)
    (F : (Fin r → ℂ) × ℂ → ℝ) :
    ∀ᵐ c ∂(dcC (r := r)), (GoodC T T').indicator
        (fun c => ENNReal.ofReal (Gv T T' (Matrix.diagonal c) ^ (k - 1) * JacV (Matrix.diagonal c) * F (phiC lam c))) c =
      ENNReal.ofReal (kapC k lam * (Formalism.QuantumDeterminants.bcWeight k r T T' (phiC lam c) * F (phiC lam c))) := by
  have hmem : {c : Fin (r + 1) → ℂ | (∀ i, c i ≠ 0) ∧ ‖c (Fin.last r)‖ ^ 2 ≠ T * T'} ∈ ae (dcC (r := r)) := by
    rw [mem_ae_iff]
    have := null_set (r := r) T T'
    simpa [Set.compl_setOf] using this
  filter_upwards [hmem] with c hc
  obtain ⟨hc0, hcT⟩ := hc
  have hP : 0 < ∏ i ∈ Finset.range r, xN c i := by
    refine Finset.prod_pos fun i hi => ?_
    rw [Finset.mem_range] at hi
    unfold xN
    rw [dif_pos (by omega)]
    exact norm_pos_iff.2 (hc0 _)
  have hP2 : 0 < (∏ i ∈ Finset.range r, xN c i) ^ 2 := by positivity
  have hns : Complex.normSq (phiC lam c).2 = ‖c (Fin.last r)‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]; rfl
  have hlamne : (∏ a : Fin r, lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (hlam a).ne'
  have hkap : kapC k lam * (∏ a : Fin r, lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2))) = 1 := by
    unfold kapC
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => inv_mul_cancel₀ (pow_ne_zero _ (hlam a).ne')
  by_cases hg : c ∈ GoodC T T'
  · rw [Set.indicator_of_mem hg]
    have hG := hg.2
    rw [gv_diag] at hG
    have hpos : 0 < ‖c (Fin.last r)‖ ^ 2 - T * T' := pos_of_mul_pos_right hG hP2.le
    unfold Formalism.QuantumDeterminants.bcWeight
    rw [if_pos (by rw [hns]; linarith), bc_prod k hk lam hlam c, hns, gv_diag, jac_diag]
    congr 1
    rw [mul_pow]
    calc ((∏ i ∈ Finset.range r, xN c i) ^ 2) ^ (k - 1) * (‖c (Fin.last r)‖ ^ 2 - T * T') ^ (k - 1) *
          (∏ i ∈ Finset.range r, (xN c i ^ 4) ^ (r - i)) * F (phiC lam c)
        = (kapC k lam * (∏ a : Fin r, lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)))) *
          (((∏ i ∈ Finset.range r, xN c i) ^ 2) ^ (k - 1) * (‖c (Fin.last r)‖ ^ 2 - T * T') ^ (k - 1) *
          (∏ i ∈ Finset.range r, (xN c i ^ 4) ^ (r - i)) * F (phiC lam c)) := by rw [hkap, one_mul]
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hg]
    have hng : ¬ 0 < Gv T T' (Matrix.diagonal c) := fun h => hg ⟨hc0, h⟩
    rw [gv_diag] at hng
    have hle : ‖c (Fin.last r)‖ ^ 2 - T * T' ≤ 0 := by
      by_contra h
      exact hng (mul_pos hP2 (lt_of_not_ge h))
    have hlt : ‖c (Fin.last r)‖ ^ 2 < T * T' := lt_of_le_of_ne (by linarith) hcT
    unfold Formalism.QuantumDeterminants.bcWeight
    rw [if_neg (by rw [hns]; linarith)]
    simp

end AE

section Map

variable {r : ℕ}

def muS (lam : Fin r → ℝ) (i : Fin (r + 1)) : ℝ := if h : (i : ℕ) < r then lam ⟨i, h⟩ else 1

/- English proof (translation)
Unfold `muS`. Use `split_ifs`. Conclude with `hlam _`. Conclude with `one_pos`.
-/
theorem muS_pos (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) (i : Fin (r + 1)) : 0 < muS lam i := by
  unfold muS
  split_ifs
  · exact hlam _
  · exact one_pos

def e1 (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) : (Fin (r + 1) → ℂ) ≃ᵐ (Fin (r + 1) → ℂ) :=
  MeasurableEquiv.piCongrRight fun i => MeasurableEquiv.smul₀ (muS lam i) (muS_pos lam hlam i).ne'

def e2 : (Fin (r + 1) → ℂ) ≃ᵐ (Fin r → ℂ) × ℂ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℂ) (Fin.last r)).trans MeasurableEquiv.prodComm

def PhiE (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) : (Fin (r + 1) → ℂ) ≃ᵐ (Fin r → ℂ) × ℂ :=
  (e1 lam hlam).trans e2

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Simplify using `only [PhiE, e1, e2, MeasurableEquiv.coe_trans, Function.comp_apply]`. Simplify using the standard rewrite rules. Use `show (muS lam (Fin.castSucc a) • c (Fin.castSucc a) : ℂ) = _`.

Establish `h : muS lam (Fin.castSucc a) = lam a` using `by simp [muS]`. Rewrite using `[h, Complex.real_smul]`. Both sides reduce to the same expression. Simplify using `only [PhiE, e1, e2, MeasurableEquiv.coe_trans, Function.comp_apply]`. Simplify using the standard rewrite rules.

Use `show (muS lam (Fin.last r) • c (Fin.last r) : ℂ) = _`. Establish `h : muS lam (Fin.last r) = 1` using `by simp [muS]`. Rewrite using `[h, one_smul]`. Both sides reduce to the same expression.
-/
theorem phiE_apply (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) (c : Fin (r + 1) → ℂ) :
    PhiE lam hlam c = phiC lam c := by
  refine Prod.ext ?_ ?_
  · funext a
    simp only [PhiE, e1, e2, MeasurableEquiv.coe_trans, Function.comp_apply]
    simp
    show (muS lam (Fin.castSucc a) • c (Fin.castSucc a) : ℂ) = _
    have h : muS lam (Fin.castSucc a) = lam a := by simp [muS]
    rw [h, Complex.real_smul]
    rfl
  · simp only [PhiE, e1, e2, MeasurableEquiv.coe_trans, Function.comp_apply]
    simp
    show (muS lam (Fin.last r) • c (Fin.last r) : ℂ) = _
    have h : muS lam (Fin.last r) = 1 := by simp [muS]
    rw [h, one_smul]
    rfl

def cN (lam : Fin r → ℝ) (i : Fin (r + 1)) : ℝ≥0 := Real.toNNReal (2 * ((muS lam i) ^ 2)⁻¹)

/- English proof (translation)
Use `(Measure.pi_eq fun s hs => ?_).symm` and prove the remaining obligations. Rewrite using `[Measure.map_apply (e1 lam hlam).measurable (MeasurableSet.univ_pi hs)]`. Establish `hpre : (e1 lam hlam) ⁻¹' Set.univ.pi s = Set.univ.pi fun i => (fun z : ℂ => muS lam i • z) ⁻¹' s i`. Use extensionality with `c`. Simplify using `only [Set.mem_preimage, Set.mem_univ_pi]`.

Conclude with `Iff.rfl`. Rewrite using `[hpre, dcC, Measure.pi_pi]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hμ` using `muS_pos lam hlam i`. Rewrite using `[Measure.smul_apply, Measure.smul_apply, ← Measure.map_apply (measurable_const_smul (muS lam i)) (hs i), Measure.map_addHaar_smul volume hμ.ne', Measure.smul_apply, Complex.finrank_real_complex]`.

Rewrite using `[abs_of_nonneg (by positivity)]`. Simplify using `only [smul_eq_mul, cN]`. Rewrite using `[ENNReal.smul_def, smul_eq_mul, ← mul_assoc]`. Use `congr 1`. Rewrite using `[show ((Real.toNNReal (2 * (muS lam i ^ 2)⁻¹) : ℝ≥0∞)) = ENNReal.ofReal (2 * (muS lam i ^ 2)⁻¹) from rfl, ENNReal.ofReal_mul (by norm_num)]`.

Simplify using the standard rewrite rules.
-/
theorem map_scaled_coordinates_pi (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) :
    (dcC (r := r)).map (e1 lam hlam) = Measure.pi fun i => (cN lam i) • (volume : Measure ℂ) := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (e1 lam hlam).measurable (MeasurableSet.univ_pi hs)]
  have hpre : (e1 lam hlam) ⁻¹' Set.univ.pi s = Set.univ.pi fun i => (fun z : ℂ => muS lam i • z) ⁻¹' s i := by
    ext c
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    exact Iff.rfl
  rw [hpre, dcC, Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hμ := muS_pos lam hlam i
  rw [Measure.smul_apply, Measure.smul_apply, ← Measure.map_apply (measurable_const_smul (muS lam i)) (hs i),
    Measure.map_addHaar_smul volume hμ.ne', Measure.smul_apply, Complex.finrank_real_complex]
  rw [abs_of_nonneg (by positivity)]
  simp only [smul_eq_mul, cN]
  rw [ENNReal.smul_def, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [show ((Real.toNNReal (2 * (muS lam i ^ 2)⁻¹) : ℝ≥0∞)) = ENNReal.ofReal (2 * (muS lam i ^ 2)⁻¹) from rfl,
    ENNReal.ofReal_mul (by norm_num)]
  simp

/- English proof (translation)
Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`.
-/
theorem pi_smul_const (c : Fin (r + 1) → ℝ≥0) :
    Measure.pi (fun i => c i • (volume : Measure ℂ)) =
      (∏ i, (c i : ℝ≥0∞)) • Measure.pi (fun _ : Fin (r + 1) => (volume : Measure ℂ)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

/- English proof (translation)
Establish `h1` using `measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => (volume : Measure ℂ)) (Fin.last r)`. Establish `h2` using `Measure.measurePreserving_swap (μ := (volume : Measure ℂ)) (ν := Measure.pi fun _ : Fin r => (volume : Measure ℂ))`. Conclude with `(h2.comp h1).map_eq`.
-/
theorem map_coordinate_change_volume : (Measure.pi fun _ : Fin (r + 1) => (volume : Measure ℂ)).map (e2 (r := r)) = volume := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => (volume : Measure ℂ)) (Fin.last r)
  have h2 := Measure.measurePreserving_swap (μ := (volume : Measure ℂ))
    (ν := Measure.pi fun _ : Fin r => (volume : Measure ℂ))
  exact (h2.comp h1).map_eq

/- English proof (translation)
Rewrite using `[PhiE, MeasurableEquiv.coe_trans, ← Measure.map_map (e2 (r := r)).measurable (e1 lam hlam).measurable, map_scaled_coordinates_pi, pi_smul_const, Measure.map_smul, map_coordinate_change_volume]`.
-/
theorem map_phiE (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) :
    (dcC (r := r)).map (PhiE lam hlam) = (∏ i, (cN lam i : ℝ≥0∞)) • (volume : Measure ((Fin r → ℂ) × ℂ)) := by
  rw [PhiE, MeasurableEquiv.coe_trans, ← Measure.map_map (e2 (r := r)).measurable (e1 lam hlam).measurable, map_scaled_coordinates_pi,
    pi_smul_const, Measure.map_smul, map_coordinate_change_volume]

/- English proof (translation)
Rewrite using `[Fin.prod_univ_castSucc]`. Establish `hc : ∀ a : Fin r, muS lam (Fin.castSucc a) = lam a` using `fun a => by simp [muS]`. Establish `hl : muS lam (Fin.last r) = 1` using `by simp [muS]`. Simplify using `only [hc, hl, one_pow, inv_one, mul_one]`. Unfold `kapC`.

Establish `hM : ∀ a : Fin r, (lam a ^ 2)⁻¹ * (lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)))⁻¹ = (lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹` using `fun a => by`. Rewrite using `[← mul_inv, ← pow_add]`. Use `congr 2`. Unfold `Formalism.QuantumDeterminants.Mdim`. Use `a.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← Finset.prod_congr rfl (fun a _ => hM a), Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem const_eq (k : ℕ) (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a) :
    (∏ i : Fin (r + 1), 2 * ((muS lam i) ^ 2)⁻¹) * kapC k lam =
      2 ^ (r + 1) * ∏ a : Fin r, (lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹ := by
  rw [Fin.prod_univ_castSucc]
  have hc : ∀ a : Fin r, muS lam (Fin.castSucc a) = lam a := fun a => by simp [muS]
  have hl : muS lam (Fin.last r) = 1 := by simp [muS]
  simp only [hc, hl, one_pow, inv_one, mul_one]
  unfold kapC
  have hM : ∀ a : Fin r, (lam a ^ 2)⁻¹ * (lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)))⁻¹ =
      (lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹ := fun a => by
    rw [← mul_inv, ← pow_add]
    congr 2
    unfold Formalism.QuantumDeterminants.Mdim
    have := a.2
    omega
  rw [← Finset.prod_congr rfl (fun a _ => hM a), Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_succ]
  ring

/- English proof (translation)
Establish `h1 : MeasurableSet {cv : Fin (r + 1) → ℂ | ∀ l, cv l ≠ 0}`. Establish `: {cv : Fin (r + 1) → ℂ | ∀ l, cv l ≠ 0} = ⋂ l, {cv | cv l ≠ 0}` using `by ext; simp`. Rewrite using `[this]`. Conclude with `MeasurableSet.iInter fun l => (measurableSet_singleton (0 : ℂ)).compl.preimage (measurable_pi_apply l)`. Establish `hc : Continuous (fun cv : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal cv))`.

Establish `hd : Continuous (fun cv : Fin (r + 1) → ℂ => Matrix.diagonal cv)` using `continuous_id.matrix_diagonal`. Establish `hD : ∀ l, Continuous (fun cv : Fin (r + 1) → ℂ => Formalism.L2.SG.RealObj.Dl (Matrix.diagonal cv) l)` using `fun l => (Formalism.L2.SG.RealObj.InfCut.dl_cont l).comp hd`. Unfold `Gv`. Conclude with `((hD _).norm.pow 2).sub (continuous_const.mul ((hD _).norm.pow 2))`. Conclude with `h1.inter (measurableSet_lt measurable_const hc.measurable)`.
-/
theorem goodC_meas (T T' : ℝ) : MeasurableSet (GoodC (r := r) T T') := by
  have h1 : MeasurableSet {cv : Fin (r + 1) → ℂ | ∀ l, cv l ≠ 0} := by
    have : {cv : Fin (r + 1) → ℂ | ∀ l, cv l ≠ 0} = ⋂ l, {cv | cv l ≠ 0} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun l => (measurableSet_singleton (0 : ℂ)).compl.preimage (measurable_pi_apply l)
  have hc : Continuous (fun cv : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal cv)) := by
    have hd : Continuous (fun cv : Fin (r + 1) → ℂ => Matrix.diagonal cv) := continuous_id.matrix_diagonal
    have hD : ∀ l, Continuous (fun cv : Fin (r + 1) → ℂ => Formalism.L2.SG.RealObj.Dl (Matrix.diagonal cv) l) :=
      fun l => (Formalism.L2.SG.RealObj.InfCut.dl_cont l).comp hd
    unfold Gv
    exact ((hD _).norm.pow 2).sub (continuous_const.mul ((hD _).norm.pow 2))
  exact h1.inter (measurableSet_lt measurable_const hc.measurable)

end Map

/- English proof (translation)
Rewrite using `[← lintegral_indicator (goodC_meas T T'), lintegral_congr_ae (ae_weight k hk T T' lam hlam F)]`. Establish `hfun : (fun c => ENNReal.ofReal (kapC k lam * (Formalism.QuantumDeterminants.bcWeight k r T T' (phiC lam c) * F (phiC lam c)))) = fun c => (fun q => ENNReal.ofReal (kapC k lam * (Formalism.QuantumDeterminants.bcWeight k r T T' q * F q))) (PhiE lam hlam c)`. Use function extensionality and compare the values at `c`. Rewrite using `[phiE_apply]`. Rewrite using `[hfun, ← lintegral_map_equiv (fun q => ENNReal.ofReal (kapC k lam * (Formalism.QuantumDeterminants.bcWeight k r T T' q * F q))) (PhiE lam hlam), map_phiE, lintegral_smul_measure]`.

Repeatedly rewrite using `[ENNReal.ofReal_mul (kapC_nonneg k lam hlam)]`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul, ← mul_assoc]`. Use `congr 1`. Rewrite using `[show (∏ i, (cN lam i : ℝ≥0∞)) = ENNReal.ofReal (∏ i, 2 * ((muS lam i) ^ 2)⁻¹) from by`. Rewrite using `[ENNReal.ofReal_prod_of_nonneg (fun i _ => by have := muS_pos lam hlam i; positivity)]; rfl,`.

Use the proof step `← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => by have := muS_pos lam hlam i; positivity),`. Use `const_eq k lam hlam]`.
-/
theorem cv_core {r : ℕ} (k : ℕ) (hk : 1 ≤ k) (T T' : ℝ) (lam : Fin r → ℝ) (hlam : ∀ a, 0 < lam a)
    (F : (Fin r → ℂ) × ℂ → ℝ) :
    ∫⁻ c in GoodC (r := r) T T',
        ENNReal.ofReal (Gv T T' (Matrix.diagonal c) ^ (k - 1) * JacV (Matrix.diagonal c) * F (phiC lam c))
        ∂(dcC (r := r)) =
      ENNReal.ofReal (2 ^ (r + 1) * ∏ a : Fin r, (lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹) *
        ∫⁻ q, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q * F q) := by
  rw [← lintegral_indicator (goodC_meas T T'), lintegral_congr_ae (ae_weight k hk T T' lam hlam F)]
  have hfun : (fun c => ENNReal.ofReal (kapC k lam * (Formalism.QuantumDeterminants.bcWeight k r T T' (phiC lam c) * F (phiC lam c)))) =
      fun c => (fun q => ENNReal.ofReal (kapC k lam * (Formalism.QuantumDeterminants.bcWeight k r T T' q * F q))) (PhiE lam hlam c) := by
    funext c
    rw [phiE_apply]
  rw [hfun, ← lintegral_map_equiv (fun q => ENNReal.ofReal (kapC k lam * (Formalism.QuantumDeterminants.bcWeight k r T T' q * F q)))
    (PhiE lam hlam), map_phiE, lintegral_smul_measure]
  simp_rw [ENNReal.ofReal_mul (kapC_nonneg k lam hlam)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [show (∏ i, (cN lam i : ℝ≥0∞)) = ENNReal.ofReal (∏ i, 2 * ((muS lam i) ^ 2)⁻¹) from by
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => by have := muS_pos lam hlam i; positivity)]; rfl,
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => by have := muS_pos lam hlam i; positivity),
    const_eq k lam hlam]

/- English proof (translation)
Substitute `hm` using the available equality. Establish `hk1 : 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `h` using `cv_core D.R.k hk1 (Tw (D := D) u) (Tw (D := D) u') lam hlam F`. Conclude with `h`.
-/
theorem cv_inst {D : D7} (u u' : D.what₂.Word) (m : ℕ) (hm : m = D.R.rS) (lam : Fin m → ℝ) (hlam : ∀ a, 0 < lam a)
    (F : (Fin m → ℂ) × ℂ → ℝ) :
    ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv *
        F ((fun a => ((lam a : ℝ) : ℂ) * cv ⟨a.val, by have := a.2; omega⟩, cv ⟨D.R.rS, by omega⟩))) ∂(dcV (D := D)) =
      ENNReal.ofReal (2 ^ (m + 1) * ∏ a : Fin m, (lam a ^ (2 * (Formalism.QuantumDeterminants.Mdim D.R.k m a - 1)))⁻¹) *
        ∫⁻ q, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight D.R.k m (Tw (D := D) u) (Tw (D := D) u') q * F q) := by
  subst hm
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have h := cv_core D.R.k hk1 (Tw (D := D) u) (Tw (D := D) u') lam hlam F
  exact h

/- English proof (translation)
Introduce `hk hT v F _`. Establish `hg' : (0 : ℝ) < P.S.g` using `by exact_mod_cast hg`. Establish `hlam : ∀ a, 0 < lamA P a` using `fun a => by unfold lamA; positivity`. Rewrite using `[(hT v).1, (hT v).2]`. Unfold `K0`.

Rewrite using `[hk]`. Conclude with `cv_inst u u' P.S.G.r hr (lamA P) hlam F`.
-/
theorem changeVar_of_pos {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word} (P : Parts X u u')
    (hr : P.S.G.r = D.R.rS) (hg : 0 < P.S.g) : ChangeVar P hr := by
  intro hk hT v F _
  have hg' : (0 : ℝ) < P.S.g := by exact_mod_cast hg
  have hlam : ∀ a, 0 < lamA P a := fun a => by unfold lamA; positivity
  rw [(hT v).1, (hT v).2]
  unfold K0
  rw [hk]
  exact cv_inst u u' P.S.G.r hr (lamA P) hlam F

end Formalism.L2.SG.Pf.Carrier.EnergyCV
