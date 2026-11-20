import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
open GlobalTheory GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.StabD

variable {K : Type} [Field K]

/- English proof (translation)
Rewrite using `[dlog, smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ u.ne_zero, one_smul]`.
-/
theorem dK_unit (u : Kˣ) : dK (u : K) = (u : K) • dlog u := by
  rw [dlog, smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ u.ne_zero, one_smul]

/- English proof (translation)
Simplify using `only [dlog, Units.val_inv_eq_inv_val, Units.val_mul, dK, Derivation.leibniz, smul_add, smul_smul]`. Rewrite using `[add_comm]`. Use `congr 1`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem dlog_mul (u w : Kˣ) : dlog (u * w) = dlog u + dlog w := by
  simp only [dlog, Units.val_inv_eq_inv_val, Units.val_mul, dK, Derivation.leibniz, smul_add, smul_smul]
  rw [add_comm]
  congr 1
  · congr 1; field_simp
  · congr 1; field_simp

/- English proof (translation)
Simplify using `[dlog]`.
-/
theorem dlog_one : dlog (1 : Kˣ) = 0 := by simp [dlog]

/- English proof (translation)
Establish `h` using `dlog_mul u⁻¹ u`. Rewrite `h` using `[inv_mul_cancel, dlog_one]`. Conclude with `eq_neg_of_add_eq_zero_left h.symm`.
-/
theorem dlog_inv (u : Kˣ) : dlog u⁻¹ = -dlog u := by
  have h := dlog_mul u⁻¹ u
  rw [inv_mul_cancel, dlog_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [dlog_one]`. Consider the case `succ m ih => rw [pow_succ, dlog_mul, ih, Nat.cast_succ, add_smul, one_smul]`.
-/
theorem dlog_pow (u : Kˣ) (m : ℕ) : dlog (u ^ m) = (m : K) • dlog u := by
  induction m with
  | zero => simp [dlog_one]
  | succ m ih => rw [pow_succ, dlog_mul, ih, Nat.cast_succ, add_smul, one_smul]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [dlog_one]`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, dlog_mul, ih]`.
-/
theorem dlog_prod {ι : Type} (s : Finset ι) (f : ι → Kˣ) : dlog (∏ i ∈ s, f i) = ∑ i ∈ s, dlog (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dlog_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, dlog_mul, ih]

/- English proof (translation)
Establish `hD : dK ((u⁻¹ : Kˣ) : K) = -(((u⁻¹ : Kˣ) : K) * ((u⁻¹ : Kˣ) : K)) • dK (u : K)`. Rewrite using `[dK_unit, dlog_inv, dlog, smul_neg, smul_smul, neg_smul]`. Rewrite using `[dlog, map_smul, CechDR.dDR_smul, CechDR.dDR_D, smul_zero, add_zero]`. Express the relevant statement in the definitionally equal form `CechDR.ι1 (dK ((u⁻¹ : Kˣ) : K)) * CechDR.ι1 (dK (u : K)) = 0`. Rewrite using `[hD, map_smul, smul_mul_assoc, ExteriorAlgebra.ι_sq_zero, smul_zero]`.
-/
theorem dDR_dlog (u : Kˣ) : CechDR.dDR ℤ K (CechDR.ι1 (dlog u)) = 0 := by
  have hD : dK ((u⁻¹ : Kˣ) : K) = -(((u⁻¹ : Kˣ) : K) * ((u⁻¹ : Kˣ) : K)) • dK (u : K) := by
    rw [dK_unit, dlog_inv, dlog, smul_neg, smul_smul, neg_smul]
  rw [dlog, map_smul, CechDR.dDR_smul, CechDR.dDR_D, smul_zero, add_zero]
  change CechDR.ι1 (dK ((u⁻¹ : Kˣ) : K)) * CechDR.ι1 (dK (u : K)) = 0
  rw [hD, map_smul, smul_mul_assoc, ExteriorAlgebra.ι_sq_zero, smul_zero]

/- English proof (translation)
Unfold `frame`. Use `split_ifs`. Conclude with `dDR_dlog _`. Conclude with `CechDR.dDR_D _`.
-/
theorem dDR_frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) :
    CechDR.dDR ℤ K (CechDR.ι1 (frame x J i)) = 0 := by
  unfold frame
  split_ifs
  · exact dDR_dlog _
  · exact CechDR.dDR_D _

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero`. Rewrite using `[ExteriorAlgebra.ιMulti_zero_apply, ← map_one (algebraMap K (abelian₂ K)), CechDR.dDR_algebraMap]`. Simplify using the standard rewrite rules. Consider the case `succ q ih`.

Rewrite using `[ExteriorAlgebra.ιMulti_succ_apply, CechDR.dDR_mul]`. Express the relevant statement in the definitionally equal form `_ * CechDR.dDR ℤ K _ + CechDR.dDR ℤ K (CechDR.ι1 (v 0)) * _ = 0`. Rewrite using `[ih (Matrix.vecTail v) (fun i => hv _), hv 0, mul_zero, zero_mul, add_zero]`.
-/
theorem dDR_ιMulti (q : ℕ) (v : Fin q → Ω[K⁄ℤ]) (hv : ∀ i, CechDR.dDR ℤ K (CechDR.ι1 (v i)) = 0) :
    CechDR.dDR ℤ K (ExteriorAlgebra.ιMulti K q v) = 0 := by
  induction q with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, ← map_one (algebraMap K (abelian₂ K)), CechDR.dDR_algebraMap]
    simp
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, CechDR.dDR_mul]
    change _ * CechDR.dDR ℤ K _ + CechDR.dDR ℤ K (CechDR.ι1 (v 0)) * _ = 0
    rw [ih (Matrix.vecTail v) (fun i => hv _), hv 0, mul_zero, zero_mul, add_zero]

/- English proof (translation)
Use `set a := c * (T : K) with ha`. Take `⟨cc, hcc, hDa⟩` from `hx.deriv a hc`. Set `e : Fin n → K` to `fun i => if i ∈ J then cc i * (x i : K) - a * (r i : K) else cc i`. Establish `he : ∀ i, e i ∈ A`. Introduce `i`.

Simplify using `only [e]`. Use `split_ifs`. Conclude with `sub_mem (mul_mem (hcc i) (hx.mem i)) (mul_mem hc (natCast_mem A _))`. Conclude with `hcc i`. Establish `hT0 : (T : K) ≠ 0` using `T.ne_zero`.

Use `⟨fun i => (T : K)⁻¹ * e i, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm, ← mul_assoc, mul_inv_cancel₀ hT0, one_mul]`. Conclude with `he i`. Establish `hsum : ∑ i, e i • frame x J i = dK a - a • ∑ j ∈ J, (r j : K) • dlog (x j)`. Establish `hpt : ∀ i, e i • frame x J i = cc i • dK (x i : K) - (if i ∈ J then (a * (r i : K)) • dlog (x i) else 0)`.

Introduce `i`. Simplify using `only [e, frame]`. Use `split_ifs`. Rewrite using `[sub_smul, mul_smul, ← dK_unit]`. Rewrite using `[sub_zero]`.

Rewrite using `[Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib, ← hDa, Finset.sum_ite_mem, Finset.univ_inter, Finset.smul_sum]`. Simplify using `only [smul_smul]`. Establish `hlead : dK a = c • dK (T : K) + (T : K) • dK c` using `Derivation.leibniz _ _ _`. Establish `hTc : (T : K) • dK c = dK a - a • dlog T`. Rewrite using `[hlead, dK_unit, smul_smul, ← ha]`.

Normalize the expressions using the abelian group laws. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hTc, hT, ← hsum, Finset.smul_sum]`. Simplify using `only [smul_smul]`.
-/
theorem dK_mem_frame (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (T : Kˣ) (r : Fin n → ℕ)
    (hx : AlgChart A x) (hT : dlog T = ∑ j ∈ J, (r j : K) • dlog (x j)) (c : K) (hc : c * (T : K) ∈ A) :
    ∃ d : Fin n → K, (∀ i, d i * (T : K) ∈ A) ∧ dK c = ∑ i, d i • frame x J i := by
  classical
  set a := c * (T : K) with ha
  obtain ⟨cc, hcc, hDa⟩ := hx.deriv a hc
  let e : Fin n → K := fun i => if i ∈ J then cc i * (x i : K) - a * (r i : K) else cc i
  have he : ∀ i, e i ∈ A := by
    intro i
    simp only [e]
    split_ifs
    · exact sub_mem (mul_mem (hcc i) (hx.mem i)) (mul_mem hc (natCast_mem A _))
    · exact hcc i
  have hT0 : (T : K) ≠ 0 := T.ne_zero
  refine ⟨fun i => (T : K)⁻¹ * e i, fun i => ?_, ?_⟩
  · rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hT0, one_mul]; exact he i
  have hsum : ∑ i, e i • frame x J i = dK a - a • ∑ j ∈ J, (r j : K) • dlog (x j) := by
    have hpt : ∀ i, e i • frame x J i =
        cc i • dK (x i : K) - (if i ∈ J then (a * (r i : K)) • dlog (x i) else 0) := by
      intro i
      simp only [e, frame]
      split_ifs
      · rw [sub_smul, mul_smul, ← dK_unit]
      · rw [sub_zero]
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib, ← hDa, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.smul_sum]
    simp only [smul_smul]
  have hlead : dK a = c • dK (T : K) + (T : K) • dK c := Derivation.leibniz _ _ _
  have hTc : (T : K) • dK c = dK a - a • dlog T := by
    rw [hlead, dK_unit, smul_smul, ← ha]; abel
  calc dK c = (T : K)⁻¹ • ((T : K) • dK c) := by rw [smul_smul, inv_mul_cancel₀ hT0, one_smul]
    _ = _ := by
      rw [hTc, hT, ← hsum, Finset.smul_sum]
      simp only [smul_smul]

/- English proof (translation)
Rewrite using `[dlog_mul, dlog_pow, CharP.cast_eq_zero, zero_smul, zero_add, dlog_prod]`. Simplify using `only [dlog_pow]`.
-/
theorem dlog_twist (p : ℕ) [CharP K p] {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ)
    (r : Fin n → ℕ) : dlog (t ^ p * ∏ j ∈ J, x j ^ r j) = ∑ j ∈ J, (r j : K) • dlog (x j) := by
  rw [dlog_mul, dlog_pow, CharP.cast_eq_zero, zero_smul, zero_add, dlog_prod]
  simp only [dlog_pow]

end GlobalTheory.LogDR.StabD

open GlobalTheory.LogDR.StabD in

/- English proof (translation)
Introduce `K _ p _ _ A n x J t r hx q η hη`. Unfold `chartForms spanForms at hη ⊢`. Proceed by induction on `hη using AddSubgroup.closure_induction with`. Consider the case `mem η hη`. Take `⟨c, hc, v, hv, rfl⟩` from `hη`.

Take `⟨d, hd, hDc⟩` from `dK_mem_frame A x J _ r hx (dlog_twist p x J t r) c hc`. Rewrite using `[extD_apply, CechDR.dDR_smul, dDR_ιMulti q v (fun i => by`. Take `⟨k, hk⟩` from `hv i`. Rewrite using `[← hk]`. Conclude with `dDR_frame x J k), smul_zero, add_zero]`.

Express the relevant statement in the definitionally equal form `CechDR.ι1 (dK c) * _ ∈ _`. Rewrite using `[hDc, map_sum, Finset.sum_mul]`. Use `sum_mem fun i _ => AddSubgroup.subset_closure ?_` and prove the remaining obligations. Use `⟨d i, hd i, Fin.cons (frame x J i) v, fun k => ?_, ?_⟩` and prove the remaining obligations. Use `Fin.cases ?_ (fun k => ?_) k` and prove the remaining obligations.

Conclude with `⟨i, rfl⟩`. Rewrite using `[Fin.cons_succ]`. Conclude with `hv k`. Rewrite using `[ExteriorAlgebra.ιMulti_succ_apply, map_smul, smul_mul_assoc]`. Both sides reduce to the same expression.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => rw [map_neg]`.

Conclude with `neg_mem ha`.
-/
theorem GlobalTheory.LogDR.extD_mem_chartForms_twist : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ), AlgChart A x → ∀ q, ∀ η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) q, extD K η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) (q + 1) := by
  intro K _ p _ _ A n x J t r hx q η hη
  unfold chartForms spanForms at hη ⊢
  induction hη using AddSubgroup.closure_induction with
  | mem η hη =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hη
    obtain ⟨d, hd, hDc⟩ := dK_mem_frame A x J _ r hx (dlog_twist p x J t r) c hc
    rw [extD_apply, CechDR.dDR_smul, dDR_ιMulti q v (fun i => by
      obtain ⟨k, hk⟩ := hv i; rw [← hk]; exact dDR_frame x J k), smul_zero, add_zero]
    change CechDR.ι1 (dK c) * _ ∈ _
    rw [hDc, map_sum, Finset.sum_mul]
    refine sum_mem fun i _ => AddSubgroup.subset_closure ?_
    refine ⟨d i, hd i, Fin.cons (frame x J i) v, fun k => ?_, ?_⟩
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact ⟨i, rfl⟩
      · rw [Fin.cons_succ]; exact hv k
    · rw [ExteriorAlgebra.ιMulti_succ_apply, map_smul, smul_mul_assoc]
      rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
