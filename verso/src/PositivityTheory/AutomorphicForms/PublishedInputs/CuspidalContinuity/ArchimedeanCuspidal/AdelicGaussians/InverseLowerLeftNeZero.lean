import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.HeisenbergLowerCommuteMiddle

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.GA.CtvP

open Ad3.GA.unipotentTranslateContinuity

local notation "𝔞" => algebraMap ℚ 𝔸[ℚ]

/- English proof (translation)
Establish `e : D * (L * X * g) = uni a b z * (D * (X * g))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e, hV.psi W hW]`.
-/
theorem W_shift {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) {W : G3 → ℂ} (hW : W ∈ V) {D L X : G3}
    {a b z : 𝔸[ℚ]} (hDL : D * L = uni a b z * D) (g : G3) :
    W (D * (L * X * g)) = (adelicChar ℚ (a + z) : ℂ) * W (D * (X * g)) := by
  have e : D * (L * X * g) = uni a b z * (D * (X * g)) := by
    calc D * (L * X * g) = D * L * (X * g) := by simp only [mul_assoc]
      _ = uni a b z * D * (X * g) := by rw [hDL]
      _ = uni a b z * (D * (X * g)) := mul_assoc _ _ _
  rw [e, hV.psi W hW]

/- English proof (translation)
Establish `hK : IsCompact ((fun y => h y * g) '' closure (vecDomain ℚ ι))` using `(FourierWhittaker.isCompact_closure_vecDomain (K := ℚ) (ι := ι)).image (hh.mul continuous_const)`. Take `⟨b, hb, hle⟩` from `hM V hV W hW _ hK`. Establish `e : ∀ y, vS W (h y * g) * χ y = ∑' q : NQ, W (dia (e2 q.out * sw) * (h y * g)) * χ y` using `fun y => by rw [vS, tsum_mul_right]`. Repeatedly rewrite using `[e]`. Conclude with `setIntegral_tsum_of_le _ (fun q => ((hC V hV W hW).comp (continuous_const.mul (hh.mul continuous_const))).mul hχ) b hb fun q y hy => by`.

Rewrite using `[norm_mul, hχ1, mul_one]`. Conclude with `hle q _ ⟨y, subset_closure hy, rfl⟩`.
-/
theorem setIntegral_vS {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) (hC : ContW) (hM : MajV)
    {W : G3 → ℂ} (hW : W ∈ V) {ι : Type} [Fintype ι] {h : (ι → 𝔸[ℚ]) → G3} (hh : Continuous h)
    {χ : (ι → 𝔸[ℚ]) → ℂ} (hχ : Continuous χ) (hχ1 : ∀ y, ‖χ y‖ = 1) (g : G3) :
    ∫ y in vecDomain ℚ ι, vS W (h y * g) * χ y ∂vecMeasure ℚ ι =
      ∑' q : NQ, ∫ y in vecDomain ℚ ι, W (dia (e2 q.out * sw) * (h y * g)) * χ y ∂vecMeasure ℚ ι := by
  have hK : IsCompact ((fun y => h y * g) '' closure (vecDomain ℚ ι)) :=
    (FourierWhittaker.isCompact_closure_vecDomain (K := ℚ) (ι := ι)).image (hh.mul continuous_const)
  obtain ⟨b, hb, hle⟩ := hM V hV W hW _ hK
  have e : ∀ y, vS W (h y * g) * χ y = ∑' q : NQ, W (dia (e2 q.out * sw) * (h y * g)) * χ y :=
    fun y => by rw [vS, tsum_mul_right]
  simp_rw [e]
  exact setIntegral_tsum_of_le _ (fun q => ((hC V hV W hW).comp (continuous_const.mul
    (hh.mul continuous_const))).mul hχ) b hb fun q y hy => by
      rw [norm_mul, hχ1, mul_one]; exact hle q _ ⟨y, subset_closure hy, rfl⟩

/- English proof (translation)
Establish `hK : IsCompact ((fun y => h y * g) '' closure (vecDomain ℚ ι))` using `(FourierWhittaker.isCompact_closure_vecDomain (K := ℚ) (ι := ι)).image (hh.mul continuous_const)`. Take `⟨b, hb, hle⟩` from `hM V hV W hW _ hK`. Establish `e : ∀ y, uS W (h y * g) * χ y = ∑' q : NQ, W (dia (e1 q.out) * (h y * g)) * χ y` using `fun y => by rw [uS, tsum_mul_right]`. Repeatedly rewrite using `[e]`. Conclude with `setIntegral_tsum_of_le _ (fun q => ((hC V hV W hW).comp (continuous_const.mul (hh.mul continuous_const))).mul hχ) b hb fun q y hy => by`.

Rewrite using `[norm_mul, hχ1, mul_one]`. Conclude with `hle q _ ⟨y, subset_closure hy, rfl⟩`.
-/
theorem setIntegral_uS {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) (hC : ContW) (hM : MajU)
    {W : G3 → ℂ} (hW : W ∈ V) {ι : Type} [Fintype ι] {h : (ι → 𝔸[ℚ]) → G3} (hh : Continuous h)
    {χ : (ι → 𝔸[ℚ]) → ℂ} (hχ : Continuous χ) (hχ1 : ∀ y, ‖χ y‖ = 1) (g : G3) :
    ∫ y in vecDomain ℚ ι, uS W (h y * g) * χ y ∂vecMeasure ℚ ι =
      ∑' q : NQ, ∫ y in vecDomain ℚ ι, W (dia (e1 q.out) * (h y * g)) * χ y ∂vecMeasure ℚ ι := by
  have hK : IsCompact ((fun y => h y * g) '' closure (vecDomain ℚ ι)) :=
    (FourierWhittaker.isCompact_closure_vecDomain (K := ℚ) (ι := ι)).image (hh.mul continuous_const)
  obtain ⟨b, hb, hle⟩ := hM V hV W hW _ hK
  have e : ∀ y, uS W (h y * g) * χ y = ∑' q : NQ, W (dia (e1 q.out) * (h y * g)) * χ y :=
    fun y => by rw [uS, tsum_mul_right]
  simp_rw [e]
  exact setIntegral_tsum_of_le _ (fun q => ((hC V hV W hW).comp (continuous_const.mul
    (hh.mul continuous_const))).mul hχ) b hb fun q y hy => by
      rw [norm_mul, hχ1, mul_one]; exact hle q _ ⟨y, subset_closure hy, rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_nx (v : Multiplicative ℚ) :
    ((nx v : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, v.toAdd; 0, 1] := rfl

/- English proof (translation)
Rewrite `h` using `[nU, MonoidHom.mem_range]`. Take `⟨v, hv⟩` from `h`. Establish `hb : b = nx v * a` using `by rw [hv, inv_mul_cancel_right]`. Use `⟨v.toAdd, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hb, Units.val_mul, val_nx]`.

Apply the tactic sequence `fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem rel_entries {a b : GL (Fin 2) ℚ} (h : b * a⁻¹ ∈ nU) :
    ∃ u : ℚ, ∀ j, b.val 0 j = a.val 0 j + u * a.val 1 j ∧ b.val 1 j = a.val 1 j := by
  rw [nU, MonoidHom.mem_range] at h
  obtain ⟨v, hv⟩ := h
  have hb : b = nx v * a := by rw [hv, inv_mul_cancel_right]
  refine ⟨v.toAdd, fun j => ?_⟩
  rw [hb, Units.val_mul, val_nx]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Use `Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)` and prove the remaining obligations. Rewrite using `[nU, MonoidHom.mem_range]`. Use `⟨Multiplicative.ofAdd u, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_mul_inv_iff_mul_eq]`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_mul, val_nx]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two, (h j).1, (h j).2]`.
-/
theorem mk_eq_of_entries {a b : GL (Fin 2) ℚ} (u : ℚ)
    (h : ∀ j, b.val 0 j = a.val 0 j + u * a.val 1 j ∧ b.val 1 j = a.val 1 j) :
    (Quotient.mk _ a : NQ) = Quotient.mk _ b := by
  refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
  rw [nU, MonoidHom.mem_range]
  refine ⟨Multiplicative.ofAdd u, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, val_nx]
  ext i j
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two, (h j).1, (h j).2]

/- English proof (translation)
The claim follows from `QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk _ γ : NQ)))`.
-/
theorem out_rel (γ : GL (Fin 2) ℚ) : γ * ((Quotient.mk _ γ : NQ).out)⁻¹ ∈ nU :=
  QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk _ γ : NQ)))

/- English proof (translation)
The claim follows from `(Quotient.out_eq q).symm`.
-/
theorem out_eq_mk (q : NQ) : q = Quotient.mk _ q.out := (Quotient.out_eq q).symm

/- English proof (translation)
Use `congrArg (fun X : Matrix (Fin 2) (Fin 2) ℚ => X i j) (Units.inv_mul γ)` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]`.
-/
theorem inv_rel_q (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (γ⁻¹).val i 0 * γ.val 0 j + (γ⁻¹).val i 1 * γ.val 1 j = if i = j then 1 else 0 := by
  have := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℚ => X i j) (Units.inv_mul γ)
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this

/- English proof (translation)
Use `congrArg (fun X : Matrix (Fin 2) (Fin 2) ℚ => X i j) (Units.mul_inv γ)` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]`.
-/
theorem mul_inv_rel_q (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    γ.val i 0 * (γ⁻¹).val 0 j + γ.val i 1 * (γ⁻¹).val 1 j = if i = j then 1 else 0 := by
  have := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℚ => X i j) (Units.mul_inv γ)
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this

/- English proof (translation)
Introduce `hN`. Establish `r10` using `inv_rel_q γ 1 0`. Establish `r11` using `inv_rel_q γ 1 1`. Rewrite `r10`, `r11` using `[hN, zero_mul, zero_add]`. Simplify using `only [Fin.isValue, one_ne_zero, if_false, if_true, mul_eq_zero] at r10 r11`.

Break down `r10 with h | h` into its components or cases. Rewrite `r11` using `[h, zero_mul]`. Conclude with `zero_ne_one r11`. Conclude with `h10 h`.
-/
theorem inverse_lower_left_ne_zero (γ : GL (Fin 2) ℚ) (h10 : γ.val 1 0 ≠ 0) : (γ⁻¹).val 1 0 ≠ 0 := by
  intro hN
  have r10 := inv_rel_q γ 1 0
  have r11 := inv_rel_q γ 1 1
  rw [hN, zero_mul, zero_add] at r10 r11
  simp only [Fin.isValue, one_ne_zero, if_false, if_true, mul_eq_zero] at r10 r11
  rcases r10 with h | h
  · rw [h, zero_mul] at r11; exact zero_ne_one r11
  · exact h10 h

/- English proof (translation)
Establish `hd` using `det_ne_zero2 γ`. Rewrite `hd` using `[h10, mul_zero, sub_zero]`. Conclude with `mul_ne_zero_iff.1 hd`.
-/
theorem diag_ne_zero (γ : GL (Fin 2) ℚ) (h10 : γ.val 1 0 = 0) :
    γ.val 0 0 ≠ 0 ∧ γ.val 1 1 ≠ 0 := by
  have hd := det_ne_zero2 γ
  rw [h10, mul_zero, sub_zero] at hd
  exact mul_ne_zero_iff.1 hd

/- English proof (translation)
Establish `r10` using `inv_rel_q γ 1 0`. Establish `r00` using `inv_rel_q γ 0 0`. Rewrite `r10`, `r00` using `[h10, mul_zero, add_zero]`. Simplify using `only [Fin.isValue, one_ne_zero, if_false, if_true, mul_eq_zero] at r10 r00`. Conclude with `⟨r10.resolve_right (diag_ne_zero γ h10).1, r00⟩`.
-/
theorem inv_upper (γ : GL (Fin 2) ℚ) (h10 : γ.val 1 0 = 0) :
    (γ⁻¹).val 1 0 = 0 ∧ (γ⁻¹).val 0 0 * γ.val 0 0 = 1 := by
  have r10 := inv_rel_q γ 1 0
  have r00 := inv_rel_q γ 0 0
  rw [h10, mul_zero, add_zero] at r10 r00
  simp only [Fin.isValue, one_ne_zero, if_false, if_true, mul_eq_zero] at r10 r00
  exact ⟨r10.resolve_right (diag_ne_zero γ h10).1, r00⟩

/- English proof (translation)
Establish `hc : Continuous fun y : Fin 2 → 𝔸[ℚ] => W (dia (e2 γ * sw) * (uni 0 (y 0) (y 1) * g))` using `(hC V hV W hW).comp (continuous_const.mul ((continuous_uni continuous_const (continuous_apply 0) (continuous_apply 1)).mul continuous_const))`. Distinguish the cases in `h10 : γ.val 1 0 = 0`. Take `⟨h00, h11⟩` from `diag_ne_zero γ h10`. Use `setIntegral_eq_zero_of_shift hc 0 (r := γ.val 0 0 / γ.val 1 1) (div_ne_zero h00 h11) fun y s => ?_` and prove the remaining obligations. Establish `e0 : (y + Pi.single 0 s : Fin 2 → 𝔸[ℚ]) 0 = y 0 + s` using `by simp`.

Establish `e1 : (y + Pi.single 0 s : Fin 2 → 𝔸[ℚ]) 1 = y 1` using `by simp`. Rewrite using `[e0, e1, hY_a, W_shift hV hW (GL2_swap_embed_commute_middle γ h10 s 0), zero_add]`. Use `setIntegral_eq_zero_of_shift hc 1 (inverse_lower_left_ne_zero γ h10) fun y s => ?_` and prove the remaining obligations. Establish `e0 : (y + Pi.single 1 s : Fin 2 → 𝔸[ℚ]) 0 = y 0` using `by simp`. Establish `e1 : (y + Pi.single 1 s : Fin 2 → 𝔸[ℚ]) 1 = y 1 + s` using `by simp`.

Rewrite using `[e0, e1, hY_b, W_shift hV hW (GL2_swap_embed_commute_corner γ s), add_zero]`.
-/
theorem ctY_term {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) (hC : ContW) {W : G3 → ℂ} (hW : W ∈ V)
    (g : G3) (γ : GL (Fin 2) ℚ) :
    ∫ y in vecDomain ℚ (Fin 2), W (dia (e2 γ * sw) * (uni 0 (y 0) (y 1) * g)) ∂vecMeasure ℚ (Fin 2)
      = 0 := by
  have hc : Continuous fun y : Fin 2 → 𝔸[ℚ] => W (dia (e2 γ * sw) * (uni 0 (y 0) (y 1) * g)) :=
    (hC V hV W hW).comp (continuous_const.mul ((continuous_uni continuous_const (continuous_apply 0)
      (continuous_apply 1)).mul continuous_const))
  by_cases h10 : γ.val 1 0 = 0
  · obtain ⟨h00, h11⟩ := diag_ne_zero γ h10
    refine setIntegral_eq_zero_of_shift hc 0 (r := γ.val 0 0 / γ.val 1 1) (div_ne_zero h00 h11)
      fun y s => ?_
    have e0 : (y + Pi.single 0 s : Fin 2 → 𝔸[ℚ]) 0 = y 0 + s := by simp
    have e1 : (y + Pi.single 0 s : Fin 2 → 𝔸[ℚ]) 1 = y 1 := by simp
    rw [e0, e1, hY_a, W_shift hV hW (GL2_swap_embed_commute_middle γ h10 s 0), zero_add]
  · refine setIntegral_eq_zero_of_shift hc 1 (inverse_lower_left_ne_zero γ h10) fun y s => ?_
    have e0 : (y + Pi.single 1 s : Fin 2 → 𝔸[ℚ]) 0 = y 0 := by simp
    have e1 : (y + Pi.single 1 s : Fin 2 → 𝔸[ℚ]) 1 = y 1 + s := by simp
    rw [e0, e1, hY_b, W_shift hV hW (GL2_swap_embed_commute_corner γ s), add_zero]

/- English proof (translation)
Establish `hc : Continuous fun y : Fin 2 → 𝔸[ℚ] => W (dia (e2 γ * sw) * (lowM (y 0) * uni 0 0 (y 1) * g))` using `(hC V hV W hW).comp (continuous_const.mul (((continuous_lowM (continuous_apply 0)).mul (continuous_uni continuous_const continuous_const (continuous_apply 1))).mul continuous_const))`. Distinguish the cases in `hN0 : (γ⁻¹).val 0 0 = 0`. Establish `hN1 : (γ⁻¹).val 1 0 ≠ 0`. Introduce `h`. Establish `r` using `mul_inv_rel_q γ 0 0`.

Rewrite `r` using `[hN0, h, mul_zero, mul_zero, add_zero]`. Simplify using `at r`. Use `setIntegral_eq_zero_of_shift hc 1 hN1 fun y s => ?_` and prove the remaining obligations. Establish `e0 : (y + Pi.single 1 s : Fin 2 → 𝔸[ℚ]) 0 = y 0` using `by simp`. Establish `e1 : (y + Pi.single 1 s : Fin 2 → 𝔸[ℚ]) 1 = y 1 + s` using `by simp`.

Rewrite using `[e0, e1, heisenberg_lower_commute_corner, W_shift hV hW (GL2_swap_embed_commute_corner γ s), add_zero]`. Use `setIntegral_eq_zero_of_shift hc 0 hN0 fun y s => ?_` and prove the remaining obligations. Establish `e0 : (y + Pi.single 0 s : Fin 2 → 𝔸[ℚ]) 0 = y 0 + s` using `by simp`. Establish `e1 : (y + Pi.single 0 s : Fin 2 → 𝔸[ℚ]) 1 = y 1` using `by simp`. Rewrite using `[e0, e1, hH_c, W_shift hV hW (dV_c γ s), add_zero]`.
-/
theorem ctY'_term {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) (hC : ContW) {W : G3 → ℂ} (hW : W ∈ V)
    (g : G3) (γ : GL (Fin 2) ℚ) :
    ∫ y in vecDomain ℚ (Fin 2), W (dia (e2 γ * sw) * (lowM (y 0) * uni 0 0 (y 1) * g))
      ∂vecMeasure ℚ (Fin 2) = 0 := by
  have hc : Continuous fun y : Fin 2 → 𝔸[ℚ] =>
      W (dia (e2 γ * sw) * (lowM (y 0) * uni 0 0 (y 1) * g)) :=
    (hC V hV W hW).comp (continuous_const.mul (((continuous_lowM (continuous_apply 0)).mul
      (continuous_uni continuous_const continuous_const (continuous_apply 1))).mul continuous_const))
  by_cases hN0 : (γ⁻¹).val 0 0 = 0
  · have hN1 : (γ⁻¹).val 1 0 ≠ 0 := by
      intro h
      have r := mul_inv_rel_q γ 0 0
      rw [hN0, h, mul_zero, mul_zero, add_zero] at r
      simp at r
    refine setIntegral_eq_zero_of_shift hc 1 hN1 fun y s => ?_
    have e0 : (y + Pi.single 1 s : Fin 2 → 𝔸[ℚ]) 0 = y 0 := by simp
    have e1 : (y + Pi.single 1 s : Fin 2 → 𝔸[ℚ]) 1 = y 1 + s := by simp
    rw [e0, e1, heisenberg_lower_commute_corner, W_shift hV hW (GL2_swap_embed_commute_corner γ s), add_zero]
  · refine setIntegral_eq_zero_of_shift hc 0 hN0 fun y s => ?_
    have e0 : (y + Pi.single 0 s : Fin 2 → 𝔸[ℚ]) 0 = y 0 + s := by simp
    have e1 : (y + Pi.single 0 s : Fin 2 → 𝔸[ℚ]) 1 = y 1 := by simp
    rw [e0, e1, hH_c, W_shift hV hW (dV_c γ s), add_zero]

/- English proof (translation)
Introduce `V hV W hW g`. Prove the components needed by the constructor for the conclusion. Establish `e` using `setIntegral_vS hV h2 h1 hW (h := fun y : Fin 2 → 𝔸[ℚ] => uni 0 (y 0) (y 1)) (continuous_uni continuous_const (continuous_apply 0) (continuous_apply 1)) (χ := fun _ => 1) continuous_const (fun _ => norm_one) g`. Simplify using `only [mul_one] at e`. Use `show ∫ y in vecDomain ℚ (Fin 2), vS W (uni 0 (y 0) (y 1) * g) ∂vecMeasure ℚ (Fin 2) = 0`.

Rewrite using `[e]`. Simplify using `only [ctY_term hV h2 hW g, tsum_zero]`. Establish `e` using `setIntegral_vS hV h2 h1 hW (h := fun y : Fin 2 → 𝔸[ℚ] => lowM (y 0) * uni 0 0 (y 1)) ((continuous_lowM (continuous_apply 0)).mul (continuous_uni continuous_const continuous_const (continuous_apply 1))) (χ := fun _ => 1) continuous_const (fun _ => norm_one) g`. Simplify using `only [mul_one] at e`. Use `show ∫ y in vecDomain ℚ (Fin 2), vS W (lowM (y 0) * uni 0 0 (y 1) * g) ∂vecMeasure ℚ (Fin 2) = 0`.

Rewrite using `[e]`. Simplify using `only [ctY'_term hV h2 hW g, tsum_zero]`.
-/
theorem ctV_of' (h1 : MajV) (h2 : ContW) : CtV := by
  intro V hV W hW g
  constructor
  · have e := setIntegral_vS hV h2 h1 hW (h := fun y : Fin 2 → 𝔸[ℚ] => uni 0 (y 0) (y 1))
      (continuous_uni continuous_const (continuous_apply 0) (continuous_apply 1))
      (χ := fun _ => 1) continuous_const (fun _ => norm_one) g
    simp only [mul_one] at e
    show ∫ y in vecDomain ℚ (Fin 2), vS W (uni 0 (y 0) (y 1) * g) ∂vecMeasure ℚ (Fin 2) = 0
    rw [e]
    simp only [ctY_term hV h2 hW g, tsum_zero]
  · have e := setIntegral_vS hV h2 h1 hW
      (h := fun y : Fin 2 → 𝔸[ℚ] => lowM (y 0) * uni 0 0 (y 1))
      ((continuous_lowM (continuous_apply 0)).mul
        (continuous_uni continuous_const continuous_const (continuous_apply 1)))
      (χ := fun _ => 1) continuous_const (fun _ => norm_one) g
    simp only [mul_one] at e
    show ∫ y in vecDomain ℚ (Fin 2), vS W (lowM (y 0) * uni 0 0 (y 1) * g) ∂vecMeasure ℚ (Fin 2) = 0
    rw [e]
    simp only [ctY'_term hV h2 hW g, tsum_zero]

def chiH (ξ : Fin 2 → ℚ) (y : Fin 3 → 𝔸[ℚ]) : ℂ :=
  (adelicChar ℚ (-(𝔞 (ξ 0) * y 0 + 𝔞 (ξ 1) * y 1)) : ℂ)

/- English proof (translation)
The claim follows from `continuous_subtype_val.comp (continuous_adelicChar.comp (by fun_prop))`.
-/
theorem continuous_chiH (ξ : Fin 2 → ℚ) : Continuous (chiH ξ) :=
  continuous_subtype_val.comp (continuous_adelicChar.comp (by fun_prop))

/- English proof (translation)
The claim follows from `(continuous_lowM (continuous_apply 0)).mul (continuous_uni continuous_const (continuous_apply 1) (continuous_apply 2))`.
-/
theorem continuous_hH : Continuous fun y : Fin 3 → 𝔸[ℚ] => lowM (y 0) * uni 0 (y 1) (y 2) :=
  (continuous_lowM (continuous_apply 0)).mul
    (continuous_uni continuous_const (continuous_apply 1) (continuous_apply 2))

def fU (W : G3 → ℂ) (g : G3) (ξ : Fin 2 → ℚ) (γ : GL (Fin 2) ℚ) (y : Fin 3 → 𝔸[ℚ]) : ℂ :=
  W (dia (e1 γ) * (lowM (y 0) * uni 0 (y 1) (y 2) * g)) * chiH ξ y

def fV (W : G3 → ℂ) (g : G3) (ξ : Fin 2 → ℚ) (γ : GL (Fin 2) ℚ) (y : Fin 3 → 𝔸[ℚ]) : ℂ :=
  W (dia (e2 γ * sw) * (lowM (y 0) * uni 0 (y 1) (y 2) * g)) * chiH ξ y

/- English proof (translation)
The claim follows from `((hC V hV W hW).comp (continuous_const.mul (continuous_hH.mul continuous_const))).mul (continuous_chiH ξ)`.
-/
theorem continuous_fU {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) (hC : ContW) {W : G3 → ℂ}
    (hW : W ∈ V) (g : G3) (ξ : Fin 2 → ℚ) (γ : GL (Fin 2) ℚ) : Continuous (fU W g ξ γ) :=
  ((hC V hV W hW).comp (continuous_const.mul (continuous_hH.mul continuous_const))).mul
    (continuous_chiH ξ)

/- English proof (translation)
The claim follows from `((hC V hV W hW).comp (continuous_const.mul (continuous_hH.mul continuous_const))).mul (continuous_chiH ξ)`.
-/
theorem continuous_fV {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) (hC : ContW) {W : G3 → ℂ}
    (hW : W ∈ V) (g : G3) (ξ : Fin 2 → ℚ) (γ : GL (Fin 2) ℚ) : Continuous (fV W g ξ γ) :=
  ((hC V hV W hW).comp (continuous_const.mul (continuous_hH.mul continuous_const))).mul
    (continuous_chiH ξ)

section shifts

variable {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) {W : G3 → ℂ} (hW : W ∈ V) (g : G3)
  (ξ : Fin 2 → ℚ) (γ : GL (Fin 2) ℚ)
include hV hW

/- English proof (translation)
Establish `e0 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 0 = y 0` using `by simp`. Establish `e1 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 1 = y 1` using `by simp`. Establish `e2 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 2 = y 2 + s` using `by simp`. Simplify using `only [fU, chiH]`. Rewrite using `[e0, e1, e2, heisenberg_lower_commute_corner, W_shift hV hW (GL2_embed_commute_corner γ s)]`.

Conclude with `psi_comb (by ring) _`.
-/
theorem shiftU_alt_alt (y : Fin 3 → 𝔸[ℚ]) (s : 𝔸[ℚ]) :
    fU W g ξ γ (y + Pi.single 2 s) = (adelicChar ℚ (𝔞 (γ.val 1 1) * s) : ℂ) * fU W g ξ γ y := by
  have e0 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 0 = y 0 := by simp
  have e1 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 1 = y 1 := by simp
  have e2 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 2 = y 2 + s := by simp
  simp only [fU, chiH]
  rw [e0, e1, e2, heisenberg_lower_commute_corner, W_shift hV hW (GL2_embed_commute_corner γ s)]
  exact psi_comb (by ring) _

/- English proof (translation)
Establish `e0 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 0 = y 0` using `by simp`. Establish `e1 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 1 = y 1 + s` using `by simp`. Establish `e2 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 2 = y 2` using `by simp`. Simplify using `only [fU, chiH]`. Rewrite using `[e0, e1, e2, heisenberg_lower_commute_middle, W_shift hV hW (GL2_embed_commute_middle γ s (y 0 * s))]`.

Use `psi_comb ?_ _` and prove the remaining obligations. Rewrite using `[h11, map_sub, map_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shiftU_alt (h11 : γ.val 1 1 = 0) (y : Fin 3 → 𝔸[ℚ]) (s : 𝔸[ℚ]) :
    fU W g ξ γ (y + Pi.single 1 s) =
      (adelicChar ℚ (𝔞 (γ.val 1 0 - ξ 1) * s) : ℂ) * fU W g ξ γ y := by
  have e0 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 0 = y 0 := by simp
  have e1 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 1 = y 1 + s := by simp
  have e2 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 2 = y 2 := by simp
  simp only [fU, chiH]
  rw [e0, e1, e2, heisenberg_lower_commute_middle, W_shift hV hW (GL2_embed_commute_middle γ s (y 0 * s))]
  refine psi_comb ?_ _
  rw [h11, map_sub, map_zero]
  ring

/- English proof (translation)
Establish `e0 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 0 = y 0 + s` using `by simp`. Establish `e1 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 1 = y 1` using `by simp`. Establish `e2 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 2 = y 2` using `by simp`. Simplify using `only [fU, chiH]`. Rewrite using `[e0, e1, e2, hH_c, W_shift hV hW (dU_c γ h11 s)]`.

Use `psi_comb ?_ _` and prove the remaining obligations. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shiftU_c (h11 : γ.val 1 1 = 0) (y : Fin 3 → 𝔸[ℚ]) (s : 𝔸[ℚ]) :
    fU W g ξ γ (y + Pi.single 0 s) =
      (adelicChar ℚ (𝔞 (γ.val 0 1 / γ.val 1 0 - ξ 0) * s) : ℂ) * fU W g ξ γ y := by
  have e0 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 0 = y 0 + s := by simp
  have e1 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 1 = y 1 := by simp
  have e2 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 2 = y 2 := by simp
  simp only [fU, chiH]
  rw [e0, e1, e2, hH_c, W_shift hV hW (dU_c γ h11 s)]
  refine psi_comb ?_ _
  rw [map_sub]
  ring

/- English proof (translation)
Establish `e0 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 0 = y 0` using `by simp`. Establish `e1 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 1 = y 1` using `by simp`. Establish `e2 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 2 = y 2 + s` using `by simp`. Simplify using `only [fV, chiH]`. Rewrite using `[e0, e1, e2, heisenberg_lower_commute_corner, W_shift hV hW (GL2_swap_embed_commute_corner γ s)]`.

Conclude with `psi_comb (by ring) _`.
-/
theorem shiftV_alt (y : Fin 3 → 𝔸[ℚ]) (s : 𝔸[ℚ]) :
    fV W g ξ γ (y + Pi.single 2 s) = (adelicChar ℚ (𝔞 ((γ⁻¹).val 1 0) * s) : ℂ) * fV W g ξ γ y := by
  have e0 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 0 = y 0 := by simp
  have e1 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 1 = y 1 := by simp
  have e2 : (y + Pi.single 2 s : Fin 3 → 𝔸[ℚ]) 2 = y 2 + s := by simp
  simp only [fV, chiH]
  rw [e0, e1, e2, heisenberg_lower_commute_corner, W_shift hV hW (GL2_swap_embed_commute_corner γ s)]
  exact psi_comb (by ring) _

/- English proof (translation)
Establish `e0 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 0 = y 0 + s` using `by simp`. Establish `e1 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 1 = y 1` using `by simp`. Establish `e2 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 2 = y 2` using `by simp`. Simplify using `only [fV, chiH]`. Rewrite using `[e0, e1, e2, hH_c, W_shift hV hW (dV_c γ s)]`.

Use `psi_comb ?_ _` and prove the remaining obligations. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shiftV_c (y : Fin 3 → 𝔸[ℚ]) (s : 𝔸[ℚ]) :
    fV W g ξ γ (y + Pi.single 0 s) =
      (adelicChar ℚ (𝔞 ((γ⁻¹).val 0 0 - ξ 0) * s) : ℂ) * fV W g ξ γ y := by
  have e0 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 0 = y 0 + s := by simp
  have e1 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 1 = y 1 := by simp
  have e2 : (y + Pi.single 0 s : Fin 3 → 𝔸[ℚ]) 2 = y 2 := by simp
  simp only [fV, chiH]
  rw [e0, e1, e2, hH_c, W_shift hV hW (dV_c γ s)]
  refine psi_comb ?_ _
  rw [map_sub]
  ring

/- English proof (translation)
Establish `e0 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 0 = y 0` using `by simp`. Establish `e1 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 1 = y 1 + s` using `by simp`. Establish `e2 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 2 = y 2` using `by simp`. Simplify using `only [fV, chiH]`. Rewrite using `[e0, e1, e2, heisenberg_lower_commute_middle, W_shift hV hW (GL2_swap_embed_commute_middle γ h10 s (y 0 * s))]`.

Use `psi_comb ?_ _` and prove the remaining obligations. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shiftV_alt_alt (h10 : γ.val 1 0 = 0) (y : Fin 3 → 𝔸[ℚ]) (s : 𝔸[ℚ]) :
    fV W g ξ γ (y + Pi.single 1 s) =
      (adelicChar ℚ (𝔞 (γ.val 0 0 / γ.val 1 1 - ξ 1) * s) : ℂ) * fV W g ξ γ y := by
  have e0 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 0 = y 0 := by simp
  have e1 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 1 = y 1 + s := by simp
  have e2 : (y + Pi.single 1 s : Fin 3 → 𝔸[ℚ]) 2 = y 2 := by simp
  simp only [fV, chiH]
  rw [e0, e1, e2, heisenberg_lower_commute_middle, W_shift hV hW (GL2_swap_embed_commute_middle γ h10 s (y 0 * s))]
  refine psi_comb ?_ _
  rw [map_sub]
  ring

end shifts

/- English proof (translation)
Use `show ∫ y in vecDomain ℚ (Fin 3), fU W g ξ γ y ∂vecMeasure ℚ (Fin 3) = _`. Establish `hc` using `continuous_fU hV hC hW g ξ γ`. Use `split_ifs with hs`. Take `⟨h11, h10, h01⟩` from `hs`. Establish `hr : γ.val 0 1 / γ.val 1 0 - ξ 0 = 0`.

Rewrite using `[h01, h10, mul_div_cancel_right₀ _ hξ1, sub_self]`. Rewrite using `[setIntegral_eq_of_shift]`. Simplify using `[fU, chiH, lowM_zero, uni_zero]`. Introduce `y i s`. Apply the tactic sequence `have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp`.

Break down `hi with rfl | rfl | rfl` into its components or cases. Rewrite using `[shiftU_c hV hW g ξ γ h11, hr, map_zero, zero_mul, psi_zero, one_mul]`. Rewrite using `[shiftU_alt hV hW g ξ γ h11, h10, sub_self, map_zero, zero_mul, psi_zero, one_mul]`. Rewrite using `[shiftU_alt_alt hV hW g ξ γ, h11, map_zero, zero_mul, psi_zero, one_mul]`. Distinguish the cases in `h11 : γ.val 1 1 = 0`.

Distinguish the cases in `h10 : γ.val 1 0 = ξ 1`. Establish `h01 : γ.val 0 1 ≠ ξ 0 * ξ 1` using `fun h => hs ⟨h11, h10, h⟩`. Use `setIntegral_eq_zero_of_shift hc 0 ?_ (shiftU_c hV hW g ξ γ h11)` and prove the remaining obligations. Rewrite using `[h10, sub_ne_zero, Ne, div_eq_iff hξ1]`. Conclude with `h01`.

Conclude with `setIntegral_eq_zero_of_shift hc 1 (sub_ne_zero.2 h10) (shiftU_alt hV hW g ξ γ h11)`. Conclude with `setIntegral_eq_zero_of_shift hc 2 h11 (shiftU_alt_alt hV hW g ξ γ)`.
-/
theorem intU {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) (hC : ContW) {W : G3 → ℂ} (hW : W ∈ V)
    {ξ : Fin 2 → ℚ} (hξ1 : ξ 1 ≠ 0) (g : G3) (γ : GL (Fin 2) ℚ) :
    ∫ y in vecDomain ℚ (Fin 3), W (dia (e1 γ) * (lowM (y 0) * uni 0 (y 1) (y 2) * g)) * chiH ξ y
      ∂vecMeasure ℚ (Fin 3) =
      if γ.val 1 1 = 0 ∧ γ.val 1 0 = ξ 1 ∧ γ.val 0 1 = ξ 0 * ξ 1 then W (dia (e1 γ) * g) else 0 := by
  show ∫ y in vecDomain ℚ (Fin 3), fU W g ξ γ y ∂vecMeasure ℚ (Fin 3) = _
  have hc := continuous_fU hV hC hW g ξ γ
  split_ifs with hs
  · obtain ⟨h11, h10, h01⟩ := hs
    have hr : γ.val 0 1 / γ.val 1 0 - ξ 0 = 0 := by
      rw [h01, h10, mul_div_cancel_right₀ _ hξ1, sub_self]
    rw [setIntegral_eq_of_shift]
    · simp [fU, chiH, lowM_zero, uni_zero]
    · intro y i s
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
      rcases hi with rfl | rfl | rfl
      · rw [shiftU_c hV hW g ξ γ h11, hr, map_zero, zero_mul, psi_zero, one_mul]
      · rw [shiftU_alt hV hW g ξ γ h11, h10, sub_self, map_zero, zero_mul, psi_zero, one_mul]
      · rw [shiftU_alt_alt hV hW g ξ γ, h11, map_zero, zero_mul, psi_zero, one_mul]
  · by_cases h11 : γ.val 1 1 = 0
    · by_cases h10 : γ.val 1 0 = ξ 1
      · have h01 : γ.val 0 1 ≠ ξ 0 * ξ 1 := fun h => hs ⟨h11, h10, h⟩
        refine setIntegral_eq_zero_of_shift hc 0 ?_ (shiftU_c hV hW g ξ γ h11)
        rw [h10, sub_ne_zero, Ne, div_eq_iff hξ1]
        exact h01
      · exact setIntegral_eq_zero_of_shift hc 1 (sub_ne_zero.2 h10) (shiftU_alt hV hW g ξ γ h11)
    · exact setIntegral_eq_zero_of_shift hc 2 h11 (shiftU_alt_alt hV hW g ξ γ)

/- English proof (translation)
Use `show ∫ y in vecDomain ℚ (Fin 3), fV W g ξ γ y ∂vecMeasure ℚ (Fin 3) = _`. Establish `hc` using `continuous_fV hV hC hW g ξ γ`. Use `split_ifs with hs`. Take `⟨h10, hN, hd⟩` from `hs`. Establish `hN10` using `(inv_upper γ h10).1`.

Rewrite using `[setIntegral_eq_of_shift]`. Simplify using `[fV, chiH, lowM_zero, uni_zero]`. Introduce `y i s`. Apply the tactic sequence `have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp`. Break down `hi with rfl | rfl | rfl` into its components or cases.

Rewrite using `[shiftV_c hV hW g ξ γ, hN, sub_self, map_zero, zero_mul, psi_zero, one_mul]`. Rewrite using `[shiftV_alt_alt hV hW g ξ γ h10, hd, sub_self, map_zero, zero_mul, psi_zero, one_mul]`. Rewrite using `[shiftV_alt hV hW g ξ γ, hN10, map_zero, zero_mul, psi_zero, one_mul]`. Distinguish the cases in `h10 : γ.val 1 0 = 0`. Distinguish the cases in `hN : (γ⁻¹).val 0 0 = ξ 0`.

Establish `hd : γ.val 0 0 / γ.val 1 1 ≠ ξ 1` using `fun h => hs ⟨h10, hN, h⟩`. Conclude with `setIntegral_eq_zero_of_shift hc 1 (sub_ne_zero.2 hd) (shiftV_alt_alt hV hW g ξ γ h10)`. Conclude with `setIntegral_eq_zero_of_shift hc 0 (sub_ne_zero.2 hN) (shiftV_c hV hW g ξ γ)`. Conclude with `setIntegral_eq_zero_of_shift hc 2 (inverse_lower_left_ne_zero γ h10) (shiftV_alt hV hW g ξ γ)`.
-/
theorem intV {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) (hC : ContW) {W : G3 → ℂ} (hW : W ∈ V)
    {ξ : Fin 2 → ℚ} (g : G3) (γ : GL (Fin 2) ℚ) :
    ∫ y in vecDomain ℚ (Fin 3), W (dia (e2 γ * sw) * (lowM (y 0) * uni 0 (y 1) (y 2) * g)) *
      chiH ξ y ∂vecMeasure ℚ (Fin 3) =
      if γ.val 1 0 = 0 ∧ (γ⁻¹).val 0 0 = ξ 0 ∧ γ.val 0 0 / γ.val 1 1 = ξ 1 then
        W (dia (e2 γ * sw) * g) else 0 := by
  show ∫ y in vecDomain ℚ (Fin 3), fV W g ξ γ y ∂vecMeasure ℚ (Fin 3) = _
  have hc := continuous_fV hV hC hW g ξ γ
  split_ifs with hs
  · obtain ⟨h10, hN, hd⟩ := hs
    have hN10 := (inv_upper γ h10).1
    rw [setIntegral_eq_of_shift]
    · simp [fV, chiH, lowM_zero, uni_zero]
    · intro y i s
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
      rcases hi with rfl | rfl | rfl
      · rw [shiftV_c hV hW g ξ γ, hN, sub_self, map_zero, zero_mul, psi_zero, one_mul]
      · rw [shiftV_alt_alt hV hW g ξ γ h10, hd, sub_self, map_zero, zero_mul, psi_zero, one_mul]
      · rw [shiftV_alt hV hW g ξ γ, hN10, map_zero, zero_mul, psi_zero, one_mul]
  · by_cases h10 : γ.val 1 0 = 0
    · by_cases hN : (γ⁻¹).val 0 0 = ξ 0
      · have hd : γ.val 0 0 / γ.val 1 1 ≠ ξ 1 := fun h => hs ⟨h10, hN, h⟩
        exact setIntegral_eq_zero_of_shift hc 1 (sub_ne_zero.2 hd) (shiftV_alt_alt hV hW g ξ γ h10)
      · exact setIntegral_eq_zero_of_shift hc 0 (sub_ne_zero.2 hN) (shiftV_c hV hW g ξ γ)
    · exact setIntegral_eq_zero_of_shift hc 2 (inverse_lower_left_ne_zero γ h10) (shiftV_alt hV hW g ξ γ)

section reps

variable {ξ : Fin 2 → ℚ} (hξ0 : ξ 0 ≠ 0) (hξ1 : ξ 1 ≠ 0)

def gU : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, ξ 0 * ξ 1; ξ 1, 0] (by
    simp [Matrix.det_fin_two_of, hξ0, hξ1])

def gV : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(ξ 0)⁻¹, 0; 0, (ξ 0 * ξ 1)⁻¹] (by
    simp [Matrix.det_fin_two_of, hξ0, hξ1])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_gU : (gU hξ0 hξ1).val = !![0, ξ 0 * ξ 1; ξ 1, 0] := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_gV : (gV hξ0 hξ1).val = !![(ξ 0)⁻¹, 0; 0, (ξ 0 * ξ 1)⁻¹] := rfl

/- English proof (translation)
Take `⟨h11, h10, h01⟩` from `h`. Rewrite using `[out_eq_mk q]`. Use `(mk_eq_of_entries (a := gU hξ0 hξ1) (b := q.out) (q.out.val 0 0 / ξ 1) fun j => ?_).symm` and prove the remaining obligations. Rewrite using `[val_gU]`. Use `fin_cases j`.

Simplify using `[h10, div_mul_cancel₀ _ hξ1]`. Simplify using `[h11, h01]`.
-/
theorem survU_eq (q : NQ)
    (h : q.out.val 1 1 = 0 ∧ q.out.val 1 0 = ξ 1 ∧ q.out.val 0 1 = ξ 0 * ξ 1) :
    q = Quotient.mk _ (gU hξ0 hξ1) := by
  obtain ⟨h11, h10, h01⟩ := h
  rw [out_eq_mk q]
  refine (mk_eq_of_entries (a := gU hξ0 hξ1) (b := q.out) (q.out.val 0 0 / ξ 1) fun j => ?_).symm
  rw [val_gU]
  fin_cases j
  · simp [h10, div_mul_cancel₀ _ hξ1]
  · simp [h11, h01]

/- English proof (translation)
Take `⟨u, hu⟩` from `rel_entries (out_rel (gU hξ0 hξ1))`. Establish `a0` using `hu 0`. Establish `a1` using `hu 1`. Rewrite `a0`, `a1` using `[val_gU]`. Simplify using `only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue] at a0 a1`.

Establish `h11` using `a1.2.symm`. Use `⟨h11, a0.2.symm, ?_⟩` and prove the remaining obligations. Use `a1.1` as an intermediate fact. Rewrite `this` using `[h11, mul_zero, add_zero]`. Conclude with `this.symm`.
-/
theorem survU_out :
    (Quotient.mk _ (gU hξ0 hξ1) : NQ).out.val 1 1 = 0 ∧
      (Quotient.mk _ (gU hξ0 hξ1) : NQ).out.val 1 0 = ξ 1 ∧
      (Quotient.mk _ (gU hξ0 hξ1) : NQ).out.val 0 1 = ξ 0 * ξ 1 := by
  obtain ⟨u, hu⟩ := rel_entries (out_rel (gU hξ0 hξ1))
  have a0 := hu 0
  have a1 := hu 1
  rw [val_gU] at a0 a1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue] at a0 a1
  have h11 := a1.2.symm
  refine ⟨h11, a0.2.symm, ?_⟩
  have := a1.1
  rw [h11, mul_zero, add_zero] at this
  exact this.symm

/- English proof (translation)
Take `⟨u, hu⟩` from `rel_entries (out_rel (gV hξ0 hξ1))`. Establish `a0` using `hu 0`. Establish `a1` using `hu 1`. Rewrite `a0`, `a1` using `[val_gV]`. Simplify using `only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue] at a0 a1`.

Establish `h10` using `a0.2.symm`. Use `⟨h10, ?_, a1.2.symm⟩` and prove the remaining obligations. Use `a0.1` as an intermediate fact. Rewrite `this` using `[h10, mul_zero, add_zero]`. Conclude with `this.symm`.
-/
theorem gV_out :
    (Quotient.mk _ (gV hξ0 hξ1) : NQ).out.val 1 0 = 0 ∧
      (Quotient.mk _ (gV hξ0 hξ1) : NQ).out.val 0 0 = (ξ 0)⁻¹ ∧
      (Quotient.mk _ (gV hξ0 hξ1) : NQ).out.val 1 1 = (ξ 0 * ξ 1)⁻¹ := by
  obtain ⟨u, hu⟩ := rel_entries (out_rel (gV hξ0 hξ1))
  have a0 := hu 0
  have a1 := hu 1
  rw [val_gV] at a0 a1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue] at a0 a1
  have h10 := a0.2.symm
  refine ⟨h10, ?_, a1.2.symm⟩
  have := a0.1
  rw [h10, mul_zero, add_zero] at this
  exact this.symm

/- English proof (translation)
Take `⟨h10, h00, h11⟩` from `gV_out hξ0 hξ1`. Use `⟨h10, ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `(inv_upper _ h10).2`. Rewrite `e` using `[h00]`. Conclude with `(mul_inv_eq_one₀ hξ0).1 e`.

Rewrite using `[h00, h11]`. Clear the denominators using the available nonvanishing facts.
-/
theorem survV_out :
    (Quotient.mk _ (gV hξ0 hξ1) : NQ).out.val 1 0 = 0 ∧
      ((Quotient.mk _ (gV hξ0 hξ1) : NQ).out⁻¹).val 0 0 = ξ 0 ∧
      (Quotient.mk _ (gV hξ0 hξ1) : NQ).out.val 0 0 /
        (Quotient.mk _ (gV hξ0 hξ1) : NQ).out.val 1 1 = ξ 1 := by
  obtain ⟨h10, h00, h11⟩ := gV_out hξ0 hξ1
  refine ⟨h10, ?_, ?_⟩
  · have e := (inv_upper _ h10).2
    rw [h00] at e
    exact (mul_inv_eq_one₀ hξ0).1 e
  · rw [h00, h11]
    field_simp

/- English proof (translation)
Take `⟨h10, hN, hd⟩` from `h`. Establish `e1 : ξ 0 * q.out.val 0 0 = 1` using `by rw [← hN]; exact (inv_upper _ h10).2`. Establish `h11ne` using `(diag_ne_zero q.out h10).2`. Establish `e2 : q.out.val 0 0 = ξ 1 * q.out.val 1 1` using `(div_eq_iff h11ne).1 hd`. Establish `hM11 : q.out.val 1 1 * (ξ 0 * ξ 1) = 1` using `by linear_combination e1 - ξ 0 * e2`.

Establish `hM00 : q.out.val 0 0 = (ξ 0)⁻¹` using `eq_inv_of_mul_eq_one_right e1`. Establish `hM11' : q.out.val 1 1 = (ξ 0 * ξ 1)⁻¹` using `eq_inv_of_mul_eq_one_left hM11`. Rewrite using `[out_eq_mk q]`. Use `(mk_eq_of_entries (a := gV hξ0 hξ1) (b := q.out) (q.out.val 0 1 * (ξ 0 * ξ 1)) fun j => ?_).symm` and prove the remaining obligations. Rewrite using `[val_gV]`.

Apply the tactic sequence `have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp`. Break down `hj with rfl | rfl` into its components or cases. Simplify using `[h10, hM00]`. Simplify using `only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue]`. Use `⟨?_, hM11'⟩` and prove the remaining obligations.

Rewrite using `[zero_add, mul_assoc, mul_inv_cancel₀ (mul_ne_zero hξ0 hξ1), mul_one]`.
-/
theorem survV_eq (q : NQ)
    (h : q.out.val 1 0 = 0 ∧ (q.out⁻¹).val 0 0 = ξ 0 ∧ q.out.val 0 0 / q.out.val 1 1 = ξ 1) :
    q = Quotient.mk _ (gV hξ0 hξ1) := by
  obtain ⟨h10, hN, hd⟩ := h
  have e1 : ξ 0 * q.out.val 0 0 = 1 := by rw [← hN]; exact (inv_upper _ h10).2
  have h11ne := (diag_ne_zero q.out h10).2
  have e2 : q.out.val 0 0 = ξ 1 * q.out.val 1 1 := (div_eq_iff h11ne).1 hd
  have hM11 : q.out.val 1 1 * (ξ 0 * ξ 1) = 1 := by linear_combination e1 - ξ 0 * e2
  have hM00 : q.out.val 0 0 = (ξ 0)⁻¹ := eq_inv_of_mul_eq_one_right e1
  have hM11' : q.out.val 1 1 = (ξ 0 * ξ 1)⁻¹ := eq_inv_of_mul_eq_one_left hM11
  rw [out_eq_mk q]
  refine (mk_eq_of_entries (a := gV hξ0 hξ1) (b := q.out) (q.out.val 0 1 * (ξ 0 * ξ 1))
    fun j => ?_).symm
  rw [val_gV]
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with rfl | rfl
  · simp [h10, hM00]
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue]
    refine ⟨?_, hM11'⟩
    rw [zero_add, mul_assoc, mul_inv_cancel₀ (mul_ne_zero hξ0 hξ1), mul_one]

end reps

/- English proof (translation)
Take `⟨g11, g10, g01⟩` from `hγ`. Take `⟨d10, d00, d11⟩` from `hδ`. Use `set s : ℚˣ := Units.mk0 (ξ 0 * ξ 1) (mul_ne_zero hξ0 hξ1) with hs`. Use `set a : ℚ := γ.val 0 0 / ξ 1 with ha`. Use `set z : ℚ := -(ξ 0 * ξ 1 * δ.val 0 1) with hz`.

Use `set b : ℚ := -(a * (ξ 0 * ξ 1) * δ.val 0 1) with hb`. Establish `hQ : e1 γ = uni a b z * (dg s s s * (e2 δ * sw))`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul]`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [e1, e2, b1M, b2M, sw, uni, dg, s, a, b, z, Matrix.mul_apply, Fin.sum_univ_three, g11, g10, g01, d10, d00, d11] <;>`. Apply the tactic sequence `first | ring1 | (field_simp; ring1) | field_simp`. Use `set S : (𝔸[ℚ])ˣ := Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom s with hS`. Establish `hdu : ∀ a b z : ℚ, dia (uni a b z) = uni (𝔞 a) (𝔞 b) (𝔞 z)`.

Introduce `a b z`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[val_uni]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [uni]`.

Establish `hdd : dia (dg s s s) = dg S S S`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dg, S]`. Establish `key : dia (e1 γ) * g = uni (𝔞 a) (𝔞 b) (𝔞 z) * (dg S S S * (dia (e2 δ * sw) * g))`.

Establish `hm : dia (uni a b z * (dg s s s * (e2 δ * sw))) = dia (uni a b z) * (dia (dg s s s) * dia (e2 δ * sw))`. Simplify using `only [dia, map_mul]`. Rewrite using `[hQ, hm, hdu, hdd]`. Simplify using `only [mul_assoc]`. Rewrite using `[key, hV.psi W hW, hV.cen W hW, ← map_add, psi_rat, one_mul]`.
-/
theorem final_eq {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) {W : G3 → ℂ} (hW : W ∈ V)
    {ξ : Fin 2 → ℚ} (hξ0 : ξ 0 ≠ 0) (hξ1 : ξ 1 ≠ 0) (γ δ : GL (Fin 2) ℚ)
    (hγ : γ.val 1 1 = 0 ∧ γ.val 1 0 = ξ 1 ∧ γ.val 0 1 = ξ 0 * ξ 1)
    (hδ : δ.val 1 0 = 0 ∧ δ.val 0 0 = (ξ 0)⁻¹ ∧ δ.val 1 1 = (ξ 0 * ξ 1)⁻¹) (g : G3) :
    W (dia (e1 γ) * g) = W (dia (e2 δ * sw) * g) := by
  obtain ⟨g11, g10, g01⟩ := hγ
  obtain ⟨d10, d00, d11⟩ := hδ
  set s : ℚˣ := Units.mk0 (ξ 0 * ξ 1) (mul_ne_zero hξ0 hξ1) with hs
  set a : ℚ := γ.val 0 0 / ξ 1 with ha
  set z : ℚ := -(ξ 0 * ξ 1 * δ.val 0 1) with hz
  set b : ℚ := -(a * (ξ 0 * ξ 1) * δ.val 0 1) with hb
  have hQ : e1 γ = uni a b z * (dg s s s * (e2 δ * sw)) := by
    apply Units.ext
    simp only [Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e1, e2, b1M, b2M, sw, uni, dg, s, a, b, z, Matrix.mul_apply, Fin.sum_univ_three, g11,
        g10, g01, d10, d00, d11] <;>
      first | ring1 | (field_simp; ring1) | field_simp
  set S : (𝔸[ℚ])ˣ := Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom s with hS
  have hdu : ∀ a b z : ℚ, dia (uni a b z) = uni (𝔞 a) (𝔞 b) (𝔞 z) := by
    intro a b z
    apply Units.ext
    rw [val_uni]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uni]
  have hdd : dia (dg s s s) = dg S S S := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg, S]
  have key : dia (e1 γ) * g = uni (𝔞 a) (𝔞 b) (𝔞 z) * (dg S S S * (dia (e2 δ * sw) * g)) := by
    have hm : dia (uni a b z * (dg s s s * (e2 δ * sw))) =
        dia (uni a b z) * (dia (dg s s s) * dia (e2 δ * sw)) := by
      simp only [dia, map_mul]
    rw [hQ, hm, hdu, hdd]
    simp only [mul_assoc]
  rw [key, hV.psi W hW, hV.cen W hW, ← map_add, psi_rat, one_mul]

/- English proof (translation)
Introduce `V hV W hW ξ hξ0 hξ1 g`. Establish `eU` using `setIntegral_uS hV h2 h1 hW continuous_hH (continuous_chiH ξ) (fun y => norm_psi _) g`. Establish `eV` using `setIntegral_vS hV h2 h1' hW continuous_hH (continuous_chiH ξ) (fun y => norm_psi _) g`. Use `beta_reduce at eU eV`. Use `show ∫ y in vecDomain ℚ (Fin 3), uS W (lowM (y 0) * uni 0 (y 1) (y 2) * g) * chiH ξ y ∂vecMeasure ℚ (Fin 3) = ∫ y in vecDomain ℚ (Fin 3), vS W (lowM (y 0) * uni 0 (y 1) (y 2) * g) * chiH ξ y ∂vecMeasure ℚ (Fin 3)`.

Rewrite using `[eU, eV]`. Simplify using `only [intU hV h2 hW hξ1 g, intV hV h2 hW g]`. Rewrite using `[tsum_eq_single (Quotient.mk _ (gU hξ0 hξ1)) fun q hq => if_neg fun h => hq (survU_eq hξ0 hξ1 q h), tsum_eq_single (Quotient.mk _ (gV hξ0 hξ1)) fun q hq => if_neg fun h => hq (survV_eq hξ0 hξ1 q h), if_pos (survU_out hξ0 hξ1), if_pos (survV_out hξ0 hξ1)]`. Conclude with `final_eq hV hW hξ0 hξ1 _ _ (survU_out hξ0 hξ1) (gV_out hξ0 hξ1) g`.
-/
theorem hGen_of' (h1 : MajU) (h1' : MajV) (h2 : ContW) : HGen := by
  intro V hV W hW ξ hξ0 hξ1 g
  have eU := setIntegral_uS hV h2 h1 hW continuous_hH (continuous_chiH ξ) (fun y => norm_psi _) g
  have eV := setIntegral_vS hV h2 h1' hW continuous_hH (continuous_chiH ξ) (fun y => norm_psi _) g
  beta_reduce at eU eV
  show ∫ y in vecDomain ℚ (Fin 3), uS W (lowM (y 0) * uni 0 (y 1) (y 2) * g) * chiH ξ y
      ∂vecMeasure ℚ (Fin 3) =
    ∫ y in vecDomain ℚ (Fin 3), vS W (lowM (y 0) * uni 0 (y 1) (y 2) * g) * chiH ξ y
      ∂vecMeasure ℚ (Fin 3)
  rw [eU, eV]
  simp only [intU hV h2 hW hξ1 g, intV hV h2 hW g]
  rw [tsum_eq_single (Quotient.mk _ (gU hξ0 hξ1)) fun q hq =>
      if_neg fun h => hq (survU_eq hξ0 hξ1 q h),
    tsum_eq_single (Quotient.mk _ (gV hξ0 hξ1)) fun q hq =>
      if_neg fun h => hq (survV_eq hξ0 hξ1 q h),
    if_pos (survU_out hξ0 hξ1), if_pos (survV_out hξ0 hξ1)]
  exact final_eq hV hW hξ0 hξ1 _ _ (survU_out hξ0 hξ1) (gV_out hξ0 hξ1) g

end Ad3.GA.CtvP

namespace Ad3.GA

/- English proof (translation)
The claim follows from `CtvP.ctV_of' h1 h2`.
-/
theorem ctV_of (h1 : MajV) (h2 : ContW) : CtV := CtvP.ctV_of' h1 h2

/- English proof (translation)
The claim follows from `CtvP.hGen_of' h1 h1' h2`.
-/
theorem hGen_of (h1 : MajU) (h1' : MajV) (h2 : ContW) : HGen := CtvP.hGen_of' h1 h1' h2

end Ad3.GA
