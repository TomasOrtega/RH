import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMdiffPos

open CongruenceSubgroup UpperTheory.V.Af.Nf
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm Pointwise

/- English proof (translation)
Establish `h1 : Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))`. Rewrite using `[← Subgroup.mem_strictPeriods_iff, Subgroup.strictPeriods_SL2Z]`. Conclude with `AddSubgroup.mem_zmultiples _`. Take `⟨N, hN, -, hm⟩` from `Subgroup.exists_pow_mem_of_relIndex_ne_zero (Subgroup.IsArithmetic.is_commensurable (𝒢 := Γ)).1 h1`. Establish `hP : (N : ℝ) ∈ Γ.strictPeriods`.

Rewrite using `[Subgroup.mem_strictPeriods_iff]`. Use `(Subgroup.mem_inf.mp hm).1` as an intermediate fact. Rewrite `this` using `[← AddChar.map_nsmul_eq_pow]`. Simplify `this` using `only [nsmul_eq_mul, mul_one]`. Establish `hN' : (0 : ℝ) < N` using `by exact_mod_cast hN`.

Establish `hper : ∀ w : ℍ, Function.Periodic (fun t : ℝ => F (t +ᵥ w)) N` using `fun w t => by`. Use `SlashInvariantForm.vAdd_apply_of_mem_strictPeriods F (t +ᵥ w) hP` as an intermediate fact. Simplify using `only`. Rewrite using `[add_comm, add_vadd]`. Conclude with `this`.

Use `⟨N, hN, hper z, ?_⟩` and prove the remaining obligations. Establish `h0` using `CuspFormClass.qExpansion_coeff_zero F hN' hP`. Rewrite `h0` using `[ModularFormClass.qExpansion_coeff_eq_intervalIntegral F hN' hP 0 z.im_pos]`. Establish `hne : (1 / ((N : ℝ) : ℂ)) ≠ 0`. Establish `: (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`.

Simplify using `using this`. Establish `h2` using `(mul_eq_zero.mp h0).resolve_left hne`. Use `set w : ℍ := (-z.re) +ᵥ z with hw`. Establish `h3 : ∫ t in (0 : ℝ)..N, F (t +ᵥ w) = 0`. Rewrite using `[← h2]`.

Use `intervalIntegral.integral_congr fun t _ => ?_` and prove the remaining obligations. Simplify using `only [pow_zero, div_one, one_mul]`. Use `congr 1`. Apply `UpperHalfPlane.ext` to reduce the goal to its premises. Apply the tactic sequence `apply Complex.ext <;> simp [hw]`.

Establish `h4` using `(hper w).intervalIntegral_add_eq z.re 0`. Rewrite `h4` using `[zero_add, h3]`. Rewrite using `[← h4]`. Establish `h5` using `intervalIntegral.integral_comp_add_right (fun t : ℝ => F (t +ᵥ w)) z.re (a := 0) (b := N)`. Rewrite `h5` using `[zero_add, add_comm (N : ℝ)]`.

Rewrite using `[← h5]`. Use `intervalIntegral.integral_congr fun t _ => ?_` and prove the remaining obligations. Simplify using `only [hw, vadd_vadd]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma aux {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} (F : CuspForm Γ k) (z : ℍ) :
    ∃ N : ℕ, 0 < N ∧ Function.Periodic (fun t : ℝ => F (t +ᵥ z)) N ∧
      ∫ t in (0 : ℝ)..N, F (t +ᵥ z) = 0 := by
  have h1 : Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := by
    rw [← Subgroup.mem_strictPeriods_iff, Subgroup.strictPeriods_SL2Z]
    exact AddSubgroup.mem_zmultiples _
  obtain ⟨N, hN, -, hm⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero
    (Subgroup.IsArithmetic.is_commensurable (𝒢 := Γ)).1 h1
  have hP : (N : ℝ) ∈ Γ.strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    have := (Subgroup.mem_inf.mp hm).1
    rw [← AddChar.map_nsmul_eq_pow] at this
    simpa only [nsmul_eq_mul, mul_one] using this
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hper : ∀ w : ℍ, Function.Periodic (fun t : ℝ => F (t +ᵥ w)) N := fun w t => by
    have := SlashInvariantForm.vAdd_apply_of_mem_strictPeriods F (t +ᵥ w) hP
    simp only
    rw [add_comm, add_vadd]
    exact this
  refine ⟨N, hN, hper z, ?_⟩
  have h0 := CuspFormClass.qExpansion_coeff_zero F hN' hP
  rw [ModularFormClass.qExpansion_coeff_eq_intervalIntegral F hN' hP 0 z.im_pos] at h0
  have hne : (1 / ((N : ℝ) : ℂ)) ≠ 0 := by
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    simpa using this
  have h2 := (mul_eq_zero.mp h0).resolve_left hne
  set w : ℍ := (-z.re) +ᵥ z with hw
  have h3 : ∫ t in (0 : ℝ)..N, F (t +ᵥ w) = 0 := by
    rw [← h2]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [pow_zero, div_one, one_mul]
    congr 1
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [hw]
  have h4 := (hper w).intervalIntegral_add_eq z.re 0
  rw [zero_add, h3] at h4
  rw [← h4]
  have h5 := intervalIntegral.integral_comp_add_right (fun t : ℝ => F (t +ᵥ w)) z.re (a := 0) (b := N)
  rw [zero_add, add_comm (N : ℝ)] at h5
  rw [← h5]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hw, vadd_vadd]
  congr 2
  ring

/- English proof (translation)
Use `haveI : NeZero M := ⟨by omega⟩`. Use `haveI : (ConjAct.toConjAct (toR γ)⁻¹ • (Gamma1 M : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by`. Use `Subgroup.IsArithmetic.conj (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) γ⁻¹` as an intermediate fact. Rewrite using `[← map_inv]`. Conclude with `this`.

Take `⟨N, hN, hp, hi⟩` from `aux (CuspForm.translate f (toR γ)) z`. Use `⟨N, hN, ?_, ?_⟩` and prove the remaining obligations. Introduce `t`. Use `hp t` as an intermediate fact. Simplify using `only [(nslSl k f).2.1 _ hγ, Pi.smul_apply]`.

Use `congr 1`. Simplify using `only [(nslSl k f).2.1 _ hγ, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[intervalIntegral.integral_const_mul]`. Conclude with `mul_eq_zero_of_right _ hi`.
-/
private lemma aux2 (k M : ℕ) (hM : 1 ≤ M) (f : CuspForm (Gamma1 M) (k : ℤ)) (γ : GL (Fin 2) ℚ)
    (hγ : 0 < (toR γ).val.det) (z : ℍ) : ∃ N : ℕ, 0 < N ∧
    Function.Periodic (fun t : ℝ => nsl k f (toR γ) (t +ᵥ z)) N ∧
      ∫ t in (0 : ℝ)..N, nsl k f (toR γ) (t +ᵥ z) = 0 := by
  haveI : NeZero M := ⟨by omega⟩
  haveI : (ConjAct.toConjAct (toR γ)⁻¹ • (Gamma1 M : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    have := Subgroup.IsArithmetic.conj (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) γ⁻¹
    rw [← map_inv]
    exact this
  obtain ⟨N, hN, hp, hi⟩ := aux (CuspForm.translate f (toR γ)) z
  refine ⟨N, hN, ?_, ?_⟩
  · intro t
    have := hp t
    simp only [(nslSl k f).2.1 _ hγ, Pi.smul_apply]
    congr 1
  · simp only [(nslSl k f).2.1 _ hγ, Pi.smul_apply, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul]
    exact mul_eq_zero_of_right _ hi

/- English proof (translation)
Introduce `k M hM f γ z`. Establish `hne : (toR γ).val.det ≠ 0` using `(toR γ).det_ne_zero`. Break down `hne.lt_or_gt with h | h` into its components or cases. Set `e : GL (Fin 2) ℚ` to `Matrix.GeneralLinearGroup.mkOfDetNeZero !![-1, 0; 0, 1] (by simp)`. Establish `he : (toR (e * γ)).val = eps * (toR γ).val`.

Rewrite using `[map_mul, Units.val_mul]`. Use `congr 1`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [toR, e, eps]`. Establish `hd : 0 < (toR (e * γ)).val.det`.

Rewrite using `[he, Matrix.det_mul]`. Simplify `h` using `[eps]`. Use `aux2 k M hM f (e * γ) hd z` as an intermediate fact. Rewrite `this` using `[he, (nslMul k f).2.1]`. Then use the resulting hypothesis. Conclude with `aux2 k M hM f γ h z`.
-/
theorem UpperTheory.V.Af.Nf.classCT :
    UpperTheory.V.Af.Nf.ClassCT := by
  intro k M hM f γ z
  have hne : (toR γ).val.det ≠ 0 := (toR γ).det_ne_zero
  rcases hne.lt_or_gt with h | h
  · let e : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![-1, 0; 0, 1] (by simp)
    have he : (toR (e * γ)).val = eps * (toR γ).val := by
      rw [map_mul, Units.val_mul]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [toR, e, eps]
    have hd : 0 < (toR (e * γ)).val.det := by
      rw [he, Matrix.det_mul]
      simpa [eps] using h
    have := aux2 k M hM f (e * γ) hd z
    rwa [he, (nslMul k f).2.1] at this
  · exact aux2 k M hM f γ h z
