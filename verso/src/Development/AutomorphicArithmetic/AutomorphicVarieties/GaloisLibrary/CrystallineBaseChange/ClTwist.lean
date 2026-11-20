import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt

noncomputable section

open CongruenceSubgroup UpperHalfPlane ModularForm UpperTheory.V.Af Matrix.GeneralLinearGroup
open scoped MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Br

/- English proof (translation)
Use `⟨fun u => (N : ℂ)⁻¹ * ZMod.dft (fun j => ψ j) u, fun n => ?_, fun d u hd => ?_⟩` and prove the remaining obligations. Establish `h` using `ZMod.invDFT_apply (ZMod.dft (fun j => ψ j)) n`. Rewrite `h` using `[LinearEquiv.symm_apply_apply]`. Rewrite using `[h, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨d, rfl⟩` from `hd`. Establish `h` using `ZMod.dft_comp_unitMul (fun j => ψ j) d (d * u)`. Simplify using `only [map_mul] at h`.

Rewrite `h` using `[ZMod.dft_const_mul, Units.inv_mul_cancel_left]`. Simplify using `only [← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem tw_coeffs {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) :
    ∃ c : ZMod N → ℂ, (∀ n : ZMod N, ∑ u, c u * ZMod.stdAddChar (u * n) = ψ n) ∧
      ∀ d u : ZMod N, IsUnit d → c u = ψ d * c (d * u) := by
  refine ⟨fun u => (N : ℂ)⁻¹ * ZMod.dft (fun j => ψ j) u, fun n => ?_, fun d u hd => ?_⟩
  · have h := ZMod.invDFT_apply (ZMod.dft (fun j => ψ j)) n
    rw [LinearEquiv.symm_apply_apply] at h
    rw [h, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_eq_mul]; ring
  · obtain ⟨d, rfl⟩ := hd
    have h := ZMod.dft_comp_unitMul (fun j => ψ j) d (d * u)
    simp only [map_mul] at h
    rw [ZMod.dft_const_mul, Units.inv_mul_cancel_left] at h
    simp only [← h]; ring

private def tG (N : ℕ) (u : ℤ) : GL (Fin 2) ℝ := upperRightHom ((u : ℝ) / N)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem tG_val (N : ℕ) (u : ℤ) : (tG N u).1 = !![1, (u : ℝ) / N; 0, 1] := rfl

/- English proof (translation)
Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, tG_val]`. Simplify using the standard rewrite rules.
-/
private theorem tG_det (N : ℕ) (u : ℤ) : (tG N u).det.val = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, tG_val]; simp

/- English proof (translation)
Establish `: 0 < (tG N u).det.val` using `by rw [tG_det]; exact one_pos`. Rewrite using `[σ, if_pos this]`. Both sides reduce to the same expression.
-/
private theorem tG_σ (N : ℕ) (u : ℤ) (c : ℂ) : σ (tG N u) c = c := by
  have : 0 < (tG N u).det.val := by rw [tG_det]; exact one_pos
  rw [σ, if_pos this]; rfl

/- English proof (translation)
Establish `e : tG N u • z = ((u : ℝ) / N) +ᵥ z`. Use `ext`. Rewrite using `[coe_smul_of_det_pos (by rw [tG_det]; exact one_pos)]`. Simplify using `[num, denom, tG_val, add_comm]`. Rewrite using `[slash_apply, tG_σ, tG_det, e]`.

Simplify using `[denom, tG_val]`.
-/
private theorem tG_apply (N : ℕ) (u : ℤ) (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[k] tG N u) z = f (((u : ℝ) / N) +ᵥ z) := by
  have e : tG N u • z = ((u : ℝ) / N) +ᵥ z := by
    ext
    rw [coe_smul_of_det_pos (by rw [tG_det]; exact one_pos)]
    simp [num, denom, tG_val, add_comm]
  rw [slash_apply, tG_σ, tG_det, e]
  simp [denom, tG_val]

/- English proof (translation)
Rewrite `hγ` using `[Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Take `⟨c, hc⟩` from `hγ`. Move the coercions through the operations in `at hc`. Establish `hd` using `γ.det_coe`. Rewrite `hd` using `[Matrix.det_fin_two, hc]`.

Establish `hd'` using `congrArg (Int.cast : ℤ → ZMod N) hd`. Move the coercions through the operations in `at hd'`. Rewrite `hd'` using `[ZMod.natCast_self]`. Establish `h1 : (N : ℤ) ∣ u * γ 1 1 - v * γ 0 0`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Use `push_cast`. Rewrite using `[h]`. Take the linear combination `(-(u : ZMod N) * ((γ 1 1 : ℤ) : ZMod N)) * hd'`. Take `⟨e, he⟩` from `h1`. Establish `hN : (N : ℤ) ≠ 0` using `by exact_mod_cast NeZero.ne N`.

Establish `hNR : (N : ℝ) ≠ 0` using `by exact_mod_cast NeZero.ne N`. Choose the witnesses or unpack the hypotheses as in `⟨δ, d00, d01, d10, d11⟩ : ∃ δ : SL(2, ℤ), δ 0 0 = γ 0 0 + u * c * N ∧ δ 0 1 = γ 0 1 + e - u * v * c ∧ δ 1 0 = N * N * c ∧ δ 1 1 = γ 1 1 - c * v * N := by`. Use `⟨⟨!![γ 0 0 + u * c * N, γ 0 1 + e - u * v * c; N * N * c, γ 1 1 - c * v * N], ?_⟩, rfl, rfl, rfl, rfl⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_fin_two_of]`. Take the linear combination `hd + N * c * he`.

Use `⟨δ, ?_, ?_, fun k f => ?_⟩` and prove the remaining obligations. Rewrite using `[Gamma0_mem, d10]`. Simplify using the standard rewrite rules. Rewrite using `[d11]`. Simplify using the standard rewrite rules.

Rewrite using `[SL_slash, SL_slash, ← SlashAction.slash_mul, ← SlashAction.slash_mul]`. Use `congr 1`. Establish `he' : (u : ℝ) * (γ 1 1 : ℤ) - v * (γ 0 0 : ℤ) = N * e` using `by exact_mod_cast he`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [tG_val, Matrix.mul_apply, Fin.sum_univ_two, hc, d00, d01, d10, d11] <;> field_simp`.

Apply the tactic sequence `all_goals first | ring1 | linear_combination he'`.
-/
private theorem tG_comm {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (N * N)) (u v : ℤ)
    (h : (v : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) ^ 2 * u) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧ ((δ 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) ∧
      ∀ (k : ℤ) (f : ℍ → ℂ), (f ∣[k] tG N u) ∣[k] γ = (f ∣[k] δ) ∣[k] tG N v := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  obtain ⟨c, hc⟩ := hγ
  push_cast at hc
  have hd := γ.det_coe
  rw [Matrix.det_fin_two, hc] at hd
  have hd' := congrArg (Int.cast : ℤ → ZMod N) hd
  push_cast at hd'
  rw [ZMod.natCast_self] at hd'
  have h1 : (N : ℤ) ∣ u * γ 1 1 - v * γ 0 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h]
    linear_combination (-(u : ZMod N) * ((γ 1 1 : ℤ) : ZMod N)) * hd'
  obtain ⟨e, he⟩ := h1
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  obtain ⟨δ, d00, d01, d10, d11⟩ : ∃ δ : SL(2, ℤ), δ 0 0 = γ 0 0 + u * c * N ∧ δ 0 1 = γ 0 1 + e - u * v * c ∧
      δ 1 0 = N * N * c ∧ δ 1 1 = γ 1 1 - c * v * N := by
    refine ⟨⟨!![γ 0 0 + u * c * N, γ 0 1 + e - u * v * c; N * N * c, γ 1 1 - c * v * N], ?_⟩, rfl, rfl, rfl, rfl⟩
    rw [Matrix.det_fin_two_of]
    linear_combination hd + N * c * he
  refine ⟨δ, ?_, ?_, fun k f => ?_⟩
  · rw [Gamma0_mem, d10]; simp
  · rw [d11]; simp
  · rw [SL_slash, SL_slash, ← SlashAction.slash_mul, ← SlashAction.slash_mul]
    congr 1
    have he' : (u : ℝ) * (γ 1 1 : ℤ) - v * (γ 0 0 : ℤ) = N * e := by exact_mod_cast he
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tG_val, Matrix.mul_apply, Fin.sum_univ_two, hc, d00, d01, d10, d11] <;> field_simp
    all_goals first | ring1 | linear_combination he'

/- English proof (translation)
Rewrite `hc`, the goal using `[isCusp_SL2Z_iff]`. Take `⟨c, rfl⟩` from `hc`. Use `⟨(upperRightHom ((u : ℚ) / N) : GL (Fin 2) ℚ) • c, ?_⟩` and prove the remaining obligations. Rewrite using `[← Rat.coe_castHom, OnePoint.map_smul]`. Use `congr 1`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [tG_val, upperRightHom]`.
-/
private theorem tG_cusp (N : ℕ) (u : ℤ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : IsCusp (tG N u • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  refine ⟨(upperRightHom ((u : ℚ) / N) : GL (Fin 2) ℚ) • c, ?_⟩
  rw [← Rat.coe_castHom, OnePoint.map_smul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tG_val, upperRightHom]

private def tw (N : ℕ) [NeZero N] (k : ℕ) (c : ZMod N → ℂ) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ u : ZMod N, c u • f ∣[(k : ℤ)] tG N (u.val : ℤ)

/- English proof (translation)
Introduce `γ hγ`. Establish `hu : IsUnit ((γ 1 1 : ℤ) : ZMod (N * N))`. Establish `dγ` using `congrArg (Int.cast : ℤ → ZMod (N * N)) (γ.det_coe)`. Rewrite `dγ` using `[Matrix.det_fin_two]`. Move the coercions through the operations in `at dγ`.

Rewrite `dγ` using `[Gamma0_mem.1 hγ, mul_zero, sub_zero]`. Conclude with `IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans dγ)`. Establish `hu' : IsUnit ((γ 1 1 : ℤ) : ZMod N)`. Simplify using `using hu.map (ZMod.castHom (dvd_mul_right N N) (ZMod N))`. Establish `e : DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ ^ 2) ((γ 1 1 : ℤ) : ZMod (N * N)) = χ ((γ 1 1 : ℤ) : ZMod N) * ψ (((γ 1 1 : ℤ) : ZMod N) ^ 2)`.

Use `DirichletCharacter.changeLevel_eq_cast_of_dvd (χ * ψ ^ 2) (dvd_mul_right N N) hu.unit` as an intermediate fact. Rewrite `this` using `[IsUnit.unit_spec, ZMod.cast_intCast (dvd_mul_right N N)]`. Rewrite using `[this, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero, map_pow]`. Establish `hb : Function.Bijective fun u : ZMod N => ((γ 1 1 : ℤ) : ZMod N) ^ 2 * u` using `((hu'.pow 2).unit.mulLeft).bijective`. Rewrite using `[e, tw, SlashAction.sum_slash, Finset.smul_sum, ← hb.sum_comp fun y => (χ ((γ 1 1 : ℤ) : ZMod N) * ψ (((γ 1 1 : ℤ) : ZMod N) ^ 2)) • c y • f ∣[(k : ℤ)] tG N (y.val : ℤ)]`.

Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Take `⟨δ, h0, h1, h⟩` from `tG_comm γ hγ (u.val : ℤ) ((((γ 1 1 : ℤ) : ZMod N) ^ 2 * u).val : ℤ) (by simp)`. Rewrite using `[SL_smul_slash, h, hf δ h0, h1, smul_slash, tG_σ, smul_smul, smul_smul, hc _ u (hu'.pow 2)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem tw_char {N : ℕ} [NeZero N] (k : ℕ) (χ ψ : DirichletCharacter ℂ N) {c : ZMod N → ℂ}
    (hc : ∀ d u : ZMod N, IsUnit d → c u = ψ d * c (d * u)) {f : ℍ → ℂ} (hf : HasChar k χ f) :
    HasChar k (DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ ^ 2)) (tw N k c f) := by
  intro γ hγ
  have hu : IsUnit ((γ 1 1 : ℤ) : ZMod (N * N)) := by
    have dγ := congrArg (Int.cast : ℤ → ZMod (N * N)) (γ.det_coe)
    rw [Matrix.det_fin_two] at dγ
    push_cast at dγ
    rw [Gamma0_mem.1 hγ, mul_zero, sub_zero] at dγ
    exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans dγ)
  have hu' : IsUnit ((γ 1 1 : ℤ) : ZMod N) := by
    simpa using hu.map (ZMod.castHom (dvd_mul_right N N) (ZMod N))
  have e : DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ ^ 2) ((γ 1 1 : ℤ) : ZMod (N * N)) =
      χ ((γ 1 1 : ℤ) : ZMod N) * ψ (((γ 1 1 : ℤ) : ZMod N) ^ 2) := by
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd (χ * ψ ^ 2) (dvd_mul_right N N) hu.unit
    rw [IsUnit.unit_spec, ZMod.cast_intCast (dvd_mul_right N N)] at this
    rw [this, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero, map_pow]
  have hb : Function.Bijective fun u : ZMod N => ((γ 1 1 : ℤ) : ZMod N) ^ 2 * u :=
    ((hu'.pow 2).unit.mulLeft).bijective
  rw [e, tw, SlashAction.sum_slash, Finset.smul_sum,
    ← hb.sum_comp fun y => (χ ((γ 1 1 : ℤ) : ZMod N) * ψ (((γ 1 1 : ℤ) : ZMod N) ^ 2)) • c y • f ∣[(k : ℤ)] tG N (y.val : ℤ)]
  refine Finset.sum_congr rfl fun u _ => ?_
  obtain ⟨δ, h0, h1, h⟩ := tG_comm γ hγ (u.val : ℤ) ((((γ 1 1 : ℤ) : ZMod N) ^ 2 * u).val : ℤ) (by simp)
  rw [SL_smul_slash, h, hf δ h0, h1, smul_slash, tG_σ, smul_smul, smul_smul, hc _ u (hu'.pow 2)]
  congr 1; ring

end UpperTheory.V.Br

/- English proof (translation)
Introduce `N k _ χ ψ f hf`. Take `⟨c, hc1, hc2⟩` from `tw_coeffs ψ`. Establish `hch` using `tw_char k χ ψ hc2 hf`. Use `haveI : NeZero (N * N) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne N)⟩`. Establish `h1 : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods` using `by simp`.

Establish `h2 : (1 : ℝ) ∈ (Gamma1 (N * N) : Subgroup (GL (Fin 2) ℝ)).strictPeriods` using `by simp`. Establish `hsum : ∀ τ : ℍ, HasSum (fun m => coef f m • Function.Periodic.qParam 1 τ ^ m) (f τ)` using `fun τ => hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f h1) f.holo' (ModularFormClass.bdd_at_infty f) τ`. Set `g : CuspForm (Gamma1 (N * N)) (k : ℤ)` to `{ toFun := tw N k c f slash_action_eq' := fun A hA => by`. Take `⟨A, hA, rfl⟩` from `hA`. Establish `h` using `hch A (Gamma1_in_Gamma0 _ hA)`.

Rewrite `h` using `[((Gamma1_mem _ A).1 hA).2.1, map_one, one_smul]`. Conclude with `h`. Use the proof step `holo' := by`. Express the relevant statement in the definitionally equal form `MDiff (tw N k c f)`. Unfold `tw`.

Use `Finset.sum_induction _ (fun F : ℍ → ℂ => MDiff F) (fun a b ha hb => ha.add hb) mdifferentiable_const fun u _ => ?_` and prove the remaining obligations. Conclude with `(MDifferentiable.slash f.holo' _ _).const_smul _`. Use the proof step `zero_at_cusps' := fun {x} hx => by`. Rewrite `hx` using `[Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]`. Rewrite using `[OnePoint.isZeroAt_iff_forall_SL2Z hx]`.

Introduce `γ hγ`. Rewrite using `[tw, SlashAction.sum_slash]`. Use `Submodule.sum_mem (zeroAtImInftySubmodule ℂ) fun u _ => ?_` and prove the remaining obligations. Rewrite using `[SL_smul_slash]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Establish `h3` using `tG_cusp N (u.val : ℤ) hx`. Rewrite `h3` using `[← Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (Gamma1 N : Subgroup (GL (Fin 2) ℝ))]`. Conclude with `OnePoint.IsZeroAt.smul_iff.1 (f.zero_at_cusps' h3) _ hγ }`. Use `⟨g, hch, fun n => ?_⟩` and prove the remaining obligations. Use `(ModularFormClass.qExpansion_coeff_unique (f := g) (c := fun n => ψ (n : ZMod N) * coef f n) one_pos h2 (fun τ => ?_) n).symm` and prove the remaining obligations.

Establish `a` using `hasSum_sum (s := Finset.univ) fun (u : ZMod N) _ => (hsum ((((u.val : ℤ) : ℝ) / N) +ᵥ τ)).mul_left (c u)`. Establish `e : ∑ u : ZMod N, c u * f ((((u.val : ℤ) : ℝ) / N) +ᵥ τ) = tw N k c f τ`. Rewrite using `[tw, Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, tG_apply, smul_eq_mul]`. Rewrite `a` using `[e]`.

Use `cast (congrArg (HasSum · (tw N k c f τ)) (funext fun m => ?_)) a` and prove the remaining obligations. Rewrite using `[← hc1, Finset.sum_mul, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Establish `e2 : ZMod.stdAddChar (u * (m : ZMod N)) * Function.Periodic.qParam 1 τ ^ m = Function.Periodic.qParam 1 (((((u.val : ℤ) : ℝ) / N) +ᵥ τ : ℍ) : ℂ) ^ m`. Establish `: u * (m : ZMod N) = ((u.val * m : ℤ) : ZMod N)` using `by simp`.

Rewrite using `[this, ZMod.stdAddChar_coe, Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, coe_vadd]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e2]`.

Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Br.clTwist :
    UpperTheory.V.Br.ClTwist := by
  intro N k _ χ ψ f hf
  obtain ⟨c, hc1, hc2⟩ := tw_coeffs ψ
  have hch := tw_char k χ ψ hc2 hf
  haveI : NeZero (N * N) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne N)⟩
  have h1 : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have h2 : (1 : ℝ) ∈ (Gamma1 (N * N) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hsum : ∀ τ : ℍ, HasSum (fun m => coef f m • Function.Periodic.qParam 1 τ ^ m) (f τ) := fun τ =>
    hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f h1) f.holo'
      (ModularFormClass.bdd_at_infty f) τ
  let g : CuspForm (Gamma1 (N * N)) (k : ℤ) :=
    { toFun := tw N k c f
      slash_action_eq' := fun A hA => by
        obtain ⟨A, hA, rfl⟩ := hA
        have h := hch A (Gamma1_in_Gamma0 _ hA)
        rw [((Gamma1_mem _ A).1 hA).2.1, map_one, one_smul] at h
        exact h
      holo' := by
        change MDiff (tw N k c f)
        unfold tw
        refine Finset.sum_induction _ (fun F : ℍ → ℂ => MDiff F) (fun a b ha hb => ha.add hb) mdifferentiable_const
          fun u _ => ?_
        exact (MDifferentiable.slash f.holo' _ _).const_smul _
      zero_at_cusps' := fun {x} hx => by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hx
        rw [OnePoint.isZeroAt_iff_forall_SL2Z hx]
        intro γ hγ
        rw [tw, SlashAction.sum_slash]
        refine Submodule.sum_mem (zeroAtImInftySubmodule ℂ) fun u _ => ?_
        rw [SL_smul_slash]
        refine Submodule.smul_mem _ _ ?_
        have h3 := tG_cusp N (u.val : ℤ) hx
        rw [← Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (Gamma1 N : Subgroup (GL (Fin 2) ℝ))] at h3
        exact OnePoint.IsZeroAt.smul_iff.1 (f.zero_at_cusps' h3) _ hγ }
  refine ⟨g, hch, fun n => ?_⟩
  refine (ModularFormClass.qExpansion_coeff_unique (f := g)
    (c := fun n => ψ (n : ZMod N) * coef f n) one_pos h2 (fun τ => ?_) n).symm
  have a := hasSum_sum (s := Finset.univ) fun (u : ZMod N) _ => (hsum ((((u.val : ℤ) : ℝ) / N) +ᵥ τ)).mul_left (c u)
  have e : ∑ u : ZMod N, c u * f ((((u.val : ℤ) : ℝ) / N) +ᵥ τ) = tw N k c f τ := by
    rw [tw, Finset.sum_apply]
    simp only [Pi.smul_apply, tG_apply, smul_eq_mul]
  rw [e] at a
  refine cast (congrArg (HasSum · (tw N k c f τ)) (funext fun m => ?_)) a
  rw [← hc1, Finset.sum_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun u _ => ?_
  have e2 : ZMod.stdAddChar (u * (m : ZMod N)) * Function.Periodic.qParam 1 τ ^ m =
      Function.Periodic.qParam 1 (((((u.val : ℤ) : ℝ) / N) +ᵥ τ : ℍ) : ℂ) ^ m := by
    have : u * (m : ZMod N) = ((u.val * m : ℤ) : ZMod N) := by simp
    rw [this, ZMod.stdAddChar_coe, Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_add, coe_vadd]
    congr 1
    push_cast
    ring
  rw [← e2]
  simp only [smul_eq_mul]
  ring
