import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped Pointwise

namespace PositivityTheory.KB.MeanLatticeAction

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

/- English proof (translation)
Use `haveI : Countable (𝓞 L) := Finsupp.Countable.of_moduleFinite (R := ℤ)`. Use `haveI : Countable (Matrix (Fin N) (Fin N) (𝓞 L)) := inferInstanceAs (Countable (Fin N → Fin N → 𝓞 L))`. Use `haveI : Countable (Matrix.SpecialLinearGroup (Fin N) (𝓞 L)) := by`. Unfold `Matrix.SpecialLinearGroup`. Use `infer_instance`.

Unfold `latS`. Conclude with `(MonoidHom.pi fun w => Matrix.SpecialLinearGroup.map (embO (L := L) w)).rangeRestrict_surjective.countable`.
-/
theorem countable_latS : Countable (latS L N) := by
  haveI : Countable (𝓞 L) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  haveI : Countable (Matrix (Fin N) (Fin N) (𝓞 L)) :=
    inferInstanceAs (Countable (Fin N → Fin N → 𝓞 L))
  haveI : Countable (Matrix.SpecialLinearGroup (Fin N) (𝓞 L)) := by
    unfold Matrix.SpecialLinearGroup; infer_instance
  unfold latS
  exact (MonoidHom.pi fun w => Matrix.SpecialLinearGroup.map (embO (L := L) w)).rangeRestrict_surjective.countable

/- English proof (translation)
Use `haveI := d.haar`. Use `haveI := d.right`. Use `haveI : Countable (latS L N) := countable_latS`. Establish `hmp : MeasurePreserving (fun y : Sp L N => y * s) d.μ d.μ` using `measurePreserving_mul_right d.μ s`. Establish `hemb : MeasurableEmbedding (fun y : Sp L N => y * s)` using `measurableEmbedding_mulRight s`.

Establish `hD' : IsFundamentalDomain (latS L N) ((fun y : Sp L N => y * s) ⁻¹' d.D) d.μ` using `d.fund.preimage_of_equiv hmp.quasiMeasurePreserving Function.bijective_id (fun g x => by simp [Subgroup.smul_def, mul_assoc])`. Use `(d.fund.setIntegral_eq hD' (f := fun y => f (y * s)) ?_).trans (hmp.setIntegral_preimage_emb hemb f d.D)` and prove the remaining obligations. Introduce `g x`. Simplify using `[Subgroup.smul_def, mul_assoc, hf]`.
-/
theorem mean_shift (d : Dom L N) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Sp L N → E)
    (hf : ∀ (g : latS L N) (x : Sp L N), f ((g : Sp L N) * x) = f x) (s : Sp L N) :
    ∫ y in d.D, f (y * s) ∂d.μ = ∫ y in d.D, f y ∂d.μ := by
  haveI := d.haar
  haveI := d.right
  haveI : Countable (latS L N) := countable_latS
  have hmp : MeasurePreserving (fun y : Sp L N => y * s) d.μ d.μ := measurePreserving_mul_right d.μ s
  have hemb : MeasurableEmbedding (fun y : Sp L N => y * s) := measurableEmbedding_mulRight s
  have hD' : IsFundamentalDomain (latS L N) ((fun y : Sp L N => y * s) ⁻¹' d.D) d.μ :=
    d.fund.preimage_of_equiv hmp.quasiMeasurePreserving Function.bijective_id
      (fun g x => by simp [Subgroup.smul_def, mul_assoc])
  refine (d.fund.setIntegral_eq hD' (f := fun y => f (y * s)) ?_).trans
    (hmp.setIntegral_preimage_emb hemb f d.D)
  intro g x
  simp [Subgroup.smul_def, mul_assoc, hf]

/- English proof (translation)
Unfold `fr`. Rewrite using `[h]`.
-/
private theorem fr_eq_of_actL_eq {q : ℕ} (ω : Form (HS L N) q) {x y : Gp L N}
    (h : actL x = actL y) : fr ω x = fr ω y := by
  unfold fr; rw [h]

/- English proof (translation)
Establish `hc : actL (x * u) = (actL x).comp (actL u)`. Use extensionality with `h`. Simplify using `[actL_mul]`. Unfold `fr`. Rewrite using `[hc, ContinuousLinearMap.comp_apply, hu]`.

Use extensionality with `v`. Simplify using `only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.coe_comp']`. Both sides reduce to the same expression.
-/
private theorem fr_mul_eq_comp_actL_of_fixes_one {q : ℕ} (ω : Form (HS L N) q) (x u : Gp L N)
    (hu : actL u (one L N).1 = (one L N).1) :
    fr ω (x * u) = (fr ω x).compContinuousLinearMap (actL u) := by
  have hc : actL (x * u) = (actL x).comp (actL u) := by
    ext h; simp [actL_mul]
  unfold fr
  rw [hc, ContinuousLinearMap.comp_apply, hu]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.coe_comp']
  rfl

/- English proof (translation)
Establish `hc : actL (emb L N γ * x) = (actL (emb L N γ)).comp (actL x)`. Use extensionality with `h`. Simplify using `[actL_mul]`. Establish `hp : actL x (one L N).1 ∈ Pos L N` using `actL_pos x (one L N).2`. Unfold `fr`.

Rewrite using `[hc, ContinuousLinearMap.comp_apply, ← hγ γ _ hp]`. Use extensionality with `v`. Simplify using `only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.coe_comp']`. Both sides reduce to the same expression.
-/
private theorem fr_emb_mul_eq_of_fInv {q : ℕ} (ω : Form (HS L N) q) (hγ : ∀ γ, FInv ω (emb L N γ))
    (γ : Gm L N) (x : Gp L N) : fr ω (emb L N γ * x) = fr ω x := by
  have hc : actL (emb L N γ * x) = (actL (emb L N γ)).comp (actL x) := by
    ext h; simp [actL_mul]
  have hp : actL x (one L N).1 ∈ Pos L N := actL_pos x (one L N).2
  unfold fr
  rw [hc, ContinuousLinearMap.comp_apply, ← hγ γ _ hp]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.coe_comp']
  rfl

/- English proof (translation)
Take `⟨A, rfl⟩` from `hg`. Use `⟨Matrix.SpecialLinearGroup.toGL A, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`.

Both sides reduce to the same expression.
-/
private theorem exists_emb_eq_ofS_of_mem_latS (g : Sp L N) (hg : g ∈ latS L N) :
    ∃ γ : Gm L N, ofS L N g = emb L N γ := by
  obtain ⟨A, rfl⟩ := hg
  refine ⟨Matrix.SpecialLinearGroup.toGL A, ?_⟩
  funext w
  apply Units.ext
  ext i j
  rfl

/- English proof (translation)
Establish `hone : ∀ w, mat ((one L N) : HS L N) w = 1`. Introduce `w`. Unfold `one`. Simplify using `[mat_mkHS]`. Establish `hN0 : N ≠ 0` using `by omega`.

Establish `hV : ∀ w, ((u w)⁻¹).valᴴ * ((u w)⁻¹).val = 1`. Introduce `w`. Use `congrArg (fun h => mat h w) hu` as an intermediate fact. Simplify using `only [mat_actL, hone, Matrix.mul_one] at this`. Conclude with `this`.

Establish `hdet : ∀ w, ‖(u w).val.det‖ = 1`. Introduce `w`. Establish `h1` using `congrArg Matrix.det (hV w)`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one]`. Establish `h2 : ‖((u w)⁻¹).val.det‖ = 1`.

Establish `h3 : ((‖((u w)⁻¹).val.det‖ : ℂ)) ^ 2 = 1`. Rewrite using `[← Complex.conj_mul']`. Simplify using `using h1`. Establish `h4 : ‖((u w)⁻¹).val.det‖ ^ 2 = 1` using `by exact_mod_cast h3`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h4`.

Establish `h5` using `congrArg Matrix.det (Units.mul_inv (u w))`. Rewrite `h5` using `[Matrix.det_mul, Matrix.det_one]`. Establish `h6` using `congrArg norm h5`. Rewrite `h6` using `[norm_mul, h2, mul_one, norm_one]`. Conclude with `h6`.

Use `set c : InfinitePlace L → ℂ := fun w => (u w).val.det ^ ((N : ℂ)⁻¹) with hc`. Establish `hcN : ∀ w, c w ^ N = (u w).val.det` using `fun w => Complex.cpow_nat_inv_pow _ hN0`. Establish `hcn : ∀ w, ‖c w‖ = 1`. Introduce `w`. Establish `h1` using `congrArg norm (hcN w)`.

Rewrite `h1` using `[norm_pow, hdet]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0).mp h1`. Establish `hc0 : ∀ w, c w ≠ 0` using `fun w h => by simpa [h] using hcn w`. Establish `hU0 : ∀ w, (u w).val.det ≠ 0` using `fun w h => by simpa [h] using hdet w`. Set `k : Sp L N` to `fun w => ⟨(c w)⁻¹ • (u w).val, by`.

Rewrite using `[Matrix.det_smul, Fintype.card_fin, inv_pow, hcN, inv_mul_cancel₀ (hU0 w)]⟩`. Use `⟨k, ?_⟩` and prove the remaining obligations. Use extensionality with `h : 1`. Apply `HS_ext` to reduce the goal to its premises. Introduce `w`.

Rewrite using `[mat_actL, mat_actL]`. Establish `hk : ((ofS L N k w)⁻¹).val = c w • ((u w)⁻¹).val`. Rewrite using `[Matrix.coe_units_inv]`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Establish `: (ofS L N k w).val = (c w)⁻¹ • (u w).val` using `rfl`.

Rewrite using `[this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (hc0 w), one_smul]`. Conclude with `Units.inv_mul (u w)`. Establish `hs : c w * star (c w) = 1`. Rewrite using `[mul_comm, show star (c w) = (starRingEnd ℂ) (c w) from rfl, Complex.conj_mul', hcn w]`. Simplify using the standard rewrite rules.

Rewrite using `[hk, Matrix.conjTranspose_smul]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Rewrite using `[hs, one_smul]`.
-/
private theorem exists_ofS_actL_eq_of_fixes_one (hN : 1 ≤ N) (u : Gp L N) (hu : actL u (one L N).1 = (one L N).1) :
    ∃ k : Sp L N, actL u = actL (ofS L N k) := by
  have hone : ∀ w, mat ((one L N) : HS L N) w = 1 := by
    intro w; unfold one; simp [mat_mkHS]
  have hN0 : N ≠ 0 := by omega
  have hV : ∀ w, ((u w)⁻¹).valᴴ * ((u w)⁻¹).val = 1 := by
    intro w
    have := congrArg (fun h => mat h w) hu
    simp only [mat_actL, hone, Matrix.mul_one] at this
    exact this
  have hdet : ∀ w, ‖(u w).val.det‖ = 1 := by
    intro w
    have h1 := congrArg Matrix.det (hV w)
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h1
    have h2 : ‖((u w)⁻¹).val.det‖ = 1 := by
      have h3 : ((‖((u w)⁻¹).val.det‖ : ℂ)) ^ 2 = 1 := by
        rw [← Complex.conj_mul']; simpa using h1
      have h4 : ‖((u w)⁻¹).val.det‖ ^ 2 = 1 := by exact_mod_cast h3
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h4
    have h5 := congrArg Matrix.det (Units.mul_inv (u w))
    rw [Matrix.det_mul, Matrix.det_one] at h5
    have h6 := congrArg norm h5
    rw [norm_mul, h2, mul_one, norm_one] at h6
    exact h6
  set c : InfinitePlace L → ℂ := fun w => (u w).val.det ^ ((N : ℂ)⁻¹) with hc
  have hcN : ∀ w, c w ^ N = (u w).val.det := fun w => Complex.cpow_nat_inv_pow _ hN0
  have hcn : ∀ w, ‖c w‖ = 1 := by
    intro w
    have h1 := congrArg norm (hcN w)
    rw [norm_pow, hdet] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0).mp h1
  have hc0 : ∀ w, c w ≠ 0 := fun w h => by simpa [h] using hcn w
  have hU0 : ∀ w, (u w).val.det ≠ 0 := fun w h => by simpa [h] using hdet w
  let k : Sp L N := fun w => ⟨(c w)⁻¹ • (u w).val, by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hcN, inv_mul_cancel₀ (hU0 w)]⟩
  refine ⟨k, ?_⟩
  ext h : 1
  apply HS_ext
  intro w
  rw [mat_actL, mat_actL]
  have hk : ((ofS L N k w)⁻¹).val = c w • ((u w)⁻¹).val := by
    rw [Matrix.coe_units_inv]
    apply Matrix.inv_eq_left_inv
    have : (ofS L N k w).val = (c w)⁻¹ • (u w).val := rfl
    rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (hc0 w), one_smul]
    exact Units.inv_mul (u w)
  have hs : c w * star (c w) = 1 := by
    rw [mul_comm, show star (c w) = (starRingEnd ℂ) (c w) from rfl, Complex.conj_mul', hcn w]; simp
  rw [hk, Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hs, one_smul]

/- English proof (translation)
Take `⟨k, hk⟩` from `exists_ofS_actL_eq_of_fixes_one hN u hu`. Establish `hinv : ∀ (g : latS L N) (x : Sp L N), fr ω (ofS L N ((g : Sp L N) * x)) = fr ω (ofS L N x)`. Introduce `g x`. Take `⟨γ, hγe⟩` from `exists_emb_eq_ofS_of_mem_latS (g : Sp L N) g.2`. Rewrite using `[map_mul, hγe]`.

Conclude with `fr_emb_mul_eq_of_fInv ω hγ γ _`. Establish `step : ∀ y : Sp L N, (fr ω (ofS L N y)).compContinuousLinearMap (actL u) = fr ω (ofS L N (y * k))`. Introduce `y`. Rewrite using `[← fr_mul_eq_comp_actL_of_fixes_one ω _ u hu]`. Apply `fr_eq_of_actL_eq` to reduce the goal to its premises.

Use extensionality with `h : 1`. Simplify using `[map_mul, actL_mul, hk]`. Establish `hcomm` using `(ContinuousAlternatingMap.compContinuousLinearMapCLM (actL u)).integral_comp_comm hi`. Establish `happ : ∀ F : HS L N [⋀^Fin q]→L[ℝ] ℝ, ContinuousAlternatingMap.compContinuousLinearMapCLM (actL u) F = F.compContinuousLinearMap (actL u)` using `fun F => rfl`. Rewrite `hcomm` using `[happ]`.

Simplify using `only [happ, step] at hcomm`. Rewrite using `[← hcomm]`. Conclude with `mean_shift d (fun y => fr ω (ofS L N y)) hinv k`.
-/
theorem mean_inv (hN : 1 ≤ N) (d : Dom L N) {q : ℕ} (ω : Form (HS L N) q)
    (hγ : ∀ γ, FInv ω (emb L N γ)) (hs : ∀ s, FInv ω (scal L N s))
    (hi : IntegrableOn (fun x => fr ω (ofS L N x)) d.D d.μ) {u : Gp L N}
    (hu : actL u (one L N).1 = (one L N).1) :
    (∫ y in d.D, fr ω (ofS L N y) ∂d.μ).compContinuousLinearMap (actL u) =
      ∫ y in d.D, fr ω (ofS L N y) ∂d.μ := by
  obtain ⟨k, hk⟩ := exists_ofS_actL_eq_of_fixes_one hN u hu
  have hinv : ∀ (g : latS L N) (x : Sp L N),
      fr ω (ofS L N ((g : Sp L N) * x)) = fr ω (ofS L N x) := by
    intro g x
    obtain ⟨γ, hγe⟩ := exists_emb_eq_ofS_of_mem_latS (g : Sp L N) g.2
    rw [map_mul, hγe]
    exact fr_emb_mul_eq_of_fInv ω hγ γ _
  have step : ∀ y : Sp L N, (fr ω (ofS L N y)).compContinuousLinearMap (actL u) =
      fr ω (ofS L N (y * k)) := by
    intro y
    rw [← fr_mul_eq_comp_actL_of_fixes_one ω _ u hu]
    apply fr_eq_of_actL_eq
    ext h : 1
    simp [map_mul, actL_mul, hk]
  have hcomm := (ContinuousAlternatingMap.compContinuousLinearMapCLM (actL u)).integral_comp_comm hi
  have happ : ∀ F : HS L N [⋀^Fin q]→L[ℝ] ℝ,
      ContinuousAlternatingMap.compContinuousLinearMapCLM (actL u) F = F.compContinuousLinearMap (actL u) :=
    fun F => rfl
  rw [happ] at hcomm
  simp only [happ, step] at hcomm
  rw [← hcomm]
  exact mean_shift d (fun y => fr ω (ofS L N y)) hinv k

end PositivityTheory.KB.MeanLatticeAction

namespace PositivityTheory.KB

/- English proof (translation)
Establish `hone : ∀ w, mat ((one L N) : HS L N) w = 1`. Introduce `w`. Unfold `one`. Simplify using `[mat_mkHS]`. Establish `hB : ∀ w, ∃ B : Matrix (Fin N) (Fin N) ℂ, mat h w = Bᴴ * B ∧ IsUnit B.det`.

Introduce `w`. Use `open scoped ComplexOrder MatrixOrder in`. Conclude with `(by`. Establish `hp : (mat h w).PosDef` using `by unfold Pos at hh; exact hh w`. Take `⟨B, hB⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hp.posSemidef.nonneg`.

Use `⟨B, hB, ?_⟩` and prove the remaining obligations. Establish `h1` using `(Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit`. Rewrite `h1` using `[hB, Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_right h1)`. Use `choose B hB hdet using hB`.

Use `⟨fun w => (Matrix.nonsingInvUnit (B w) (hdet w))⁻¹, ?_⟩` and prove the remaining obligations. Apply `HS_ext` to reduce the goal to its premises. Introduce `w`. Rewrite using `[mat_actL, hone, hB w, inv_inv, Matrix.mul_one]`. Both sides reduce to the same expression.
-/
private theorem exists_actL_one_eq_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hh : h ∈ Pos L N) : ∃ x : Gp L N, actL x (one L N).1 = h := by
  have hone : ∀ w, mat ((one L N) : HS L N) w = 1 := by
    intro w; unfold one; simp [mat_mkHS]
  have hB : ∀ w, ∃ B : Matrix (Fin N) (Fin N) ℂ, mat h w = Bᴴ * B ∧ IsUnit B.det := by
    intro w
    open scoped ComplexOrder MatrixOrder in
    exact (by
      have hp : (mat h w).PosDef := by unfold Pos at hh; exact hh w
      obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hp.posSemidef.nonneg
      refine ⟨B, hB, ?_⟩
      have h1 := (Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit
      rw [hB, Matrix.det_mul] at h1
      exact isUnit_of_mul_isUnit_right h1)
  choose B hB hdet using hB
  refine ⟨fun w => (Matrix.nonsingInvUnit (B w) (hdet w))⁻¹, ?_⟩
  apply HS_ext
  intro w
  rw [mat_actL, hone, hB w, inv_inv, Matrix.mul_one]
  rfl

/- English proof (translation)
Introduce `L _ _ N q hN d ω _hc hγ hs hi`. Establish `hmul : ∀ (a b : Gp L N) (t : HS L N), actL a (actL b t) = actL (a * b) t` using `fun a b t => (actL_mul a b t).symm`. Use `set I := ∫ y in d.D, fr ω (ofS L N y) ∂d.μ with hI`. Use `set M : HS L N [⋀^Fin q]→L[ℝ] ℝ := (d.μ.real d.D)⁻¹ • I with hM0`. Establish `hM : ∀ u : Gp L N, actL u (one L N).1 = (one L N).1 → M.compContinuousLinearMap (actL u) = M`.

Introduce `u hu`. Establish `h1` using `MeanLatticeAction.mean_inv hN d ω hγ hs hi hu`. Use extensionality with `v`. Establish `h2` using `congrArg (fun F : HS L N [⋀^Fin q]→L[ℝ] ℝ => F v) h1`. Simplify using `only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h2`.

Simplify using `only [M, ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.smul_apply]`. Rewrite using `[hI, h2]`. Set `ωb : Form (HS L N) q` to `fun h => if hx : ∃ x : Gp L N, actL x (one L N).1 = h then M.compContinuousLinearMap (actL hx.choose⁻¹) else 0`. Establish `hωb : ∀ z : Gp L N, ωb (actL z (one L N).1) = M.compContinuousLinearMap (actL z⁻¹)`. Introduce `z`.

Establish `hx : ∃ x : Gp L N, actL x (one L N).1 = actL z (one L N).1` using `⟨z, rfl⟩`. Simplify using `only [ωb, dif_pos hx]`. Establish `hy : actL hx.choose (one L N).1 = actL z (one L N).1` using `hx.choose_spec`. Generalize the expression as in `hx.choose = y at hy ⊢`. Establish `hs1 : actL (y⁻¹ * z) (one L N).1 = (one L N).1`.

Rewrite using `[← hmul, ← hy, hmul, inv_mul_cancel, actL_one]`. Use `conv_rhs => rw [← hM _ hs1]`. Use extensionality with `v`. Simplify using `only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hmul]`. Simplify using `[mul_assoc]`.

Use `⟨ωb, ?_, ?_⟩` and prove the remaining obligations. Introduce `g h hh`. Take `⟨x, rfl⟩` from `exists_actL_one_eq_of_mem_Pos h hh`. Rewrite using `[hmul, hωb, hωb]`. Use extensionality with `v`.

Simplify using `only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hmul]`. Simplify using `[mul_assoc]`. Introduce `x`. Unfold `fr`. Rewrite using `[hωb]`.

Use extensionality with `v`. Simplify using `only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hmul]`. Simplify using `[actL_one]`.
-/
theorem sMean_of : SMean := by
  intro L _ _ N q hN d ω _hc hγ hs hi
  have hmul : ∀ (a b : Gp L N) (t : HS L N), actL a (actL b t) = actL (a * b) t :=
    fun a b t => (actL_mul a b t).symm
  set I := ∫ y in d.D, fr ω (ofS L N y) ∂d.μ with hI
  set M : HS L N [⋀^Fin q]→L[ℝ] ℝ := (d.μ.real d.D)⁻¹ • I with hM0
  have hM : ∀ u : Gp L N, actL u (one L N).1 = (one L N).1 →
      M.compContinuousLinearMap (actL u) = M := by
    intro u hu
    have h1 := MeanLatticeAction.mean_inv hN d ω hγ hs hi hu
    ext v
    have h2 := congrArg (fun F : HS L N [⋀^Fin q]→L[ℝ] ℝ => F v) h1
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h2
    simp only [M, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.smul_apply]
    rw [hI, h2]
  classical
  let ωb : Form (HS L N) q := fun h =>
    if hx : ∃ x : Gp L N, actL x (one L N).1 = h then M.compContinuousLinearMap (actL hx.choose⁻¹)
    else 0
  have hωb : ∀ z : Gp L N, ωb (actL z (one L N).1) = M.compContinuousLinearMap (actL z⁻¹) := by
    intro z
    have hx : ∃ x : Gp L N, actL x (one L N).1 = actL z (one L N).1 := ⟨z, rfl⟩
    simp only [ωb, dif_pos hx]
    have hy : actL hx.choose (one L N).1 = actL z (one L N).1 := hx.choose_spec
    generalize hx.choose = y at hy ⊢
    have hs1 : actL (y⁻¹ * z) (one L N).1 = (one L N).1 := by
      rw [← hmul, ← hy, hmul, inv_mul_cancel, actL_one]
    conv_rhs => rw [← hM _ hs1]
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hmul]
    simp [mul_assoc]
  refine ⟨ωb, ?_, ?_⟩
  · intro g h hh
    obtain ⟨x, rfl⟩ := exists_actL_one_eq_of_mem_Pos h hh
    rw [hmul, hωb, hωb]
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hmul]
    simp [mul_assoc]
  · intro x
    unfold fr
    rw [hωb]
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hmul]
    simp [actL_one]

end PositivityTheory.KB
