import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt

open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Af.Nf

/- English proof (translation)
Establish `h : (((g.val 0 0 : ℝ) : ℂ) * z + g.val 0 1) / (((g.val 1 0 : ℝ) : ℂ) * z + g.val 1 1) = ((g • z : ℍ) : ℂ)`. Rewrite using `[coe_smul_of_det_pos (by simpa using hg)]`. Both sides reduce to the same expression. Unfold `nsl`. Rewrite using `[h, sign_pos hg, abs_of_pos hg]`.

Simplify using `only [SignType.coe_one, Complex.ofReal_one, one_mul, ofComplex_apply, mul_assoc]`. Both sides reduce to the same expression.
-/
private theorem nsl_pos (k : ℕ) (f : ℍ → ℂ) (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (z : ℍ) :
    nsl k f g z = ((g.val.det ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (denom g z ^ (-(k : ℤ)) * f (g • z)) := by
  have h : (((g.val 0 0 : ℝ) : ℂ) * z + g.val 0 1) / (((g.val 1 0 : ℝ) : ℂ) * z + g.val 1 1) = ((g • z : ℍ) : ℂ) := by
    rw [coe_smul_of_det_pos (by simpa using hg)]
    rfl
  unfold nsl
  rw [h, sign_pos hg, abs_of_pos hg]
  simp only [SignType.coe_one, Complex.ofReal_one, one_mul, ofComplex_apply, mul_assoc]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `hσ : σ x (f (x • z)) = f (x • z)` using `by simp [σ, hx]`. Establish `hr : x.val.det ^ ((k : ℝ) / 2) = x.val.det ^ (1 - (k : ℝ) / 2) * x.val.det ^ ((k : ℤ) - 1)`. Rewrite using `[← Real.rpow_intCast, ← Real.rpow_add hx]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[nsl_pos k f x hx, Pi.smul_apply, ModularForm.slash_apply, hσ, Matrix.GeneralLinearGroup.val_det_apply, abs_of_pos hx, hr, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem nsl_slash (k : ℕ) (f : ℍ → ℂ) (x : GL (Fin 2) ℝ) (hx : 0 < x.val.det) :
    nsl k f x = (((x.val.det ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)) • f ∣[(k : ℤ)] x := by
  funext z
  have hσ : σ x (f (x • z)) = f (x • z) := by simp [σ, hx]
  have hr : x.val.det ^ ((k : ℝ) / 2) = x.val.det ^ (1 - (k : ℝ) / 2) * x.val.det ^ ((k : ℤ) - 1) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add hx]
    congr 1
    push_cast
    ring
  rw [nsl_pos k f x hx, Pi.smul_apply, ModularForm.slash_apply, hσ, Matrix.GeneralLinearGroup.val_det_apply,
    abs_of_pos hx, hr, smul_eq_mul]
  push_cast
  ring

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `hd : (eps * x).det = -x.det` using `by rw [Matrix.det_mul]; simp [eps]`. Establish `h0 : ∀ j, (eps * x) 0 j = -x 0 j` using `fun j => by simp [eps, Matrix.mul_apply]`. Establish `h1 : ∀ j, (eps * x) 1 j = x 1 j` using `fun j => by simp [eps, Matrix.mul_apply]`. Unfold `nsl`.

Rewrite using `[hd, h0, h0, h1, h1, abs_neg, Left.sign_neg]`. Use `congr 3`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem nsl_eps (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) : nsl k f (eps * x) = nsl k f x := by
  funext z
  have hd : (eps * x).det = -x.det := by rw [Matrix.det_mul]; simp [eps]
  have h0 : ∀ j, (eps * x) 0 j = -x 0 j := fun j => by simp [eps, Matrix.mul_apply]
  have h1 : ∀ j, (eps * x) 1 j = x 1 j := fun j => by simp [eps, Matrix.mul_apply]
  unfold nsl
  rw [hd, h0, h0, h1, h1, abs_neg, Left.sign_neg]
  congr 3
  push_cast
  ring

/- English proof (translation)
Set `g : GL (Fin 2) ℝ` to `Matrix.GeneralLinearGroup.mkOfDetNeZero x hx.ne'`. Establish `hg : 0 < g.val.det` using `hx`. Establish `: nsl k f x = fun z : ℍ => ((g.val.det ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (denom g z ^ (-(k : ℤ)) * f (g • z))`. Use function extensionality and compare the values at `(nsl_pos k f g hg)`. Rewrite using `[this]`.

Conclude with `mdifferentiable_const.mul ((mdifferentiable_denom_zpow g _).mul (hf.comp (mdifferentiable_smul (by simpa using hg))))`.
-/
private theorem nsl_mdiff_pos (k : ℕ) (f : ℍ → ℂ) (hf : MDiff f) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < x.det) :
    MDiff (nsl k f x) := by
  let g : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx.ne'
  have hg : 0 < g.val.det := hx
  have : nsl k f x = fun z : ℍ => ((g.val.det ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (denom g z ^ (-(k : ℤ)) * f (g • z)) :=
    funext (nsl_pos k f g hg)
  rw [this]
  exact mdifferentiable_const.mul ((mdifferentiable_denom_zpow g _).mul
    (hf.comp (mdifferentiable_smul (by simpa using hg))))

end UpperTheory.V.Af.Nf

/- English proof (translation)
Introduce `k f`. Use `⟨fun δ => ?_, nsl_slash k f, fun hf x hx => ?_⟩` and prove the remaining obligations. Establish `hv : (δ : GL (Fin 2) ℝ).val = δ.1.map (Int.cast : ℤ → ℝ)` using `rfl`. Establish `hd : (δ : GL (Fin 2) ℝ).val.det = 1` using `(Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) δ).det_coe`. Rewrite using `[← hv, nsl_slash k f _ (by rw [hd]; exact one_pos), hd, ModularForm.SL_slash]`.

Simplify using the standard rewrite rules. Break down `hx.lt_or_gt with h | h` into its components or cases. Rewrite using `[← nsl_eps]`. Use `nsl_mdiff_pos k f hf _ ?_` and prove the remaining obligations. Establish `hd : (eps * x).det = -x.det` using `by rw [Matrix.det_mul]; simp [eps]`.

Rewrite using `[hd]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `nsl_mdiff_pos k f hf x h`.
-/
theorem UpperTheory.V.Af.Nf.nslSl :
    UpperTheory.V.Af.Nf.NslSl := by
  intro k f
  refine ⟨fun δ => ?_, nsl_slash k f, fun hf x hx => ?_⟩
  · have hv : (δ : GL (Fin 2) ℝ).val = δ.1.map (Int.cast : ℤ → ℝ) := rfl
    have hd : (δ : GL (Fin 2) ℝ).val.det = 1 :=
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) δ).det_coe
    rw [← hv, nsl_slash k f _ (by rw [hd]; exact one_pos), hd, ModularForm.SL_slash]
    simp
  · rcases hx.lt_or_gt with h | h
    · rw [← nsl_eps]
      refine nsl_mdiff_pos k f hf _ ?_
      have hd : (eps * x).det = -x.det := by rw [Matrix.det_mul]; simp [eps]
      rw [hd]; linarith
    · exact nsl_mdiff_pos k f hf x h
