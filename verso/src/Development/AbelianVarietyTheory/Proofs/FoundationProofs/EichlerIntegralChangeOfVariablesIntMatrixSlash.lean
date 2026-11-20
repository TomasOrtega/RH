import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromISlashChangeOfVariables
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
noncomputable section
namespace GlobalTheory.EichlerChangeGL
open GlobalTheory.EichlerChange

/- English proof (translation)
Unfold `toGL`. Rewrite using `[dif_neg h]`. Both sides reduce to the same expression.
-/
lemma toGL_entry (g : Matrix (Fin 2) (Fin 2) ℤ) (h : g.det ≠ 0) (i j : Fin 2) :
    (toGL g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  unfold toGL; rw [dif_neg h]; rfl

/- English proof (translation)
Apply the tactic sequence `rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two, toGL_entry g h, toGL_entry g h, toGL_entry g h, toGL_entry g h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma toGL_det (g : Matrix (Fin 2) (Fin 2) ℤ) (h : g.det ≠ 0) :
    (toGL g).det.val = ((g.det : ℤ) : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two,
    toGL_entry g h, toGL_entry g h, toGL_entry g h, toGL_entry g h]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[toGL_det g h.ne']`. Conclude with `h` after adjusting the coercions.
-/
lemma toGL_det_pos (g : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < g.det) : 0 < (toGL g).det.val := by
  rw [toGL_det g h.ne']
  exact_mod_cast h

/- English proof (translation)
Apply the tactic sequence `rw [denom, toGL_entry g h, toGL_entry g h]`. Simplify using the standard rewrite rules.
-/
lemma denom_toGL (g : Matrix (Fin 2) (Fin 2) ℤ) (h : g.det ≠ 0) (z : ℂ) :
    denom (toGL g) z = ((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ) := by
  rw [denom, toGL_entry g h, toGL_entry g h]
  simp

/- English proof (translation)
Apply the tactic sequence `rw [coe_smul_of_det_pos (toGL_det_pos g h), denom_toGL g h.ne', num, toGL_entry g h.ne', toGL_entry g h.ne']`. Simplify using the standard rewrite rules.
-/
lemma coe_toGL_smul (g : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < g.det) (τ : ℍ) :
    ((toGL g • τ : ℍ) : ℂ) = (((g 0 0 : ℤ) : ℂ) * τ + ((g 0 1 : ℤ) : ℂ)) /
      (((g 1 0 : ℤ) : ℂ) * τ + ((g 1 1 : ℤ) : ℂ)) := by
  rw [coe_smul_of_det_pos (toGL_det_pos g h), denom_toGL g h.ne', num, toGL_entry g h.ne',
    toGL_entry g h.ne']
  simp

/- English proof (translation)
Establish `hpos` using `toGL_det_pos g h`. Rewrite using `[ModularForm.slash_apply, σ, if_pos hpos, abs_of_pos hpos, toGL_det g h.ne', denom_toGL g h.ne']`. Simplify using the standard rewrite rules.
-/
lemma slash_toGL (k : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < g.det) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] toGL g) τ = f (toGL g • τ) * ((g.det : ℤ) : ℂ) ^ (k - 1) *
      (((g 1 0 : ℤ) : ℂ) * τ + ((g 1 1 : ℤ) : ℂ)) ^ (-k) := by
  have hpos := toGL_det_pos g h
  rw [ModularForm.slash_apply, σ, if_pos hpos, abs_of_pos hpos, toGL_det g h.ne', denom_toGL g h.ne']
  simp

/- English proof (translation)
Simplify using `[eichler]`.
-/
lemma eichler_I (w : ℕ) (h : ℍ → ℂ) : eichler w h UpperHalfPlane.I = 0 := by
  simp [eichler]

/- English proof (translation)
Introduce `k hk f hf β hβ τ`. Take `⟨w, rfl⟩ : ∃ w, k = w + 2` from `⟨k - 2, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Use `set h : ℍ → ℂ := f ∣[((w + 2 : ℕ) : ℤ)] toGL β with hdef`. Establish `hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h` using `hf.slash _ _`.

Use `set a : ℂ := ((β 0 0 : ℤ) : ℂ) with ha`. Use `set b : ℂ := ((β 0 1 : ℤ) : ℂ) with hb`. Use `set c : ℂ := ((β 1 0 : ℤ) : ℂ) with hc`. Use `set d : ℂ := ((β 1 1 : ℤ) : ℂ) with hd`. Use `set D : ℂ := ((β.det : ℤ) : ℂ) with hD`.

Establish `hdet : a * d - b * c = D`. Rewrite using `[ha, hb, hc, hd, hD, Matrix.det_fin_two]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `n`.

Use `set q : ℕ → ℂ := fun i => ((C a * X + C b) ^ i * (C c * X + C d) ^ (w - i)).coeff n with hq`. Establish `hslP : ∀ p : ℂ[X], (slP w β p).coeff n = ∑ i ∈ Finset.range (w + 1), p.coeff i * q i`. Introduce `p`. Rewrite using `[polySlash_apply, finset_sum_coeff]`. Simplify using `only [coeff_smul, smul_eq_mul]`.

Both sides reduce to the same expression. Use `set Φ : ℂ → ℂ := fun v => ∑ i ∈ Finset.range (w + 1), (w.choose i : ℂ) * ecoef w f i ((a * v + b) / (c * v + d)) * q i - (w.choose n : ℂ) * ecoef w h n v with hΦ`. Establish `hΦ1 : ∀ τ : ℍ, Φ τ = (slP w β (eichler w f (toGL β • τ))).coeff n - (eichler w h τ).coeff n`. Introduce `τ`. Simplify using `only [hΦ, hslP, coeff_eichler, coe_toGL_smul β hβ]`.

Both sides reduce to the same expression. Establish `hder : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt Φ 0 z`. Introduce `z hz`. Take `⟨τ, rfl⟩ : ∃ τ : ℍ, (τ : ℂ) = z` from `⟨⟨z, hz⟩, rfl⟩`. Establish `hj : c * τ + d ≠ 0`.

Rewrite using `[hc, hd, ← denom_toGL β hβ.ne']`. Conclude with `denom_ne_zero _ _`. Establish `hs : ((toGL β • τ : ℍ) : ℂ) = (a * τ + b) / (c * τ + d)` using `coe_toGL_smul β hβ τ`. Establish `hm : HasDerivAt (fun v : ℂ => (a * v + b) / (c * v + d)) (D * (c * τ + d)⁻¹ ^ 2) (τ : ℂ)`. Establish `h1 : HasDerivAt (fun v : ℂ => a * v + b) a (τ : ℂ)`.

Simplify using `using ((hasDerivAt_id (τ : ℂ)).const_mul a).add_const b`. Establish `h2 : HasDerivAt (fun v : ℂ => c * v + d) c (τ : ℂ)`. Simplify using `using ((hasDerivAt_id (τ : ℂ)).const_mul c).add_const d`. Use `(h1.fun_div h2 hj).congr_deriv ?_` and prove the remaining obligations. Rewrite using `[inv_pow, div_eq_mul_inv]`.

Take the linear combination `((c * τ + d) ^ 2)⁻¹ * hdet`. Establish `hA : ∀ i, HasDerivAt (fun v : ℂ => ecoef w f i ((a * v + b) / (c * v + d))) (f (toGL β • τ) * (-((toGL β • τ : ℍ) : ℂ)) ^ (w - i) * (D * (c * τ + d)⁻¹ ^ 2)) (τ : ℂ)`. Introduce `i`. Use `hasDerivAt_ecoef w f hf i _ (toGL β • τ).im_pos` as an intermediate fact. Simplify using `only [Function.comp_apply, ofComplex_apply] at this`.

Conclude with `HasDerivAt.comp (τ : ℂ) (h₂ := ecoef w f i) (by rw [← hs]; exact this) hm`. Establish `hB` using `hasDerivAt_ecoef w h hh n _ τ.im_pos`. Simplify using `only [Function.comp_apply, ofComplex_apply] at hB`. Establish `hP` using `congrArg (fun p : ℂ[X] => p.coeff n) (polySlash_pow w β ((toGL β • τ : ℍ) : ℂ) τ (D * (c * τ + d)⁻¹) (by rw [hs, ← ha, ← hc]; rw [div_eq_mul_inv]`. Take the linear combination `(-a) * mul_inv_cancel₀ hj + (c * τ + d)⁻¹ * hdet)`.

Use the proof step `(by rw [hs, ← hb, ← hd]; rw [div_eq_mul_inv]`. Take the linear combination `(-b) * mul_inv_cancel₀ hj - (c * τ + d)⁻¹ * τ * hdet))`. Simplify using `only [hslP, coeff_C_mul, coeff_X_add_C_pow] at hP`. Establish `hv : h τ = f (toGL β • τ) * D ^ (w + 1) * (c * τ + d)⁻¹ ^ (w + 2)`. Establish `e : ((w + 2 : ℕ) : ℤ) - 1 = ((w + 1 : ℕ) : ℤ)` using `by push_cast; ring`.

Rewrite using `[hdef, slash_toGL _ β hβ, e, zpow_neg, zpow_natCast, zpow_natCast, inv_pow]`. Use `((HasDerivAt.fun_sum (u := Finset.range (w + 1)) fun i _ => ((hA i).const_mul (w.choose i : ℂ)).mul_const (q i)).fun_sub (hB.const_mul (w.choose n : ℂ))).congr_deriv ?_` and prove the remaining obligations. Establish `: ∑ i ∈ Finset.range (w + 1), (w.choose i : ℂ) * (f (toGL β • τ) * (-((toGL β • τ : ℍ) : ℂ)) ^ (w - i) * (D * (c * τ + d)⁻¹ ^ 2)) * q i = f (toGL β • τ) * (D * (c * τ + d)⁻¹ ^ 2) * ∑ i ∈ Finset.range (w + 1), (-((toGL β • τ : ℍ) : ℂ)) ^ (w - i) * (w.choose i : ℂ) * q i`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.

Rewrite using `[this, hP, hv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hconst : Φ τ = Φ (I : ℍ)` using `isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero (convex_halfSpace_im_gt 0).isPreconnected (fun z hz => (hder z hz).differentiableAt.differentiableWithinAt) (fun z hz => (hder z hz).deriv) τ.im_pos (I : ℍ).im_pos`. Rewrite `hconst` using `[hΦ1, hΦ1, eichler_I, coeff_zero]`. Rewrite using `[coeff_add]`.

Take the linear combination `hconst`.
-/
theorem polySlash_eichler_toGL_smul : ∀ (k : ℕ), 2 ≤ k → ∀ (f : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
    ∀ (β : Matrix (Fin 2) (Fin 2) ℤ), 0 < β.det → ∀ τ : ℍ,
      slP (k - 2) β (eichler (k - 2) f (toGL β • τ)) = eichler (k - 2) (f ∣[(k : ℤ)] toGL β) τ +
        slP (k - 2) β (eichler (k - 2) f (toGL β • UpperHalfPlane.I)) := by
  intro k hk f hf β hβ τ
  obtain ⟨w, rfl⟩ : ∃ w, k = w + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  set h : ℍ → ℂ := f ∣[((w + 2 : ℕ) : ℤ)] toGL β with hdef
  have hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := hf.slash _ _
  set a : ℂ := ((β 0 0 : ℤ) : ℂ) with ha
  set b : ℂ := ((β 0 1 : ℤ) : ℂ) with hb
  set c : ℂ := ((β 1 0 : ℤ) : ℂ) with hc
  set d : ℂ := ((β 1 1 : ℤ) : ℂ) with hd
  set D : ℂ := ((β.det : ℤ) : ℂ) with hD
  have hdet : a * d - b * c = D := by
    rw [ha, hb, hc, hd, hD, Matrix.det_fin_two]
    push_cast
    ring
  ext n
  set q : ℕ → ℂ := fun i => ((C a * X + C b) ^ i * (C c * X + C d) ^ (w - i)).coeff n with hq
  have hslP : ∀ p : ℂ[X], (slP w β p).coeff n = ∑ i ∈ Finset.range (w + 1), p.coeff i * q i := by
    intro p
    rw [polySlash_apply, finset_sum_coeff]
    simp only [coeff_smul, smul_eq_mul]
    rfl
  set Φ : ℂ → ℂ := fun v => ∑ i ∈ Finset.range (w + 1),
      (w.choose i : ℂ) * ecoef w f i ((a * v + b) / (c * v + d)) * q i -
    (w.choose n : ℂ) * ecoef w h n v with hΦ
  have hΦ1 : ∀ τ : ℍ, Φ τ =
      (slP w β (eichler w f (toGL β • τ))).coeff n - (eichler w h τ).coeff n := by
    intro τ
    simp only [hΦ, hslP, coeff_eichler, coe_toGL_smul β hβ]
    rfl
  have hder : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt Φ 0 z := by
    intro z hz
    obtain ⟨τ, rfl⟩ : ∃ τ : ℍ, (τ : ℂ) = z := ⟨⟨z, hz⟩, rfl⟩
    have hj : c * τ + d ≠ 0 := by
      rw [hc, hd, ← denom_toGL β hβ.ne']
      exact denom_ne_zero _ _
    have hs : ((toGL β • τ : ℍ) : ℂ) = (a * τ + b) / (c * τ + d) := coe_toGL_smul β hβ τ
    have hm : HasDerivAt (fun v : ℂ => (a * v + b) / (c * v + d)) (D * (c * τ + d)⁻¹ ^ 2) (τ : ℂ) := by
      have h1 : HasDerivAt (fun v : ℂ => a * v + b) a (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul a).add_const b
      have h2 : HasDerivAt (fun v : ℂ => c * v + d) c (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).const_mul c).add_const d
      refine (h1.fun_div h2 hj).congr_deriv ?_
      rw [inv_pow, div_eq_mul_inv]
      linear_combination ((c * τ + d) ^ 2)⁻¹ * hdet
    have hA : ∀ i, HasDerivAt (fun v : ℂ => ecoef w f i ((a * v + b) / (c * v + d)))
        (f (toGL β • τ) * (-((toGL β • τ : ℍ) : ℂ)) ^ (w - i) * (D * (c * τ + d)⁻¹ ^ 2)) (τ : ℂ) := by
      intro i
      have := hasDerivAt_ecoef w f hf i _ (toGL β • τ).im_pos
      simp only [Function.comp_apply, ofComplex_apply] at this
      exact HasDerivAt.comp (τ : ℂ) (h₂ := ecoef w f i) (by rw [← hs]; exact this) hm
    have hB := hasDerivAt_ecoef w h hh n _ τ.im_pos
    simp only [Function.comp_apply, ofComplex_apply] at hB
    have hP := congrArg (fun p : ℂ[X] => p.coeff n)
      (polySlash_pow w β ((toGL β • τ : ℍ) : ℂ) τ (D * (c * τ + d)⁻¹)
        (by rw [hs, ← ha, ← hc]; rw [div_eq_mul_inv]
            linear_combination (-a) * mul_inv_cancel₀ hj + (c * τ + d)⁻¹ * hdet)
        (by rw [hs, ← hb, ← hd]; rw [div_eq_mul_inv]
            linear_combination (-b) * mul_inv_cancel₀ hj - (c * τ + d)⁻¹ * τ * hdet))
    simp only [hslP, coeff_C_mul, coeff_X_add_C_pow] at hP
    have hv : h τ = f (toGL β • τ) * D ^ (w + 1) * (c * τ + d)⁻¹ ^ (w + 2) := by
      have e : ((w + 2 : ℕ) : ℤ) - 1 = ((w + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hdef, slash_toGL _ β hβ, e, zpow_neg, zpow_natCast, zpow_natCast, inv_pow]
    refine ((HasDerivAt.fun_sum (u := Finset.range (w + 1)) fun i _ =>
      ((hA i).const_mul (w.choose i : ℂ)).mul_const (q i)).fun_sub
        (hB.const_mul (w.choose n : ℂ))).congr_deriv ?_
    have : ∑ i ∈ Finset.range (w + 1), (w.choose i : ℂ) *
        (f (toGL β • τ) * (-((toGL β • τ : ℍ) : ℂ)) ^ (w - i) * (D * (c * τ + d)⁻¹ ^ 2)) * q i =
        f (toGL β • τ) * (D * (c * τ + d)⁻¹ ^ 2) * ∑ i ∈ Finset.range (w + 1),
          (-((toGL β • τ : ℍ) : ℂ)) ^ (w - i) * (w.choose i : ℂ) * q i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hP, hv]
    ring
  have hconst : Φ τ = Φ (I : ℍ) :=
    isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero (convex_halfSpace_im_gt 0).isPreconnected
      (fun z hz => (hder z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hder z hz).deriv) τ.im_pos (I : ℍ).im_pos
  rw [hΦ1, hΦ1, eichler_I, coeff_zero] at hconst
  rw [coeff_add]
  linear_combination hconst

end GlobalTheory.EichlerChangeGL
