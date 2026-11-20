import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

/- English proof (translation)
Set `g : SL(2, ℤ)` to `⟨!![A, B; C, D], by simp [Matrix.det_fin_two_of]; linarith⟩`. Establish `hg : g ∈ lev N l`. Apply the tactic sequence `refine Subgroup.mem_inf.2 ⟨(Gamma1_mem N g).2 ⟨?_, ?_, ?_⟩, Gamma0_mem.2 ?_⟩ <;> simpa [g]`. Set `w : ℍ` to `⟨z, hz⟩`. Establish `h1` using `congrFun (hf g hg) w`.

Rewrite `h1` using `[SL_slash_apply]`. Establish `hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (w : ℂ) = C * z + D`. Establish `e1 : g 1 0 = C` using `rfl`. Establish `e2 : g 1 1 = D` using `rfl`. Use `(show denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (w : ℂ) = ((g 1 0 : ℤ) : ℂ) * z + (g 1 1 : ℤ) by` as an intermediate fact.

Simplify using `[denom, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, w])`. Rewrite using `[this, e1, e2]`. Establish `hsm : ((g • w : ℍ) : ℂ) = (A * z + B) / (C * z + D)`. Rewrite using `[specialLinearGroup_apply]`. Simplify using `[g, w]`.

Establish `hne : (C * z + D : ℂ) ≠ 0` using `by rw [← hden]; exact denom_ne_zero _ _`. Rewrite `h1` using `[hden]`. Establish `hw : ofComplex z = w` using `ofComplex_apply_of_im_pos hz`. Rewrite using `[← hsm, ofComplex_apply, hw, ← h1, zpow_neg]`. Clear the denominators using the available nonvanishing facts.
-/
theorem lev_transform {N l : ℕ} {k : ℤ} {f : ℍ → ℂ}
    (hf : ∀ γ ∈ lev N l, f ∣[k] γ = f) (A B C D : ℤ) (hdet : A * D - B * C = 1)
    (hA : (A : ZMod N) = 1) (hD : (D : ZMod N) = 1) (hCN : (C : ZMod N) = 0)
    (hCl : (C : ZMod l) = 0) (z : ℂ) (hz : 0 < z.im) :
    f (ofComplex ((A * z + B) / (C * z + D))) = (C * z + D) ^ k * f (ofComplex z) := by
  let g : SL(2, ℤ) := ⟨!![A, B; C, D], by simp [Matrix.det_fin_two_of]; linarith⟩
  have hg : g ∈ lev N l := by
    refine Subgroup.mem_inf.2 ⟨(Gamma1_mem N g).2 ⟨?_, ?_, ?_⟩, Gamma0_mem.2 ?_⟩ <;> simpa [g]
  let w : ℍ := ⟨z, hz⟩
  have h1 := congrFun (hf g hg) w
  rw [SL_slash_apply] at h1
  have hden : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (w : ℂ) = C * z + D := by
    have e1 : g 1 0 = C := rfl
    have e2 : g 1 1 = D := rfl
    have := (show denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (w : ℂ) = ((g 1 0 : ℤ) : ℂ) * z + (g 1 1 : ℤ) by
      simp [denom, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, w])
    rw [this, e1, e2]
  have hsm : ((g • w : ℍ) : ℂ) = (A * z + B) / (C * z + D) := by
    rw [specialLinearGroup_apply]; simp [g, w]
  have hne : (C * z + D : ℂ) ≠ 0 := by rw [← hden]; exact denom_ne_zero _ _
  rw [hden] at h1
  have hw : ofComplex z = w := ofComplex_apply_of_im_pos hz
  rw [← hsm, ofComplex_apply, hw, ← h1, zpow_neg]
  field_simp

/- English proof (translation)
Establish `h` using `lev_transform hf 1 1 0 1 (by norm_num) (by simp) (by simp) (by simp) (by simp) z hz`. Simplify using `using h`.
-/
theorem lev_periodic {N l : ℕ} {k : ℤ} {f : ℍ → ℂ}
    (hf : ∀ γ ∈ lev N l, f ∣[k] γ = f) (z : ℂ) (hz : 0 < z.im) :
    f (ofComplex (z + 1)) = f (ofComplex z) := by
  have h := lev_transform hf 1 1 0 1 (by norm_num) (by simp) (by simp) (by simp) (by simp) z hz
  simpa using h

/- English proof (translation)
Use `haveI : NeZero q := ⟨hq.ne'⟩`. Set `G : ZMod q → ℂ` to `fun x => F (x.val : ℤ)`. Establish `hFG : ∀ m : ℤ, F m = G m`. Introduce `m`. Simplify using `only [G, ZMod.val_intCast]`.

Use `(hF.int_mul (m / q)) (m % q)` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Rewrite using `[Int.cast_id]`. Take the linear combination `(Int.mul_ediv_add_emod m q).symm`.

Establish `hsum : ∀ H : ZMod q → ℂ, ∑ j ∈ Finset.range q, H (j : ZMod q) = ∑ x, H x`. Introduce `H`. Use `symm`. Use `Finset.sum_bij' (fun x _ => x.val) (fun j _ => (j : ZMod q)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x _`.

Conclude with `Finset.mem_range.2 (ZMod.val_lt x)`. Introduce `j _`. Conclude with `Finset.mem_univ _`. Introduce `x _`. Conclude with `ZMod.natCast_zmod_val x`.

Introduce `j hj`. Conclude with `ZMod.val_cast_of_lt (Finset.mem_range.1 hj)`. Introduce `x _`. Rewrite using `[ZMod.natCast_zmod_val]`. Take `⟨w, hw⟩` from `hu`.

Establish `hbij : Function.Bijective (fun x : ZMod q => (v : ZMod q) + u * x)`. Use `Finite.injective_iff_bijective.1 ?_` and prove the remaining obligations. Introduce `x y hxy`. Establish `: (u : ZMod q) * x = u * y` using `add_left_cancel hxy`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[hFG]`. Use `push_cast`. Both sides reduce to the same expression.

Use `_ = ∑ x, G ((v : ZMod q) + u * x) := hsum (fun x => G ((v : ZMod q) + u * x))`. Use `_ = ∑ x, G x := hbij.sum_comp G`. Use `_ = ∑ j ∈ Finset.range q, G (j : ZMod q) := (hsum G).symm`. Use `_ = ∑ j ∈ Finset.range q, F j := by`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations.

Rewrite using `[hFG]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem sum_range_affine {q : ℕ} (hq : 0 < q) (F : ℤ → ℂ) (hF : Function.Periodic F q)
    (u v : ℤ) (hu : ∃ w : ZMod q, w * u = 1) :
    ∑ j ∈ Finset.range q, F (v + u * j) = ∑ j ∈ Finset.range q, F j := by
  haveI : NeZero q := ⟨hq.ne'⟩
  let G : ZMod q → ℂ := fun x => F (x.val : ℤ)
  have hFG : ∀ m : ℤ, F m = G m := by
    intro m
    simp only [G, ZMod.val_intCast]
    have := (hF.int_mul (m / q)) (m % q)
    rw [← this]; congr 1
    rw [Int.cast_id]; linear_combination (Int.mul_ediv_add_emod m q).symm
  have hsum : ∀ H : ZMod q → ℂ, ∑ j ∈ Finset.range q, H (j : ZMod q) = ∑ x, H x := by
    intro H
    symm
    refine Finset.sum_bij' (fun x _ => x.val) (fun j _ => (j : ZMod q)) ?_ ?_ ?_ ?_ ?_
    · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
    · intro j _; exact Finset.mem_univ _
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro j hj; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hj)
    · intro x _; rw [ZMod.natCast_zmod_val]
  obtain ⟨w, hw⟩ := hu
  have hbij : Function.Bijective (fun x : ZMod q => (v : ZMod q) + u * x) := by
    refine Finite.injective_iff_bijective.1 ?_
    intro x y hxy
    have : (u : ZMod q) * x = u * y := add_left_cancel hxy
    calc x = w * (u * x) := by rw [← mul_assoc, hw, one_mul]
      _ = y := by rw [this, ← mul_assoc, hw, one_mul]
  calc ∑ j ∈ Finset.range q, F (v + u * j)
      = ∑ j ∈ Finset.range q, G ((v : ZMod q) + u * (j : ZMod q)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hFG]; push_cast; rfl
    _ = ∑ x, G ((v : ZMod q) + u * x) := hsum (fun x => G ((v : ZMod q) + u * x))
    _ = ∑ x, G x := hbij.sum_comp G
    _ = ∑ j ∈ Finset.range q, G (j : ZMod q) := (hsum G).symm
    _ = ∑ j ∈ Finset.range q, F j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hFG]; push_cast; rfl

/- English proof (translation)
Introduce `N l q k f _ _ hq hqNl hf γ hγ`. Establish `hq0 : (q : ℂ) ≠ 0` using `by exact_mod_cast hq.ne_zero`. Establish `hqpos : (0 : ℝ) < q` using `by exact_mod_cast hq.pos`. Take `⟨h1, h0⟩` from `Subgroup.mem_inf.1 hγ`. Rewrite `h1` using `[Gamma1_mem]`.

Rewrite `h0` using `[Gamma0_mem]`. Take `⟨ha, hd, hcN⟩` from `h1`. Establish `hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1`. Use `γ.2` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`.

Conclude with `this`. Establish `hqc : (q : ℤ) ∣ γ 1 0`. Break down `hq.dvd_mul.1 hqNl with h | h` into its components or cases. Conclude with `(Int.natCast_dvd_natCast.2 h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 hcN)`. Conclude with `(Int.natCast_dvd_natCast.2 h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 h0)`.

Take `⟨t, ht⟩` from `hqc`. Use function extensionality and compare the values at `τ`. Rewrite using `[SL_slash_apply]`. Establish `hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ) = (γ 1 0 : ℂ) * τ + γ 1 1`. Simplify using `[denom, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]`.

Establish `hsm : ((γ • τ : ℍ) : ℂ) = ((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1)`. Rewrite using `[specialLinearGroup_apply]`. Simplify using the standard rewrite rules. Establish `hcd : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0` using `by rw [← hden]; exact denom_ne_zero _ _`. Use `set a := γ 0 0 with ha_def`.

Use `set b := γ 0 1 with hb_def`. Use `set c := γ 1 0 with hc_def`. Use `set d := γ 1 1 with hd_def`. Set `F : ℤ → ℂ` to `fun m => f (ofComplex (((τ : ℂ) + m) / q))`. Establish `hzim : ∀ m : ℤ, 0 < (((τ : ℂ) + m) / q).im`.

Introduce `m`. Establish `: (((τ : ℂ) + m) / q).im = τ.im / q` using `by simp [Complex.div_natCast_im]`. Rewrite using `[this]`. Conclude with `div_pos τ.im_pos hqpos`. Establish `hper : Function.Periodic F (q : ℤ)`.

Introduce `m`. Establish `e : ((τ : ℂ) + ((m + q : ℤ) : ℂ)) / q = ((τ : ℂ) + m) / q + 1` using `by push_cast; field_simp; ring`. Use `show f (ofComplex (((τ : ℂ) + ((m + q : ℤ) : ℂ)) / q)) = f (ofComplex (((τ : ℂ) + m) / q))`. Rewrite using `[e]`. Conclude with `lev_periodic hf _ (hzim m)`.

Establish `hterm : ∀ j : ℕ, f (ofComplex (((a * τ + b) / (c * τ + d) + j) / q)) = (c * τ + d) ^ k * F (d * b + d * d * j)`. Introduce `j`. Use `set j' : ℤ := d * b + d * d * j with hj'`. Use `set e : ℤ := t * (-(b * b) - 2 * j * b * d - j * j * d * d) with he_def`. Establish `he : e * q = b + j * d - (a + j * c) * j'`.

Rewrite using `[he_def, hj']`. Take the linear combination `(b + j * d) * hdet + (b * b + 2 * j * b * d + j * j * d * d) * ht`. Establish `heC : (e : ℂ) * q = b + j * d - (a + j * c) * j'` using `by exact_mod_cast he`. Establish `h` using `lev_transform hf (a + j * c) e (q * c) (d - c * j') (by linear_combination hdet - c * he) (by push_cast; simp [ha, hcN]) (by push_cast; simp [hd, hcN]) (by push_cast; simp [hcN]) (by push_cast; simp [h0]) _ (hzim j')`. Establish `hCD : ((q * c : ℤ) : ℂ) * (((τ : ℂ) + j') / q) + ((d - c * j' : ℤ) : ℂ) = c * τ + d` using `by push_cast; field_simp; ring`.

Rewrite `h` using `[hCD]`. Establish `harg : (((a + j * c : ℤ) : ℂ) * (((τ : ℂ) + j') / q) + (e : ℂ)) / (c * τ + d) = ((a * τ + b) / (c * τ + d) + j) / q`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take the linear combination `heC`.

Rewrite `h` using `[harg]`. Conclude with `h`. Establish `hunit : ∃ w : ZMod q, w * ((d * d : ℤ) : ZMod q) = 1`. Use `⟨(a : ZMod q) * a, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (Int.cast : ℤ → ZMod q) hdet`.

Rewrite `h` using `[ht]`. Move the coercions through the operations in `at h`. Rewrite `h` using `[ZMod.natCast_self]`. Use `push_cast`. Take the linear combination `((a : ZMod q) * d + 1) * h`.

Unfold `uOp`. Rewrite using `[hsm, hden]`. Repeatedly rewrite using `[hterm]`. Rewrite using `[← Finset.mul_sum, sum_range_affine hq.pos F hper _ _ hunit]`. Establish `hF : ∑ j ∈ Finset.range q, F j = ∑ j ∈ Finset.range q, f (ofComplex (((τ : ℂ) + j) / q))` using `by simp [F]`.

Rewrite using `[hF, zpow_neg]`. Clear the denominators using the available nonvanishing facts.
-/
theorem uOp_slash_lev : ∀ (N l q : ℕ) (k : ℤ) (f : ℍ → ℂ), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    (∀ γ ∈ lev N l, f ∣[k] γ = f) → ∀ γ ∈ lev N l, uOp q f ∣[k] γ = uOp q f := by
  intro N l q k f _ _ hq hqNl hf γ hγ
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.1 hγ
  rw [Gamma1_mem] at h1
  rw [Gamma0_mem] at h0
  obtain ⟨ha, hd, hcN⟩ := h1
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hqc : (q : ℤ) ∣ γ 1 0 := by
    rcases hq.dvd_mul.1 hqNl with h | h
    · exact (Int.natCast_dvd_natCast.2 h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 hcN)
    · exact (Int.natCast_dvd_natCast.2 h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 h0)
  obtain ⟨t, ht⟩ := hqc
  funext τ
  rw [SL_slash_apply]
  have hden : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ) = (γ 1 0 : ℂ) * τ + γ 1 1 := by
    simp [denom, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hsm : ((γ • τ : ℍ) : ℂ) = ((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1) := by
    rw [specialLinearGroup_apply]; simp
  have hcd : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := by rw [← hden]; exact denom_ne_zero _ _
  set a := γ 0 0 with ha_def
  set b := γ 0 1 with hb_def
  set c := γ 1 0 with hc_def
  set d := γ 1 1 with hd_def
  let F : ℤ → ℂ := fun m => f (ofComplex (((τ : ℂ) + m) / q))
  have hzim : ∀ m : ℤ, 0 < (((τ : ℂ) + m) / q).im := by
    intro m
    have : (((τ : ℂ) + m) / q).im = τ.im / q := by simp [Complex.div_natCast_im]
    rw [this]; exact div_pos τ.im_pos hqpos
  have hper : Function.Periodic F (q : ℤ) := by
    intro m
    have e : ((τ : ℂ) + ((m + q : ℤ) : ℂ)) / q = ((τ : ℂ) + m) / q + 1 := by
      push_cast; field_simp; ring
    show f (ofComplex (((τ : ℂ) + ((m + q : ℤ) : ℂ)) / q)) = f (ofComplex (((τ : ℂ) + m) / q))
    rw [e]; exact lev_periodic hf _ (hzim m)
  have hterm : ∀ j : ℕ, f (ofComplex (((a * τ + b) / (c * τ + d) + j) / q)) =
      (c * τ + d) ^ k * F (d * b + d * d * j) := by
    intro j
    set j' : ℤ := d * b + d * d * j with hj'
    set e : ℤ := t * (-(b * b) - 2 * j * b * d - j * j * d * d) with he_def
    have he : e * q = b + j * d - (a + j * c) * j' := by
      rw [he_def, hj']
      linear_combination (b + j * d) * hdet + (b * b + 2 * j * b * d + j * j * d * d) * ht
    have heC : (e : ℂ) * q = b + j * d - (a + j * c) * j' := by exact_mod_cast he
    have h := lev_transform hf (a + j * c) e (q * c) (d - c * j')
      (by linear_combination hdet - c * he)
      (by push_cast; simp [ha, hcN]) (by push_cast; simp [hd, hcN]) (by push_cast; simp [hcN])
      (by push_cast; simp [h0]) _ (hzim j')
    have hCD : ((q * c : ℤ) : ℂ) * (((τ : ℂ) + j') / q) + ((d - c * j' : ℤ) : ℂ) = c * τ + d := by
      push_cast; field_simp; ring
    rw [hCD] at h
    have harg : (((a + j * c : ℤ) : ℂ) * (((τ : ℂ) + j') / q) + (e : ℂ)) / (c * τ + d) =
        ((a * τ + b) / (c * τ + d) + j) / q := by
      push_cast
      field_simp
      linear_combination heC
    rw [harg] at h
    exact h
  have hunit : ∃ w : ZMod q, w * ((d * d : ℤ) : ZMod q) = 1 := by
    refine ⟨(a : ZMod q) * a, ?_⟩
    have h := congrArg (Int.cast : ℤ → ZMod q) hdet
    rw [ht] at h
    push_cast at h
    rw [ZMod.natCast_self] at h
    push_cast
    linear_combination ((a : ZMod q) * d + 1) * h
  unfold uOp
  rw [hsm, hden]
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_range_affine hq.pos F hper _ _ hunit]
  have hF : ∑ j ∈ Finset.range q, F j =
      ∑ j ∈ Finset.range q, f (ofComplex (((τ : ℂ) + j) / q)) := by simp [F]
  rw [hF, zpow_neg]
  field_simp

end GlobalTheory.Hk
