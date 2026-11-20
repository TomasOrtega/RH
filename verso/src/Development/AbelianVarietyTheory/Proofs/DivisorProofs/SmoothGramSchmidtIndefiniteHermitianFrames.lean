import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfA

noncomputable section

open Matrix GlobalTheory.HolDict ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open scoped ContDiff

namespace GlobalTheory.HolDict.GS

section Smooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Use `ContDiffOn.sum fun σ _ => contDiffOn_const.mul ?_` and prove the remaining obligations. Conclude with `contDiffOn_prod fun i _ => hf _ _`.
-/
theorem contDiffOn_det {m : Type} [Fintype m] [DecidableEq m] (f : E → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) : ContDiffOn ℝ ∞ (fun x => (f x).det) s := by
  simp only [Matrix.det_apply']
  refine ContDiffOn.sum fun σ _ => contDiffOn_const.mul ?_
  exact contDiffOn_prod fun i _ => hf _ _

/- English proof (translation)
Simplify using `only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]`. Use `((contDiffOn_det f hf).inv hd).mul (contDiffOn_det _ fun a b => ?_)` and prove the remaining obligations. Simplify using `only [Matrix.updateRow_apply]`. Use `split_ifs`. Conclude with `contDiffOn_const`.

Conclude with `hf _ _`.
-/
theorem contDiffOn_minv {m : Type} [Fintype m] [DecidableEq m] (f : E → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hd : ∀ x ∈ s, (f x).det ≠ 0) (i j : m) :
    ContDiffOn ℝ ∞ (fun x => (f x)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  refine ((contDiffOn_det f hf).inv hd).mul (contDiffOn_det _ fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hf _ _

/- English proof (translation)
Simplify using `only [Matrix.mul_apply]`. Conclude with `ContDiffOn.sum fun k _ => (hf _ _).mul (hg _ _)`.
-/
theorem contDiffOn_mmul {m : Type} [Fintype m] (f g : E → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) s) (i j : m) :
    ContDiffOn ℝ ∞ (fun x => (f x * g x) i j) s := by
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hf _ _).mul (hg _ _)

/- English proof (translation)
Simplify using `only [Lm, Matrix.of_apply]`. Use `split_ifs with h1 h2`. Use `ContDiffOn.neg ?_` and prove the remaining obligations. Simplify using `only [wv, vecMul, dotProduct]`. Use `ContDiffOn.sum fun k _ => (hf _ _).mul ?_` and prove the remaining obligations.

Conclude with `contDiffOn_minv (fun x => lb (f x) i) (fun a b => hf _ _) (fun x hx => hd x hx (Fin.castSucc i)) _ _`. Conclude with `contDiffOn_const`. Conclude with `contDiffOn_const`.
-/
theorem contDiffOn_Lm {n : ℕ} (f : E → Matrix (Fin n) (Fin n) ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hd : ∀ x ∈ s, ∀ k, lminor (f x) k ≠ 0) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun x => Lm (f x) i j) s := by
  simp only [Lm, Matrix.of_apply]
  split_ifs with h1 h2
  · refine ContDiffOn.neg ?_
    simp only [wv, vecMul, dotProduct]
    refine ContDiffOn.sum fun k _ => (hf _ _).mul ?_
    exact contDiffOn_minv (fun x => lb (f x) i) (fun a b => hf _ _) (fun x hx => hd x hx (Fin.castSucc i)) _ _
  · exact contDiffOn_const
  · exact contDiffOn_const

end Smooth

variable {n : ℕ}

/- English proof (translation)
Establish `hU : (Lm A * A).BlockTriangular id` using `fun a c h => Lm_mul_up A hM a c h`. Establish `hL : ((Lm A)ᴴ).BlockTriangular id` using `fun a c h => by`. Rewrite using `[conjTranspose_apply, Lm_up A c a h, star_zero]`. Establish `hD` using `hU.mul hL`. Establish `hH : (Lm A * A * (Lm A)ᴴ)ᴴ = Lm A * A * (Lm A)ᴴ`.

Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, hA, Matrix.mul_assoc]`. Use extensionality with `a c`. Break down `lt_trichotomy a c with h | h | h` into its components or cases. Rewrite using `[diagonal_apply_ne _ h.ne, ← hH, conjTranspose_apply, hD (show id a < id c from h), star_zero]`. Substitute `h` using the available equality.

Rewrite using `[diagonal_apply_eq, Matrix.mul_apply, Finset.sum_eq_single a]`. Rewrite using `[conjTranspose_apply, Lm_diag, star_one, mul_one]`. Introduce `b _ hb`. Break down `lt_or_gt_of_ne hb with h | h` into its components or cases. Rewrite using `[hU (show id b < id a from h), zero_mul]`.

Rewrite using `[hL (show id a < id b from h), mul_zero]`. Simplify using the standard rewrite rules. Rewrite using `[diagonal_apply_ne _ h.ne', hD (show id c < id a from h)]`.
-/
theorem Lm_conj_diag (A : Mt n) (hA : Aᴴ = A) (hM : ∀ k, lminor A k ≠ 0) :
    Lm A * A * (Lm A)ᴴ = diagonal fun a => (Lm A * A) a a := by
  have hU : (Lm A * A).BlockTriangular id := fun a c h => Lm_mul_up A hM a c h
  have hL : ((Lm A)ᴴ).BlockTriangular id := fun a c h => by
    rw [conjTranspose_apply, Lm_up A c a h, star_zero]
  have hD := hU.mul hL
  have hH : (Lm A * A * (Lm A)ᴴ)ᴴ = Lm A * A * (Lm A)ᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA, Matrix.mul_assoc]
  ext a c
  rcases lt_trichotomy a c with h | h | h
  · rw [diagonal_apply_ne _ h.ne, ← hH, conjTranspose_apply, hD (show id a < id c from h), star_zero]
  · subst h
    rw [diagonal_apply_eq, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [conjTranspose_apply, Lm_diag, star_one, mul_one]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hU (show id b < id a from h), zero_mul]
      · rw [hL (show id a < id b from h), mul_zero]
    · simp
  · rw [diagonal_apply_ne _ h.ne', hD (show id c < id a from h)]

/- English proof (translation)
Establish `key : ∀ i : Fin (n + 1), lminor A i = ∏ j : Fin i, (Lm A * A) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)`. Introduce `i`. Establish `hN : ((Lm A)ᵀ).BlockTriangular id` using `fun a c h => Lm_up A c a h`. Establish `h1` using `FrameDegreeData.lminor_conj (A := A) hN i`. Establish `h2 : (Lm A)ᵀᵀ * A * ((Lm A)ᵀ).map (starRingEnd ℂ) = Lm A * A * (Lm A)ᴴ` using `rfl`.

Rewrite `h1` using `[h2, Lm_conj_diag A hA hM]`. Simplify using `only [transpose_apply, Lm_diag, Finset.prod_const_one, map_one, one_mul, mul_one] at h1`. Rewrite using `[← h1, lminor, FrameDegreeData.det_sub_upper _ (blockTriangular_diagonal _)]`. Simplify using `only [diagonal_apply_eq]`. Rewrite using `[key, key]`.

Conclude with `Fin.prod_univ_castSucc (n := a) _`.
-/
theorem lminor_succ (A : Mt n) (hA : Aᴴ = A) (hM : ∀ k, lminor A k ≠ 0) (a : Fin n) :
    lminor A a.succ = lminor A a.castSucc * (Lm A * A) a a := by
  have key : ∀ i : Fin (n + 1), lminor A i = ∏ j : Fin i, (Lm A * A) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
    intro i
    have hN : ((Lm A)ᵀ).BlockTriangular id := fun a c h => Lm_up A c a h
    have h1 := FrameDegreeData.lminor_conj (A := A) hN i
    have h2 : (Lm A)ᵀᵀ * A * ((Lm A)ᵀ).map (starRingEnd ℂ) = Lm A * A * (Lm A)ᴴ := rfl
    rw [h2, Lm_conj_diag A hA hM] at h1
    simp only [transpose_apply, Lm_diag, Finset.prod_const_one, map_one, one_mul, mul_one] at h1
    rw [← h1, lminor, FrameDegreeData.det_sub_upper _ (blockTriangular_diagonal _)]
    simp only [diagonal_apply_eq]
  rw [key, key]
  exact Fin.prod_univ_castSucc (n := a) _

/- English proof (translation)
Establish `hH : (Lm A * A * (Lm A)ᴴ)ᴴ = Lm A * A * (Lm A)ᴴ`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, hA, Matrix.mul_assoc]`. Rewrite `hH` using `[Lm_conj_diag A hA hM]`. Use `congrFun (congrFun hH a) a` as an intermediate fact. Rewrite `this` using `[conjTranspose_apply, diagonal_apply_eq]`.

Conclude with `Complex.conj_eq_iff_re.mp this`.
-/
theorem diag_real (A : Mt n) (hA : Aᴴ = A) (hM : ∀ k, lminor A k ≠ 0) (a : Fin n) :
    (((Lm A * A) a a).re : ℂ) = (Lm A * A) a a := by
  have hH : (Lm A * A * (Lm A)ᴴ)ᴴ = Lm A * A * (Lm A)ᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA, Matrix.mul_assoc]
  rw [Lm_conj_diag A hA hM] at hH
  have := congrFun (congrFun hH a) a
  rw [conjTranspose_apply, diagonal_apply_eq] at this
  exact Complex.conj_eq_iff_re.mp this

/- English proof (translation)
Introduce `h0` and use `by have := h k rw [h0] at this simp at this`.
-/
theorem minor_ne {q : ℕ} {A : Mt n} (h : ∀ i : Fin (n + 1), 0 < psgn q i * (lminor A i).re) (k : Fin (n + 1)) :
    lminor A k ≠ 0 := fun h0 => by
  have := h k
  rw [h0] at this
  simp at this

/- English proof (translation)
Apply the tactic sequence `unfold sgn; split_ifs <;> norm_num`.
-/
theorem sgn_sq (q a : ℕ) : sgn q a * sgn q a = 1 := by
  unfold sgn; split_ifs <;> norm_num

/- English proof (translation)
Establish `h1` using `h a.succ`. Establish `h2` using `h a.castSucc`. Rewrite `h1` using `[lminor_succ A hA (minor_ne h) a, ← diag_real A hA (minor_ne h) a, Complex.re_mul_ofReal]`. Simplify using `only [Fin.val_succ, psgn, Finset.prod_range_succ, Fin.val_castSucc] at h1 h2`. Establish `e : (∏ x ∈ Finset.range a, sgn q x) * sgn q a * ((lminor A a.castSucc).re * ((Lm A * A) a a).re) = ((∏ x ∈ Finset.range a, sgn q x) * (lminor A a.castSucc).re) * (sgn q a * ((Lm A * A) a a).re)` using `by ring`.

Rewrite `h1` using `[e]`. Conclude with `(pos_iff_pos_of_mul_pos h1).mp h2`.
-/
theorem diag_pos {q : ℕ} (A : Mt n) (hA : Aᴴ = A) (h : ∀ i : Fin (n + 1), 0 < psgn q i * (lminor A i).re)
    (a : Fin n) : 0 < sgn q a * ((Lm A * A) a a).re := by
  have h1 := h a.succ
  have h2 := h a.castSucc
  rw [lminor_succ A hA (minor_ne h) a, ← diag_real A hA (minor_ne h) a, Complex.re_mul_ofReal] at h1
  simp only [Fin.val_succ, psgn, Finset.prod_range_succ, Fin.val_castSucc] at h1 h2
  have e : (∏ x ∈ Finset.range a, sgn q x) * sgn q a * ((lminor A a.castSucc).re * ((Lm A * A) a a).re) =
      ((∏ x ∈ Finset.range a, sgn q x) * (lminor A a.castSucc).re) * (sgn q a * ((Lm A * A) a a).re) := by ring
  rw [e] at h1
  exact (pos_iff_pos_of_mul_pos h1).mp h2

def fac (q : ℕ) (A : Mt n) : Mt n :=
  diagonal (fun a : Fin n => (((Real.sqrt (sgn q a * ((Lm A * A) a a).re))⁻¹ : ℝ) : ℂ)) * (Lm A * A)

/- English proof (translation)
Use `set d : Fin n → ℝ := fun a => ((Lm A * A) a a).re with hd`. Use `set r : Fin n → ℝ := fun a : Fin n => Real.sqrt (sgn q a * d a) with hr`. Establish `hpos : ∀ a : Fin n, 0 < sgn q a * d a` using `diag_pos A hA h`. Establish `hr0 : ∀ a, r a ≠ 0` using `fun a => (Real.sqrt_pos.mpr (hpos a)).ne'`. Establish `hr2 : ∀ a : Fin n, r a * r a = sgn q a * d a` using `fun a => Real.mul_self_sqrt (hpos a).le`.

Establish `hd0 : ∀ a, d a ≠ 0` using `fun a h0 => by have := hpos a; rw [h0] at this; simp at this`. Establish `hD : Lm A * A * (Lm A)ᴴ = diagonal fun a => (d a : ℂ)`. Rewrite using `[Lm_conj_diag A hA (minor_ne h)]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Conclude with `(diag_real A hA (minor_ne h) a).symm`. Establish `hone : fac q A * ((Lm A)ᴴ * diagonal fun a => ((r a / d a : ℝ) : ℂ)) = 1`. Rewrite using `[fac, Matrix.mul_assoc, ← Matrix.mul_assoc (Lm A * A), hD, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Establish `h1` using `hr0 a`. Establish `h2` using `hd0 a`. Express the relevant statement in the definitionally equal form `(((r a)⁻¹ : ℝ) : ℂ) * _ = _`. Rewrite using `[← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Use `⟨⟨(Matrix.isUnit_det_of_right_inverse hone).ne_zero, fun a c hc => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[fac, diagonal_mul, Lm_mul_up A (minor_ne h) a c hc, mul_zero]`. Rewrite using `[Matrix.inv_eq_right_inv hone, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]`. Establish `e : ∀ X Y : Mt n, X * Lm A * A * ((Lm A)ᴴ * Y) = X * (Lm A * A * (Lm A)ᴴ) * Y` using `fun X Y => by`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, hD, diagonal_mul_diagonal, diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Establish `h2` using `hd0 a`.

Establish `h3` using `hr2 a`. Simplify using `only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]`. Rewrite using `[← Complex.ofReal_mul, ← Complex.ofReal_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `h3`.
-/
theorem fac_spec {q : ℕ} (A : Mt n) (hA : Aᴴ = A) (h : ∀ i : Fin (n + 1), 0 < psgn q i * (lminor A i).re) :
    UpT (fac q A) ∧ ((fac q A)⁻¹)ᴴ * A * (fac q A)⁻¹ = diagonal fun a : Fin n => ((sgn q a : ℝ) : ℂ) := by
  set d : Fin n → ℝ := fun a => ((Lm A * A) a a).re with hd
  set r : Fin n → ℝ := fun a : Fin n => Real.sqrt (sgn q a * d a) with hr
  have hpos : ∀ a : Fin n, 0 < sgn q a * d a := diag_pos A hA h
  have hr0 : ∀ a, r a ≠ 0 := fun a => (Real.sqrt_pos.mpr (hpos a)).ne'
  have hr2 : ∀ a : Fin n, r a * r a = sgn q a * d a := fun a => Real.mul_self_sqrt (hpos a).le
  have hd0 : ∀ a, d a ≠ 0 := fun a h0 => by have := hpos a; rw [h0] at this; simp at this
  have hD : Lm A * A * (Lm A)ᴴ = diagonal fun a => (d a : ℂ) := by
    rw [Lm_conj_diag A hA (minor_ne h)]
    congr 1
    funext a
    exact (diag_real A hA (minor_ne h) a).symm
  have hone : fac q A * ((Lm A)ᴴ * diagonal fun a => ((r a / d a : ℝ) : ℂ)) = 1 := by
    rw [fac, Matrix.mul_assoc, ← Matrix.mul_assoc (Lm A * A), hD, diagonal_mul_diagonal, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext a
    have h1 := hr0 a
    have h2 := hd0 a
    change (((r a)⁻¹ : ℝ) : ℂ) * _ = _
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    field_simp
  refine ⟨⟨(Matrix.isUnit_det_of_right_inverse hone).ne_zero, fun a c hc => ?_⟩, ?_⟩
  · rw [fac, diagonal_mul, Lm_mul_up A (minor_ne h) a c hc, mul_zero]
  · rw [Matrix.inv_eq_right_inv hone, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
    have e : ∀ X Y : Mt n, X * Lm A * A * ((Lm A)ᴴ * Y) = X * (Lm A * A * (Lm A)ᴴ) * Y := fun X Y => by
      simp only [Matrix.mul_assoc]
    rw [e, hD, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext a
    have h2 := hd0 a
    have h3 := hr2 a
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
    linear_combination h3

/- English proof (translation)
Establish `hU` using `contDiffOn_mmul (fun x => Lm (f x)) f (contDiffOn_Lm f hf fun x hx => minor_ne (h x hx)) hf`. Simplify using `only [fac, diagonal_mul]`. Use `ContDiffOn.mul ?_ (hU i j)` and prove the remaining obligations. Use `Complex.ofRealCLM.contDiff.comp_contDiffOn (f := fun x => (Real.sqrt (sgn q i * ((Lm (f x) * f x) i i).re))⁻¹) ?_` and prove the remaining obligations. Use `ContDiffOn.inv (ContDiffOn.sqrt (contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn (hU i i))) fun x hx => (diag_pos _ (hA x hx) (h x hx) i).ne') fun x hx => (Real.sqrt_pos.mpr (diag_pos _ (hA x hx) (h x hx) i)).ne'` and prove the remaining obligations.
-/
theorem contDiffOn_fac {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} (q : ℕ) (f : E → Mt n)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hA : ∀ x ∈ s, (f x)ᴴ = f x)
    (h : ∀ x ∈ s, ∀ i : Fin (n + 1), 0 < psgn q i * (lminor (f x) i).re) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun x => fac q (f x) i j) s := by
  have hU := contDiffOn_mmul (fun x => Lm (f x)) f
    (contDiffOn_Lm f hf fun x hx => minor_ne (h x hx)) hf
  simp only [fac, diagonal_mul]
  refine ContDiffOn.mul ?_ (hU i j)
  refine Complex.ofRealCLM.contDiff.comp_contDiffOn
    (f := fun x => (Real.sqrt (sgn q i * ((Lm (f x) * f x) i i).re))⁻¹) ?_
  refine ContDiffOn.inv (ContDiffOn.sqrt (contDiffOn_const.mul
    (Complex.reCLM.contDiff.comp_contDiffOn (hU i i))) fun x hx => (diag_pos _ (hA x hx) (h x hx) i).ne')
    fun x hx => (Real.sqrt_pos.mpr (diag_pos _ (hA x hx) (h x hx) i)).ne'

/- English proof (translation)
Introduce `n Hm q x₀ ⟨_, h0⟩`. Establish `hdet : IsUnit x₀.det`. Use `congrArg Matrix.det h0` as an intermediate fact. Rewrite `this` using `[det_mul, det_diagonal]`. Use `isUnit_iff_ne_zero.mpr fun hz => ?_` and prove the remaining obligations.

Rewrite `this` using `[hz, mul_zero]`. Use `Finset.prod_ne_zero_iff.mpr (fun a _ => ?_) this.symm` and prove the remaining obligations. Unfold `sgn`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hHm : ∀ X : Mt n, X = x₀ᴴ * Hm * x₀ → (x₀⁻¹)ᴴ * X * x₀⁻¹ = Hm`.

Introduce and unpack `X rfl`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_assoc, mul_nonsing_inv _ hdet, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Establish `hH : Hmᴴ = Hm`. Rewrite using `[← hHm _ h0.symm]`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, Matrix.mul_assoc]`.

Use `congr 3`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules. Establish `hA : ∀ x : Mt n, (-(xᴴ * Hm * x))ᴴ = -(xᴴ * Hm * x)` using `fun x => by`. Simplify using `only [conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]`.

Use `⟨fun x i j => fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)) i j, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Use `contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_` and prove the remaining obligations. Use `contDiffOn_fac q (fun x => -((Matrix.of x)ᴴ * Hm * Matrix.of x)) (fun a b => ?_) (fun x _ => hA _) (fun x hx => hx.2) i j` and prove the remaining obligations. Simplify using `only [Matrix.neg_apply]`. Establish `hx : ∀ a b : Fin n, ContDiff ℝ ∞ fun x : Fin n → Fin n → ℂ => x a b` using `fun a b => by fun_prop`.

Use `(contDiffOn_mmul _ _ (contDiffOn_mmul _ (fun _ => Hm) (fun a b => ?_) fun _ _ => contDiffOn_const) (fun a b => (hx a b).contDiffOn) a b).neg` and prove the remaining obligations. Conclude with `(Complex.conjCLE.contDiff.comp (hx b a)).contDiffOn`. Take `⟨h1, h2⟩` from `fac_spec _ (hA (Matrix.of x)) hx.2`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Matrix.of x * (fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ * x₀⁻¹)ᴴ * Hm * (Matrix.of x * (fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ * x₀⁻¹) = Hm`.

Generalize the expression as in `(fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ = γ at h2 ⊢`. Establish `h3 : γᴴ * ((Matrix.of x)ᴴ * Hm * Matrix.of x) * γ = x₀ᴴ * Hm * x₀`. Rewrite using `[h0, ← diagonal_neg, ← h2]`. Simplify using the standard rewrite rules. Use `Eq.trans ?_ (hHm _ h3)` and prove the remaining obligations.

Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.
-/
theorem smooth_gramSchmidt : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n), OrthFr Hm q x₀ →
    ∃ β : (Fin n → Fin n → ℂ) → (Fin n → Fin n → ℂ), ContDiffOn ℝ ∞ β {x | Matrix.of x ∈ frDom Hm q} ∧
      ∀ x : Fin n → Fin n → ℂ, Matrix.of x ∈ frDom Hm q → UpT (Matrix.of (β x)) ∧
        Matrix.of x * (Matrix.of (β x))⁻¹ * x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH Hm := by
  intro n Hm q x₀ ⟨_, h0⟩
  have hdet : IsUnit x₀.det := by
    have := congrArg Matrix.det h0
    rw [det_mul, det_diagonal] at this
    refine isUnit_iff_ne_zero.mpr fun hz => ?_
    rw [hz, mul_zero] at this
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => ?_) this.symm
    unfold sgn
    split_ifs <;> simp
  have hHm : ∀ X : Mt n, X = x₀ᴴ * Hm * x₀ → (x₀⁻¹)ᴴ * X * x₀⁻¹ = Hm := by
    rintro X rfl
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_assoc,
      mul_nonsing_inv _ hdet, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hH : Hmᴴ = Hm := by
    rw [← hHm _ h0.symm]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, Matrix.mul_assoc]
    congr 3
    funext a
    simp
  have hA : ∀ x : Mt n, (-(xᴴ * Hm * x))ᴴ = -(xᴴ * Hm * x) := fun x => by
    simp only [conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
  refine ⟨fun x i j => fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)) i j, ?_, fun x hx => ?_⟩
  · refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
    refine contDiffOn_fac q (fun x => -((Matrix.of x)ᴴ * Hm * Matrix.of x)) (fun a b => ?_) (fun x _ => hA _)
      (fun x hx => hx.2) i j
    simp only [Matrix.neg_apply]
    have hx : ∀ a b : Fin n, ContDiff ℝ ∞ fun x : Fin n → Fin n → ℂ => x a b := fun a b => by fun_prop
    refine (contDiffOn_mmul _ _ (contDiffOn_mmul _ (fun _ => Hm) (fun a b => ?_) fun _ _ => contDiffOn_const)
      (fun a b => (hx a b).contDiffOn) a b).neg
    exact (Complex.conjCLE.contDiff.comp (hx b a)).contDiffOn
  · obtain ⟨h1, h2⟩ := fac_spec _ (hA (Matrix.of x)) hx.2
    refine ⟨h1, ?_⟩
    change (Matrix.of x * (fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ * x₀⁻¹)ᴴ * Hm *
      (Matrix.of x * (fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ * x₀⁻¹) = Hm
    generalize (fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ = γ at h2 ⊢
    have h3 : γᴴ * ((Matrix.of x)ᴴ * Hm * Matrix.of x) * γ = x₀ᴴ * Hm * x₀ := by
      rw [h0, ← diagonal_neg, ← h2]
      simp
    refine Eq.trans ?_ (hHm _ h3)
    simp only [conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.HolDict.GS
