import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelDer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InhabA

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def blkMinor (ε : Fin n → Bool) (a : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (x.submatrix (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))).det

open Classical in

def mexp (ε : Fin n → Bool) (m : Fin n → ℤ) (a : Fin n) : ℤ :=
  if h : (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).Nonempty then
    m a - m ((Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).min' h)
  else m a

def NonnegDom (ε : Fin n → Bool) (m : Fin n → ℤ) : Prop :=
  (∀ a b, a < b → ε a = ε b → m b ≤ m a) ∧ ∀ a, 0 ≤ m a

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b _ _`. Simplify using the standard rewrite rules. Introduce `a`. Simplify using the standard rewrite rules.
-/
theorem nonnegDom_zero (ε : Fin n → Bool) : NonnegDom ε 0 := by
  constructor
  · intro a b _ _
    simp
  · intro a
    simp

def f0 (ε : Fin n → Bool) (m : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ a, blkMinor ε a x ^ (mexp ε m a).toNat

def f0K (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) : ℂ := f0 ε m (toMK k)

/- English proof (translation)
Unfold `mexp`. Use `split_ifs with h`. Establish `hb` using `(Finset.mem_filter.1 (Finset.min'_mem _ h)).2`. Conclude with `sub_nonneg.2 (hm.1 a _ hb.1 hb.2.symm)`. Conclude with `hm.2 a`.
-/
theorem mexp_nonneg (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) : 0 ≤ mexp ε m a := by
  unfold mexp
  split_ifs with h
  · have hb := (Finset.mem_filter.1 (Finset.min'_mem _ h)).2
    exact sub_nonneg.2 (hm.1 a _ hb.1 hb.2.symm)
  · exact hm.2 a

/- English proof (translation)
Use `first`. Consider the case `exact ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj i) : (Fin n → Fin n → ℂ) →L[ℂ] ℂ).differentiable`. Consider the case `fun_prop`. Consider the case `exact (differentiable_apply j).comp (differentiable_apply i)`.
-/
lemma hwmf_diff_entry (i j : Fin n) : Differentiable ℂ (fun x : Matrix (Fin n) (Fin n) ℂ => x i j) := by
  first
    | exact ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj i) :
        (Fin n → Fin n → ℂ) →L[ℂ] ℂ).differentiable
    | fun_prop
    | exact (differentiable_apply j).comp (differentiable_apply i)

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `only [Finset.prod_empty]`. Conclude with `differentiable_const _`. Introduce `a s ha ih`. Simplify using `only [Finset.prod_insert ha]`.

Conclude with `(h a).mul ih`.
-/
lemma hwmf_diff_prod {ι : Type} (s : Finset ι) (g : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ i, Differentiable ℂ (g i)) : Differentiable ℂ (fun x => ∏ i ∈ s, g i x) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact differentiable_const _
  · intro a s ha ih
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

/- English proof (translation)
Use `show Differentiable ℂ (fun x : Matrix (Fin n) (Fin n) ℂ => blkMinor ε a x)`. Simplify using `only [blkMinor, Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]`. Use `first`. Consider the case `(apply Differentiable.fun_sum`. Introduce `σ _`.

Apply the tactic sequence `exact (differentiable_const _).mul (hwmf_diff_prod _ _ (fun i => hwmf_diff_entry _ _)))`. Consider the case `fun_prop`. Consider the case `(apply Differentiable.sum`. Introduce `σ _`. Apply the tactic sequence `exact (differentiable_const _).mul (hwmf_diff_prod _ _ (fun i => hwmf_diff_entry _ _)))`.
-/
lemma hwmf_diff_blkMinor (ε : Fin n → Bool) (a : Fin n) : Differentiable ℂ (blkMinor ε a) := by
  show Differentiable ℂ (fun x : Matrix (Fin n) (Fin n) ℂ => blkMinor ε a x)
  simp only [blkMinor, Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
  first
    | (apply Differentiable.fun_sum
       intro σ _
       exact (differentiable_const _).mul (hwmf_diff_prod _ _ (fun i => hwmf_diff_entry _ _)))
    | fun_prop
    | (apply Differentiable.sum
       intro σ _
       exact (differentiable_const _).mul (hwmf_diff_prod _ _ (fun i => hwmf_diff_entry _ _)))

/- English proof (translation)
Use `show Differentiable ℂ (fun x : Matrix (Fin n) (Fin n) ℂ => f0 ε m x)`. Simplify using `only [f0]`. Conclude with `hwmf_diff_prod _ _ (fun a => (hwmf_diff_blkMinor ε a).pow _)`.
-/
theorem differentiable_highest_weight_fn (ε : Fin n → Bool) (m : Fin n → ℤ) : Differentiable ℂ (f0 ε m) := by
  show Differentiable ℂ (fun x : Matrix (Fin n) (Fin n) ℂ => f0 ε m x)
  simp only [f0]
  exact hwmf_diff_prod _ _ (fun a => (hwmf_diff_blkMinor ε a).pow _)

/- English proof (translation)
Establish `hc : Continuous (toMK (ε` using `ε)) := by first`. Consider the case `exact continuous_toMK`. Consider the case `exact continuous_toMK ε`. Consider the case `(unfold toMK; fun_prop)`. Consider the case `(unfold toMK; exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val))`.

Conclude with `(differentiable_highest_weight_fn ε m).continuous.comp hc`.
-/
theorem continuous_f0K (ε : Fin n → Bool) (m : Fin n → ℤ) : Continuous (f0K ε m) := by
  have hc : Continuous (toMK (ε := ε)) := by
    first
      | exact continuous_toMK
      | exact continuous_toMK ε
      | (unfold toMK; fun_prop)
      | (unfold toMK; exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val))
  exact (differentiable_highest_weight_fn ε m).continuous.comp hc

/- English proof (translation)
Establish `h1 : toMK (1 : KG ε) = 1` using `by first`. Consider the case `exact toMK_one`. Consider the case `simp [toMK]`. Consider the case `rfl`. Unfold `f0K f0 blkMinor`.

Rewrite using `[h1]`. Simplify using `[Matrix.submatrix_one _ Subtype.val_injective]`.
-/
theorem highest_weight_fn_K_one (ε : Fin n → Bool) (m : Fin n → ℤ) : f0K ε m 1 = 1 := by
  have h1 : toMK (1 : KG ε) = 1 := by
    first
      | exact toMK_one
      | simp [toMK]
      | rfl
  unfold f0K f0 blkMinor
  rw [h1]
  simp [Matrix.submatrix_one _ Subtype.val_injective]

/- English proof (translation)
Use `hasDerivAt_pi.2 fun i => ?_` and prove the remaining obligations. Use `hasDerivAt_pi.2 fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply]`. Use `HasDerivAt.fun_sum fun k _ => HasDerivAt.const_mul _ ?_` and prove the remaining obligations. Apply the tactic sequence `have h := InhabA.hasDerivAt_exp_entry X k j`.

Establish `e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) k j) = fun t : ℝ => (NormedSpace.exp (t • X)) k j`. Use function extensionality and compare the values at `t`. Use `congr 3`. Rewrite using `[e]`. Conclude with `h`.
-/
lemma hwmf_hasDerivAt_A (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => Y * NormedSpace.exp ((t : ℂ) • X)) (Y * X) 0 := by
  refine hasDerivAt_pi.2 fun i => ?_
  refine hasDerivAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  refine HasDerivAt.fun_sum fun k _ => HasDerivAt.const_mul _ ?_
  have h := InhabA.hasDerivAt_exp_entry X k j
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) k j) = fun t : ℝ => (NormedSpace.exp (t • X)) k j := by
    funext t; congr 3
  rw [e]; exact h

/- English proof (translation)
Establish `hspec` using `(kcurve_spec ε hX).2.1`. Establish `hmul : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b`. Introduce `a b`. Use `first`. Consider the case `exact toMK_mul a b`.

Consider the case `(simp [toMK, toM]; done)`. Consider the case `(simp only [toMK]; exact map_mul _ _ _)`. Consider the case `(simp only [toMK, toM]; rfl)`. Establish `hfun : (fun t : ℝ => f0K ε m (x * kcurve ε X t)) = fun t : ℝ => f0 ε m (toMK x * NormedSpace.exp ((t : ℂ) • X))`. Use function extensionality and compare the values at `t`.

Use `show f0 ε m (toMK (x * kcurve ε X t)) = _`. Rewrite using `[hmul, hspec t]`. Rewrite using `[hfun]`. Establish `hd : HasFDerivAt (f0 ε m) (fderiv ℂ (f0 ε m) (toMK x)) (toMK x * NormedSpace.exp (((0 : ℝ) : ℂ) • X))`. Rewrite using `[Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]`.

Conclude with `(differentiable_highest_weight_fn ε m (toMK x)).hasFDerivAt`. Conclude with `(hd.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) (hwmf_hasDerivAt_A X (toMK x))`.
-/
theorem hasDerivAt_f0K (ε : Fin n → Bool) (m : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (x : KG ε) :
    HasDerivAt (fun t : ℝ => f0K ε m (x * kcurve ε X t)) (fderiv ℂ (f0 ε m) (toMK x) (toMK x * X)) 0 := by
  have hspec := (kcurve_spec ε hX).2.1
  have hmul : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := by
    intro a b
    first
      | exact toMK_mul a b
      | (simp [toMK, toM]; done)
      | (simp only [toMK]; exact map_mul _ _ _)
      | (simp only [toMK, toM]; rfl)
  have hfun : (fun t : ℝ => f0K ε m (x * kcurve ε X t)) =
      fun t : ℝ => f0 ε m (toMK x * NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    show f0 ε m (toMK (x * kcurve ε X t)) = _
    rw [hmul, hspec t]
  rw [hfun]
  have hd : HasFDerivAt (f0 ε m) (fderiv ℂ (f0 ε m) (toMK x))
      (toMK x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
    exact (differentiable_highest_weight_fn ε m (toMK x)).hasFDerivAt
  exact (hd.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) (hwmf_hasDerivAt_A X (toMK x))

/- English proof (translation)
Unfold `cpart1 cpart2`. Use extensionality with `i j`. Use `first`. Consider the case `(simp`. Take the linear combination `(-(1 / 2) * (Z i j + (Jm ε * Zᴴ * Jm ε) i j)) * Complex.I_sq)`.

Consider the case `(simp [Complex.I_sq]; ring)`.
-/
lemma hwmf_cpart_sum (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε Z + Complex.I • cpart2 ε Z = Z := by
  unfold cpart1 cpart2
  ext i j
  first
    | (simp
       linear_combination (-(1 / 2) * (Z i j + (Jm ε * Zᴴ * Jm ε) i j)) * Complex.I_sq)
    | (simp [Complex.I_sq]; ring)

/- English proof (translation)
Unfold `inK inG cpart1 Jm bdPart`. Apply the tactic sequence `constructor <;> ext a b <;>`. Apply the tactic sequence `simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, map_div₀] <;>`. Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>`. Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>`.

Apply the tactic sequence `simp [ha, hb, Complex.conj_ofNat, map_ofNat] <;> ring`.
-/
private theorem inK_cp1_lemma (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inK ε (cpart1 ε (bdPart ε Z)) := by
  unfold inK inG cpart1 Jm bdPart
  constructor <;> ext a b <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, map_div₀] <;>
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
    simp [ha, hb, Complex.conj_ofNat, map_ofNat] <;> ring

/- English proof (translation)
Unfold `inK inG cpart2 Jm bdPart`. Apply the tactic sequence `constructor <;> ext a b <;>`. Apply the tactic sequence `simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, map_div₀, Complex.conj_I] <;>`. Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>`. Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>`.

Apply the tactic sequence `simp [ha, hb, Complex.conj_ofNat, map_ofNat] <;> ring`.
-/
private theorem inK_cp2_lemma_2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inK ε (cpart2 ε (bdPart ε Z)) := by
  unfold inK inG cpart2 Jm bdPart
  constructor <;> ext a b <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, map_div₀,
      Complex.conj_I] <;>
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
    simp [ha, hb, Complex.conj_ofNat, map_ofNat] <;> ring

/- English proof (translation)
Establish `h1` using `hasDerivAt_f0K ε m (inK_cp1_lemma ε Z) x`. Establish `h2` using `hasDerivAt_f0K ε m (inK_cp2_lemma_2 ε Z) x`. Unfold `rdc`. Rewrite using `[h1.deriv, h2.deriv]`. Rewrite using `[show Complex.I * fderiv ℂ (f0 ε m) (toMK x) (toMK x * cpart2 ε (bdPart ε Z)) = fderiv ℂ (f0 ε m) (toMK x) (Complex.I • (toMK x * cpart2 ε (bdPart ε Z))) from ((fderiv ℂ (f0 ε m) (toMK x)).map_smul Complex.I _).symm]`.

Rewrite using `[← map_add, ← Matrix.mul_smul, ← Matrix.mul_add, hwmf_cpart_sum]`.
-/
lemma hwmf_rdc (ε : Fin n → Bool) (m : Fin n → ℤ) (Z : Matrix (Fin n) (Fin n) ℂ) (x : KG ε) :
    rdc ε Z (f0K ε m) x = fderiv ℂ (f0 ε m) (toMK x) (toMK x * bdPart ε Z) := by
  have h1 := hasDerivAt_f0K ε m (inK_cp1_lemma ε Z) x
  have h2 := hasDerivAt_f0K ε m (inK_cp2_lemma_2 ε Z) x
  unfold rdc
  rw [h1.deriv, h2.deriv]
  rw [show Complex.I * fderiv ℂ (f0 ε m) (toMK x) (toMK x * cpart2 ε (bdPart ε Z)) =
      fderiv ℂ (f0 ε m) (toMK x) (Complex.I • (toMK x * cpart2 ε (bdPart ε Z))) from
      ((fderiv ℂ (f0 ε m) (toMK x)).map_smul Complex.I _).symm]
  rw [← map_add, ← Matrix.mul_smul, ← Matrix.mul_add, hwmf_cpart_sum]

/- English proof (translation)
Establish `hin : HasDerivAt (fun s : ℂ => x * (1 + s • W)) (x * W) 0`. Establish `hfun : (fun s : ℂ => x * (1 + s • W)) = fun s => x + s • (x * W)`. Use function extensionality and compare the values at `s`. Rewrite using `[Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]`. Rewrite using `[hfun]`.

Establish `h` using `((hasDerivAt_id' (0 : ℂ)).smul_const (x * W)).const_add x`. Rewrite `h` using `[one_smul]`. Conclude with `h`. Establish `hd : HasFDerivAt (f0 ε m) (fderiv ℂ (f0 ε m) x) (x * (1 + (0 : ℂ) • W))`. Rewrite using `[zero_smul, add_zero, Matrix.mul_one]`.

Conclude with `(differentiable_highest_weight_fn ε m x).hasFDerivAt`. Conclude with `hd.comp_hasDerivAt (0 : ℂ) hin`.
-/
lemma hwmf_line (ε : Fin n → Bool) (m : Fin n → ℤ) (x W : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℂ => f0 ε m (x * (1 + s • W))) (fderiv ℂ (f0 ε m) x (x * W)) 0 := by
  have hin : HasDerivAt (fun s : ℂ => x * (1 + s • W)) (x * W) 0 := by
    have hfun : (fun s : ℂ => x * (1 + s • W)) = fun s => x + s • (x * W) := by
      funext s
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [hfun]
    have h := ((hasDerivAt_id' (0 : ℂ)).smul_const (x * W)).const_add x
    rw [one_smul] at h
    exact h
  have hd : HasFDerivAt (f0 ε m) (fderiv ℂ (f0 ε m) x) (x * (1 + (0 : ℂ) • W)) := by
    rw [zero_smul, add_zero, Matrix.mul_one]
    exact (differentiable_highest_weight_fn ε m x).hasFDerivAt
  exact hd.comp_hasDerivAt (0 : ℂ) hin

/- English proof (translation)
Rewrite using `[Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Use `congr 1`. Distinguish the cases in `hq : q = b`. Substitute `hq` using the available equality. Rewrite using `[if_pos rfl, Matrix.mul_apply]`.

Simplify using `[Matrix.single_apply]`. Rewrite using `[if_neg hq, Matrix.mul_apply]`. Simplify using `[Matrix.single_apply, Ne.symm hq]`.
-/
lemma hwmf_mul_tv (x : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (s : ℂ) (r q : Fin n) :
    (x * (1 + s • single a b (1 : ℂ))) r q = x r q + (if q = b then s * x r a else 0) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  congr 1
  by_cases hq : q = b
  · subst hq
    rw [if_pos rfl, Matrix.mul_apply]
    simp [Matrix.single_apply]
  · rw [if_neg hq, Matrix.mul_apply]
    simp [Matrix.single_apply, Ne.symm hq]

/- English proof (translation)
Unfold `blkMinor`. Distinguish the cases in `hb : ε b = ε c ∧ b ≤ c`. Take `⟨B, hB⟩ : ∃ B : {d : Fin n // ε d = ε c ∧ d ≤ c}, (B : Fin n) = b` from `⟨⟨b, hb⟩, rfl⟩`. Take `⟨A, hA⟩ : ∃ A : {d : Fin n // ε d = ε c ∧ d ≤ c}, (A : Fin n) = a` from `⟨⟨a, he.trans hb.1, hab.le.trans hb.2⟩, rfl⟩`. Establish `hBA : B ≠ A` using `fun h => (ne_of_lt hab) (by rw [← hA, ← hB, h])`.

Establish `hM : (x * (1 + s • single a b (1 : ℂ))).submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) = (x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} …`. Use extensionality with `i j`. Rewrite using `[Matrix.submatrix_apply, hwmf_mul_tv, Matrix.updateCol_apply]`. Distinguish the cases in `hj : j = B`. Substitute `hj` using the available equality.

Simplify using `[hB, hA, smul_eq_mul]`. Establish `hj' : (j : Fin n) ≠ b` using `fun h => hj (Subtype.ext (h.trans hB.symm))`. Simplify using `[hj, hj']`. Rewrite using `[hM, Matrix.det_updateCol_add_smul_self _ hBA]`. Use `congr 1`.

Use extensionality with `i j`. Rewrite using `[Matrix.submatrix_apply, Matrix.submatrix_apply, hwmf_mul_tv]`. Establish `hj : (j : Fin n) ≠ b` using `fun h => hb (h ▸ j.2)`. Simplify using `[hj]`.
-/
lemma hwmf_blk_tv (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) (c : Fin n)
    (x : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    blkMinor ε c (x * (1 + s • single a b (1 : ℂ))) = blkMinor ε c x := by
  unfold blkMinor
  by_cases hb : ε b = ε c ∧ b ≤ c
  · obtain ⟨B, hB⟩ : ∃ B : {d : Fin n // ε d = ε c ∧ d ≤ c}, (B : Fin n) = b := ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A : {d : Fin n // ε d = ε c ∧ d ≤ c}, (A : Fin n) = a :=
      ⟨⟨a, he.trans hb.1, hab.le.trans hb.2⟩, rfl⟩
    have hBA : B ≠ A := fun h => (ne_of_lt hab) (by rw [← hA, ← hB, h])
    have hM : (x * (1 + s • single a b (1 : ℂ))).submatrix
        (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) =
        (x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n))).updateCol B
          (fun k => x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) k B +
            s • x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) k A) := by
      ext i j
      rw [Matrix.submatrix_apply, hwmf_mul_tv, Matrix.updateCol_apply]
      by_cases hj : j = B
      · subst hj
        simp [hB, hA, smul_eq_mul]
      · have hj' : (j : Fin n) ≠ b := fun h => hj (Subtype.ext (h.trans hB.symm))
        simp [hj, hj']
    rw [hM, Matrix.det_updateCol_add_smul_self _ hBA]
  · congr 1
    ext i j
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hwmf_mul_tv]
    have hj : (j : Fin n) ≠ b := fun h => hb (h ▸ j.2)
    simp [hj]

/- English proof (translation)
Rewrite using `[hwmf_mul_tv]`. Distinguish the cases in `hq : q = a`. Substitute `hq` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg hq, if_neg hq]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hwmf_mul_dg (x : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (s : ℂ) (r q : Fin n) :
    (x * (1 + s • single a a (1 : ℂ))) r q = x r q * (if q = a then 1 + s else 1) := by
  rw [hwmf_mul_tv]
  by_cases hq : q = a
  · subst hq
    rw [if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg hq, if_neg hq]
    ring

/- English proof (translation)
Unfold `blkMinor`. Establish `hx : (x * (1 + s • single a a (1 : ℂ))).submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) = x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} …`. Use extensionality with `r q`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_diagonal, hwmf_mul_dg]`. Rewrite using `[hx, det_mul, det_diagonal]`.

Use `congr 1`. Use `split_ifs with ha`. Rewrite using `[Fintype.prod_eq_single (⟨a, ha⟩ : {d : Fin n // ε d = ε c ∧ d ≤ c})]`. Simplify using the standard rewrite rules. Introduce `q hq`.

Establish `: (q : Fin n) ≠ a` using `fun h => hq (Subtype.ext h)`. Simplify using `[this]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `q _`. Establish `: (q : Fin n) ≠ a` using `fun h => ha (h ▸ q.2)`.

Simplify using `[this]`.
-/
lemma hwmf_blk_dg (ε : Fin n → Bool) (a c : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    blkMinor ε c (x * (1 + s • single a a (1 : ℂ))) =
      blkMinor ε c x * (if ε a = ε c ∧ a ≤ c then 1 + s else 1) := by
  unfold blkMinor
  have hx : (x * (1 + s • single a a (1 : ℂ))).submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n))
      (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) =
      x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n))
        (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) *
      diagonal (fun q : {d : Fin n // ε d = ε c ∧ d ≤ c} => if (q : Fin n) = a then 1 + s else 1) := by
    ext r q
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, hwmf_mul_dg]
  rw [hx, det_mul, det_diagonal]
  congr 1
  split_ifs with ha
  · rw [Fintype.prod_eq_single (⟨a, ha⟩ : {d : Fin n // ε d = ε c ∧ d ≤ c})]
    · simp
    · intro q hq
      have : (q : Fin n) ≠ a := fun h => hq (Subtype.ext h)
      simp [this]
  · apply Finset.prod_eq_one
    intro q _
    have : (q : Fin n) ≠ a := fun h => ha (h ▸ q.2)
    simp [this]

/- English proof (translation)
Introduce `k`. Use `Nat.strong_induction_on k ?_` and prove the remaining obligations. Introduce `k ih a hk`. Establish `hsplit : Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c) = insert a (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a)`. Use extensionality with `c`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Break down `h2.lt_or_eq with h | h` into its components or cases. Conclude with `Or.inr ⟨h, h1.symm⟩`.

Conclude with `Or.inl h.symm`. Introduce and unpack `(h | ⟨h1, h2⟩)`. Substitute `h` using the available equality. Conclude with `⟨rfl, le_rfl⟩`. Conclude with `⟨h2.symm, h1.le⟩`.

Establish `hnot : a ∉ Finset.univ.filter (fun b : Fin n => a < b ∧ ε b = ε a)` using `by simp`. Rewrite using `[hsplit, Finset.sum_insert hnot]`. Distinguish the cases in `hne : (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).Nonempty`. Take `⟨a', ha'def⟩ : ∃ a', (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).min' hne = a'` from `⟨_, rfl⟩`. Establish `ha'mem : a < a' ∧ ε a' = ε a`.

Use `Finset.min'_mem _ hne` as an intermediate fact. Rewrite `this` using `[ha'def]`. Conclude with `(Finset.mem_filter.1 this).2`. Establish `hset : (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a) = Finset.univ.filter (fun c : Fin n => ε a' = ε c ∧ a' ≤ c)`. Use extensionality with `c`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨ha'mem.2.trans h2.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[← ha'def]`.

Conclude with `Finset.min'_le _ _ (by simp [h1, h2])`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨lt_of_lt_of_le ha'mem.1 h2, h1.symm.trans ha'mem.2⟩`. Establish `hcard : (Finset.univ.filter fun b : Fin n => a' < b ∧ ε b = ε a').card < k`. Rewrite using `[← hk]`.

Establish `hsub : (Finset.univ.filter fun b : Fin n => a' < b ∧ ε b = ε a') ⊆ (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a)`. Introduce `c hc`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢`. Conclude with `⟨ha'mem.1.trans hc.1, hc.2.trans ha'mem.2⟩`. Apply `Finset.card_lt_card` to reduce the goal to its premises.

Rewrite using `[Finset.ssubset_iff_of_subset hsub]`. Conclude with `⟨a', by simp [ha'mem.1, ha'mem.2], by simp⟩`. Rewrite using `[hset, ih _ hcard a' rfl]`. Unfold `mexp`. Rewrite using `[dif_pos hne, ha'def]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hemp` using `Finset.not_nonempty_iff_eq_empty.1 hne`. Rewrite using `[hemp, Finset.sum_empty, add_zero]`. Unfold `mexp`. Rewrite using `[dif_neg hne]`.
-/
lemma hwmf_tele (ε : Fin n → Bool) (m : Fin n → ℤ) : ∀ k : ℕ, ∀ a : Fin n,
    (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).card = k →
    ∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c), mexp ε m c = m a := by
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih a hk
  have hsplit : Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c) =
      insert a (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h2.lt_or_eq with h | h
      · exact Or.inr ⟨h, h1.symm⟩
      · exact Or.inl h.symm
    · rintro (h | ⟨h1, h2⟩)
      · subst h
        exact ⟨rfl, le_rfl⟩
      · exact ⟨h2.symm, h1.le⟩
  have hnot : a ∉ Finset.univ.filter (fun b : Fin n => a < b ∧ ε b = ε a) := by simp
  rw [hsplit, Finset.sum_insert hnot]
  by_cases hne : (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).Nonempty
  · obtain ⟨a', ha'def⟩ : ∃ a', (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).min' hne = a' :=
      ⟨_, rfl⟩
    have ha'mem : a < a' ∧ ε a' = ε a := by
      have := Finset.min'_mem _ hne
      rw [ha'def] at this
      exact (Finset.mem_filter.1 this).2
    have hset : (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a) =
        Finset.univ.filter (fun c : Fin n => ε a' = ε c ∧ a' ≤ c) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨ha'mem.2.trans h2.symm, ?_⟩
        rw [← ha'def]
        exact Finset.min'_le _ _ (by simp [h1, h2])
      · rintro ⟨h1, h2⟩
        exact ⟨lt_of_lt_of_le ha'mem.1 h2, h1.symm.trans ha'mem.2⟩
    have hcard : (Finset.univ.filter fun b : Fin n => a' < b ∧ ε b = ε a').card < k := by
      rw [← hk]
      have hsub : (Finset.univ.filter fun b : Fin n => a' < b ∧ ε b = ε a') ⊆
          (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a) := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        exact ⟨ha'mem.1.trans hc.1, hc.2.trans ha'mem.2⟩
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hsub]
      exact ⟨a', by simp [ha'mem.1, ha'mem.2], by simp⟩
    rw [hset, ih _ hcard a' rfl]
    unfold mexp
    rw [dif_pos hne, ha'def]
    ring
  · have hemp := Finset.not_nonempty_iff_eq_empty.1 hne
    rw [hemp, Finset.sum_empty, add_zero]
    unfold mexp
    rw [dif_neg hne]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [bdPart, Matrix.of_apply]`. Distinguish the cases in `h : a = i ∧ b = j`. Take `⟨rfl, rfl⟩` from `h`. Rewrite using `[if_pos he]`.

Rewrite using `[Matrix.single_apply, if_neg h, ite_self]`.
-/
lemma hwmf_bd_single (ε : Fin n → Bool) {a b : Fin n} (he : ε a = ε b) :
    bdPart ε (single a b (1 : ℂ)) = single a b 1 := by
  ext i j
  simp only [bdPart, Matrix.of_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos he]
  · rw [Matrix.single_apply, if_neg h, ite_self]

/- English proof (translation)
Unfold `f0`. Simplify using `only [hwmf_blk_dg, mul_pow, Finset.prod_mul_distrib, ite_pow, one_pow]`. Use `congr 1`. Rewrite using `[← Finset.prod_filter, Finset.prod_pow_eq_pow_sum]`.
-/
private theorem f0_dg_lemma (ε : Fin n → Bool) (m : Fin n → ℤ) (a : Fin n) (X : Matrix (Fin n) (Fin n) ℂ)
    (s : ℂ) : f0 ε m (X * (1 + s • single a a (1 : ℂ))) =
      f0 ε m X * (1 + s) ^ (∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c),
        (mexp ε m c).toNat) := by
  unfold f0
  simp only [hwmf_blk_dg, mul_pow, Finset.prod_mul_distrib, ite_pow, one_pow]
  congr 1
  rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum]

/- English proof (translation)
Rewrite using `[hwmf_rdc, hwmf_bd_single ε rfl]`. Establish `h1` using `hwmf_line ε m (toMK x) (single a a 1)`. Establish `hc : (fun s : ℂ => f0 ε m (toMK x * (1 + s • single a a (1 : ℂ)))) = fun s => f0 ε m (toMK x) * (1 + s) ^ (∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c), (mexp ε m c).toNat)`. Use function extensionality and compare the values at `s`. Conclude with `f0_dg_lemma ε m a (toMK x) s`.

Rewrite `h1` using `[hc]`. Establish `h2` using `(((hasDerivAt_id' (0 : ℂ)).const_add 1).pow (∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c), (mexp ε m c).toNat)).const_mul (f0 ε m (toMK x))`. Rewrite using `[h1.unique h2]`. Establish `hsum : ((∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c), (mexp ε m c).toNat : ℕ) : ℤ) = m a`. Rewrite using `[Nat.cast_sum, ← hwmf_tele ε m _ a rfl]`.

Conclude with `Finset.sum_congr rfl fun c _ => Int.toNat_of_nonneg (mexp_nonneg ε hm c)`. Establish `hsumC : ((∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c), (mexp ε m c).toNat : ℕ) : ℂ) = ((m a : ℤ) : ℂ)`. Rewrite using `[← hsum, Int.cast_natCast]`. Simplify using `only [add_zero, one_pow, mul_one]`. Rewrite using `[hsumC]`.

Unfold `f0K`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rdc_f0K_wt (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) (x : KG ε) :
    rdc ε (Matrix.single a a 1) (f0K ε m) x = ((m a : ℤ) : ℂ) * f0K ε m x := by
  rw [hwmf_rdc, hwmf_bd_single ε rfl]
  have h1 := hwmf_line ε m (toMK x) (single a a 1)
  have hc : (fun s : ℂ => f0 ε m (toMK x * (1 + s • single a a (1 : ℂ)))) = fun s =>
      f0 ε m (toMK x) * (1 + s) ^ (∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c),
        (mexp ε m c).toNat) := by
    funext s
    exact f0_dg_lemma ε m a (toMK x) s
  rw [hc] at h1
  have h2 := (((hasDerivAt_id' (0 : ℂ)).const_add 1).pow (∑ c ∈ Finset.univ.filter
    (fun c : Fin n => ε a = ε c ∧ a ≤ c), (mexp ε m c).toNat)).const_mul (f0 ε m (toMK x))
  rw [h1.unique h2]
  have hsum : ((∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c), (mexp ε m c).toNat : ℕ) : ℤ)
      = m a := by
    rw [Nat.cast_sum, ← hwmf_tele ε m _ a rfl]
    exact Finset.sum_congr rfl fun c _ => Int.toNat_of_nonneg (mexp_nonneg ε hm c)
  have hsumC : ((∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c), (mexp ε m c).toNat : ℕ) : ℂ)
      = ((m a : ℤ) : ℂ) := by
    rw [← hsum, Int.cast_natCast]
  simp only [add_zero, one_pow, mul_one]
  rw [hsumC]
  unfold f0K
  ring

/- English proof (translation)
Rewrite using `[hwmf_rdc, hwmf_bd_single ε he]`. Establish `h1` using `hwmf_line ε m (toMK x) (single a b 1)`. Establish `hc : (fun s : ℂ => f0 ε m (toMK x * (1 + s • single a b (1 : ℂ)))) = fun _ => f0 ε m (toMK x)`. Use function extensionality and compare the values at `s`. Unfold `f0`.

Simplify using `only [hwmf_blk_tv ε hab he]`. Rewrite `h1` using `[hc]`. Conclude with `h1.unique (hasDerivAt_const _ _)`.
-/
theorem rdc_f0K_hw (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) {a b : Fin n} (hab : a < b)
    (he : ε a = ε b) (x : KG ε) : rdc ε (Matrix.single a b 1) (f0K ε m) x = 0 := by
  rw [hwmf_rdc, hwmf_bd_single ε he]
  have h1 := hwmf_line ε m (toMK x) (single a b 1)
  have hc : (fun s : ℂ => f0 ε m (toMK x * (1 + s • single a b (1 : ℂ)))) = fun _ => f0 ε m (toMK x) := by
    funext s
    unfold f0
    simp only [hwmf_blk_tv ε hab he]
  rw [hc] at h1
  exact h1.unique (hasDerivAt_const _ _)

end ReciprocityTheory.ChartRestriction.DS.HW
