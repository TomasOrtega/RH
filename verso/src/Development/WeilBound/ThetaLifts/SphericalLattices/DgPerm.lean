import Mathlib

noncomputable section

namespace PositivityTheory.Sph.M2.GenA

open Matrix

variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Use `congrArg ψ h` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, mul_comm]`. Conclude with `mul_right_cancel₀ (hpos g).ne' this`.
-/
theorem conj_eq (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) {g a b : GL n K} (h : g * a = b * g) : ψ a = ψ b := by
  have := congrArg ψ h
  rw [map_mul, map_mul, mul_comm] at this
  exact mul_right_cancel₀ (hpos g).ne' this

def dg : (n → Kˣ) →* GL n K where
  toFun D := ⟨diagonal fun i => (D i : K), diagonal fun i => (((D i)⁻¹ : Kˣ) : K),
    by simp [diagonal_mul_diagonal], by simp [diagonal_mul_diagonal]⟩
  map_one' := by ext1; simp
  map_mul' a b := by ext1; simp [diagonal_mul_diagonal]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dg_val (D : n → Kˣ) : ((dg D : GL n K) : Matrix n n K) = diagonal fun i => (D i : K) := rfl

def tv {i j : n} (h : i ≠ j) (s : K) : GL n K :=
  ⟨transvection i j s, transvection i j (-s), by rw [transvection_mul_transvection_same i j h]; simp,
    by rw [transvection_mul_transvection_same i j h]; simp⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tv_val {i j : n} (h : i ≠ j) (s : K) : ((tv h s : GL n K) : Matrix n n K) = transvection i j s := rfl

/- English proof (translation)
Use `ext1`. Rewrite using `[Units.val_mul, tv_val, tv_val, tv_val, transvection_mul_transvection_same i j h]`.
-/
theorem tv_mul {i j : n} (h : i ≠ j) (s t : K) : tv h s * tv h t = tv h (s + t) := by
  ext1
  rw [Units.val_mul, tv_val, tv_val, tv_val, transvection_mul_transvection_same i j h]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Units.val_mul, Units.val_mul, dg_val, tv_val, tv_val, diagonal_mul, mul_diagonal]`. Simplify using `only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single, of_apply]`. Distinguish the cases in `h1 : a = b`. Substitute `h1` using the available equality.

Establish `: ¬ (i = a ∧ j = a)` using `fun e => h (e.1.trans e.2.symm)`. Simplify using `[this]`. Distinguish the cases in `h2 : i = a ∧ j = b`. Take `⟨rfl, rfl⟩` from `h2`. Simplify using `[h1, Function.update_of_ne (Ne.symm h)]`.

Simplify using `[h1, h2]`.
-/
theorem dg_tv {i j : n} (h : i ≠ j) (d : Kˣ) (s : K) :
    dg (Function.update 1 i d) * tv h s = tv h (d * s) * dg (Function.update 1 i d) := by
  ext a b
  rw [Units.val_mul, Units.val_mul, dg_val, tv_val, tv_val, diagonal_mul, mul_diagonal]
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single, of_apply]
  by_cases h1 : a = b
  · subst h1
    have : ¬ (i = a ∧ j = a) := fun e => h (e.1.trans e.2.symm)
    simp [this]
  · by_cases h2 : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h2
      simp [h1, Function.update_of_ne (Ne.symm h)]
    · simp [h1, h2]

/- English proof (translation)
Establish `e1` using `conj_eq ψ hpos (dg_tv h (Units.mk0 w h0) s)`. Establish `e2` using `conj_eq ψ hpos (dg_tv h (Units.mk0 _ h1) s)`. Establish `e3` using `congrArg ψ (tv_mul h s (w * s))`. Simplify using `only [Units.val_mk0] at e1 e2`. Rewrite `e3` using `[map_mul, ← e1, show s + w * s = (1 + w) * s by ring, ← e2]`.

Conclude with `mul_left_cancel₀ (hpos _).ne' (e3.trans (mul_one _).symm)`.
-/
theorem tv_one (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) {w : K} (h0 : w ≠ 0) (h1 : 1 + w ≠ 0) {i j : n} (h : i ≠ j)
    (s : K) : ψ (tv h s) = 1 := by
  have e1 := conj_eq ψ hpos (dg_tv h (Units.mk0 w h0) s)
  have e2 := conj_eq ψ hpos (dg_tv h (Units.mk0 _ h1) s)
  have e3 := congrArg ψ (tv_mul h s (w * s))
  simp only [Units.val_mk0] at e1 e2
  rw [map_mul, ← e1, show s + w * s = (1 + w) * s by ring, ← e2] at e3
  exact mul_left_cancel₀ (hpos _).ne' (e3.trans (mul_one _).symm)

/- English proof (translation)
Establish `hd : ((1 : Matrix n n K).submatrix σ id).det ≠ 0`. Rewrite using `[det_permute, det_one, mul_one]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]`. Use `conj_eq ψ hpos (g := GeneralLinearGroup.mkOfDetNeZero _ hd) ?_` and prove the remaining obligations. Use extensionality with `a b`.

Rewrite using `[Units.val_mul, Units.val_mul, dg_val, dg_val, diagonal_mul, mul_diagonal]`. Use `show ((1 : Matrix n n K).submatrix σ id) a b * _ = _ * ((1 : Matrix n n K).submatrix σ id) a b`. Simplify using `only [submatrix_apply, id, Matrix.one_apply]`. Use `split_ifs with e`. Simplify using `[e]`.

Simplify using the standard rewrite rules.
-/
theorem dg_perm (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) (σ : Equiv.Perm n) (D : n → Kˣ) :
    ψ (dg D) = ψ (dg fun i => D (σ i)) := by
  have hd : ((1 : Matrix n n K).submatrix σ id).det ≠ 0 := by
    rw [det_permute, det_one, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]
  refine conj_eq ψ hpos (g := GeneralLinearGroup.mkOfDetNeZero _ hd) ?_
  ext a b
  rw [Units.val_mul, Units.val_mul, dg_val, dg_val, diagonal_mul, mul_diagonal]
  show ((1 : Matrix n n K).submatrix σ id) a b * _ = _ * ((1 : Matrix n n K).submatrix σ id) a b
  simp only [submatrix_apply, id, Matrix.one_apply]
  split_ifs with e
  · simp [e]
  · simp

/- English proof (translation)
Break down `isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩` into its components or cases. Rewrite using `[Subsingleton.elim D 1, map_one, map_one]`. Establish `e1 : (∏ σ : Equiv.Perm n, fun i => D (σ i)) = fun _ => ∏ σ : Equiv.Perm n, D (σ i₀)`. Use function extensionality and compare the values at `i`. Rewrite using `[Finset.prod_apply]`.

Use `Fintype.prod_equiv (Equiv.mulRight (Equiv.swap i i₀)) _ _ fun σ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `e2` using `hsc (∏ σ : Equiv.Perm n, D (σ i₀))`. Rewrite `e2` using `[← e1, ← MonoidHom.comp_apply, map_prod]`. Simplify using `only [MonoidHom.comp_apply, ← dg_perm ψ hpos _ D, Finset.prod_const, Finset.card_univ] at e2`.

Conclude with `(pow_eq_one_iff_of_nonneg (hpos _).le Fintype.card_ne_zero).1 e2`.
-/
theorem dg_one (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) (hsc : ∀ u : Kˣ, ψ (dg fun _ => u) = 1) (D : n → Kˣ) :
    ψ (dg D) = 1 := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · rw [Subsingleton.elim D 1, map_one, map_one]
  have e1 : (∏ σ : Equiv.Perm n, fun i => D (σ i)) = fun _ => ∏ σ : Equiv.Perm n, D (σ i₀) := by
    funext i
    rw [Finset.prod_apply]
    refine Fintype.prod_equiv (Equiv.mulRight (Equiv.swap i i₀)) _ _ fun σ => ?_
    simp
  have e2 := hsc (∏ σ : Equiv.Perm n, D (σ i₀))
  rw [← e1, ← MonoidHom.comp_apply, map_prod] at e2
  simp only [MonoidHom.comp_apply, ← dg_perm ψ hpos _ D, Finset.prod_const, Finset.card_univ] at e2
  exact (pow_eq_one_iff_of_nonneg (hpos _).le Fintype.card_ne_zero).1 e2

/- English proof (translation)
Establish `key : ∀ M : Matrix n n K, M.det ≠ 0 → ∀ g : GL n K, (g : Matrix n n K) = M → ψ g = 1`. Introduce `M hM`. Use `diagonal_transvection_induction_of_det_ne_zero (fun M => ∀ g : GL n K, (g : Matrix n n K) = M → ψ g = 1) M hM ?_ ?_ ?_` and prove the remaining obligations. Introduce `D hD g hg`. Rewrite `hD` using `[det_diagonal]`.

Establish `hD' : ∀ i, D i ≠ 0` using `fun i => Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)`. Establish `: g = dg fun i => Units.mk0 (D i) (hD' i)` using `Units.ext hg`. Rewrite using `[this]`. Conclude with `dg_one ψ hpos hsc _`. Introduce `t g hg`.

Establish `: g = tv t.hij t.c` using `Units.ext hg`. Rewrite using `[this]`. Conclude with `tv_one ψ hpos h0 h1 _ _`. Introduce `A B hA hB pA pB g hg`. Establish `: g = GeneralLinearGroup.mkOfDetNeZero A hA * GeneralLinearGroup.mkOfDetNeZero B hB` using `Units.ext hg`.

Rewrite using `[this, map_mul, pA _ rfl, pB _ rfl, one_mul]`. Conclude with `key _ (Matrix.GeneralLinearGroup.det_ne_zero g) g rfl`.
-/
theorem all_one (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) {w : K} (h0 : w ≠ 0) (h1 : 1 + w ≠ 0)
    (hsc : ∀ u : Kˣ, ψ (dg fun _ => u) = 1) (g : GL n K) : ψ g = 1 := by
  have key : ∀ M : Matrix n n K, M.det ≠ 0 → ∀ g : GL n K, (g : Matrix n n K) = M → ψ g = 1 := by
    intro M hM
    refine diagonal_transvection_induction_of_det_ne_zero
      (fun M => ∀ g : GL n K, (g : Matrix n n K) = M → ψ g = 1) M hM ?_ ?_ ?_
    · intro D hD g hg
      rw [det_diagonal] at hD
      have hD' : ∀ i, D i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
      have : g = dg fun i => Units.mk0 (D i) (hD' i) := Units.ext hg
      rw [this]
      exact dg_one ψ hpos hsc _
    · intro t g hg
      have : g = tv t.hij t.c := Units.ext hg
      rw [this]
      exact tv_one ψ hpos h0 h1 _ _
    · intro A B hA hB pA pB g hg
      have : g = GeneralLinearGroup.mkOfDetNeZero A hA * GeneralLinearGroup.mkOfDetNeZero B hB := Units.ext hg
      rw [this, map_mul, pA _ rfl, pB _ rfl, one_mul]
  exact key _ (Matrix.GeneralLinearGroup.det_ne_zero g) g rfl

end PositivityTheory.Sph.M2.GenA

end
