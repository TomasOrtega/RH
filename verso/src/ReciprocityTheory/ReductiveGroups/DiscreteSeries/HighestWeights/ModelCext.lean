import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OpEqExp

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def bdPart (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if ε a = ε b then Z a b else 0

/- English proof (translation)
Apply the tactic sequence `by_cases ha : ε a <;> by_cases hb : ε b <;>`. Apply the tactic sequence `simp [cpart1, bdPart, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, ha, hb] <;> ring`.
-/
theorem cpart1_bdPart_apply (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    cpart1 ε (bdPart ε Z) a b = if ε a = ε b then (Z a b - star (Z b a)) / 2 else 0 := by
  by_cases ha : ε a <;> by_cases hb : ε b <;>
    simp [cpart1, bdPart, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, ha, hb] <;> ring

/- English proof (translation)
Establish `hI : (1 / (2 * Complex.I)) = -Complex.I / 2`. Rewrite using `[one_div, mul_inv, Complex.inv_I]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `by_cases ha : ε a <;> by_cases hb : ε b <;>`. Apply the tactic sequence `simp [cpart2, hI, bdPart, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, ha, hb] <;> ring`.
-/
theorem cpart2_bdPart_apply (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    cpart2 ε (bdPart ε Z) a b = if ε a = ε b then -Complex.I * (Z a b + star (Z b a)) / 2 else 0 := by
  have hI : (1 / (2 * Complex.I)) = -Complex.I / 2 := by
    rw [one_div, mul_inv, Complex.inv_I]; ring
  by_cases ha : ε a <;> by_cases hb : ε b <;>
    simp [cpart2, hI, bdPart, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, ha, hb] <;> ring

/- English proof (translation)
Establish `h1` using `congrFun (congrFun hX.1 a) b`. Establish `h2` using `congrFun (congrFun hX.2 a) b`. Apply the tactic sequence `by_cases ha : ε a <;> by_cases hb : ε b <;>`. Simplify using `[Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, ha, hb] at h1 h2 ⊢`. Apply the tactic sequence `all_goals first`.

Consider the case `exact ⟨by linear_combination h2 / 2, by linear_combination h1 + h2⟩`. Consider the case `exact ⟨by linear_combination -h2 / 2, by linear_combination -h1 - h2⟩`. Consider the case `linear_combination h1 | linear_combination -h1`.
-/
theorem inK_apply (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (a b : Fin n) :
    (ε a ≠ ε b → X a b = 0) ∧ star (X b a) = - X a b := by
  have h1 := congrFun (congrFun hX.1 a) b
  have h2 := congrFun (congrFun hX.2 a) b
  by_cases ha : ε a <;> by_cases hb : ε b <;>
    simp [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, ha, hb] at h1 h2 ⊢
  all_goals first
    | exact ⟨by linear_combination h2 / 2, by linear_combination h1 + h2⟩
    | exact ⟨by linear_combination -h2 / 2, by linear_combination -h1 - h2⟩
    | linear_combination h1 | linear_combination -h1

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> ext a b <;>`. Apply the tactic sequence `simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.conjTranspose_apply, cpart1_bdPart_apply, Matrix.zero_apply] <;>`. Apply the tactic sequence `by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb] <;> ring`.
-/
theorem inK_cpart1_bdPart (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inK ε (cpart1 ε (bdPart ε Z)) := by
  refine ⟨?_, ?_⟩ <;> ext a b <;>
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.conjTranspose_apply,
      cpart1_bdPart_apply, Matrix.zero_apply] <;>
    by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb] <;> ring

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> ext a b <;>`. Apply the tactic sequence `simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.conjTranspose_apply, cpart2_bdPart_apply, Matrix.zero_apply] <;>`. Apply the tactic sequence `by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb] <;> ring`.
-/
theorem inK_cpart2_bdPart (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inK ε (cpart2 ε (bdPart ε Z)) := by
  refine ⟨?_, ?_⟩ <;> ext a b <;>
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.conjTranspose_apply,
      cpart2_bdPart_apply, Matrix.zero_apply] <;>
    by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb] <;> ring

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> ext a b`. Take `⟨h0, hs⟩` from `inK_apply ε hX a b`. Rewrite using `[cpart1_bdPart_apply]`. Use `split_ifs with h`. Rewrite using `[hs]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `(h0 h).symm`. Take `⟨h0, hs⟩` from `inK_apply ε hX a b`. Rewrite using `[Matrix.zero_apply, cpart2_bdPart_apply]`. Use `split_ifs with h`.

Rewrite using `[hs]`. Expand and normalize the polynomial expressions, which then agree. Both sides reduce to the same expression.
-/
theorem cpart_bdPart_of_inK (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    cpart1 ε (bdPart ε X) = X ∧ cpart2 ε (bdPart ε X) = 0 := by
  refine ⟨?_, ?_⟩ <;> ext a b
  · obtain ⟨h0, hs⟩ := inK_apply ε hX a b
    rw [cpart1_bdPart_apply]
    split_ifs with h
    · rw [hs]; ring
    · exact (h0 h).symm
  · obtain ⟨h0, hs⟩ := inK_apply ε hX a b
    rw [Matrix.zero_apply, cpart2_bdPart_apply]
    split_ifs with h
    · rw [hs]; ring
    · rfl

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.add_apply, cpart1_bdPart_apply, star_add]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem cpart1_bdPart_add (ε : Fin n → Bool) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (bdPart ε (Z + Z')) = cpart1 ε (bdPart ε Z) + cpart1 ε (bdPart ε Z') := by
  ext a b
  simp only [Matrix.add_apply, cpart1_bdPart_apply, star_add]
  split_ifs <;> ring

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.add_apply, cpart2_bdPart_apply, star_add]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem cpart2_bdPart_add (ε : Fin n → Bool) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (bdPart ε (Z + Z')) = cpart2 ε (bdPart ε Z) + cpart2 ε (bdPart ε Z') := by
  ext a b
  simp only [Matrix.add_apply, cpart2_bdPart_apply, star_add]
  split_ifs <;> ring

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cpart1_bdPart_apply, cpart2_bdPart_apply, star_mul']`. Use `split_ifs`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`. Simplify using the standard rewrite rules.
-/
theorem cpart1_bdPart_smul (ε : Fin n → Bool) (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (bdPart ε (c • Z)) =
      ((c.re : ℝ) : ℂ) • cpart1 ε (bdPart ε Z) + ((-c.im : ℝ) : ℂ) • cpart2 ε (bdPart ε Z) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cpart1_bdPart_apply, cpart2_bdPart_apply, star_mul']
  split_ifs
  · apply Complex.ext <;> simp <;> ring
  · simp

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cpart1_bdPart_apply, cpart2_bdPart_apply, star_mul']`. Use `split_ifs`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`. Simplify using the standard rewrite rules.
-/
theorem cpart2_bdPart_smul (ε : Fin n → Bool) (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (bdPart ε (c • Z)) =
      ((c.im : ℝ) : ℂ) • cpart1 ε (bdPart ε Z) + ((c.re : ℝ) : ℂ) • cpart2 ε (bdPart ε Z) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, cpart1_bdPart_apply, cpart2_bdPart_apply, star_mul']
  split_ifs
  · apply Complex.ext <;> simp <;> ring
  · simp

/- English proof (translation)
Take `⟨h1, h2⟩` from `hX`. Establish `hr : star (r : ℂ) = r` using `by simp`. Prove the components needed by the constructor for the conclusion. Express the relevant statement in the definitionally equal form `((r : ℂ) • X)ᴴ * Jm ε + Jm ε * ((r : ℂ) • X) = 0`. Express the relevant statement in the definitionally equal form `Xᴴ * Jm ε + Jm ε * X = 0 at h1`.

Rewrite using `[conjTranspose_smul, hr, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, h2]`.
-/
theorem inK_ofReal_smul (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (r : ℝ) :
    inK ε ((r : ℂ) • X) := by
  obtain ⟨h1, h2⟩ := hX
  have hr : star (r : ℂ) = r := by simp
  constructor
  · change ((r : ℂ) • X)ᴴ * Jm ε + Jm ε * ((r : ℂ) • X) = 0
    change Xᴴ * Jm ε + Jm ε * X = 0 at h1
    rw [conjTranspose_smul, hr, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, h2]

section Op

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def RLinOnK (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) : Prop :=
  ∀ (X Y : Matrix (Fin n) (Fin n) ℂ) (r : ℝ), inK ε X → inK ε Y →
    A (X + Y) = A X + A Y ∧ A ((r : ℂ) • X) = (r : ℂ) • A X

/- English proof (translation)
Introduce `_ _ _ _ _` and use `by simp`.
-/
theorem rLinOnK_zero (ε : Fin n → Bool) : RLinOnK ε (0 : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) :=
  fun _ _ _ _ _ => by simp

def cext (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (Z : Matrix (Fin n) (Fin n) ℂ) :
    V →L[ℂ] V :=
  A (cpart1 ε (bdPart ε Z)) + Complex.I • A (cpart2 ε (bdPart ε Z))

/- English proof (translation)
Establish `hc : (c.re : ℂ) + c.im * Complex.I = c` using `Complex.re_add_im c`. Use `push_cast`. Take the linear combination `(norm := module) hc • (u + Complex.I • v) - ((c.im : ℂ) * Complex.I_sq) • v`.
-/
theorem smul_combo (c : ℂ) (u v : V →L[ℂ] V) :
    ((c.re : ℝ) : ℂ) • u + ((-c.im : ℝ) : ℂ) • v + Complex.I • (((c.im : ℝ) : ℂ) • u + ((c.re : ℝ) : ℂ) • v) =
      c • (u + Complex.I • v) := by
  have hc : (c.re : ℂ) + c.im * Complex.I = c := Complex.re_add_im c
  push_cast
  linear_combination (norm := module) hc • (u + Complex.I • v) - ((c.im : ℂ) * Complex.I_sq) • v

/- English proof (translation)
Unfold `cext`. Rewrite using `[cpart1_bdPart_add, cpart2_bdPart_add, (hA _ _ 0 (inK_cpart1_bdPart ε Z) (inK_cpart1_bdPart ε Z')).1, (hA _ _ 0 (inK_cpart2_bdPart ε Z) (inK_cpart2_bdPart ε Z')).1, smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem cext_add (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (hA : RLinOnK ε A)
    (Z Z' : Matrix (Fin n) (Fin n) ℂ) : cext ε A (Z + Z') = cext ε A Z + cext ε A Z' := by
  unfold cext
  rw [cpart1_bdPart_add, cpart2_bdPart_add,
    (hA _ _ 0 (inK_cpart1_bdPart ε Z) (inK_cpart1_bdPart ε Z')).1,
    (hA _ _ 0 (inK_cpart2_bdPart ε Z) (inK_cpart2_bdPart ε Z')).1, smul_add]
  abel

/- English proof (translation)
Establish `hP` using `inK_cpart1_bdPart ε Z`. Establish `hQ` using `inK_cpart2_bdPart ε Z`. Unfold `cext`. Rewrite using `[cpart1_bdPart_smul, cpart2_bdPart_smul, (hA _ _ 0 (inK_ofReal_smul ε hP _) (inK_ofReal_smul ε hQ _)).1, (hA _ _ 0 (inK_ofReal_smul ε hP _) (inK_ofReal_smul ε hQ _)).1, (hA _ _ c.re hP hP).2, (hA _ _ (-c.im) hQ hQ).2, (hA _ _ c.im hP hP).2, (hA _ _ c.re hQ hQ).2]`. Conclude with `smul_combo c _ _`.
-/
theorem cext_smul (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (hA : RLinOnK ε A)
    (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) : cext ε A (c • Z) = c • cext ε A Z := by
  have hP := inK_cpart1_bdPart ε Z
  have hQ := inK_cpart2_bdPart ε Z
  unfold cext
  rw [cpart1_bdPart_smul, cpart2_bdPart_smul,
    (hA _ _ 0 (inK_ofReal_smul ε hP _) (inK_ofReal_smul ε hQ _)).1,
    (hA _ _ 0 (inK_ofReal_smul ε hP _) (inK_ofReal_smul ε hQ _)).1,
    (hA _ _ c.re hP hP).2, (hA _ _ (-c.im) hQ hQ).2, (hA _ _ c.im hP hP).2, (hA _ _ c.re hQ hQ).2]
  exact smul_combo c _ _

/- English proof (translation)
Take `⟨h1, h2⟩` from `cpart_bdPart_of_inK ε hX`. Establish `h0 : A 0 = 0`. Use `(hA X X 0 hX hX).2` as an intermediate fact. Simplify using `using this`. Unfold `cext`.

Rewrite using `[h1, h2, h0, smul_zero, add_zero]`.
-/
theorem cext_of_inK (ε : Fin n → Bool) {A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (hA : RLinOnK ε A)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : cext ε A X = A X := by
  obtain ⟨h1, h2⟩ := cpart_bdPart_of_inK ε hX
  have h0 : A 0 = 0 := by
    have := (hA X X 0 hX hX).2
    simpa using this
  unfold cext
  rw [h1, h2, h0, smul_zero, add_zero]

def cextL (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (hA : RLinOnK ε A) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V) where
  toFun := cext ε A
  map_add' := cext_add ε hA
  map_smul' := cext_smul ε hA

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cextL_apply (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (hA : RLinOnK ε A)
    (Z : Matrix (Fin n) (Fin n) ℂ) : cextL ε A hA Z = cext ε A Z := rfl

end Op

end ReciprocityTheory.ChartRestriction.DS.HW
