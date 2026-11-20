import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn

noncomputable section

open Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.HPol

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Log

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Use `first`. Consider the case `exact hasStrictFDerivAt_exp_zero`. Consider the case `exact hasStrictFDerivAt_exp_zero.congr_fderiv (by ext; simp)`.
-/
theorem exp_strict :
    HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ)) 0 := by
  first
  | exact hasStrictFDerivAt_exp_zero
  | exact hasStrictFDerivAt_exp_zero.congr_fderiv (by ext; simp)

variable (n) in

def logM : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
  (exp_strict (n := n)).localInverse _ _ _

/- English proof (translation)
Conclude with `(exp_strict (n := n)).eventually_left_inverse`.
-/
theorem logM_exp : ∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), logM n (NormedSpace.exp X) = X := by
  exact (exp_strict (n := n)).eventually_left_inverse

/- English proof (translation)
Establish `h` using `(exp_strict (n := n)).eventually_right_inverse`. Rewrite `h` using `[NormedSpace.exp_zero]`. Conclude with `h`.
-/
theorem exp_logM : ∀ᶠ h in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (logM n h) = h := by
  have h := (exp_strict (n := n)).eventually_right_inverse
  rw [NormedSpace.exp_zero] at h
  exact h

/- English proof (translation)
Establish `h` using `(exp_strict (n := n)).localInverse_apply_image`. Rewrite `h` using `[NormedSpace.exp_zero]`. Conclude with `h`.
-/
theorem logM_one : logM n 1 = 0 := by
  have h := (exp_strict (n := n)).localInverse_apply_image
  rw [NormedSpace.exp_zero] at h
  exact h

/- English proof (translation)
Establish `h` using `(exp_strict (n := n)).to_localInverse`. Rewrite `h` using `[NormedSpace.exp_zero]`. Conclude with `h`.
-/
theorem logM_strict : HasStrictFDerivAt (logM n) (ContinuousLinearMap.id ℝ _) 1 := by
  have h := (exp_strict (n := n)).to_localInverse
  rw [NormedSpace.exp_zero] at h
  exact h

end Log

/- English proof (translation)
Rewrite using `[Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem Jm_mul_self_eq_one' (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

/- English proof (translation)
Conclude with `Matrix.inv_eq_left_inv (Jm_mul_self_eq_one' ε)`.
-/
theorem Jm_inv (ε : Fin n → Bool) : (Jm ε)⁻¹ = Jm ε := by
  exact Matrix.inv_eq_left_inv (Jm_mul_self_eq_one' ε)

/- English proof (translation)
Conclude with `⟨⟨Jm ε, Jm ε, Jm_mul_self_eq_one' ε, Jm_mul_self_eq_one' ε⟩, rfl⟩`.
-/
theorem Jm_isUnit (ε : Fin n → Bool) : IsUnit (Jm ε) := by
  exact ⟨⟨Jm ε, Jm ε, Jm_mul_self_eq_one' ε, Jm_mul_self_eq_one' ε⟩, rfl⟩

/- English proof (translation)
Establish `hJ` using `Jm_mul_self_eq_one' ε`. Establish `h' : Yᴴ * Jm ε + Jm ε * Y = 0` using `h`. Establish `h1 : Yᴴ * Jm ε = -(Jm ε * Y)` using `eq_neg_of_add_eq_zero_left h'`. Rewrite using `[Jm_inv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conjT_of_inG {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) :
    Yᴴ = Jm ε * (-Y) * (Jm ε)⁻¹ := by
  have hJ := Jm_mul_self_eq_one' ε
  have h' : Yᴴ * Jm ε + Jm ε * Y = 0 := h
  have h1 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left h'
  rw [Jm_inv]
  calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε * (-Y) * Jm ε := by rw [h1, Matrix.mul_neg]

/- English proof (translation)
Establish `hJ` using `Jm_mul_self_eq_one' ε`. Use `show (NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y = Jm ε`. Rewrite using `[← Matrix.exp_conjTranspose, conjT_of_inG h, Matrix.exp_conj _ _ (Jm_isUnit ε), Jm_inv, Matrix.mul_assoc (Jm ε * NormedSpace.exp (-Y)) (Jm ε) (Jm ε), hJ, Matrix.mul_one, Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel, NormedS …`.
-/
theorem exp_inUJ {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) :
    inUJ ε (NormedSpace.exp Y) := by
  have hJ := Jm_mul_self_eq_one' ε
  show (NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y = Jm ε
  rw [← Matrix.exp_conjTranspose, conjT_of_inG h, Matrix.exp_conj _ _ (Jm_isUnit ε), Jm_inv,
    Matrix.mul_assoc (Jm ε * NormedSpace.exp (-Y)) (Jm ε) (Jm ε), hJ, Matrix.mul_one, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

/- English proof (translation)
Establish `hJ` using `Jm_mul_self_eq_one' ε`. Establish `hU' : (NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y = Jm ε` using `hU`. Establish `hEE : NormedSpace.exp Y * NormedSpace.exp (-Y) = 1`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl Y)), add_neg_cancel, NormedSpace.exp_zero]`. Establish `key : NormedSpace.exp (Jm ε * (-Yᴴ) * Jm ε) = NormedSpace.exp Y`.

Establish `e1 : Jm ε * (-Yᴴ) * Jm ε = Jm ε * (-Y)ᴴ * (Jm ε)⁻¹`. Rewrite using `[Jm_inv, Matrix.conjTranspose_neg]`. Rewrite using `[e1, Matrix.exp_conj _ _ (Jm_isUnit ε), Jm_inv, Matrix.exp_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hU']`.

Use `_ = Jm ε * (NormedSpace.exp Y * NormedSpace.exp (-Y))ᴴ * Jm ε * NormedSpace.exp Y := by`. Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = NormedSpace.exp Y := by`. Rewrite using `[hEE, Matrix.conjTranspose_one, Matrix.mul_one, hJ, Matrix.one_mul]`.

Establish `hY : Y = Jm ε * (-Yᴴ) * Jm ε` using `by rw [← h2, key, h1]`. Establish `h3 : Jm ε * Y = -(Yᴴ * Jm ε)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul, Matrix.neg_mul]`. Use `show Yᴴ * Jm ε + Jm ε * Y = 0`.

Rewrite using `[h3, add_neg_cancel]`.
-/
theorem inG_of_exp {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (hU : inUJ ε (NormedSpace.exp Y)) (h1 : ℓ (NormedSpace.exp Y) = Y)
    (h2 : ℓ (NormedSpace.exp (Jm ε * (-Yᴴ) * Jm ε)) = Jm ε * (-Yᴴ) * Jm ε) : inG ε Y := by
  have hJ := Jm_mul_self_eq_one' ε
  have hU' : (NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y = Jm ε := hU
  have hEE : NormedSpace.exp Y * NormedSpace.exp (-Y) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl Y)), add_neg_cancel,
      NormedSpace.exp_zero]
  have key : NormedSpace.exp (Jm ε * (-Yᴴ) * Jm ε) = NormedSpace.exp Y := by
    have e1 : Jm ε * (-Yᴴ) * Jm ε = Jm ε * (-Y)ᴴ * (Jm ε)⁻¹ := by
      rw [Jm_inv, Matrix.conjTranspose_neg]
    rw [e1, Matrix.exp_conj _ _ (Jm_isUnit ε), Jm_inv, Matrix.exp_conjTranspose]
    calc Jm ε * (NormedSpace.exp (-Y))ᴴ * Jm ε
        = Jm ε * (NormedSpace.exp (-Y))ᴴ * ((NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y) := by
          rw [hU']
      _ = Jm ε * (NormedSpace.exp Y * NormedSpace.exp (-Y))ᴴ * Jm ε * NormedSpace.exp Y := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = NormedSpace.exp Y := by
          rw [hEE, Matrix.conjTranspose_one, Matrix.mul_one, hJ, Matrix.one_mul]
  have hY : Y = Jm ε * (-Yᴴ) * Jm ε := by rw [← h2, key, h1]
  have h3 : Jm ε * Y = -(Yᴴ * Jm ε) := by
    calc Jm ε * Y = Jm ε * (Jm ε * (-Yᴴ) * Jm ε) := congrArg (Jm ε * ·) hY
      _ = -(Yᴴ * Jm ε) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul, Matrix.neg_mul]
  show Yᴴ * Jm ε + Jm ε * Y = 0
  rw [h3, add_neg_cancel]

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

/- English proof (translation)
Establish `h'` using `congrFun (congrFun (show Yᴴ * Jm ε + Jm ε * Y = 0 from h) i) j`. Simplify `h'` using `[Jm, sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]`.
-/
theorem entry_of_inG {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) (i j : Fin n) :
    star (Y j i) * sg ε j + sg ε i * Y i j = 0 := by
  have h' := congrFun (congrFun (show Yᴴ * Jm ε + Jm ε * Y = 0 from h) i) j
  simpa [Jm, sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h'

/- English proof (translation)
Use `show Yᴴ * Jm ε + Jm ε * Y = 0`. Use extensionality with `i j`. Simplify `h i j` using `[Jm, sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]`.
-/
theorem inG_of_entry' {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i j, star (Y j i) * sg ε j + sg ε i * Y i j = 0) : inG ε Y := by
  show Yᴴ * Jm ε + Jm ε * Y = 0
  ext i j
  simpa [Jm, sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h i j

def cLin (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] GCo ε where
  toFun Y := ((fun a => (Y a a).im, fun ab => Y ab.1.1 ab.1.2), fun ab => Y ab.1.1 ab.1.2)
  map_add' _ _ := by
    ext <;> simp
  map_smul' _ _ := by
    ext <;> simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cLin_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cLin ε Y = ((fun a => (Y a a).im, fun ab => Y ab.1.1 ab.1.2), fun ab => Y ab.1.1 ab.1.2) := rfl

/- English proof (translation)
Take `⟨⟨d, k⟩, p⟩` from `s`. Rewrite using `[cLin_apply]`. Use `Prod.ext (Prod.ext ?_ ?_) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Simplify using `[gMat, kMat, pmat]`.

Use function extensionality and compare the values at `ab`. Take `⟨⟨a, b⟩, hab⟩` from `ab`. Establish `h1 : a ≠ b` using `ne_of_gt hab.1`. Establish `h2 : ¬ a < b` using `not_lt_of_gt hab.1`. Simplify using `[gMat, kMat, pmat, h1, h2, hab.1, hab.2]`.

Use function extensionality and compare the values at `ab`. Take `⟨⟨a, b⟩, hab⟩` from `ab`. Establish `h1 : a ≠ b` using `ne_of_gt hab.1`. Establish `h2 : ¬ a < b` using `not_lt_of_gt hab.1`. Simplify using `[gMat, kMat, pmat, h1, h2, hab.1, hab.2]`.
-/
theorem cLin_gMat {ε : Fin n → Bool} (s : GCo ε) : cLin ε (gMat s) = s := by
  obtain ⟨⟨d, k⟩, p⟩ := s
  rw [cLin_apply]
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a
    simp [gMat, kMat, pmat]
  · funext ab
    obtain ⟨⟨a, b⟩, hab⟩ := ab
    have h1 : a ≠ b := ne_of_gt hab.1
    have h2 : ¬ a < b := not_lt_of_gt hab.1
    simp [gMat, kMat, pmat, h1, h2, hab.1, hab.2]
  · funext ab
    obtain ⟨⟨a, b⟩, hab⟩ := ab
    have h1 : a ≠ b := ne_of_gt hab.1
    have h2 : ¬ a < b := not_lt_of_gt hab.1
    simp [gMat, kMat, pmat, h1, h2, hab.1, hab.2]

/- English proof (translation)
Use extensionality with `a b`. Establish `hE` using `entry_of_inG h a b`. Rewrite using `[cLin_apply]`. Simplify using `only [gMat, kMat, pmat, Matrix.add_apply]`. Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases.

Establish `h1 : a ≠ b` using `ne_of_lt hab`. Establish `h2 : ¬ b < a` using `not_lt_of_gt hab`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;>`. Apply the tactic sequence `simp only [sg, ha, hb, ↓reduceIte, Bool.false_eq_true] at hE <;>`. Apply the tactic sequence `simp [ha, hb, h1, h2, hab] <;>`.

Apply the tactic sequence `(try simp only [Complex.star_def] at hE) <;>`. Apply the tactic sequence `first | linear_combination hE | linear_combination -hE`. Establish `h0 : star (Y a a) + Y a a = 0`. Apply the tactic sequence `cases ha : ε a <;> simp only [sg, ha, ↓reduceIte, Bool.false_eq_true] at hE <;> first | linear_combination hE | linear_combination -hE`. Establish `hre : (Y a a).re = 0`.

Establish `h4` using `congrArg Complex.re h0`. Simplify using `at h4`. Combine the linear equalities and inequalities to obtain the conclusion. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`. Establish `h1 : a ≠ b` using `ne_of_gt hab`.

Establish `h2 : ¬ a < b` using `not_lt_of_gt hab`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, h1, h2, hab]`.
-/
theorem gMat_cLin {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) :
    gMat (cLin ε Y) = Y := by
  ext a b
  have hE := entry_of_inG h a b
  rw [cLin_apply]
  simp only [gMat, kMat, pmat, Matrix.add_apply]
  rcases lt_trichotomy a b with hab | rfl | hab
  · have h1 : a ≠ b := ne_of_lt hab
    have h2 : ¬ b < a := not_lt_of_gt hab
    cases ha : ε a <;> cases hb : ε b <;>
      simp only [sg, ha, hb, ↓reduceIte, Bool.false_eq_true] at hE <;>
      simp [ha, hb, h1, h2, hab] <;>
      (try simp only [Complex.star_def] at hE) <;>
      first | linear_combination hE | linear_combination -hE
  · have h0 : star (Y a a) + Y a a = 0 := by
      cases ha : ε a <;> simp only [sg, ha, ↓reduceIte, Bool.false_eq_true] at hE <;>
        first | linear_combination hE | linear_combination -hE
    have hre : (Y a a).re = 0 := by
      have h4 := congrArg Complex.re h0
      simp at h4
      linarith
    apply Complex.ext <;> simp [hre]
  · have h1 : a ≠ b := ne_of_gt hab
    have h2 : ¬ a < b := not_lt_of_gt hab
    cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb, h1, h2, hab]

/- English proof (translation)
Simplify using `[sg, h]`.
-/
theorem sg_eq {ε : Fin n → Bool} {i j : Fin n} (h : ε i = ε j) : sg ε i = sg ε j := by
  simp [sg, h]

/- English proof (translation)
Unfold `sg`. Apply the tactic sequence `cases hi : ε i <;> cases hj : ε j <;> simp_all`.
-/
theorem sg_ne {ε : Fin n → Bool} {i j : Fin n} (h : ¬ ε i = ε j) : sg ε i = -sg ε j := by
  unfold sg
  cases hi : ε i <;> cases hj : ε j <;> simp_all

/- English proof (translation)
Apply `inG_of_entry'` to reduce the goal to its premises. Introduce `i j`. Take `⟨⟨d, k⟩, p⟩` from `s`. Simplify using `only [gMat, kMat, pmat, Matrix.add_apply]`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases.

Establish `h1 : i ≠ j` using `ne_of_lt hij`. Establish `h2 : ¬ j < i` using `not_lt_of_gt hij`. Distinguish the cases in `hε : ε i = ε j`. Simplify using `[hε, h1, h1.symm, h2, hij, sg_eq hε]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[hε, Ne.symm hε, h1, h1.symm, h2, hij, sg_ne hε]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `simp <;> ring`. Establish `h1 : i ≠ j` using `ne_of_gt hij`. Establish `h2 : ¬ i < j` using `not_lt_of_gt hij`.

Distinguish the cases in `hε : ε i = ε j`. Simplify using `[hε, h1, h1.symm, h2, hij, sg_eq hε]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hε, Ne.symm hε, h1, h1.symm, h2, hij, sg_ne hε]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inG_gMat {ε : Fin n → Bool} (s : GCo ε) : inG ε (gMat s) := by
  apply inG_of_entry'
  intro i j
  obtain ⟨⟨d, k⟩, p⟩ := s
  simp only [gMat, kMat, pmat, Matrix.add_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · have h1 : i ≠ j := ne_of_lt hij
    have h2 : ¬ j < i := not_lt_of_gt hij
    by_cases hε : ε i = ε j
    · simp [hε, h1, h1.symm, h2, hij, sg_eq hε]
      ring
    · simp [hε, Ne.symm hε, h1, h1.symm, h2, hij, sg_ne hε]
      ring
  · simp <;> ring
  · have h1 : i ≠ j := ne_of_gt hij
    have h2 : ¬ i < j := not_lt_of_gt hij
    by_cases hε : ε i = ε j
    · simp [hε, h1, h1.symm, h2, hij, sg_eq hε]
      ring
    · simp [hε, Ne.symm hε, h1, h1.symm, h2, hij, sg_ne hε]
      ring

end ReciprocityTheory.ChartRestriction.DS.HPol
