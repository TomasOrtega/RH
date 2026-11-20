import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Unfold `Jm`. Rewrite using `[Matrix.mul_diagonal]`.
-/
lemma kfa_mul_Jm_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Y * Jm ε) a b = Y a b * (if ε b then 1 else -1) := by
  unfold Jm
  rw [Matrix.mul_diagonal]

/- English proof (translation)
Unfold `Jm`. Rewrite using `[Matrix.diagonal_mul]`.
-/
lemma kfa_Jm_mul_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Jm ε * Y) a b = (if ε a then 1 else -1) * Y a b := by
  unfold Jm
  rw [Matrix.diagonal_mul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h a b hab`. Establish `h1` using `congrFun (congrFun h a) b`. Rewrite `h1` using `[kfa_mul_Jm_apply, kfa_Jm_mul_apply]`. Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>`.

Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>`. Apply the tactic sequence `simp [ha, hb] at h1 hab <;>`. Use `first`. Consider the case `exact h1`. Consider the case `linear_combination h1`.

Consider the case `linear_combination (-1 / 2 : ℂ) * h1`. Consider the case `linear_combination (1 / 2 : ℂ) * h1`. Introduce `h`. Use extensionality with `a b`. Rewrite using `[kfa_mul_Jm_apply, kfa_Jm_mul_apply]`.

Distinguish the cases in `hab : ε a = ε b`. Rewrite using `[hab]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h a b hab]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma kfa_comm_iff_block (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y * Jm ε = Jm ε * Y ↔ IsBlock ε Y := by
  constructor
  · intro h a b hab
    have h1 := congrFun (congrFun h a) b
    rw [kfa_mul_Jm_apply, kfa_Jm_mul_apply] at h1
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
      simp [ha, hb] at h1 hab <;>
      first
      | exact h1
      | linear_combination h1
      | linear_combination (-1 / 2 : ℂ) * h1
      | linear_combination (1 / 2 : ℂ) * h1
  · intro h
    ext a b
    rw [kfa_mul_Jm_apply, kfa_Jm_mul_apply]
    by_cases hab : ε a = ε b
    · rw [hab]
      ring
    · rw [h a b hab]
      ring

/- English proof (translation)
Establish `hJJ : Jm ε * Jm ε = 1`. Unfold `Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `split_ifs <;> norm_num`. Unfold `inK inG`. Rewrite using `[← kfa_comm_iff_block]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨?_, h2⟩` and prove the remaining obligations. Establish `h3 : (Yᴴ + Y) * Jm ε = 0`. Rewrite using `[Matrix.add_mul, h2]`. Conclude with `h1`. Establish `h4` using `congrArg (· * Jm ε) h3`.

Simplify using `only [Matrix.mul_assoc, hJJ, Matrix.mul_one, Matrix.zero_mul] at h4`. Conclude with `eq_neg_of_add_eq_zero_left h4`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨?_, h2⟩` and prove the remaining obligations. Rewrite using `[h1, Matrix.neg_mul, h2, neg_add_cancel]`.
-/
lemma kfa_inK_iff (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    inK ε Y ↔ Yᴴ = -Y ∧ IsBlock ε Y := by
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  unfold inK inG
  rw [← kfa_comm_iff_block]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have h3 : (Yᴴ + Y) * Jm ε = 0 := by
      rw [Matrix.add_mul, h2]
      exact h1
    have h4 := congrArg (· * Jm ε) h3
    simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one, Matrix.zero_mul] at h4
    exact eq_neg_of_add_eq_zero_left h4
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1, Matrix.neg_mul, h2, neg_add_cancel]

section ExpL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Use `first`. Consider the case `exact NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)`. Consider the case `fun_prop`.
-/
lemma kfa_exp_cont (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
  first
  | exact NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)
  | fun_prop

/- English proof (translation)
The claim follows from `Commute.exp_left h`.
-/
lemma kfa_exp_comm {J X : Matrix (Fin n) (Fin n) ℂ} (h : X * J = J * X) :
    NormedSpace.exp X * J = J * NormedSpace.exp X := Commute.exp_left h

end ExpL

/- English proof (translation)
Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_left, neg_add_cancel, NormedSpace.exp_zero]`.
-/
lemma kfa_exp_neg_mul (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_left, neg_add_cancel, NormedSpace.exp_zero]

/- English proof (translation)
Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_right, add_neg_cancel, NormedSpace.exp_zero]`.
-/
lemma kfa_exp_mul_neg (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_right, add_neg_cancel, NormedSpace.exp_zero]

/- English proof (translation)
Rewrite using `[← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hY, smul_neg]`. Simplify using `only [Complex.star_def, Complex.conj_ofReal]`.
-/
lemma kfa_exp_conjTranspose {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Yᴴ = -Y) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Y))ᴴ = NormedSpace.exp (-((t : ℂ) • Y)) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hY, smul_neg]
  simp only [Complex.star_def, Complex.conj_ofReal]

def kfaUnit (Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  ⟨NormedSpace.exp ((t : ℂ) • Y), NormedSpace.exp (-((t : ℂ) • Y)), kfa_exp_mul_neg _, kfa_exp_neg_mul _⟩

/- English proof (translation)
Establish `hYJ : Y * Jm ε = Jm ε * Y` using `hY.2`. Establish `hsk : Yᴴ = -Y` using `((kfa_inK_iff ε Y).1 hY).1`. Unfold `Kset`. Rewrite using `[Set.mem_setOf_eq]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, kfa_exp_conjTranspose hsk, kfa_exp_mul_neg]`. Conclude with `kfa_exp_comm (by rw [Matrix.smul_mul, Matrix.mul_smul, hYJ])`.
-/
lemma kfa_mem_Kset (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Y) ∈ Kset ε := by
  have hYJ : Y * Jm ε = Jm ε * Y := hY.2
  have hsk : Yᴴ = -Y := ((kfa_inK_iff ε Y).1 hY).1
  unfold Kset
  rw [Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, kfa_exp_conjTranspose hsk,
      kfa_exp_mul_neg]
  · exact kfa_exp_comm (by rw [Matrix.smul_mul, Matrix.mul_smul, hYJ])

/- English proof (translation)
Establish `hYJ : Y * Jm ε = Jm ε * Y` using `hY.2`. Establish `hsk : Yᴴ = -Y` using `((kfa_inK_iff ε Y).1 hY).1`. Establish `hc : NormedSpace.exp ((t : ℂ) • Y) * Jm ε = Jm ε * NormedSpace.exp ((t : ℂ) • Y)` using `kfa_exp_comm (by rw [Matrix.smul_mul, Matrix.mul_smul, hYJ])`. Unfold `inUJ`. Rewrite using `[kfa_exp_conjTranspose hsk, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, kfa_exp_neg_mul, Matrix.one_mul]`.
-/
lemma kfa_inUJ (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    inUJ ε (NormedSpace.exp ((t : ℂ) • Y)) := by
  have hYJ : Y * Jm ε = Jm ε * Y := hY.2
  have hsk : Yᴴ = -Y := ((kfa_inK_iff ε Y).1 hY).1
  have hc : NormedSpace.exp ((t : ℂ) • Y) * Jm ε = Jm ε * NormedSpace.exp ((t : ℂ) • Y) :=
    kfa_exp_comm (by rw [Matrix.smul_mul, Matrix.mul_smul, hYJ])
  unfold inUJ
  rw [kfa_exp_conjTranspose hsk, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, kfa_exp_neg_mul,
    Matrix.one_mul]

def kfaUJ (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) : UJ ε :=
  ⟨kfaUnit Y t, kfa_inUJ ε hY t⟩

def kfaKG (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) : KG ε :=
  ⟨kfaUJ ε hY t, kfa_mem_Kset ε hY t⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma kfa_toMK (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    toMK (kfaKG ε hY t) = NormedSpace.exp ((t : ℂ) • Y) := rfl

/- English proof (translation)
Establish `hu : Continuous (kfaUnit Y)`. Use `Units.continuous_iff.2 ⟨kfa_exp_cont Y, ?_⟩` and prove the remaining obligations. Use `show Continuous fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Y))`. Simplify `kfa_exp_cont (-Y)` using `only [smul_neg]`. Conclude with `(hu.subtype_mk _).subtype_mk _`.
-/
lemma kfa_continuous (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    Continuous (kfaKG ε hY) := by
  have hu : Continuous (kfaUnit Y) := by
    refine Units.continuous_iff.2 ⟨kfa_exp_cont Y, ?_⟩
    show Continuous fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Y))
    simpa only [smul_neg] using kfa_exp_cont (-Y)
  exact (hu.subtype_mk _).subtype_mk _

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show NormedSpace.exp (((s + t : ℝ) : ℂ) • Y) = NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y)`. Rewrite using `[Complex.ofReal_add, add_smul]`.

Conclude with `Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)`.
-/
lemma kfa_add (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (s t : ℝ) :
    kfaKG ε hY (s + t) = kfaKG ε hY s * kfaKG ε hY t := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • Y) =
    NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y)
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)

end ReciprocityTheory.ChartRestriction.DS.S7
