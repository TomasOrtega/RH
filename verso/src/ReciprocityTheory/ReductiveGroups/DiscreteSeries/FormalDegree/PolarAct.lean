import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.AdKMeasurePreserving
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def plog (h : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Matrix.isHermitian_conjTranspose_mul_self h).cfc Real.log

def actR {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ) (z : PCoord ε → ℂ) : PCoord ε → ℂ :=
  fun ab => plog (NormedSpace.exp (pmat z) * g) ab.1.1 ab.1.2

/- English proof (translation)
Establish `hSA : IsSelfAdjoint X` using `Matrix.isHermitian_iff_isSelfAdjoint.mp hX`. Take `⟨W, hWdef⟩ : ∃ W, W = (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)` from `⟨_, rfl⟩`. Establish `hW : star W * W = 1`. Rewrite using `[hWdef]`. Conclude with `Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2`.

Establish `hWi : W⁻¹ = star W` using `Matrix.inv_eq_left_inv hW`. Establish `hWu : IsUnit W` using `(Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hW)`. Establish `hexp : NormedSpace.exp X = hX.cfc Real.exp`. Establish `hd : NormedSpace.exp (RCLike.ofReal ∘ hX.eigenvalues : Fin n → ℂ) = (RCLike.ofReal ∘ Real.exp ∘ hX.eigenvalues : Fin n → ℂ)`. Use function extensionality and compare the values at `i`.

Simplify using `[Complex.ofReal_exp, ← Complex.exp_eq_exp_ℂ]`. Use `conv_lhs => rw [hX.spectral_theorem]`. Rewrite using `[Matrix.IsHermitian.cfc]`. Simplify using `only [Unitary.conjStarAlgAut_apply, Unitary.coe_star]`. Rewrite using `[← hWdef, ← hWi, Matrix.exp_conj _ _ hWu, Matrix.exp_diagonal, hd]`.

Rewrite using `[← Matrix.IsHermitian.cfc_eq, hexp, ← Matrix.IsHermitian.cfc_eq, ← cfc_comp Real.log Real.exp X hSA (Real.continuousOn_log.mono (by rintro _ ⟨x, -, rfl⟩; exact (Real.exp_pos x).ne')) Real.continuous_exp.continuousOn]`. Establish `hle : Real.log ∘ Real.exp = id` using `funext Real.log_exp`. Rewrite using `[hle]`. Conclude with `cfc_id ℝ X hSA`.
-/
theorem pact_cfc_log_exp (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian)
    (h : (NormedSpace.exp X).IsHermitian) : h.cfc Real.log = X := by
  have hSA : IsSelfAdjoint X := Matrix.isHermitian_iff_isSelfAdjoint.mp hX
  obtain ⟨W, hWdef⟩ : ∃ W, W = (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hW : star W * W = 1 := by
    rw [hWdef]
    exact Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2
  have hWi : W⁻¹ = star W := Matrix.inv_eq_left_inv hW
  have hWu : IsUnit W := (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hW)
  have hexp : NormedSpace.exp X = hX.cfc Real.exp := by
    have hd : NormedSpace.exp (RCLike.ofReal ∘ hX.eigenvalues : Fin n → ℂ) =
        (RCLike.ofReal ∘ Real.exp ∘ hX.eigenvalues : Fin n → ℂ) := by
      funext i
      simp [Complex.ofReal_exp, ← Complex.exp_eq_exp_ℂ]
    conv_lhs => rw [hX.spectral_theorem]
    rw [Matrix.IsHermitian.cfc]
    simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star]
    rw [← hWdef, ← hWi, Matrix.exp_conj _ _ hWu, Matrix.exp_diagonal, hd]
  rw [← Matrix.IsHermitian.cfc_eq, hexp, ← Matrix.IsHermitian.cfc_eq,
    ← cfc_comp Real.log Real.exp X hSA
      (Real.continuousOn_log.mono (by rintro _ ⟨x, -, rfl⟩; exact (Real.exp_pos x).ne'))
      Real.continuous_exp.continuousOn]
  have hle : Real.log ∘ Real.exp = id := funext Real.log_exp
  rw [hle]
  exact cfc_id ℝ X hSA

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem pact_cfc_congr {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) (f : ℝ → ℝ) : hA.cfc f = hB.cfc f := by
  subst h
  rfl

/- English proof (translation)
Establish `hE : (NormedSpace.exp X)ᴴ = NormedSpace.exp X`. Rewrite using `[← Matrix.exp_conjTranspose, hX.eq]`. Establish `h2 : (k * NormedSpace.exp X)ᴴ * (k * NormedSpace.exp X) = NormedSpace.exp (X + X)`. Rewrite using `[Matrix.exp_add_of_commute X X (Commute.refl X), Matrix.conjTranspose_mul, hE, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k, hk, Matrix.one_mul]`. Establish `hB : (NormedSpace.exp (X + X)).IsHermitian`.

Rewrite using `[← h2]`. Conclude with `Matrix.isHermitian_conjTranspose_mul_self _`. Unfold `plog`. Rewrite using `[pact_cfc_congr (Matrix.isHermitian_conjTranspose_mul_self (k * NormedSpace.exp X)) hB h2 Real.log, pact_cfc_log_exp (X + X) (hX.add hX) hB, ← two_smul ℂ X, smul_smul]`. Evaluate the numerical expressions.
-/
theorem plog_unitary_mul_exp (k X : Matrix (Fin n) (Fin n) ℂ) (hk : kᴴ * k = 1) (hX : X.IsHermitian) :
    plog (k * NormedSpace.exp X) = X := by
  have hE : (NormedSpace.exp X)ᴴ = NormedSpace.exp X := by
    rw [← Matrix.exp_conjTranspose, hX.eq]
  have h2 : (k * NormedSpace.exp X)ᴴ * (k * NormedSpace.exp X) = NormedSpace.exp (X + X) := by
    rw [Matrix.exp_add_of_commute X X (Commute.refl X), Matrix.conjTranspose_mul, hE,
      Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k, hk, Matrix.one_mul]
  have hB : (NormedSpace.exp (X + X)).IsHermitian := by
    rw [← h2]
    exact Matrix.isHermitian_conjTranspose_mul_self _
  unfold plog
  rw [pact_cfc_congr (Matrix.isHermitian_conjTranspose_mul_self (k * NormedSpace.exp X)) hB h2 Real.log,
    pact_cfc_log_exp (X + X) (hX.add hX) hB, ← two_smul ℂ X, smul_smul]
  norm_num

/- English proof (translation)
Establish `hk` using `k.2`. Unfold `S7.KG Kset at hk`. Unfold `S7.toMK`. Conclude with `Matrix.mem_unitaryGroup_iff'.mp hk.1`.
-/
private theorem toMK_unit_lemma {ε : Fin n → Bool} (k : KG ε) : (toMK k)ᴴ * toMK k = 1 := by
  have hk := k.2
  unfold S7.KG Kset at hk
  unfold S7.toMK
  exact Matrix.mem_unitaryGroup_iff'.mp hk.1

/- English proof (translation)
The claim follows from `plog_unitary_mul_exp (toMK k) (pmat z) (toMK_unit_lemma k) (pmat_isHermitian z)`.
-/
theorem plog_polarM {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : plog (polarM (k, z)) = pmat z :=
  plog_unitary_mul_exp (toMK k) (pmat z) (toMK_unit_lemma k) (pmat_isHermitian z)

/- English proof (translation)
Use function extensionality and compare the values at `ab`. Take `⟨⟨a, b⟩, h⟩` from `ab`. Simplify using `only [pmat]`. Rewrite using `[dif_pos h]`.
-/
theorem pact_pmat_coords {ε : Fin n → Bool} (w : PCoord ε → ℂ) :
    (fun ab : PCoord ε => pmat w ab.1.1 ab.1.2) = w := by
  funext ab
  obtain ⟨⟨a, b⟩, h⟩ := ab
  simp only [pmat]
  rw [dif_pos h]

/- English proof (translation)
Unfold `actR`. Rewrite using `[h, plog_unitary_mul_exp U (pmat w) hU (pmat_isHermitian w)]`. Conclude with `pact_pmat_coords w`.
-/
private theorem actR_eq_lemma {ε : Fin n → Bool} {g U : Matrix (Fin n) (Fin n) ℂ} {z w : PCoord ε → ℂ}
    (hU : Uᴴ * U = 1) (h : NormedSpace.exp (pmat z) * g = U * NormedSpace.exp (pmat w)) :
    actR g z = w := by
  unfold actR
  rw [h, plog_unitary_mul_exp U (pmat w) hU (pmat_isHermitian w)]
  exact pact_pmat_coords w

/- English proof (translation)
Unfold `actR`. Rewrite using `[h, plog_polarM]`. Conclude with `pact_pmat_coords w`.
-/
theorem actR_of_eq_polarM {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} {z w : PCoord ε → ℂ} {k : KG ε}
    (h : NormedSpace.exp (pmat z) * g = polarM (k, w)) : actR g z = w := by
  unfold actR
  rw [h, plog_polarM]
  exact pact_pmat_coords w

/- English proof (translation)
Unfold `inUJ at *`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pact_inUJ_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) :
    inUJ ε (g * h) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hh]

/- English proof (translation)
Take `⟨⟨k, w⟩, hkw⟩` from `polarM_surj _ (pact_inUJ_mul (exp_pmat_inUJ z) hg)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[actR_of_eq_polarM hkw.symm]`. Conclude with `hkw.symm`.
-/
theorem actR_spec {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (z : PCoord ε → ℂ) :
    ∃ k : KG ε, NormedSpace.exp (pmat z) * g = polarM (k, actR g z) := by
  obtain ⟨⟨k, w⟩, hkw⟩ := polarM_surj _ (pact_inUJ_mul (exp_pmat_inUJ z) hg)
  refine ⟨k, ?_⟩
  rw [actR_of_eq_polarM hkw.symm]
  exact hkw.symm

/- English proof (translation)
Take `⟨k1, h1⟩` from `actR_spec hg z`. Take `⟨k2, h2⟩` from `actR_spec hh (actR g z)`. Simplify using `only [polarM] at h1 h2`. Apply `actR_eq_lemma (U := toMK k1 * toMK k2)` to reduce the goal to its premises. Rewrite using `[Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (toMK k1)ᴴ, toMK_unit_lemma k1, Matrix.one_mul, toMK_unit_lemma k2]`.

Rewrite using `[← Matrix.mul_assoc, h1, Matrix.mul_assoc (toMK k1) (NormedSpace.exp (pmat (actR g z))) h, h2, Matrix.mul_assoc (toMK k1) (toMK k2)]`.
-/
theorem actR_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h)
    (z : PCoord ε → ℂ) : actR (g * h) z = actR h (actR g z) := by
  obtain ⟨k1, h1⟩ := actR_spec hg z
  obtain ⟨k2, h2⟩ := actR_spec hh (actR g z)
  simp only [polarM] at h1 h2
  apply actR_eq_lemma (U := toMK k1 * toMK k2)
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (toMK k1)ᴴ, toMK_unit_lemma k1,
      Matrix.one_mul, toMK_unit_lemma k2]
  · rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc (toMK k1) (NormedSpace.exp (pmat (actR g z))) h, h2,
      Matrix.mul_assoc (toMK k1) (toMK k2)]

/- English proof (translation)
Apply `actR_eq_lemma (U := 1)` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[Matrix.mul_one, Matrix.one_mul]`.
-/
theorem actR_one {ε : Fin n → Bool} (z : PCoord ε → ℂ) : actR (1 : Matrix (Fin n) (Fin n) ℂ) z = z := by
  apply actR_eq_lemma (U := 1)
  · simp
  · rw [Matrix.mul_one, Matrix.one_mul]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[pmat]`.
-/
theorem pact_pmat_zero {ε : Fin n → Bool} : pmat (0 : PCoord ε → ℂ) = 0 := by
  ext a b
  simp [pmat]

/- English proof (translation)
Establish `hk` using `k.2`. Unfold `S7.KG Kset at hk`. Unfold `S7.toMK`. Conclude with `Matrix.mem_unitaryGroup_iff.mp hk.1`.
-/
private theorem toMK_unit_lemma_2 {ε : Fin n → Bool} (k : KG ε) : toMK k * (toMK k)ᴴ = 1 := by
  have hk := k.2
  unfold S7.KG Kset at hk
  unfold S7.toMK
  exact Matrix.mem_unitaryGroup_iff.mp hk.1

/- English proof (translation)
Establish `hU` using `toMK_unit_lemma k`. Establish `hU' : toMK k * (toMK k)ᴴ = 1` using `toMK_unit_lemma_2 k`. Establish `hinv : toMK k⁻¹ * toMK k = 1`. Simplify using `[S7.toMK, S7.toM]`. Establish `hi1 : (toMK k)⁻¹ = (toMK k)ᴴ` using `Matrix.inv_eq_left_inv hU`.

Establish `hi2 : (toMK k)⁻¹ = toMK k⁻¹` using `Matrix.inv_eq_left_inv hinv`. Establish `hunit : IsUnit (toMK k)` using `(Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hU)`. Apply `actR_eq_lemma hU` to reduce the goal to its premises. Establish `hi3 : (toMK k)⁻¹ᴴ = toMK k` using `by rw [hi1, Matrix.conjTranspose_conjTranspose]`. Rewrite using `[pmat_adK, ← hi2, hi3, Matrix.exp_conj' _ _ hunit, hi1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', Matrix.one_mul]`.
-/
theorem actR_K {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : actR (toMK k) z = adK k⁻¹ z := by
  have hU := toMK_unit_lemma k
  have hU' : toMK k * (toMK k)ᴴ = 1 := toMK_unit_lemma_2 k
  have hinv : toMK k⁻¹ * toMK k = 1 := by
    simp [S7.toMK, S7.toM]
  have hi1 : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_left_inv hU
  have hi2 : (toMK k)⁻¹ = toMK k⁻¹ := Matrix.inv_eq_left_inv hinv
  have hunit : IsUnit (toMK k) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hU)
  apply actR_eq_lemma hU
  have hi3 : (toMK k)⁻¹ᴴ = toMK k := by rw [hi1, Matrix.conjTranspose_conjTranspose]
  rw [pmat_adK, ← hi2, hi3, Matrix.exp_conj' _ _ hunit, hi1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU',
    Matrix.one_mul]

/- English proof (translation)
Apply `actR_eq_lemma (U := 1)` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[pact_pmat_zero, NormedSpace.exp_zero, Matrix.one_mul]`.
-/
theorem actR_exp_zero {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    actR (NormedSpace.exp (pmat y)) (0 : PCoord ε → ℂ) = y := by
  apply actR_eq_lemma (U := 1)
  · simp
  · rw [pact_pmat_zero, NormedSpace.exp_zero, Matrix.one_mul]

end ReciprocityTheory.ChartRestriction.DS
