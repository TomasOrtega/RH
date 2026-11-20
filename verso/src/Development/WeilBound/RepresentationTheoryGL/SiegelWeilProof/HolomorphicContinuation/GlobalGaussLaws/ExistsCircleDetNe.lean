import Mathlib

noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacU

variable {n : ℕ}

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `set p := (-W).charpoly with hp`. Establish `hp0 : p ≠ 0` using `(Matrix.charpoly_monic _).ne_zero`. Establish `hev : ∀ x : ℂ, p.eval x = (W + x • 1).det`.

Introduce `x`. Rewrite using `[hp, Matrix.eval_charpoly]`. Use `congr 1`. Rewrite using `[Matrix.scalar_apply, sub_neg_eq_add, add_comm, Matrix.smul_one_eq_diagonal]`. Set `r : Fin (n + 1) → ℝ` to `fun k => (k : ℝ) / ((n : ℝ) + 1)`.

Set `f : Fin (n + 1) → ℂ` to `fun k => cexp (I * (r k : ℂ))`. Establish `hr0 : ∀ k, 0 ≤ r k` using `fun k => by simp only [r]; positivity`. Establish `hr1 : ∀ k, r k < 1` using `fun k => by`. Simplify using `only [r]; rw [div_lt_one (by positivity)]; exact_mod_cast k.2`. Establish `hf : Function.Injective f`.

Introduce `k k' h`. Take `⟨z, hz⟩` from `Complex.exp_eq_exp_iff_exists_int.1 h`. Establish `hre : r k = r k' + z * (2 * Real.pi)`. Use `congrArg Complex.im hz` as an intermediate fact. Simplify `this` using `[Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im]`.

Establish `hz0 : z = 0`. Assume the negation of the conclusion as `hz0`. Establish `h1 : (1 : ℝ) ≤ |(z : ℝ)|`. Rewrite using `[← Int.cast_abs]`. Conclude with `Int.one_le_abs hz0` after adjusting the coercions.

Establish `habs : |(z : ℝ) * (2 * Real.pi)| < 1`. Apply the tactic sequence `rw [abs_lt]; constructor <;> linarith [hr0 k, hr0 k', hr1 k, hr1 k']`. Rewrite `habs` using `[abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]`. Use polynomial arithmetic with `[Real.pi_gt_three]`. Rewrite `hre` using `[hz0]`.

Simplify using `only [Int.cast_zero, zero_mul, add_zero, r] at hre`. Establish `hpos : (0 : ℝ) < (n : ℝ) + 1` using `by positivity`. Establish `: (k : ℝ) = k'`. Clear denominators, using `at hre` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `Fin.ext (by exact_mod_cast this)`. Establish `hroot : ∀ k, f k ∈ p.roots.toFinset`. Introduce `k`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot, hev]`. Apply `hcon` to reduce the goal to its premises.

Simplify using `only [f]`. Rewrite using `[Complex.norm_exp]`. Simplify using the standard rewrite rules. Establish `hcard : (Finset.univ.image f).card ≤ p.roots.toFinset.card` using `Finset.card_le_card (fun x hx => by`. Take `⟨k, _, rfl⟩` from `Finset.mem_image.1 hx`.

Conclude with `hroot k)`. Rewrite `hcard` using `[Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]`. Establish `h1` using `(Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)`. Establish `h2 : p.natDegree = n`. Rewrite using `[hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_circle_det_ne (W : Matrix (Fin n) (Fin n) ℂ) : ∃ lam : ℂ, ‖lam‖ = 1 ∧ (W + lam • 1).det ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set p := (-W).charpoly with hp
  have hp0 : p ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hev : ∀ x : ℂ, p.eval x = (W + x • 1).det := by
    intro x
    rw [hp, Matrix.eval_charpoly]
    congr 1
    rw [Matrix.scalar_apply, sub_neg_eq_add, add_comm, Matrix.smul_one_eq_diagonal]
  let r : Fin (n + 1) → ℝ := fun k => (k : ℝ) / ((n : ℝ) + 1)
  let f : Fin (n + 1) → ℂ := fun k => cexp (I * (r k : ℂ))
  have hr0 : ∀ k, 0 ≤ r k := fun k => by simp only [r]; positivity
  have hr1 : ∀ k, r k < 1 := fun k => by
    simp only [r]; rw [div_lt_one (by positivity)]; exact_mod_cast k.2
  have hf : Function.Injective f := by
    intro k k' h
    obtain ⟨z, hz⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    have hre : r k = r k' + z * (2 * Real.pi) := by
      have := congrArg Complex.im hz
      simpa [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im] using this
    have hz0 : z = 0 := by
      by_contra hz0
      have h1 : (1 : ℝ) ≤ |(z : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz0
      have habs : |(z : ℝ) * (2 * Real.pi)| < 1 := by
        rw [abs_lt]; constructor <;> linarith [hr0 k, hr0 k', hr1 k, hr1 k']
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at habs
      nlinarith [Real.pi_gt_three]
    rw [hz0] at hre
    simp only [Int.cast_zero, zero_mul, add_zero, r] at hre
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have : (k : ℝ) = k' := by
      field_simp at hre; linarith
    exact Fin.ext (by exact_mod_cast this)
  have hroot : ∀ k, f k ∈ p.roots.toFinset := by
    intro k
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot, hev]
    apply hcon
    simp only [f]
    rw [Complex.norm_exp]
    simp
  have hcard : (Finset.univ.image f).card ≤ p.roots.toFinset.card :=
    Finset.card_le_card (fun x hx => by
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hx; exact hroot k)
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] at hcard
  have h1 := (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)
  have h2 : p.natDegree = n := by
    rw [hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  omega

/- English proof (translation)
Establish `hW' : W * Wᴴ = 1` using `mul_eq_one_comm.1 hW`. Take `⟨lam, hlam1, hdet⟩` from `exists_circle_det_ne W`. Establish `hlam0 : lam ≠ 0` using `by intro h; rw [h, norm_zero] at hlam1; exact zero_ne_one hlam1`. Establish `hconj : starRingEnd ℂ lam * lam = 1`. Rewrite using `[Complex.conj_mul', hlam1]`.

Simplify using the standard rewrite rules. Use `set V' := lam⁻¹ • W with hV'`. Establish `hV'u : V'ᴴ * V' = 1`. Rewrite using `[hV', Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hW]`. Rewrite using `[RCLike.star_def, map_inv₀]`.

Rewrite using `[show (starRingEnd ℂ lam)⁻¹ * lam⁻¹ = (starRingEnd ℂ lam * lam)⁻¹ by rw [mul_inv], hconj, inv_one, one_smul]`. Use `set B := 1 + V' with hB`. Use `set A := 1 - V' with hA`. Establish `hBdet : IsUnit B.det`. Rewrite using `[isUnit_iff_ne_zero]`.

Establish `: B = lam⁻¹ • (W + lam • 1)`. Rewrite using `[hB, hV', smul_add, smul_smul, inv_mul_cancel₀ hlam0, one_smul, add_comm]`. Rewrite using `[this, Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ (inv_ne_zero hlam0)) hdet`. Use `set H := (Complex.I • A) * B⁻¹ with hH`.

Establish `hHB : H * B = Complex.I • A`. Rewrite using `[hH, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBdet, Matrix.mul_one]`. Establish `hBc : IsUnit Bᴴ.det` using `by rw [Matrix.det_conjTranspose]; exact hBdet.star`. Establish `hid : Bᴴ * A = -(Aᴴ * B)`. Rewrite using `[hB, hA, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]`.

Simplify using `only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hV'u]`. Normalize the expressions using the abelian group laws. Establish `hHerm : H.IsHermitian`. Establish `hk : Bᴴ * Hᴴ * B = Bᴴ * H * B`. Establish `e1 : Bᴴ * Hᴴ = -(Complex.I • Aᴴ)`.

Rewrite using `[← Matrix.conjTranspose_mul, hHB, Matrix.conjTranspose_smul]`. Simplify using `[RCLike.star_def, Complex.conj_I]`. Rewrite using `[e1, Matrix.mul_assoc, hHB, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, hid, smul_neg]`. Establish `hk2 : Hᴴ = H`. Use `congrArg (fun M => (Bᴴ)⁻¹ * M * B⁻¹) hk` as an intermediate fact.

Rewrite `this` using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBc, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBdet, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBc, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv …`. Then use the resulting hypothesis. Conclude with `hk2`. Use `set U : Matrix (Fin n) (Fin n) ℂ := (hHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU`. Use `set d : Fin n → ℝ := hHerm.eigenvalues with hd`. Establish `hUu : Uᴴ * U = 1`.

Rewrite using `[hU]`. Conclude with `Matrix.mem_unitaryGroup_iff'.1 hHerm.eigenvectorUnitary.2`. Establish `hUu' : U * Uᴴ = 1` using `mul_eq_one_comm.1 hUu`. Establish `hspec : H = U * diagonal (fun j => ((d j : ℝ) : ℂ)) * Uᴴ`. Use `hHerm.spectral_theorem` as an intermediate fact.

Rewrite `this` using `[Unitary.conjStarAlgAut_apply]`. Conclude with `this`. Establish `hdI : ∀ j, ((d j : ℝ) : ℂ) + Complex.I ≠ 0`. Introduce `j h`. Use `congrArg Complex.im h` as an intermediate fact.

Simplify using `at this`. Use `set E : Fin n → ℂ := fun j => (Complex.I - (d j : ℂ)) / (Complex.I + (d j : ℂ)) with hE`. Establish `hHdiag : H + Complex.I • 1 = U * diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * Uᴴ`. Establish `e : diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) = diagonal (fun j => ((d j : ℝ) : ℂ)) + Complex.I • 1`. Rewrite using `[Matrix.smul_one_eq_diagonal, diagonal_add]`.

Rewrite using `[e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUu', hspec]`. Establish `hHI : IsUnit (H + Complex.I • 1).det`. Rewrite using `[isUnit_iff_ne_zero, hHdiag, Matrix.det_mul, Matrix.det_mul, det_diagonal]`. Establish `hU1 : U.det * Uᴴ.det = 1` using `by rw [← Matrix.det_mul, hUu', Matrix.det_one]`. Introduce `h0`.

Establish `: U.det * Uᴴ.det * ∏ j, (((d j : ℝ) : ℂ) + Complex.I) = 0`. Rewrite using `[show U.det * Uᴴ.det * ∏ j, (((d j : ℝ) : ℂ) + Complex.I) = U.det * (∏ j, (((d j : ℝ) : ℂ) + Complex.I)) * Uᴴ.det by ring]`. Conclude with `h0`. Rewrite `this` using `[hU1, one_mul]`. Conclude with `(Finset.prod_ne_zero_iff.2 fun j _ => hdI j) this`.

Establish `hEq1 : (H + Complex.I • 1) * V' = Complex.I • 1 - H`. Use `hHB` as an intermediate fact. Rewrite `this` using `[hB, hA, Matrix.mul_add, Matrix.mul_one, smul_sub]`. Rewrite using `[Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]`. Rewrite using `[← sub_eq_zero]`.

Rewrite `this` using `[← sub_eq_zero]`. Rewrite using `[← this]`. Normalize the expressions using the abelian group laws. Establish `hEq2 : (H + Complex.I • 1) * (U * diagonal E * Uᴴ) = Complex.I • 1 - H`. Rewrite using `[hHdiag]`.

Establish `e1 : U * diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * Uᴴ * (U * diagonal E * Uᴴ) = U * (diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * diagonal E) * Uᴴ`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Uᴴ U, hUu, Matrix.one_mul]`. Rewrite using `[e1, diagonal_mul_diagonal]`. Establish `e2 : (fun j => (((d j : ℝ) : ℂ) + Complex.I) * E j) = fun j => Complex.I - ((d j : ℝ) : ℂ)`.

Use function extensionality and compare the values at `j`. Establish `hdI' : Complex.I + ((d j : ℝ) : ℂ) ≠ 0` using `by rw [add_comm]; exact hdI j`. Rewrite using `[hE]`. Simplify using `only`. Rewrite using `[add_comm ((d j : ℝ) : ℂ) Complex.I]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e2, hspec]`. Establish `e3 : diagonal (fun j => Complex.I - ((d j : ℝ) : ℂ)) = Complex.I • 1 - diagonal (fun j => ((d j : ℝ) : ℂ))`. Rewrite using `[Matrix.smul_one_eq_diagonal, ← diagonal_sub]`. Rewrite using `[e3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUu']`.

Establish `hV'eq : V' = U * diagonal E * Uᴴ`. Establish `h0 : (H + Complex.I • 1) * (V' - U * diagonal E * Uᴴ) = 0`. Rewrite using `[Matrix.mul_sub, hEq1, hEq2, sub_self]`. Use `congrArg (fun M => (H + Complex.I • 1)⁻¹ * M) h0` as an intermediate fact. Simplify using `only [Matrix.mul_zero] at this`.

Rewrite `this` using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHI, Matrix.one_mul, sub_eq_zero]`. Conclude with `this`. Use `⟨U, fun j => lam * E j, hUu, hUu', ?_, ?_⟩` and prove the remaining obligations. Introduce `j`. Rewrite using `[norm_mul, hlam1, one_mul, hE]`.

Simplify using `only`. Rewrite using `[norm_div]`. Establish `h1 : ‖Complex.I - ((d j : ℝ) : ℂ)‖ = ‖Complex.I + ((d j : ℝ) : ℂ)‖`. Rewrite using `[← Complex.norm_conj (Complex.I + _)]`. Simplify using `[Complex.conj_I, Complex.conj_ofReal, ← neg_add']`.

Rewrite using `[← norm_neg]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, div_self]`. Introduce `h0; rw [norm_eq_zero] at h0; exact hdI j (by rw [add_comm]; exact h0)`.

Establish `: W = lam • V'` using `by rw [hV', smul_smul, mul_inv_cancel₀ hlam0, one_smul]`. Establish `hd2 : diagonal (fun j => lam * E j) = lam • diagonal E`. Apply the tactic sequence `ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]`. Rewrite using `[this, hV'eq, hd2, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem unitary_diag (W : Matrix (Fin n) (Fin n) ℂ) (hW : Wᴴ * W = 1) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ), Pᴴ * P = 1 ∧ P * Pᴴ = 1 ∧ (∀ j, ‖w j‖ = 1) ∧
      W = P * diagonal w * Pᴴ := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.1 hW
  obtain ⟨lam, hlam1, hdet⟩ := exists_circle_det_ne W
  have hlam0 : lam ≠ 0 := by intro h; rw [h, norm_zero] at hlam1; exact zero_ne_one hlam1
  have hconj : starRingEnd ℂ lam * lam = 1 := by
    rw [Complex.conj_mul', hlam1]; simp
  set V' := lam⁻¹ • W with hV'
  have hV'u : V'ᴴ * V' = 1 := by
    rw [hV', Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hW]
    rw [RCLike.star_def, map_inv₀]
    rw [show (starRingEnd ℂ lam)⁻¹ * lam⁻¹ = (starRingEnd ℂ lam * lam)⁻¹ by rw [mul_inv], hconj, inv_one, one_smul]
  set B := 1 + V' with hB
  set A := 1 - V' with hA
  have hBdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    have : B = lam⁻¹ • (W + lam • 1) := by
      rw [hB, hV', smul_add, smul_smul, inv_mul_cancel₀ hlam0, one_smul, add_comm]
    rw [this, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hlam0)) hdet
  set H := (Complex.I • A) * B⁻¹ with hH
  have hHB : H * B = Complex.I • A := by
    rw [hH, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBdet, Matrix.mul_one]
  have hBc : IsUnit Bᴴ.det := by rw [Matrix.det_conjTranspose]; exact hBdet.star
  have hid : Bᴴ * A = -(Aᴴ * B) := by
    rw [hB, hA, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hV'u]
    abel
  have hHerm : H.IsHermitian := by
    have hk : Bᴴ * Hᴴ * B = Bᴴ * H * B := by
      have e1 : Bᴴ * Hᴴ = -(Complex.I • Aᴴ) := by
        rw [← Matrix.conjTranspose_mul, hHB, Matrix.conjTranspose_smul]
        simp [RCLike.star_def, Complex.conj_I]
      rw [e1, Matrix.mul_assoc, hHB, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, hid, smul_neg]
    have hk2 : Hᴴ = H := by
      have := congrArg (fun M => (Bᴴ)⁻¹ * M * B⁻¹) hk
      rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBc, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hBdet, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hBc, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBdet,
        Matrix.mul_one] at this
    exact hk2
  set U : Matrix (Fin n) (Fin n) ℂ := (hHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set d : Fin n → ℝ := hHerm.eigenvalues with hd
  have hUu : Uᴴ * U = 1 := by
    rw [hU]; exact Matrix.mem_unitaryGroup_iff'.1 hHerm.eigenvectorUnitary.2
  have hUu' : U * Uᴴ = 1 := mul_eq_one_comm.1 hUu
  have hspec : H = U * diagonal (fun j => ((d j : ℝ) : ℂ)) * Uᴴ := by
    have := hHerm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hdI : ∀ j, ((d j : ℝ) : ℂ) + Complex.I ≠ 0 := by
    intro j h; have := congrArg Complex.im h; simp at this
  set E : Fin n → ℂ := fun j => (Complex.I - (d j : ℂ)) / (Complex.I + (d j : ℂ)) with hE
  have hHdiag : H + Complex.I • 1 = U * diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * Uᴴ := by
    have e : diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) = diagonal (fun j => ((d j : ℝ) : ℂ)) + Complex.I • 1 := by
      rw [Matrix.smul_one_eq_diagonal, diagonal_add]
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUu', hspec]
  have hHI : IsUnit (H + Complex.I • 1).det := by
    rw [isUnit_iff_ne_zero, hHdiag, Matrix.det_mul, Matrix.det_mul, det_diagonal]
    have hU1 : U.det * Uᴴ.det = 1 := by rw [← Matrix.det_mul, hUu', Matrix.det_one]
    intro h0
    have : U.det * Uᴴ.det * ∏ j, (((d j : ℝ) : ℂ) + Complex.I) = 0 := by
      rw [show U.det * Uᴴ.det * ∏ j, (((d j : ℝ) : ℂ) + Complex.I) = U.det * (∏ j, (((d j : ℝ) : ℂ) + Complex.I)) * Uᴴ.det by ring]
      exact h0
    rw [hU1, one_mul] at this
    exact (Finset.prod_ne_zero_iff.2 fun j _ => hdI j) this
  have hEq1 : (H + Complex.I • 1) * V' = Complex.I • 1 - H := by
    have := hHB
    rw [hB, hA, Matrix.mul_add, Matrix.mul_one, smul_sub] at this
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at this
    rw [← this]
    abel
  have hEq2 : (H + Complex.I • 1) * (U * diagonal E * Uᴴ) = Complex.I • 1 - H := by
    rw [hHdiag]
    have e1 : U * diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * Uᴴ * (U * diagonal E * Uᴴ) =
        U * (diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * diagonal E) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hUu, Matrix.one_mul]
    rw [e1, diagonal_mul_diagonal]
    have e2 : (fun j => (((d j : ℝ) : ℂ) + Complex.I) * E j) = fun j => Complex.I - ((d j : ℝ) : ℂ) := by
      funext j
      have hdI' : Complex.I + ((d j : ℝ) : ℂ) ≠ 0 := by rw [add_comm]; exact hdI j
      rw [hE]; simp only; rw [add_comm ((d j : ℝ) : ℂ) Complex.I]; field_simp
    rw [e2, hspec]
    have e3 : diagonal (fun j => Complex.I - ((d j : ℝ) : ℂ)) = Complex.I • 1 - diagonal (fun j => ((d j : ℝ) : ℂ)) := by
      rw [Matrix.smul_one_eq_diagonal, ← diagonal_sub]
    rw [e3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUu']
  have hV'eq : V' = U * diagonal E * Uᴴ := by
    have h0 : (H + Complex.I • 1) * (V' - U * diagonal E * Uᴴ) = 0 := by
      rw [Matrix.mul_sub, hEq1, hEq2, sub_self]
    have := congrArg (fun M => (H + Complex.I • 1)⁻¹ * M) h0
    simp only [Matrix.mul_zero] at this
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHI, Matrix.one_mul, sub_eq_zero] at this
    exact this
  refine ⟨U, fun j => lam * E j, hUu, hUu', ?_, ?_⟩
  · intro j
    rw [norm_mul, hlam1, one_mul, hE]
    simp only
    rw [norm_div]
    have h1 : ‖Complex.I - ((d j : ℝ) : ℂ)‖ = ‖Complex.I + ((d j : ℝ) : ℂ)‖ := by
      rw [← Complex.norm_conj (Complex.I + _)]; simp [Complex.conj_I, Complex.conj_ofReal, ← neg_add']
      rw [← norm_neg]; congr 1; ring
    rw [h1, div_self]
    intro h0; rw [norm_eq_zero] at h0; exact hdI j (by rw [add_comm]; exact h0)
  · have : W = lam • V' := by rw [hV', smul_smul, mul_inv_cancel₀ hlam0, one_smul]
    have hd2 : diagonal (fun j => lam * E j) = lam • diagonal E := by
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
    rw [this, hV'eq, hd2, Matrix.mul_smul, Matrix.smul_mul]

end PositivityTheory.Rg.Sw.Glob.VacU
