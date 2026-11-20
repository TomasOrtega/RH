import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolTBase

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.HolTPf

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.LVs.HolB

variable {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨mkGR (nU h) (inG_upper hh), rfl⟩`.
-/
theorem nU_mem' {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.IsHermitian) : ∃ x : GR n, mR x = nU h :=
  ⟨mkGR (nU h) (inG_upper hh), rfl⟩

def mab (a b : Matrix (Fin n) (Fin n) ℂ) : M2 n := fromBlocks a 0 0 bᴴ

/- English proof (translation)
Establish `h1 : aᴴ * bᴴ = 1` using `by rw [← conjTranspose_mul, hba, conjTranspose_one]`. Unfold `InG JJ mab`. Simplify using `[fromBlocks_conjTranspose, fromBlocks_multiply, h1, hba]`.
-/
theorem inG_mab {a b : Matrix (Fin n) (Fin n) ℂ} (hba : b * a = 1) : InG (mab a b) := by
  have h1 : aᴴ * bᴴ = 1 := by rw [← conjTranspose_mul, hba, conjTranspose_one]
  unfold InG JJ mab
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, h1, hba]

/- English proof (translation)
The claim follows from `inG_mul (inG_upper hX) (inG_mab hba)`.
-/
theorem inG_nm {X a b : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) (hba : b * a = 1) :
    InG (nU X * mab a b) := inG_mul (inG_upper hX) (inG_mab hba)

/- English proof (translation)
Establish `hbh : bᴴ * aᴴ = 1` using `by rw [← conjTranspose_mul, hab, conjTranspose_one]`. Establish `hinv : (bᴴ)⁻¹ = aᴴ` using `Matrix.inv_eq_right_inv hbh`. Simplify using `only [zOf, mR_mkGR, u1, nU, mab, fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, smul_zero]`. Rewrite using `[hinv, Matrix.add_mul, Matrix.mul_assoc, hbh, Matrix.mul_one, Matrix.smul_mul, add_comm]`.
-/
theorem zOf_nm {X a b : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) (hab : a * b = 1) (hba : b * a = 1) :
    zOf (mkGR (nU X * mab a b) (inG_nm hX hba)) = X + Complex.I • (a * aᴴ) := by
  have hbh : bᴴ * aᴴ = 1 := by rw [← conjTranspose_mul, hab, conjTranspose_one]
  have hinv : (bᴴ)⁻¹ = aᴴ := Matrix.inv_eq_right_inv hbh
  simp only [zOf, mR_mkGR, u1, nU, mab, fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂,
    toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, smul_zero]
  rw [hinv, Matrix.add_mul, Matrix.mul_assoc, hbh, Matrix.mul_one, Matrix.smul_mul, add_comm]

/- English proof (translation)
Use `set hA := hY.1`. Use `set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU`. Establish `hUm : U ∈ unitaryGroup (Fin n) ℂ` using `hA.eigenvectorUnitary.2`. Establish `hUU : U * star U = 1` using `Matrix.mem_unitaryGroup_iff.mp hUm`. Establish `hUU' : star U * U = 1` using `Matrix.mem_unitaryGroup_iff'.mp hUm`.

Establish `hspec : Y = U * diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ)) * star U` using `by conv_lhs => rw [hA.spectral_theorem]`. Both sides reduce to the same expression. Use `⟨U, fun j => Real.sqrt (hA.eigenvalues j), hUm, fun j => Real.sqrt_pos.mpr (hY.eigenvalues_pos j), fun j => Real.sq_sqrt (hY.eigenvalues_pos j).le, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]`. Use `Eq.trans ?_ hspec.symm` and prove the remaining obligations.

Rewrite using `[Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose]`. Use `congr 2`. Use `congr 1`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]`.

Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (hY.eigenvalues_pos _).le]`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]`. Establish `: (fun j => ((Real.sqrt (hA.eigenvalues j) : ℝ) : ℂ) * (((Real.sqrt (hA.eigenvalues j))⁻¹ : ℝ) : ℂ)) = fun _ => 1`. Use function extensionality and compare the values at `j`. Rewrite using `[← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hY.eigenvalues_pos j)).ne', Complex.ofReal_one]`.

Simplify using `only [Complex.ofReal_inv] at this ⊢`. Rewrite using `[this, diagonal_one, Matrix.one_mul, hUU]`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (star U), hUU', Matrix.one_mul, diagonal_mul_diagonal]`. Establish `: (fun j => (((Real.sqrt (hA.eigenvalues j))⁻¹ : ℝ) : ℂ) * ((Real.sqrt (hA.eigenvalues j) : ℝ) : ℂ)) = fun _ => 1`. Use function extensionality and compare the values at `j`.

Rewrite using `[← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.mpr (hY.eigenvalues_pos j)).ne', Complex.ofReal_one]`. Simplify using `only [Complex.ofReal_inv] at this ⊢`. Rewrite using `[this, diagonal_one]`.
-/
theorem posdef_factor {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y.PosDef) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), U ∈ unitaryGroup (Fin n) ℂ ∧ (∀ j, 0 < d j) ∧
      (∀ j, d j ^ 2 = hY.1.eigenvalues j) ∧
      (U * diagonal (fun j => (d j : ℂ))) * (U * diagonal (fun j => (d j : ℂ)))ᴴ = Y ∧
      (U * diagonal (fun j => (d j : ℂ))) * (diagonal (fun j => ((d j)⁻¹ : ℂ)) * star U) = 1 ∧
      (diagonal (fun j => ((d j)⁻¹ : ℂ)) * star U) * (U * diagonal (fun j => (d j : ℂ))) = 1 := by
  set hA := hY.1
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUm : U ∈ unitaryGroup (Fin n) ℂ := hA.eigenvectorUnitary.2
  have hUU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hUm
  have hUU' : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hUm
  have hspec : Y = U * diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  refine ⟨U, fun j => Real.sqrt (hA.eigenvalues j), hUm, fun j => Real.sqrt_pos.mpr (hY.eigenvalues_pos j),
    fun j => Real.sq_sqrt (hY.eigenvalues_pos j).le, ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _),
      diagonal_mul_diagonal]
    refine Eq.trans ?_ hspec.symm
    rw [Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose]
    congr 2
    congr 1
    funext j
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hY.eigenvalues_pos _).le]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    have : (fun j => ((Real.sqrt (hA.eigenvalues j) : ℝ) : ℂ) * (((Real.sqrt (hA.eigenvalues j))⁻¹ : ℝ) : ℂ)) = fun _ => 1 := by
      funext j
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hY.eigenvalues_pos j)).ne', Complex.ofReal_one]
    simp only [Complex.ofReal_inv] at this ⊢
    rw [this, diagonal_one, Matrix.one_mul, hUU]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star U), hUU', Matrix.one_mul, diagonal_mul_diagonal]
    have : (fun j => (((Real.sqrt (hA.eigenvalues j))⁻¹ : ℝ) : ℂ) * ((Real.sqrt (hA.eigenvalues j) : ℝ) : ℂ)) = fun _ => 1 := by
      funext j
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.mpr (hY.eigenvalues_pos j)).ne', Complex.ofReal_one]
    simp only [Complex.ofReal_inv] at this ⊢
    rw [this, diagonal_one]

/- English proof (translation)
Establish `hY : ((-(Complex.I / 2)) • (Matrix.of W - (Matrix.of W)ᴴ)).PosDef` using `hW`. Take `⟨U, d, hU, hd, -, haa, hab, hba⟩` from `posdef_factor hY`. Use `set X : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (Matrix.of W + (Matrix.of W)ᴴ) with hXdef`. Establish `hX : X.IsHermitian`. Simplify using `only [IsHermitian, hXdef, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]`.

Rewrite using `[add_comm]`. Use `congr 1`. Simplify using `[Complex.ext_iff]`. Use `⟨mkGR (nU X * mab _ _) (inG_nm hX hba), ?_⟩` and prove the remaining obligations. Rewrite using `[zOf_nm hX hab hba, haa, hXdef]`.

Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, conjTranspose_apply, smul_eq_mul]`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zOf_surj' {W : Fin n → Fin n → ℂ} (hW : W ∈ Dom n) : ∃ y : GR n, zOf y = W := by
  have hY : ((-(Complex.I / 2)) • (Matrix.of W - (Matrix.of W)ᴴ)).PosDef := hW
  obtain ⟨U, d, hU, hd, -, haa, hab, hba⟩ := posdef_factor hY
  set X : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (Matrix.of W + (Matrix.of W)ᴴ) with hXdef
  have hX : X.IsHermitian := by
    simp only [IsHermitian, hXdef, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
    rw [add_comm]; congr 1; simp [Complex.ext_iff]
  refine ⟨mkGR (nU X * mab _ _) (inG_nm hX hba), ?_⟩
  rw [zOf_nm hX hab hba, haa, hXdef]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, conjTranspose_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/- English proof (translation)
Establish `hM : ∀ i j, ‖M i j‖ ≤ ‖M‖` using `fun i j => (norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i)`. Establish `hv : ∀ i, ‖v i‖ ≤ ‖v‖` using `fun i => norm_le_pi_norm v i`. Simplify using `only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_star]`. Use `mul_le_mul (hv i) ?_ (norm_nonneg _) (norm_nonneg _)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul (hM i j) (hv j) (norm_nonneg _) (norm_nonneg _)`. Use `_ = (n : ℝ) * (‖M‖ * ‖v‖) := by simp`. Use `_ = (n : ℝ) ^ 2 * ‖M‖ * ‖v‖ ^ 2 := by simp; ring`.
-/
theorem norm_form_le (M : Fin n → Fin n → ℂ) (v : Fin n → ℂ) :
    ‖star v ⬝ᵥ (Matrix.of M *ᵥ v)‖ ≤ (n : ℝ) ^ 2 * ‖M‖ * ‖v‖ ^ 2 := by
  have hM : ∀ i j, ‖M i j‖ ≤ ‖M‖ := fun i j => (norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i)
  have hv : ∀ i, ‖v i‖ ≤ ‖v‖ := fun i => norm_le_pi_norm v i
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply]
  calc ‖∑ i, star (v i) * ∑ j, M i j * v j‖ ≤ ∑ i, ‖star (v i) * ∑ j, M i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖v‖ * ((n : ℝ) * (‖M‖ * ‖v‖)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, norm_star]
        refine mul_le_mul (hv i) ?_ (norm_nonneg _) (norm_nonneg _)
        calc ‖∑ j, M i j * v j‖ ≤ ∑ j, ‖M i j * v j‖ := norm_sum_le _ _
          _ ≤ ∑ _j : Fin n, ‖M‖ * ‖v‖ := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [norm_mul]
              exact mul_le_mul (hM i j) (hv j) (norm_nonneg _) (norm_nonneg _)
          _ = (n : ℝ) * (‖M‖ * ‖v‖) := by simp
    _ = (n : ℝ) ^ 2 * ‖M‖ * ‖v‖ ^ 2 := by simp; ring

/- English proof (translation)
Rewrite using `[star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul]`. Simplify using `only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]`. Rewrite using `[← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem re_form_smul (Y : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (c : ℝ) :
    (star ((c : ℂ) • v) ⬝ᵥ (Y *ᵥ ((c : ℂ) • v))).re = c ^ 2 * (star v ⬝ᵥ (Y *ᵥ v)).re := by
  rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Break down `isEmpty_or_nonempty (Fin n) with hn | hn` into its components or cases. Use `⟨1, one_pos, fun v => ?_⟩` and prove the remaining obligations. Establish `: v = 0` using `Subsingleton.elim _ _`. Substitute `this` using the available equality. Simplify using the standard rewrite rules.

Establish `hcpt : IsCompact (Metric.sphere (0 : Fin n → ℂ) 1)` using `isCompact_sphere 0 1`. Take `⟨i₀⟩` from `hn`. Establish `hne : (Metric.sphere (0 : Fin n → ℂ) 1).Nonempty`. Use `⟨Pi.single i₀ 1, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_sphere_zero_iff_norm]`.

Apply `le_antisymm` to reduce the goal to its premises. Use `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : i = i₀ <;> simp [h, Pi.single_apply]`. Simplify using `using norm_le_pi_norm (Pi.single i₀ (1 : ℂ) : Fin n → ℂ) i₀`. Establish `hcont : Continuous fun v : Fin n → ℂ => (star v ⬝ᵥ (Y *ᵥ v)).re` using `Complex.continuous_re.comp ((continuous_id.star).dotProduct (continuous_const.matrix_mulVec continuous_id))`.

Take `⟨v₀, hv₀, hmin⟩` from `hcpt.exists_isMinOn hne hcont.continuousOn`. Establish `hv₀ne : v₀ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hv₀`. Establish `hpos : 0 < (star v₀ ⬝ᵥ (Y *ᵥ v₀)).re` using `(Complex.lt_def.mp (hY.dotProduct_mulVec_pos hv₀ne)).1`.

Use `⟨_, hpos, fun v => ?_⟩` and prove the remaining obligations. Break down `eq_or_ne v 0 with rfl | hv` into its components or cases. Simplify using the standard rewrite rules. Establish `hc0 : 0 < ‖v‖` using `norm_pos_iff.mpr hv`. Establish `hu : ((‖v‖⁻¹ : ℝ) : ℂ) • v ∈ Metric.sphere (0 : Fin n → ℂ) 1`.

Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hc0.ne']`. Establish `h1 : (star v₀ ⬝ᵥ (Y *ᵥ v₀)).re ≤ (star (((‖v‖⁻¹ : ℝ) : ℂ) • v) ⬝ᵥ (Y *ᵥ (((‖v‖⁻¹ : ℝ) : ℂ) • v))).re` using `hmin hu`. Rewrite `h1` using `[re_form_smul]`. Establish `h2 : ‖v‖⁻¹ ^ 2 * ‖v‖ ^ 2 = 1` using `by field_simp`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem posdef_margin {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y.PosDef) :
    ∃ m > 0, ∀ v : Fin n → ℂ, m * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (Y *ᵥ v)).re := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · refine ⟨1, one_pos, fun v => ?_⟩
    have : v = 0 := Subsingleton.elim _ _
    subst this
    simp
  · have hcpt : IsCompact (Metric.sphere (0 : Fin n → ℂ) 1) := isCompact_sphere 0 1
    obtain ⟨i₀⟩ := hn
    have hne : (Metric.sphere (0 : Fin n → ℂ) 1).Nonempty := by
      refine ⟨Pi.single i₀ 1, ?_⟩
      rw [mem_sphere_zero_iff_norm]
      apply le_antisymm
      · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
        by_cases h : i = i₀ <;> simp [h, Pi.single_apply]
      · simpa using norm_le_pi_norm (Pi.single i₀ (1 : ℂ) : Fin n → ℂ) i₀
    have hcont : Continuous fun v : Fin n → ℂ => (star v ⬝ᵥ (Y *ᵥ v)).re :=
      Complex.continuous_re.comp ((continuous_id.star).dotProduct (continuous_const.matrix_mulVec continuous_id))
    obtain ⟨v₀, hv₀, hmin⟩ := hcpt.exists_isMinOn hne hcont.continuousOn
    have hv₀ne : v₀ ≠ 0 := by
      rintro rfl
      simp at hv₀
    have hpos : 0 < (star v₀ ⬝ᵥ (Y *ᵥ v₀)).re := (Complex.lt_def.mp (hY.dotProduct_mulVec_pos hv₀ne)).1
    refine ⟨_, hpos, fun v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · have hc0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hu : ((‖v‖⁻¹ : ℝ) : ℂ) • v ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ hc0.ne']
      have h1 : (star v₀ ⬝ᵥ (Y *ᵥ v₀)).re ≤ (star (((‖v‖⁻¹ : ℝ) : ℂ) • v) ⬝ᵥ (Y *ᵥ (((‖v‖⁻¹ : ℝ) : ℂ) • v))).re :=
        hmin hu
      rw [re_form_smul] at h1
      have h2 : ‖v‖⁻¹ ^ 2 * ‖v‖ ^ 2 = 1 := by field_simp
      calc (star v₀ ⬝ᵥ (Y *ᵥ v₀)).re * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 * (star v ⬝ᵥ (Y *ᵥ v)).re) * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (star v ⬝ᵥ (Y *ᵥ v)).re := by rw [mul_comm, ← mul_assoc, mul_comm (‖v‖ ^ 2), h2, one_mul]

def toP (Y : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ := fun i j => Y i j

def ImM (W : Fin n → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := (-(Complex.I / 2)) • (Matrix.of W - (Matrix.of W)ᴴ)

/- English proof (translation)
Simplify using `[ImM, Matrix.sub_apply, conjTranspose_apply]`.
-/
theorem ImM_apply (W : Fin n → Fin n → ℂ) (i j : Fin n) :
    ImM W i j = (-(Complex.I / 2)) * (W i j - star (W j i)) := by
  simp [ImM, Matrix.sub_apply, conjTranspose_apply]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [conjTranspose_apply, ImM_apply, star_mul', star_sub, star_star, star_neg, star_div₀]`. Simplify using `[Complex.ext_iff]`. Apply the tactic sequence `constructor <;> ring`.
-/
theorem ImM_herm (W : Fin n → Fin n → ℂ) : (ImM W).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, ImM_apply, star_mul', star_sub, star_star, star_neg, star_div₀]
  simp [Complex.ext_iff]
  constructor <;> ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [ImM_apply, Matrix.add_apply, Pi.add_apply, star_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ImM_add (W W' : Fin n → Fin n → ℂ) : ImM (W + W') = ImM W + ImM W' := by
  ext i j
  simp only [ImM_apply, Matrix.add_apply, Pi.add_apply, star_add]
  ring

/- English proof (translation)
Establish `hW : ∀ i j, ‖W i j‖ ≤ ‖W‖` using `fun i j => (norm_le_pi_norm (W i) j).trans (norm_le_pi_norm W i)`. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_` and prove the remaining obligations. Use `show ‖ImM W i j‖ ≤ ‖W‖`. Rewrite using `[ImM_apply, norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_two]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `norm_sub_le _ _`. Use `_ ≤ 1 / 2 * (‖W‖ + ‖W‖) := by`. Rewrite using `[norm_star]`. Use `gcongr`. Conclude with `hW i j`.

Conclude with `hW j i`. Use `_ = ‖W‖ := by ring`.
-/
theorem norm_ImM_le (W : Fin n → Fin n → ℂ) : ‖toP (ImM W)‖ ≤ ‖W‖ := by
  have hW : ∀ i j, ‖W i j‖ ≤ ‖W‖ := fun i j => (norm_le_pi_norm (W i) j).trans (norm_le_pi_norm W i)
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  show ‖ImM W i j‖ ≤ ‖W‖
  rw [ImM_apply, norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_two]
  calc 1 / 2 * ‖W i j - star (W j i)‖ ≤ 1 / 2 * (‖W i j‖ + ‖star (W j i)‖) := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ 1 / 2 * (‖W‖ + ‖W‖) := by
        rw [norm_star]
        gcongr
        · exact hW i j
        · exact hW j i
    _ = ‖W‖ := by ring

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem dom_iff (W : Fin n → Fin n → ℂ) : W ∈ Dom n ↔ (ImM W).PosDef := Iff.rfl

/- English proof (translation)
Rewrite using `[dom_iff]`. Use `PosDef.of_dotProduct_mulVec_pos (ImM_herm W) fun x hx => ?_` and prove the remaining obligations. Establish `hx' : 0 < ‖x‖` using `norm_pos_iff.mpr hx`. Use `Complex.lt_def.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `using lt_of_lt_of_le (by positivity) (h x)`.

Use `(ImM_herm W).im_star_dotProduct_mulVec_self x` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem mem_dom_of (W : Fin n → Fin n → ℂ) (c : ℝ) (hc : 0 < c)
    (h : ∀ v : Fin n → ℂ, c * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (ImM W *ᵥ v)).re) : W ∈ Dom n := by
  rw [dom_iff]
  refine PosDef.of_dotProduct_mulVec_pos (ImM_herm W) fun x hx => ?_
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine Complex.lt_def.mpr ⟨?_, ?_⟩
  · simpa using lt_of_lt_of_le (by positivity) (h x)
  · have := (ImM_herm W).im_star_dotProduct_mulVec_self x
    simpa using this.symm

/- English proof (translation)
Use `set e := hY.1.eigenvectorBasis j`. Use `set f : Fin n → ℂ := ⇑e with hf`. Establish `he : ‖e‖ = 1` using `hY.1.eigenvectorBasis.orthonormal.1 j`. Establish `hfi : ∀ i, ‖f i‖ ≤ 1` using `fun i => by simpa [he] using PiLp.norm_apply_le e i`. Establish `hf1 : ‖f‖ ≤ 1` using `(pi_norm_le_iff_of_nonneg zero_le_one).2 hfi`.

Establish `hsum : ∑ i, ‖f i‖ ^ 2 = 1`. Use `EuclideanSpace.norm_sq_eq e` as an intermediate fact. Rewrite `this` using `[he]`. Simplify using `using this.symm`. Establish `hn : (0 : ℝ) < n`.

Establish `: 0 < Fintype.card (Fin n)` using `Fintype.card_pos_iff.mpr ⟨j⟩`. Simplify using `using this`. Establish `hlow : 1 / (n : ℝ) ≤ ‖f‖ ^ 2`. Establish `: (1 : ℝ) ≤ n * ‖f‖ ^ 2`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `norm_le_pi_norm f i`. Use `_ = n * ‖f‖ ^ 2 := by simp`. Rewrite using `[div_le_iff₀ hn]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hev : hY.1.eigenvalues j = (star f ⬝ᵥ (Y *ᵥ f)).re`.

Rewrite using `[hY.1.eigenvalues_eq j]`. Both sides reduce to the same expression. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hev]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hev]`. Establish `hM0 : 0 ≤ M` using `(norm_nonneg _).trans hM`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Use `_ = (n : ℝ) ^ 2 * M := mul_one _`.
-/
theorem eig_bounds {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y.PosDef) (c M : ℝ) (hc : 0 ≤ c)
    (hcv : ∀ v : Fin n → ℂ, c * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (Y *ᵥ v)).re) (hM : ‖toP Y‖ ≤ M)
    (j : Fin n) : c / n ≤ hY.1.eigenvalues j ∧ hY.1.eigenvalues j ≤ (n : ℝ) ^ 2 * M := by
  set e := hY.1.eigenvectorBasis j
  set f : Fin n → ℂ := ⇑e with hf
  have he : ‖e‖ = 1 := hY.1.eigenvectorBasis.orthonormal.1 j
  have hfi : ∀ i, ‖f i‖ ≤ 1 := fun i => by simpa [he] using PiLp.norm_apply_le e i
  have hf1 : ‖f‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 hfi
  have hsum : ∑ i, ‖f i‖ ^ 2 = 1 := by
    have := EuclideanSpace.norm_sq_eq e
    rw [he] at this
    simpa using this.symm
  have hn : (0 : ℝ) < n := by
    have : 0 < Fintype.card (Fin n) := Fintype.card_pos_iff.mpr ⟨j⟩
    simpa using this
  have hlow : 1 / (n : ℝ) ≤ ‖f‖ ^ 2 := by
    have : (1 : ℝ) ≤ n * ‖f‖ ^ 2 := by
      calc (1 : ℝ) = ∑ i, ‖f i‖ ^ 2 := hsum.symm
        _ ≤ ∑ _i : Fin n, ‖f‖ ^ 2 := Finset.sum_le_sum fun i _ => by
            gcongr
            exact norm_le_pi_norm f i
        _ = n * ‖f‖ ^ 2 := by simp
    rw [div_le_iff₀ hn]
    linarith
  have hev : hY.1.eigenvalues j = (star f ⬝ᵥ (Y *ᵥ f)).re := by
    rw [hY.1.eigenvalues_eq j]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hev]
    calc c / n = c * (1 / n) := by ring
      _ ≤ c * ‖f‖ ^ 2 := by gcongr
      _ ≤ _ := hcv f
  · rw [hev]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
    calc (star f ⬝ᵥ (Y *ᵥ f)).re ≤ ‖star f ⬝ᵥ (Y *ᵥ f)‖ := Complex.re_le_norm _
      _ ≤ (n : ℝ) ^ 2 * ‖toP Y‖ * ‖f‖ ^ 2 := norm_form_le (toP Y) f
      _ ≤ (n : ℝ) ^ 2 * M * 1 := by
          gcongr
          calc ‖f‖ ^ 2 ≤ 1 ^ 2 := by gcongr
            _ = 1 := one_pow 2
      _ = (n : ℝ) ^ 2 * M := mul_one _

def ReM (W : Fin n → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (Matrix.of W + (Matrix.of W)ᴴ)

/- English proof (translation)
Simplify using `only [IsHermitian, ReM, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]`. Rewrite using `[add_comm]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem ReM_herm (W : Fin n → Fin n → ℂ) : (ReM W).IsHermitian := by
  simp only [IsHermitian, ReM, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
  rw [add_comm]; congr 1; simp

/- English proof (translation)
Establish `hW : ∀ i j, ‖W i j‖ ≤ ‖W‖` using `fun i j => (norm_le_pi_norm (W i) j).trans (norm_le_pi_norm W i)`. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_` and prove the remaining obligations. Use `show ‖ReM W i j‖ ≤ ‖W‖`. Simplify using `only [ReM, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, conjTranspose_apply, smul_eq_mul]`. Rewrite using `[norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]`. Use `gcongr`. Conclude with `norm_add_le _ _`. Use `_ ≤ 1 / 2 * (‖W‖ + ‖W‖) := by`.

Rewrite using `[norm_star]`. Use `gcongr`. Conclude with `hW i j`. Conclude with `hW j i`. Use `_ = ‖W‖ := by ring`.
-/
theorem norm_ReM_le (W : Fin n → Fin n → ℂ) : ‖toP (ReM W)‖ ≤ ‖W‖ := by
  have hW : ∀ i j, ‖W i j‖ ≤ ‖W‖ := fun i j => (norm_le_pi_norm (W i) j).trans (norm_le_pi_norm W i)
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  show ‖ReM W i j‖ ≤ ‖W‖
  simp only [ReM, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, conjTranspose_apply, smul_eq_mul]
  rw [norm_mul]
  calc ‖(1 / 2 : ℂ)‖ * ‖W i j + star (W j i)‖ ≤ 1 / 2 * (‖W i j‖ + ‖star (W j i)‖) := by
        rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
        gcongr
        exact norm_add_le _ _
    _ ≤ 1 / 2 * (‖W‖ + ‖W‖) := by
        rw [norm_star]
        gcongr
        · exact hW i j
        · exact hW j i
    _ = ‖W‖ := by ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [ReM, ImM, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, conjTranspose_apply, smul_eq_mul]`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ReM_ImM (W : Fin n → Fin n → ℂ) : ReM W + Complex.I • ImM W = Matrix.of W := by
  ext i j
  simp only [ReM, ImM, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, conjTranspose_apply,
    smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/- English proof (translation)
Take `⟨m, hm, hmarg⟩` from `posdef_margin ((dom_iff W₀).mp hW₀)`. Use `set r : ℝ := m / (2 * ((n : ℝ) ^ 2 + 1)) with hr_def`. Establish `hr : 0 < r` using `by positivity`. Establish `hnr : (n : ℝ) ^ 2 * r ≤ m / 2`. Rewrite using `[hr_def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]`.

Use polynomial arithmetic with `[sq_nonneg (n : ℝ)]`. Establish `key : ∀ W ∈ Metric.closedBall W₀ r, ∀ v : Fin n → ℂ, m / 2 * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (ImM W *ᵥ v)).re`. Introduce `W hW v`. Establish `hWd : ‖W - W₀‖ ≤ r` using `by rwa [Metric.mem_closedBall, dist_eq_norm] at hW`. Establish `hsplit : ImM W = ImM W₀ + ImM (W - W₀)` using `by rw [← ImM_add]; congr 1; abel`.

Establish `h1` using `hmarg v`. Establish `h2 : ‖star v ⬝ᵥ (ImM (W - W₀) *ᵥ v)‖ ≤ (n : ℝ) ^ 2 * r * ‖v‖ ^ 2`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(norm_ImM_le _).trans hWd`. Establish `h4` using `(abs_le.mp ((Complex.abs_re_le_norm _).trans h2)).1`.

Establish `h5 : (n : ℝ) ^ 2 * r * ‖v‖ ^ 2 ≤ m / 2 * ‖v‖ ^ 2` using `mul_le_mul_of_nonneg_right hnr (sq_nonneg _)`. Rewrite using `[hsplit, add_mulVec, dotProduct_add, Complex.add_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hball : Metric.closedBall W₀ r ⊆ Dom n` using `fun W hW => mem_dom_of W (m / 2) (by positivity) (key W hW)`. Use `⟨r, hr, hball, ?_⟩` and prove the remaining obligations.

Use `set R1 : ℝ := ‖W₀‖ + r with hR1`. Use `set Δ : ℝ := Real.sqrt ((n : ℝ) ^ 2 * R1) with hΔ`. Use `set δ : ℝ := Real.sqrt (m / 2 / n) with hδ`. Establish `hR1n : 0 ≤ R1` using `by positivity`. Use `set P' : Set ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) := {p | (Matrix.of p.1)ᴴ = Matrix.of p.1} ∩ {p | Matrix.of p.2.2 * Matrix.of p.2.1 = 1} ∩ {p | Matrix.of p.2.1 * Matrix.of p.2.2 = 1} ∩ {p | ‖p.1‖ ≤ R1} ∩ {p | ‖p.2.1‖ ≤ Δ} ∩ {p | ‖p.2.2‖ ≤ δ⁻¹} with h …`.

Establish `hc1 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of p.1` using `continuous_fst`. Establish `hc2 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of p.2.1` using `continuous_fst.comp continuous_snd`. Establish `hc3 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of p.2.2` using `continuous_snd.comp continuous_snd`. Establish `hclosed : IsClosed P'`. Use `((((( isClosed_eq hc1.matrix_conjTranspose hc1).inter (isClosed_eq (hc3.matrix_mul hc2) continuous_const)).inter (isClosed_eq (hc2.matrix_mul hc3) continuous_const)).inter (isClosed_le (continuous_norm.comp continuous_fst) continuous_const)).inter (isClosed_le (continuous_norm.co …` and prove the remaining obligations.

Establish `hbdd : Bornology.IsBounded P'`. Use `(Metric.isBounded_closedBall (x := 0) (r := R1 + Δ + δ⁻¹)).subset fun p hp => ?_` and prove the remaining obligations. Take `⟨⟨⟨⟨⟨-, -⟩, -⟩, h1⟩, h2⟩, h3⟩` from `hp`. Simplify using `only [Set.mem_setOf_eq] at h1 h2 h3`. Rewrite using `[Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]`.

Establish `hΔ0 : 0 ≤ Δ` using `Real.sqrt_nonneg _`. Establish `hδ0 : 0 ≤ δ⁻¹` using `inv_nonneg.mpr (Real.sqrt_nonneg _)`. Apply the tactic sequence `refine max_le ?_ (max_le ?_ ?_) <;> linarith`. Establish `hcpt : IsCompact P'` using `Metric.isCompact_of_isClosed_isBounded hclosed hbdd`. Use `haveI : CompactSpace P' := isCompact_iff_compactSpace.mp hcpt`.

Set `Ψ : P' → GR n` to `fun p => mkGR (nU (Matrix.of p.1.1) * mab (Matrix.of p.1.2.1) (Matrix.of p.1.2.2)) (inG_nm p.2.1.1.1.1.1 p.2.1.1.1.1.2)`. Establish `hval : Continuous fun p : P' => nU (Matrix.of p.1.1) * mab (Matrix.of p.1.2.1) (Matrix.of p.1.2.2)`. Establish `g1 : Continuous fun p : P' => Matrix.of p.1.1` using `hc1.comp continuous_subtype_val`. Establish `g2 : Continuous fun p : P' => Matrix.of p.1.2.1` using `hc2.comp continuous_subtype_val`. Establish `g3 : Continuous fun p : P' => Matrix.of p.1.2.2` using `hc3.comp continuous_subtype_val`.

Conclude with `(continuous_const.matrix_fromBlocks g1 continuous_const continuous_const).matrix_mul (g2.matrix_fromBlocks continuous_const continuous_const g3.matrix_conjTranspose)`. Establish `hΨ : Continuous Ψ`. Use `continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hval, ?_⟩)` and prove the remaining obligations. Conclude with `((continuous_const.matrix_mul hval.matrix_conjTranspose).matrix_mul continuous_const)`. Use `⟨Set.range Ψ, isCompact_range hΨ, fun W hW => ?_⟩` and prove the remaining obligations.

Establish `hY : (ImM W).PosDef` using `(dom_iff W).mp (hball hW)`. Take `⟨U, d, hU, hd, hdl, haa, hab, hba⟩` from `posdef_factor hY`. Establish `hWn : ‖W‖ ≤ R1`. Establish `: ‖W‖ ≤ ‖W₀‖ + ‖W - W₀‖`. Combine the equalities or inequalities in the displayed calculation.

Establish `hWd : ‖W - W₀‖ ≤ r` using `by rwa [Metric.mem_closedBall, dist_eq_norm] at hW`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `heig` using `fun j => eig_bounds hY (m / 2) R1 (by positivity) (key W hW) ((norm_ImM_le W).trans hWn) j`. Establish `hdΔ : ∀ j, d j ≤ Δ` using `fun j => by`. Rewrite using `[← Real.sqrt_sq (hd j).le, hdl j]`.

Conclude with `Real.sqrt_le_sqrt (heig j).2`. Establish `hdδ : ∀ j, (d j)⁻¹ ≤ δ⁻¹` using `fun j => by`. Establish `hn : (0 : ℝ) < n`. Establish `: 0 < Fintype.card (Fin n)` using `Fintype.card_pos_iff.mpr ⟨j⟩`. Simplify using `using this`.

Establish `hδpos : 0 < δ` using `Real.sqrt_pos.mpr (by positivity)`. Establish `: δ ≤ d j`. Rewrite using `[← Real.sqrt_sq (hd j).le, hdl j]`. Conclude with `Real.sqrt_le_sqrt (heig j).1`. Conclude with `(inv_le_inv₀ (hd j) hδpos).mpr this`.

Use `set a : Matrix (Fin n) (Fin n) ℂ := U * diagonal (fun j => (d j : ℂ)) with ha`. Use `set b : Matrix (Fin n) (Fin n) ℂ := diagonal (fun j => ((d j)⁻¹ : ℂ)) * star U with hb`. Establish `hUe : ∀ i j, ‖U i j‖ ≤ 1` using `fun i j => entry_norm_bound_of_unitary hU i j`. Establish `hp : (toP (ReM W), toP a, toP b) ∈ P'`. Use `⟨⟨⟨⟨⟨ReM_herm W, hba⟩, hab⟩, (norm_ReM_le W).trans hWn⟩, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `show ‖toP a‖ ≤ Δ`. Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_` and prove the remaining obligations. Use `show ‖a i j‖ ≤ Δ`. Rewrite using `[ha, mul_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hd j)]`. Combine the equalities or inequalities in the displayed calculation.

Use `show ‖toP b‖ ≤ δ⁻¹`. Use `(pi_norm_le_iff_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))).2 fun i => (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))).2 fun j => ?_` and prove the remaining obligations. Use `show ‖b i j‖ ≤ δ⁻¹`. Rewrite using `[hb, diagonal_mul, norm_mul, star_apply, norm_star]`. Rewrite using `[show ‖((d i)⁻¹ : ℂ)‖ = (d i)⁻¹ by`.

Rewrite using `[← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hd i))]]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨Ψ ⟨_, hp⟩, Set.mem_range_self _, ?_⟩` and prove the remaining obligations. Use `show zOf (mkGR (nU (ReM W) * mab a b) (inG_nm (ReM_herm W) hba)) = W`. Rewrite using `[zOf_nm (ReM_herm W) hab hba, haa, ReM_ImM]`.

Both sides reduce to the same expression.
-/
theorem zOf_surj_bdd' (W₀ : Fin n → Fin n → ℂ) (hW₀ : W₀ ∈ Dom n) : ∃ r > 0, Metric.closedBall W₀ r ⊆ Dom n ∧
    ∃ S : Set (GR n), IsCompact S ∧ ∀ W ∈ Metric.closedBall W₀ r, ∃ y ∈ S, zOf y = W := by
  obtain ⟨m, hm, hmarg⟩ := posdef_margin ((dom_iff W₀).mp hW₀)
  set r : ℝ := m / (2 * ((n : ℝ) ^ 2 + 1)) with hr_def
  have hr : 0 < r := by positivity
  have hnr : (n : ℝ) ^ 2 * r ≤ m / 2 := by
    rw [hr_def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (n : ℝ)]
  have key : ∀ W ∈ Metric.closedBall W₀ r, ∀ v : Fin n → ℂ, m / 2 * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (ImM W *ᵥ v)).re := by
    intro W hW v
    have hWd : ‖W - W₀‖ ≤ r := by rwa [Metric.mem_closedBall, dist_eq_norm] at hW
    have hsplit : ImM W = ImM W₀ + ImM (W - W₀) := by rw [← ImM_add]; congr 1; abel
    have h1 := hmarg v
    have h2 : ‖star v ⬝ᵥ (ImM (W - W₀) *ᵥ v)‖ ≤ (n : ℝ) ^ 2 * r * ‖v‖ ^ 2 := by
      calc _ ≤ (n : ℝ) ^ 2 * ‖toP (ImM (W - W₀))‖ * ‖v‖ ^ 2 := norm_form_le (toP (ImM (W - W₀))) v
        _ ≤ (n : ℝ) ^ 2 * r * ‖v‖ ^ 2 := by
            gcongr
            exact (norm_ImM_le _).trans hWd
    have h4 := (abs_le.mp ((Complex.abs_re_le_norm _).trans h2)).1
    have h5 : (n : ℝ) ^ 2 * r * ‖v‖ ^ 2 ≤ m / 2 * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hnr (sq_nonneg _)
    rw [hsplit, add_mulVec, dotProduct_add, Complex.add_re]
    linarith
  have hball : Metric.closedBall W₀ r ⊆ Dom n := fun W hW => mem_dom_of W (m / 2) (by positivity) (key W hW)
  refine ⟨r, hr, hball, ?_⟩
  set R1 : ℝ := ‖W₀‖ + r with hR1
  set Δ : ℝ := Real.sqrt ((n : ℝ) ^ 2 * R1) with hΔ
  set δ : ℝ := Real.sqrt (m / 2 / n) with hδ
  have hR1n : 0 ≤ R1 := by positivity
  set P' : Set ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) :=
    {p | (Matrix.of p.1)ᴴ = Matrix.of p.1} ∩ {p | Matrix.of p.2.2 * Matrix.of p.2.1 = 1} ∩
      {p | Matrix.of p.2.1 * Matrix.of p.2.2 = 1} ∩ {p | ‖p.1‖ ≤ R1} ∩ {p | ‖p.2.1‖ ≤ Δ} ∩ {p | ‖p.2.2‖ ≤ δ⁻¹}
    with hP'
  have hc1 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of p.1 :=
    continuous_fst
  have hc2 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of p.2.1 :=
    continuous_fst.comp continuous_snd
  have hc3 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of p.2.2 :=
    continuous_snd.comp continuous_snd
  have hclosed : IsClosed P' := by
    refine ((((( isClosed_eq hc1.matrix_conjTranspose hc1).inter (isClosed_eq (hc3.matrix_mul hc2) continuous_const)).inter
      (isClosed_eq (hc2.matrix_mul hc3) continuous_const)).inter (isClosed_le (continuous_norm.comp continuous_fst)
      continuous_const)).inter (isClosed_le (continuous_norm.comp (continuous_fst.comp continuous_snd))
      continuous_const)).inter (isClosed_le (continuous_norm.comp (continuous_snd.comp continuous_snd)) continuous_const)
  have hbdd : Bornology.IsBounded P' := by
    refine (Metric.isBounded_closedBall (x := 0) (r := R1 + Δ + δ⁻¹)).subset fun p hp => ?_
    obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, h1⟩, h2⟩, h3⟩ := hp
    simp only [Set.mem_setOf_eq] at h1 h2 h3
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]
    have hΔ0 : 0 ≤ Δ := Real.sqrt_nonneg _
    have hδ0 : 0 ≤ δ⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    refine max_le ?_ (max_le ?_ ?_) <;> linarith
  have hcpt : IsCompact P' := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  haveI : CompactSpace P' := isCompact_iff_compactSpace.mp hcpt
  let Ψ : P' → GR n := fun p => mkGR (nU (Matrix.of p.1.1) * mab (Matrix.of p.1.2.1) (Matrix.of p.1.2.2))
    (inG_nm p.2.1.1.1.1.1 p.2.1.1.1.1.2)
  have hval : Continuous fun p : P' => nU (Matrix.of p.1.1) * mab (Matrix.of p.1.2.1) (Matrix.of p.1.2.2) := by
    have g1 : Continuous fun p : P' => Matrix.of p.1.1 := hc1.comp continuous_subtype_val
    have g2 : Continuous fun p : P' => Matrix.of p.1.2.1 := hc2.comp continuous_subtype_val
    have g3 : Continuous fun p : P' => Matrix.of p.1.2.2 := hc3.comp continuous_subtype_val
    exact (continuous_const.matrix_fromBlocks g1 continuous_const continuous_const).matrix_mul
      (g2.matrix_fromBlocks continuous_const continuous_const g3.matrix_conjTranspose)
  have hΨ : Continuous Ψ := by
    refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hval, ?_⟩)
    exact ((continuous_const.matrix_mul hval.matrix_conjTranspose).matrix_mul continuous_const)
  refine ⟨Set.range Ψ, isCompact_range hΨ, fun W hW => ?_⟩
  have hY : (ImM W).PosDef := (dom_iff W).mp (hball hW)
  obtain ⟨U, d, hU, hd, hdl, haa, hab, hba⟩ := posdef_factor hY
  have hWn : ‖W‖ ≤ R1 := by
    have : ‖W‖ ≤ ‖W₀‖ + ‖W - W₀‖ := by
      calc ‖W‖ = ‖W₀ + (W - W₀)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hWd : ‖W - W₀‖ ≤ r := by rwa [Metric.mem_closedBall, dist_eq_norm] at hW
    linarith
  have heig := fun j => eig_bounds hY (m / 2) R1 (by positivity) (key W hW) ((norm_ImM_le W).trans hWn) j
  have hdΔ : ∀ j, d j ≤ Δ := fun j => by
    rw [← Real.sqrt_sq (hd j).le, hdl j]
    exact Real.sqrt_le_sqrt (heig j).2
  have hdδ : ∀ j, (d j)⁻¹ ≤ δ⁻¹ := fun j => by
    have hn : (0 : ℝ) < n := by
      have : 0 < Fintype.card (Fin n) := Fintype.card_pos_iff.mpr ⟨j⟩
      simpa using this
    have hδpos : 0 < δ := Real.sqrt_pos.mpr (by positivity)
    have : δ ≤ d j := by
      rw [← Real.sqrt_sq (hd j).le, hdl j]
      exact Real.sqrt_le_sqrt (heig j).1
    exact (inv_le_inv₀ (hd j) hδpos).mpr this
  set a : Matrix (Fin n) (Fin n) ℂ := U * diagonal (fun j => (d j : ℂ)) with ha
  set b : Matrix (Fin n) (Fin n) ℂ := diagonal (fun j => ((d j)⁻¹ : ℂ)) * star U with hb
  have hUe : ∀ i j, ‖U i j‖ ≤ 1 := fun i j => entry_norm_bound_of_unitary hU i j
  have hp : (toP (ReM W), toP a, toP b) ∈ P' := by
    refine ⟨⟨⟨⟨⟨ReM_herm W, hba⟩, hab⟩, (norm_ReM_le W).trans hWn⟩, ?_⟩, ?_⟩
    · show ‖toP a‖ ≤ Δ
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i =>
        (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
      show ‖a i j‖ ≤ Δ
      rw [ha, mul_diagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hd j)]
      calc ‖U i j‖ * d j ≤ 1 * d j := mul_le_mul_of_nonneg_right (hUe i j) (hd j).le
        _ ≤ Δ := by rw [one_mul]; exact hdΔ j
    · show ‖toP b‖ ≤ δ⁻¹
      refine (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))).2 fun i =>
        (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))).2 fun j => ?_
      show ‖b i j‖ ≤ δ⁻¹
      rw [hb, diagonal_mul, norm_mul, star_apply, norm_star]
      rw [show ‖((d i)⁻¹ : ℂ)‖ = (d i)⁻¹ by
        rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hd i))]]
      calc (d i)⁻¹ * ‖U j i‖ ≤ (d i)⁻¹ * 1 := mul_le_mul_of_nonneg_left (hUe j i) (inv_nonneg.mpr (hd i).le)
        _ ≤ δ⁻¹ := by rw [mul_one]; exact hdδ i
  refine ⟨Ψ ⟨_, hp⟩, Set.mem_range_self _, ?_⟩
  show zOf (mkGR (nU (ReM W) * mab a b) (inG_nm (ReM_herm W) hba)) = W
  rw [zOf_nm (ReM_herm W) hab hba, haa, ReM_ImM]
  rfl

end PositivityTheory.Rg.Sw.HSt.HolTPf
