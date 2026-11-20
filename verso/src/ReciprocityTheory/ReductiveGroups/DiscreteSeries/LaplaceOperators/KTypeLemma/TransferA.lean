import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DerivGA

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section CurveL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Establish `h` using `(dga_exp (-X)).mul_const y`. Establish `e : (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * y) = fun t : ℝ => NormedSpace.exp ((t : ℂ) • -X) * y`. Simplify using `only [smul_neg]`. Rewrite using `[e]`. Conclude with `h`.
-/
lemma ta_curve_neg (X y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * y) (-X * y) 0 := by
  have h := (dga_exp (-X)).mul_const y
  have e : (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * y) =
      fun t : ℝ => NormedSpace.exp ((t : ℂ) • -X) * y := by
    simp only [smul_neg]
  rw [e]
  exact h

/- English proof (translation)
Conclude with `(dga_exp X).const_mul g`.
-/
lemma ta_curve (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
  exact (dga_exp X).const_mul g

end CurveL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Rewrite using `[Jm, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private lemma jm_sq_lemma (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

/- English proof (translation)
Rewrite using `[Jm, diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> simp [*]`.
-/
private lemma Jm_conjTranspose_eq_selfKType (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1
  funext a
  split_ifs <;> simp [*]

/- English proof (translation)
Rewrite using `[← mul_assoc, jm_sq_lemma, one_mul]`.
-/
lemma ta_Jm_Jm (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * X) = X := by
  rw [← mul_assoc, jm_sq_lemma, one_mul]

/- English proof (translation)
Unfold `inG cpart1`. Rewrite using `[conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose_eq_selfKType, conjTranspose_conjTranspose]`. Simplify using `only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, mul_assoc, jm_sq_lemma, ta_Jm_Jm, mul_one]`. Establish `h2 : star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Rewrite using `[h2]`.

Use `module`.
-/
lemma ta_inG_cpart1 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (cpart1 ε Z) := by
  unfold inG cpart1
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose_eq_selfKType,
    conjTranspose_conjTranspose]
  simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, mul_assoc, jm_sq_lemma, ta_Jm_Jm, mul_one]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h2]
  module

/- English proof (translation)
Unfold `inG cpart2`. Rewrite using `[conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose_eq_selfKType, conjTranspose_conjTranspose]`. Simplify using `only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, mul_assoc, jm_sq_lemma, ta_Jm_Jm, mul_one]`. Establish `h2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I))`. Rewrite using `[star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I]`.

Rewrite using `[map_ofNat]`. Rewrite using `[mul_neg, div_neg]`. Rewrite using `[h2]`. Use `module`.
-/
lemma ta_inG_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (cpart2 ε Z) := by
  unfold inG cpart2
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose_eq_selfKType,
    conjTranspose_conjTranspose]
  simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, mul_assoc, jm_sq_lemma, ta_Jm_Jm, mul_one]
  have h2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I]
    rw [map_ofNat]
    rw [mul_neg, div_neg]
  rw [h2]
  module

/- English proof (translation)
Unfold `cpart1 cpart2`. Rewrite using `[smul_smul]`. Establish `h : Complex.I * (1 / (2 * Complex.I)) = 1 / 2`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h]`.

Use `module`.
-/
lemma ta_cpart_sum (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε Z + Complex.I • cpart2 ε Z = Z := by
  unfold cpart1 cpart2
  rw [smul_smul]
  have h : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  rw [h]
  module

/- English proof (translation)
Establish `hJ : IsUnit (Jm ε)` using `⟨⟨Jm ε, Jm ε, jm_sq_lemma ε, jm_sq_lemma ε⟩, rfl⟩`. Establish `hJi : (Jm ε)⁻¹ = Jm ε` using `Matrix.inv_eq_left_inv (jm_sq_lemma ε)`. Establish `hXc : Xᴴ = Jm ε * (-X) * Jm ε`. Establish `h1 : Xᴴ * Jm ε * Jm ε + Jm ε * X * Jm ε = 0`. Rewrite using `[← add_mul, hX, zero_mul]`.

Rewrite `h1` using `[mul_assoc Xᴴ, jm_sq_lemma, mul_one]`. Rewrite using `[mul_neg, neg_mul, ← sub_eq_zero, sub_neg_eq_add, h1]`. Establish `hs : (t : ℂ) • (Jm ε * (-X) * Jm ε) = Jm ε * ((t : ℂ) • -X) * (Jm ε)⁻¹`. Rewrite using `[hJi, mul_smul_comm, smul_mul_assoc]`. Rewrite using `[← Matrix.exp_conjTranspose, conjTranspose_smul, hXc, Complex.star_def, Complex.conj_ofReal, hs, Matrix.exp_conj _ _ hJ, hJi, smul_neg]`.
-/
lemma ta_exp_conjT (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • X))ᴴ = Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε := by
  have hJ : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, jm_sq_lemma ε, jm_sq_lemma ε⟩, rfl⟩
  have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (jm_sq_lemma ε)
  have hXc : Xᴴ = Jm ε * (-X) * Jm ε := by
    have h1 : Xᴴ * Jm ε * Jm ε + Jm ε * X * Jm ε = 0 := by
      rw [← add_mul, hX, zero_mul]
    rw [mul_assoc Xᴴ, jm_sq_lemma, mul_one] at h1
    rw [mul_neg, neg_mul, ← sub_eq_zero, sub_neg_eq_add, h1]
  have hs : (t : ℂ) • (Jm ε * (-X) * Jm ε) = Jm ε * ((t : ℂ) • -X) * (Jm ε)⁻¹ := by
    rw [hJi, mul_smul_comm, smul_mul_assoc]
  rw [← Matrix.exp_conjTranspose, conjTranspose_smul, hXc, Complex.star_def, Complex.conj_ofReal, hs,
    Matrix.exp_conj _ _ hJ, hJi, smul_neg]

/- English proof (translation)
Unfold `inUJ at hg ⊢`. Rewrite using `[conjTranspose_mul, ta_exp_conjT ε hX t]`. Establish `he : NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) = 1`. Rewrite using `[← Matrix.exp_add_of_commute (-((t : ℂ) • X)) ((t : ℂ) • X) ((Commute.refl ((t : ℂ) • X)).neg_left), neg_add_cancel, NormedSpace.exp_zero]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [mul_assoc]`. Use `_ = Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) := by`. Rewrite using `[hg]`. Simplify using `only [mul_assoc, ta_Jm_Jm]`. Use `_ = Jm ε := by rw [mul_assoc, he, mul_one]`.
-/
lemma ta_inUJ_mul_exp (ε : Fin n → Bool) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X)
    (t : ℝ) : inUJ ε (g * NormedSpace.exp ((t : ℂ) • X)) := by
  unfold inUJ at hg ⊢
  rw [conjTranspose_mul, ta_exp_conjT ε hX t]
  have he : NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) = 1 := by
    rw [← Matrix.exp_add_of_commute (-((t : ℂ) • X)) ((t : ℂ) • X) ((Commute.refl ((t : ℂ) • X)).neg_left),
      neg_add_cancel, NormedSpace.exp_zero]
  calc Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε * gᴴ * Jm ε * (g * NormedSpace.exp ((t : ℂ) • X))
      = Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε * (gᴴ * Jm ε * g) * NormedSpace.exp ((t : ℂ) • X) := by
        simp only [mul_assoc]
    _ = Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) := by
        rw [hg]; simp only [mul_assoc, ta_Jm_Jm]
    _ = Jm ε := by rw [mul_assoc, he, mul_one]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `hc` using `ta_curve g X`. Establish `hnear : ∀ᶠ t : ℝ in nhds (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ W`. Apply `hc.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Establish `h0 : g * NormedSpace.exp ((((0 : ℝ) : ℂ)) • X) = g`. Simplify using `only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one]`.

Rewrite using `[h0]`. Conclude with `hW.mem_nhds hg`. Establish `hcn` using `ta_curve_neg X (g⁻¹ * m)`. Establish `hcomp : HasDerivAt (fun t : ℝ => F (NormedSpace.exp (-((t : ℂ) • X)) * (g⁻¹ * m))) (fderiv ℂ F (g⁻¹ * m) (-X * (g⁻¹ * m))) 0`. Use `(hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hcn (by simp only [Complex.ofReal_zero, zero_smul, neg_zero, NormedSpace.exp_zero, one_mul])` as an intermediate fact.

Conclude with `this`. Establish `heq : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0] (fun t : ℝ => F (NormedSpace.exp (-((t : ℂ) • X)) * (g⁻¹ * m)))` using `by filter_upwards [hnear] with t ht`. Rewrite using `[hf _ ht (ta_inUJ_mul_exp ε hgu hX t), Matrix.mul_inv_rev, ← Matrix.exp_neg, mul_assoc]`. Conclude with `(hcomp.congr_of_eventuallyEq heq).deriv`.
-/
theorem ta_rdV_local (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {W : Set (Matrix (Fin n) (Fin n) ℂ)} {m g X : Matrix (Fin n) (Fin n) ℂ}
    (hW : IsOpen W) (hg : g ∈ W) (hgu : inUJ ε g) (hX : inG ε X)
    (hF : DifferentiableAt ℂ F (g⁻¹ * m)) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ∀ h ∈ W, inUJ ε h → f h = F (h⁻¹ * m)) :
    RdV X f g = fderiv ℂ F (g⁻¹ * m) (-X * (g⁻¹ * m)) := by
  have hc := ta_curve g X
  have hnear : ∀ᶠ t : ℝ in nhds (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ W := by
    apply hc.continuousAt.preimage_mem_nhds
    have h0 : g * NormedSpace.exp ((((0 : ℝ) : ℂ)) • X) = g := by
      simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one]
    rw [h0]
    exact hW.mem_nhds hg
  have hcn := ta_curve_neg X (g⁻¹ * m)
  have hcomp : HasDerivAt (fun t : ℝ => F (NormedSpace.exp (-((t : ℂ) • X)) * (g⁻¹ * m)))
      (fderiv ℂ F (g⁻¹ * m) (-X * (g⁻¹ * m))) 0 := by
    have := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hcn
      (by simp only [Complex.ofReal_zero, zero_smul, neg_zero, NormedSpace.exp_zero, one_mul])
    exact this
  have heq : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0]
      (fun t : ℝ => F (NormedSpace.exp (-((t : ℂ) • X)) * (g⁻¹ * m))) := by
    filter_upwards [hnear] with t ht
    rw [hf _ ht (ta_inUJ_mul_exp ε hgu hX t), Matrix.mul_inv_rev, ← Matrix.exp_neg, mul_assoc]
  exact (hcomp.congr_of_eventuallyEq heq).deriv

/- English proof (translation)
Unfold `EcV Lhol`. Rewrite using `[ta_rdV_local ε hW hg hgu (ta_inG_cpart1 ε Z) hF hf, ta_rdV_local ε hW hg hgu (ta_inG_cpart2 ε Z) hF hf, ← map_smul, ← map_add]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [neg_mul, smul_neg, add_mul, smul_mul_assoc, neg_add]`.

Use `_ = -Z * (g⁻¹ * m) := by rw [ta_cpart_sum ε Z]`.
-/
theorem ta_ecV_local (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {W : Set (Matrix (Fin n) (Fin n) ℂ)} {m g : Matrix (Fin n) (Fin n) ℂ}
    (hW : IsOpen W) (hg : g ∈ W) (hgu : inUJ ε g)
    (hF : DifferentiableAt ℂ F (g⁻¹ * m)) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ∀ h ∈ W, inUJ ε h → f h = F (h⁻¹ * m)) (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcV ε Z f g = Lhol (-Z) F (g⁻¹ * m) := by
  unfold EcV Lhol
  rw [ta_rdV_local ε hW hg hgu (ta_inG_cpart1 ε Z) hF hf, ta_rdV_local ε hW hg hgu (ta_inG_cpart2 ε Z) hF hf,
    ← map_smul, ← map_add]
  congr 1
  calc -cpart1 ε Z * (g⁻¹ * m) + Complex.I • (-cpart2 ε Z * (g⁻¹ * m))
      = -(cpart1 ε Z + Complex.I • cpart2 ε Z) * (g⁻¹ * m) := by
        simp only [neg_mul, smul_neg, add_mul, smul_mul_assoc, neg_add]
    _ = -Z * (g⁻¹ * m) := by rw [ta_cpart_sum ε Z]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
