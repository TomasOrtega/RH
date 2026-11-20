import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InPApplyEqZero

noncomputable section

open Finset

open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private theorem Jm_mul_Jm (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

/- English proof (translation)
Rewrite using `[Jm, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs with h <;> simp [h]`.
-/
private theorem Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  split_ifs with h <;> simp [h]

/- English proof (translation)
The claim follows from `Matrix.inv_eq_right_inv (Jm_mul_Jm ε)`.
-/
private theorem Jm_inv (ε : Fin n → Bool) : (Jm ε)⁻¹ = Jm ε :=
  Matrix.inv_eq_right_inv (Jm_mul_Jm ε)

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨Jm ε, Jm ε, Jm_mul_Jm ε, Jm_mul_Jm ε⟩, rfl⟩`.
-/
private theorem isUnit_Jm (ε : Fin n → Bool) : IsUnit (Jm ε) :=
  ⟨⟨Jm ε, Jm ε, Jm_mul_Jm ε, Jm_mul_Jm ε⟩, rfl⟩

/- English proof (translation)
Establish `h1 : Xᴴ * Jm ε = -(Jm ε * X)` using `eq_neg_of_add_eq_zero_left hX`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem conjTranspose_eq_of_inG {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Xᴴ = -(Jm ε * X * Jm ε) := by
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, Jm_mul_Jm, mul_one]
    _ = -(Jm ε * X * Jm ε) := by rw [h1, neg_mul]

/- English proof (translation)
Use `show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε`. Establish `hc : ((t : ℂ) • X)ᴴ = Jm ε * (-((t : ℂ) • X)) * (Jm ε)⁻¹`. Rewrite using `[Matrix.conjTranspose_smul, conjTranspose_eq_of_inG hX, Jm_inv]`. Simplify using the standard rewrite rules. Rewrite using `[← Matrix.exp_conjTranspose, hc, Matrix.exp_conj _ _ (isUnit_Jm ε), Jm_inv]`.

Establish `hcomm : Commute (-((t : ℂ) • X)) ((t : ℂ) • X)` using `(Commute.refl _).neg_left`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc (Jm ε * _) (Jm ε) (Jm ε), Jm_mul_Jm, mul_one, mul_assoc]`. Use `_ = Jm ε := by`. Rewrite using `[← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, mul_one]`.
-/
theorem exp_smul_mem_UJset {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := by
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
  have hc : ((t : ℂ) • X)ᴴ = Jm ε * (-((t : ℂ) • X)) * (Jm ε)⁻¹ := by
    rw [Matrix.conjTranspose_smul, conjTranspose_eq_of_inG hX, Jm_inv]
    simp
  rw [← Matrix.exp_conjTranspose, hc, Matrix.exp_conj _ _ (isUnit_Jm ε), Jm_inv]
  have hcomm : Commute (-((t : ℂ) • X)) ((t : ℂ) • X) := (Commute.refl _).neg_left
  calc Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε * Jm ε * NormedSpace.exp ((t : ℂ) • X)
      = Jm ε * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by
        rw [mul_assoc (Jm ε * _) (Jm ε) (Jm ε), Jm_mul_Jm, mul_one, mul_assoc]
    _ = Jm ε := by
        rw [← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, mul_one]

/- English proof (translation)
Rewrite using `[Complex.ofReal_add, add_smul]`. Conclude with `Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)`.
-/
theorem exp_add_smul (X : Matrix (Fin n) (Fin n) ℂ) (s t : ℝ) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • X) =
      NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X) := by
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)

/- English proof (translation)
Rewrite using `[Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]`.
-/
theorem exp_zero_smul (X : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by
  rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]

/- English proof (translation)
Establish `hZh : Zᴴ = -Z`. Rewrite using `[conjTranspose_eq_of_inG hZ.1, ← hZ.2, mul_assoc, Jm_mul_Jm, mul_one]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff'] show (NormedSpace.exp Z)ᴴ * NormedSpace.exp Z = 1`. Rewrite using `[← Matrix.exp_conjTranspose, hZh, ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel, NormedSpace.exp_zero]`.

Conclude with `((Commute.exp_left (hZ.2 : Commute Z (Jm ε))) : _)`.
-/
theorem exp_mem_Kset {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) :
    NormedSpace.exp Z ∈ Kset ε := by
  have hZh : Zᴴ = -Z := by
    rw [conjTranspose_eq_of_inG hZ.1, ← hZ.2, mul_assoc, Jm_mul_Jm, mul_one]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    show (NormedSpace.exp Z)ᴴ * NormedSpace.exp Z = 1
    rw [← Matrix.exp_conjTranspose, hZh,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  · exact ((Commute.exp_left (hZ.2 : Commute Z (Jm ε))) : _)

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero .. | (apply UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh16.inP_apply_eq_ …`.
-/
theorem inP_apply_eq_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X)
    {a b : Fin n} (hab : ε a = ε b) : X a b = 0 := by
  first | exact UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero .. | (apply UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero <;> first | assumption | infer_instance)

/- English proof (translation)
Establish `h` using `congrFun (congrFun hZ.2 a) b`. Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b`. Apply the tactic sequence `all_goals first`. Consider the case `exact absurd (ha.trans hb.symm) hab`.

Consider the case `(simp [ha, hb] at h; first | linear_combination h / 2 | linear_combination -h / 2)`.
-/
theorem inK_apply_eq_zero {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z)
    {a b : Fin n} (hab : ε a ≠ ε b) : Z a b = 0 := by
  have h := congrFun (congrFun hZ.2 a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  cases ha : ε a <;> cases hb : ε b
  all_goals first
    | exact absurd (ha.trans hb.symm) hab
    | (simp [ha, hb] at h; first | linear_combination h / 2 | linear_combination -h / 2)

end ReciprocityTheory.ChartRestriction.DS
