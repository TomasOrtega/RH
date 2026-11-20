import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.DualCols

open scoped ComplexOrder in

/- English proof (translation)
Establish `hr : eᵀ.rank = r` using `by simpa using LinearIndependent.rank_matrix (M := eᵀ) he`. Establish `hr2 : (eᴴ * J).rank = r`. Rewrite using `[Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det J).1 hJ), Matrix.rank_conjTranspose, ← Matrix.rank_transpose, hr]`. Establish `hs : Function.Surjective (eᴴ * J).mulVec`. Establish `h : LinearMap.range (eᴴ * J).mulVecLin = ⊤` using `Submodule.eq_top_of_finrank_eq (by simpa [Matrix.rank] using hr2)`.

Conclude with `LinearMap.range_eq_top.1 h`. Conclude with `Matrix.mulVec_surjective_iff_exists_right_inverse.1 hs`.
-/
theorem exists_right_inv {n r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {e : Matrix (Fin n) (Fin r) ℂ}
    (hJ : IsUnit J) (he : LinearIndependent ℂ eᵀ) : ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 := by
  have hr : eᵀ.rank = r := by simpa using LinearIndependent.rank_matrix (M := eᵀ) he
  have hr2 : (eᴴ * J).rank = r := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det J).1 hJ),
      Matrix.rank_conjTranspose, ← Matrix.rank_transpose, hr]
  have hs : Function.Surjective (eᴴ * J).mulVec := by
    have h : LinearMap.range (eᴴ * J).mulVecLin = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by simpa [Matrix.rank] using hr2)
    exact LinearMap.range_eq_top.1 h
  exact Matrix.mulVec_surjective_iff_exists_right_inverse.1 hs

/- English proof (translation)
Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]`.
-/
theorem adj {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) {α β : Type} [Fintype α] [Fintype β]
    (X : Matrix (Fin n) α ℂ) (Y : Matrix (Fin n) β ℂ) : (Xᴴ * J * Y)ᴴ = Yᴴ * J * X := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]

/- English proof (translation)
Establish `heF : eᴴ * J * F = 0` using `by rw [← adj hJ F e, hFe, conjTranspose_zero]`. Establish `hZF : Zᴴ * J * F = 0` using `by rw [← adj hJ F Z, hFZ, conjTranspose_zero]`. Establish `hZe : Zᴴ * J * e = 0` using `by rw [← adj hJ e Z, heZ, conjTranspose_zero]`. Take `⟨P, hP⟩ : ∃ P, J₀ * P = Fᴴ * J * f'` from `⟨J₀⁻¹ * (Fᴴ * J * f'), by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]⟩`. Take `⟨Q, hQ⟩ : ∃ Q, Zᴴ * J * Z * Q = Zᴴ * J * f'` from `⟨c⁻¹ • (Zᴴ * J * f'), by rw [hZZ, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩`.

Take `⟨f₂, h₂⟩ : ∃ f₂, f₂ = f' - F * P - Z * Q` from `⟨_, rfl⟩`. Establish `hF₂ : Fᴴ * J * f₂ = 0`. Rewrite using `[h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, hFF, hFZ, hP, Matrix.zero_mul, sub_self, sub_zero]`. Establish `hZ₂ : Zᴴ * J * f₂ = 0`. Rewrite using `[h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, hZF, hQ, Matrix.zero_mul, sub_zero, sub_self]`.

Establish `he₂ : eᴴ * J * f₂ = 1`. Rewrite using `[h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, heF, heZ, hf', Matrix.zero_mul, Matrix.zero_mul, sub_zero, sub_zero]`. Establish `he₂' : f₂ᴴ * J * e = 1` using `by rw [← adj hJ e f₂, he₂, conjTranspose_one]`. Choose the witnesses or unpack the hypotheses as in `⟨H, hH, hHH⟩ : ∃ H : Matrix (Fin r) (Fin r) ℂ, Hᴴ = H ∧ H + H = f₂ᴴ * J * f₂ := by`. Use `⟨(1 / 2 : ℝ) • (f₂ᴴ * J * f₂), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[conjTranspose_smul, adj hJ f₂ f₂]`. Simplify using the standard rewrite rules. Rewrite using `[← add_smul]`. Evaluate the numerical expressions. Establish `hfH : (f₂ - e * H)ᴴ = f₂ᴴ - H * eᴴ`.

Rewrite using `[conjTranspose_sub, conjTranspose_mul, hH]`. Use `⟨f₂ - e * H, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_sub, ← Matrix.mul_assoc _ e, hee, he₂, Matrix.zero_mul, sub_zero]`. Establish `h1 : (f₂ᴴ - H * eᴴ) * J * f₂ = f₂ᴴ * J * f₂ - H`. Rewrite using `[Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc H, Matrix.mul_assoc H, he₂, Matrix.mul_one]`.

Establish `h2 : (f₂ᴴ - H * eᴴ) * J * e = 1`. Rewrite using `[Matrix.sub_mul, Matrix.sub_mul, he₂', Matrix.mul_assoc H, Matrix.mul_assoc H, hee, Matrix.mul_zero, sub_zero]`. Rewrite using `[hfH, Matrix.mul_sub, ← Matrix.mul_assoc _ e, h1, h2, Matrix.one_mul, ← hHH]`. Normalize the expressions using the abelian group laws. Rewrite using `[Matrix.mul_sub, ← Matrix.mul_assoc _ e, hFe, hF₂, Matrix.zero_mul, sub_zero]`.

Rewrite using `[Matrix.mul_sub, ← Matrix.mul_assoc _ e, hZe, hZ₂, Matrix.zero_mul, sub_zero]`.
-/
theorem core {n m r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ}
    {F : Matrix (Fin n) (Fin m) ℂ} {e f' : Matrix (Fin n) (Fin r) ℂ} {Z : Matrix (Fin n) Unit ℂ} {c : ℂ}
    (hJ : Jᴴ = J) (hd : IsUnit J₀.det) (hc : c ≠ 0) (hFF : Fᴴ * J * F = J₀) (hFe : Fᴴ * J * e = 0)
    (hFZ : Fᴴ * J * Z = 0) (hee : eᴴ * J * e = 0) (heZ : eᴴ * J * Z = 0) (hZZ : Zᴴ * J * Z = c • 1)
    (hf' : eᴴ * J * f' = 1) :
    ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 ∧ fᴴ * J * f = 0 ∧ Fᴴ * J * f = 0 ∧ Zᴴ * J * f = 0 := by
  have heF : eᴴ * J * F = 0 := by rw [← adj hJ F e, hFe, conjTranspose_zero]
  have hZF : Zᴴ * J * F = 0 := by rw [← adj hJ F Z, hFZ, conjTranspose_zero]
  have hZe : Zᴴ * J * e = 0 := by rw [← adj hJ e Z, heZ, conjTranspose_zero]
  obtain ⟨P, hP⟩ : ∃ P, J₀ * P = Fᴴ * J * f' :=
    ⟨J₀⁻¹ * (Fᴴ * J * f'), by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Zᴴ * J * Z * Q = Zᴴ * J * f' :=
    ⟨c⁻¹ • (Zᴴ * J * f'), by rw [hZZ, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  obtain ⟨f₂, h₂⟩ : ∃ f₂, f₂ = f' - F * P - Z * Q := ⟨_, rfl⟩
  have hF₂ : Fᴴ * J * f₂ = 0 := by
    rw [h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, hFF, hFZ, hP,
      Matrix.zero_mul, sub_self, sub_zero]
  have hZ₂ : Zᴴ * J * f₂ = 0 := by
    rw [h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, hZF, hQ,
      Matrix.zero_mul, sub_zero, sub_self]
  have he₂ : eᴴ * J * f₂ = 1 := by
    rw [h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, heF, heZ, hf',
      Matrix.zero_mul, Matrix.zero_mul, sub_zero, sub_zero]
  have he₂' : f₂ᴴ * J * e = 1 := by rw [← adj hJ e f₂, he₂, conjTranspose_one]
  obtain ⟨H, hH, hHH⟩ : ∃ H : Matrix (Fin r) (Fin r) ℂ, Hᴴ = H ∧ H + H = f₂ᴴ * J * f₂ := by
    refine ⟨(1 / 2 : ℝ) • (f₂ᴴ * J * f₂), ?_, ?_⟩
    · rw [conjTranspose_smul, adj hJ f₂ f₂]; simp
    · rw [← add_smul]; norm_num
  have hfH : (f₂ - e * H)ᴴ = f₂ᴴ - H * eᴴ := by
    rw [conjTranspose_sub, conjTranspose_mul, hH]
  refine ⟨f₂ - e * H, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc _ e, hee, he₂, Matrix.zero_mul, sub_zero]
  · have h1 : (f₂ᴴ - H * eᴴ) * J * f₂ = f₂ᴴ * J * f₂ - H := by
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc H, Matrix.mul_assoc H, he₂,
        Matrix.mul_one]
    have h2 : (f₂ᴴ - H * eᴴ) * J * e = 1 := by
      rw [Matrix.sub_mul, Matrix.sub_mul, he₂', Matrix.mul_assoc H, Matrix.mul_assoc H, hee,
        Matrix.mul_zero, sub_zero]
    rw [hfH, Matrix.mul_sub, ← Matrix.mul_assoc _ e, h1, h2, Matrix.one_mul, ← hHH]
    abel
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc _ e, hFe, hF₂, Matrix.zero_mul, sub_zero]
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc _ e, hZe, hZ₂, Matrix.zero_mul, sub_zero]

/- English proof (translation)
Take `⟨f', hf'⟩` from `exists_right_inv hf.unit hf.e_indep`. Take `⟨Z, hZ⟩ : ∃ Z : Matrix (Fin n) Unit ℂ, Z = Matrix.of fun i _ => z i` from `⟨_, rfl⟩`. Establish `hcol : ∀ {a : Type} (M : Matrix a (Fin n) ℂ) (i : a) (u : Unit), (M * Z) i u = (M *ᵥ z) i`. Introduce `a M i u`. Substitute `hZ` using the available equality.

Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Establish `hFZ : Fᴴ * J * Z = 0`. Use extensionality with `i u`. Rewrite using `[hcol, hf.z_perpF]`. Both sides reduce to the same expression.

Establish `heZ : eᴴ * J * Z = 0`. Use extensionality with `i u`. Rewrite using `[hcol, hf.z_perpE]`. Both sides reduce to the same expression. Establish `hZZ : Zᴴ * J * Z = (Formalism.QuantumDeterminants.herm J z z) • (1 : Matrix Unit Unit ℂ)`.

Use extensionality with `u v`. Substitute `hZ` using the available equality. Simplify using `[Formalism.QuantumDeterminants.herm, Matrix.mul_apply, dotProduct, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Take `⟨f, h1, h2, h3, h4⟩` from `core hf.herm ((Matrix.isUnit_iff_isUnit_det J₀).1 hf.unit₀) hf.z_ne hf.gram hf.e_perp hFZ hf.e_iso heZ hZZ hf'`. Use `⟨f, h1, h2, h3, ?_⟩` and prove the remaining obligations. Establish `h5 : fᴴ * J * Z = 0` using `by rw [← adj hf.herm Z f, h4, conjTranspose_zero]`. Use function extensionality and compare the values at `i`.

Rewrite using `[← hcol _ i (), h5]`. Both sides reduce to the same expression.
-/
theorem exists_dual_cols {n m r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ}
    {F : Matrix (Fin n) (Fin m) ℂ} {e : Matrix (Fin n) (Fin r) ℂ} {z : Fin n → ℂ} (hf : IsFrame J J₀ F e z) :
    ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 ∧ fᴴ * J * f = 0 ∧ Fᴴ * J * f = 0 ∧ (fᴴ * J) *ᵥ z = 0 := by
  obtain ⟨f', hf'⟩ := exists_right_inv hf.unit hf.e_indep
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin n) Unit ℂ, Z = Matrix.of fun i _ => z i := ⟨_, rfl⟩
  have hcol : ∀ {a : Type} (M : Matrix a (Fin n) ℂ) (i : a) (u : Unit), (M * Z) i u = (M *ᵥ z) i := by
    intro a M i u
    subst hZ
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hFZ : Fᴴ * J * Z = 0 := by
    ext i u
    rw [hcol, hf.z_perpF]
    rfl
  have heZ : eᴴ * J * Z = 0 := by
    ext i u
    rw [hcol, hf.z_perpE]
    rfl
  have hZZ : Zᴴ * J * Z = (Formalism.QuantumDeterminants.herm J z z) • (1 : Matrix Unit Unit ℂ) := by
    ext u v
    subst hZ
    simp [Formalism.QuantumDeterminants.herm, Matrix.mul_apply, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  obtain ⟨f, h1, h2, h3, h4⟩ := core hf.herm ((Matrix.isUnit_iff_isUnit_det J₀).1 hf.unit₀) hf.z_ne hf.gram
    hf.e_perp hFZ hf.e_iso heZ hZZ hf'
  refine ⟨f, h1, h2, h3, ?_⟩
  have h5 : fᴴ * J * Z = 0 := by rw [← adj hf.herm Z f, h4, conjTranspose_zero]
  funext i
  rw [← hcol _ i (), h5]
  rfl

end UpperTheory.Lit.Bur.DualCols

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Bur.DualCols.exists_dual_cols | exact UpperTheory.Lit.Bur.DualCols.exists_dual_cols | (intros; apply UpperTheory.Lit.Bur.DualCols.exists_dual_cols <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Bur.isFrame_exists_isotropic_dual_columns : ∀ {n m r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ} {F : Matrix (Fin n) (Fin m) ℂ} {e : Matrix (Fin n) (Fin r) ℂ} {z : Fin n → ℂ} (hf : IsFrame J J₀ F e z), ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 ∧ fᴴ * J * f = 0 ∧ Fᴴ * J * f = 0 ∧ (fᴴ * J) *ᵥ z = 0 := by
  first | exact @UpperTheory.Lit.Bur.DualCols.exists_dual_cols | exact UpperTheory.Lit.Bur.DualCols.exists_dual_cols | (intros; apply UpperTheory.Lit.Bur.DualCols.exists_dual_cols <;> assumption)
