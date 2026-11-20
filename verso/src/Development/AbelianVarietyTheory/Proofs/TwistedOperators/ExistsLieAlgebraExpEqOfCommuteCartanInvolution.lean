import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

open Matrix

namespace GlobalTheory.ExpCartan

open scoped Matrix.Norms.L2Operator ComplexOrder

open scoped MatrixOrder in

/- English proof (translation)
Use `⟨CFC.sqrt P, ?_, CFC.sqrt_mul_sqrt_self _ hP.posSemidef.nonneg⟩` and prove the remaining obligations. Establish `hP'` using `hP`. Rewrite `hP'`, the goal using `[← isStrictlyPositive_iff_posDef]`. Conclude with `IsStrictlyPositive.sqrt _ hP'`.
-/
theorem exists_posDef_mul_self {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) :
    ∃ S : Matrix (Fin n) (Fin n) ℂ, S.PosDef ∧ S * S = P := by
  refine ⟨CFC.sqrt P, ?_, CFC.sqrt_mul_sqrt_self _ hP.posSemidef.nonneg⟩
  have hP' := hP
  rw [← isStrictlyPositive_iff_posDef] at hP' ⊢
  exact IsStrictlyPositive.sqrt _ hP'

/- English proof (translation)
Establish `h : star (star x ⬝ᵥ M *ᵥ x) = star x ⬝ᵥ M *ᵥ x`. Rewrite using `[← Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hM]`. Conclude with `Complex.conj_eq_iff_im.1 h`.
-/
theorem im_star_dotProduct_mulVec {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M)
    (x : Fin n → ℂ) : (star x ⬝ᵥ M *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ M *ᵥ x) = star x ⬝ᵥ M *ᵥ x := by
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hM]
  exact Complex.conj_eq_iff_im.1 h

/- English proof (translation)
Introduce `n G C g hG hC hg hgC`. Take `⟨hCC, hCG, hpos⟩` from `hC`. Establish `hCG' : Cᴴ * G * C = G`. Establish `h` using `congrArg Matrix.transpose hCG`. Simplify `h` using `[Matrix.transpose_mul, Matrix.conjTranspose, Matrix.transpose_map, Matrix.mul_assoc]`.

Establish `hCG2 : Cᴴ * G = G * C`. Combine the equalities or inequalities in the displayed calculation. Use `set P := G * C with hPdef`. Establish `hPh : Pᴴ = P` using `by rw [hPdef, Matrix.conjTranspose_mul, hG, hCG2]`. Establish `hPpd : P.PosDef`.

Use `Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hPh, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `hpos x hx`. Establish `he : (C *ᵥ x) ⬝ᵥ Gᵀ *ᵥ star x = star x ⬝ᵥ P *ᵥ x`. Rewrite using `[dotProduct_comm, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hPdef, ← Matrix.mulVec_mulVec]`. Rewrite `h1` using `[he]`.

Conclude with `Complex.lt_def.2 ⟨by simpa using h1, by simpa using (im_star_dotProduct_mulVec hPh x).symm⟩`. Take `⟨S, hSpd, hSS⟩` from `exists_posDef_mul_self hPpd`. Establish `hSh : Sᴴ = S` using `hSpd.isHermitian`. Establish `hSu : IsUnit S.det` using `(Matrix.isUnit_iff_isUnit_det S).1 hSpd.isUnit`. Use `set Si := S⁻¹ with hSidef`.

Establish `h1 : S * Si = 1` using `Matrix.mul_nonsing_inv _ hSu`. Establish `h2 : Si * S = 1` using `Matrix.nonsing_inv_mul _ hSu`. Establish `hSih : Siᴴ = Si` using `by rw [hSidef, Matrix.conjTranspose_nonsing_inv, hSh]`. Establish `hgP : gᴴ * P * g = P`. Combine the equalities or inequalities in the displayed calculation.

Use `set u := S * g * Si with hudef`. Establish `hsu : star u = Si * gᴴ * S`. Rewrite using `[hudef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hSih, Matrix.mul_assoc]`. Establish `huu : star u * u = 1`. Rewrite using `[hsu, hudef]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hu : u ∈ unitary (Matrix (Fin n) (Fin n) ℂ)` using `⟨huu, mul_eq_one_comm.1 huu⟩`. Use `set C' := S * C * Si with hC'def`. Establish `hSC : S * C = C' * S` using `by rw [hC'def, Matrix.mul_assoc _ Si, h2, Matrix.mul_one]`. Establish `hSiC' : Si * C' = C * Si`.

Rewrite using `[hC'def, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]`. Establish `huC : Commute u C'` using `by show u * C' = C' * u`. Rewrite using `[hudef, hC'def]`. Combine the equalities or inequalities in the displayed calculation. Establish `huC' : Commute (star u) C'`.

Establish `hus : u * star u = 1` using `mul_eq_one_comm.1 huu`. Use `show star u * C' = C' * star u`. Combine the equalities or inequalities in the displayed calculation. Establish `hN : IsStarNormal u` using `⟨by show star u * u = u * star u`. Rewrite using `[huu, mul_eq_one_comm.1 huu]⟩`.

Establish `hfin : (spectrum ℂ u).Finite` using `Matrix.finite_spectrum u`. Establish `hsph : ∀ z ∈ spectrum ℂ u, ‖z‖ = 1` using `fun z hz => by`. Simplify using `using spectrum.subset_circle_of_unitary hu hz`. Use `set Y := cfc Complex.log u with hYdef`. Establish `hlog : ContinuousOn Complex.log (spectrum ℂ u)` using `hfin.continuousOn _`.

Establish `hexp : NormedSpace.exp Y = u`. Rewrite using `[hYdef, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← Complex.exp_eq_exp_ℂ, ← cfc_comp Complex.exp Complex.log u (hf := hlog) (ha := hN)]`. Use `conv_rhs => rw [← cfc_id' ℂ u hN]`. Use `cfc_congr fun z hz => ?_` and prove the remaining obligations. Establish `hz0 : z ≠ 0` using `by intro h; have := hsph z hz; rw [h] at this; simp at this`.

Simplify using `[Complex.exp_log hz0]`. Establish `hstar : star Y = -Y`. Rewrite using `[hYdef, ← cfc_star, ← cfc_neg]`. Use `cfc_congr fun z hz => ?_` and prove the remaining obligations. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using `[Complex.log_re, hsph z hz]`. Simplify using the standard rewrite rules. Establish `hYC : Commute Y C'` using `huC.cfc huC' Complex.log`. Establish `hYh : Yᴴ = -Y` using `by rw [← Matrix.star_eq_conjTranspose, hstar]`. Use `⟨Si * Y * S, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hGP : G = S * S * C`. Rewrite using `[hSS, hPdef, Matrix.mul_assoc, hCC, Matrix.mul_one]`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hSih, hYh, hGP]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]`.

Use `_ = -(S * (Y * C') * S) + S * (C' * Y) * S := by`. Rewrite using `[h2, Matrix.mul_one, hSC, Matrix.mul_assoc C' S Si, h1, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 0 := by rw [hYC.eq, neg_add_cancel]`. Use `show Si * Y * S * C = C * (Si * Y * S)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hSun : IsUnit S` using `hSpd.isUnit`. Rewrite using `[hSidef, Matrix.exp_conj' S Y hSun, hexp, hudef, ← hSidef]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_exp_eq_of_commute_cartan : ∀ {n : ℕ} {G C g : Matrix (Fin n) (Fin n) ℂ}, Gᴴ = G →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan Gᵀ C → gᴴ * G * g = G → Commute g C →
    ∃ Z : Matrix (Fin n) (Fin n) ℂ, Zᴴ * G + G * Z = 0 ∧ Commute Z C ∧ NormedSpace.exp Z = g := by
  intro n G C g hG hC hg hgC
  obtain ⟨hCC, hCG, hpos⟩ := hC
  have hCG' : Cᴴ * G * C = G := by
    have h := congrArg Matrix.transpose hCG
    simpa [Matrix.transpose_mul, Matrix.conjTranspose, Matrix.transpose_map, Matrix.mul_assoc] using h
  have hCG2 : Cᴴ * G = G * C := by
    calc Cᴴ * G = Cᴴ * G * (C * C) := by rw [hCC, Matrix.mul_one]
      _ = G * C := by rw [← Matrix.mul_assoc, hCG']
  set P := G * C with hPdef
  have hPh : Pᴴ = P := by rw [hPdef, Matrix.conjTranspose_mul, hG, hCG2]
  have hPpd : P.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hPh, fun x hx => ?_⟩
    have h1 := hpos x hx
    have he : (C *ᵥ x) ⬝ᵥ Gᵀ *ᵥ star x = star x ⬝ᵥ P *ᵥ x := by
      rw [dotProduct_comm, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
        hPdef, ← Matrix.mulVec_mulVec]
    rw [he] at h1
    exact Complex.lt_def.2 ⟨by simpa using h1, by simpa using (im_star_dotProduct_mulVec hPh x).symm⟩
  obtain ⟨S, hSpd, hSS⟩ := exists_posDef_mul_self hPpd
  have hSh : Sᴴ = S := hSpd.isHermitian
  have hSu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hSpd.isUnit
  set Si := S⁻¹ with hSidef
  have h1 : S * Si = 1 := Matrix.mul_nonsing_inv _ hSu
  have h2 : Si * S = 1 := Matrix.nonsing_inv_mul _ hSu
  have hSih : Siᴴ = Si := by rw [hSidef, Matrix.conjTranspose_nonsing_inv, hSh]
  have hgP : gᴴ * P * g = P := by
    calc gᴴ * P * g = gᴴ * G * (C * g) := by rw [hPdef]; simp only [Matrix.mul_assoc]
      _ = gᴴ * G * g * C := by rw [← hgC.eq]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hg]
  set u := S * g * Si with hudef
  have hsu : star u = Si * gᴴ * S := by
    rw [hudef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hSih,
      Matrix.mul_assoc]
  have huu : star u * u = 1 := by
    rw [hsu, hudef]
    calc Si * gᴴ * S * (S * g * Si) = Si * (gᴴ * (S * S) * g) * Si := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSS, hgP, ← hSS, ← Matrix.mul_assoc, h2, Matrix.one_mul, h1]
  have hu : u ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := ⟨huu, mul_eq_one_comm.1 huu⟩
  set C' := S * C * Si with hC'def
  have hSC : S * C = C' * S := by rw [hC'def, Matrix.mul_assoc _ Si, h2, Matrix.mul_one]
  have hSiC' : Si * C' = C * Si := by
    rw [hC'def, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have huC : Commute u C' := by
    show u * C' = C' * u
    rw [hudef, hC'def]
    calc S * g * Si * (S * C * Si) = S * g * (Si * S) * C * Si := by simp only [Matrix.mul_assoc]
      _ = S * (C * g) * Si := by rw [h2, Matrix.mul_one, Matrix.mul_assoc S g C, hgC.eq]
      _ = S * C * (Si * S) * g * Si := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = S * C * Si * (S * g * Si) := by simp only [Matrix.mul_assoc]
  have huC' : Commute (star u) C' := by
    have hus : u * star u = 1 := mul_eq_one_comm.1 huu
    show star u * C' = C' * star u
    calc star u * C' = star u * (C' * (u * star u)) := by rw [hus, Matrix.mul_one]
      _ = star u * (u * C' * star u) := by rw [huC.eq]; simp only [Matrix.mul_assoc]
      _ = (star u * u) * C' * star u := by simp only [Matrix.mul_assoc]
      _ = C' * star u := by rw [huu, Matrix.one_mul]
  have hN : IsStarNormal u := ⟨by
    show star u * u = u * star u
    rw [huu, mul_eq_one_comm.1 huu]⟩
  have hfin : (spectrum ℂ u).Finite := Matrix.finite_spectrum u
  have hsph : ∀ z ∈ spectrum ℂ u, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary hu hz
  set Y := cfc Complex.log u with hYdef
  have hlog : ContinuousOn Complex.log (spectrum ℂ u) := hfin.continuousOn _
  have hexp : NormedSpace.exp Y = u := by
    rw [hYdef, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← Complex.exp_eq_exp_ℂ,
      ← cfc_comp Complex.exp Complex.log u (hf := hlog) (ha := hN)]
    conv_rhs => rw [← cfc_id' ℂ u hN]
    refine cfc_congr fun z hz => ?_
    have hz0 : z ≠ 0 := by intro h; have := hsph z hz; rw [h] at this; simp at this
    simp [Complex.exp_log hz0]
  have hstar : star Y = -Y := by
    rw [hYdef, ← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz => ?_
    apply Complex.ext
    · simp [Complex.log_re, hsph z hz]
    · simp
  have hYC : Commute Y C' := huC.cfc huC' Complex.log
  have hYh : Yᴴ = -Y := by rw [← Matrix.star_eq_conjTranspose, hstar]
  refine ⟨Si * Y * S, ?_, ?_, ?_⟩
  · have hGP : G = S * S * C := by
      rw [hSS, hPdef, Matrix.mul_assoc, hCC, Matrix.mul_one]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hSih, hYh, hGP]
    calc S * (-Y * Si) * (S * S * C) + S * S * C * (Si * Y * S)
        = -(S * Y * (Si * S) * (S * C)) + S * ((S * C) * Si) * Y * S := by
          simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
      _ = -(S * (Y * C') * S) + S * (C' * Y) * S := by
          rw [h2, Matrix.mul_one, hSC, Matrix.mul_assoc C' S Si, h1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hYC.eq, neg_add_cancel]
  · show Si * Y * S * C = C * (Si * Y * S)
    calc Si * Y * S * C = Si * (Y * C') * S := by rw [Matrix.mul_assoc _ S C, hSC]; simp only [Matrix.mul_assoc]
      _ = (Si * C') * Y * S := by rw [hYC.eq]; simp only [Matrix.mul_assoc]
      _ = C * (Si * Y * S) := by rw [hSiC']; simp only [Matrix.mul_assoc]
  · have hSun : IsUnit S := hSpd.isUnit
    rw [hSidef, Matrix.exp_conj' S Y hSun, hexp, hudef, ← hSidef]
    calc Si * (S * g * Si) * S = (Si * S) * g * (Si * S) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [h2, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.ExpCartan
