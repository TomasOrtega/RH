import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConstApprox

variable {n : ℕ}

/- English proof (translation)
Apply the tactic sequence `have hs : ∀ a, ‖(if ε a then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp`. Unfold `nrm`. Use `congr 1`. Unfold `Formalism.REAL.hs Formalism.REAL.Jm`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul, norm_mul, hs, hs, one_mul, mul_one]`.
-/
theorem nrm_conj_Jm (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    nrm (Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) = nrm X := by

  have hs : ∀ a, ‖(if ε a then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp
  unfold nrm
  congr 1
  unfold Formalism.REAL.hs Formalism.REAL.Jm
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul, norm_mul, hs, hs, one_mul, mul_one]

/- English proof (translation)
Establish `hON : IsON E` using `h.isON`. Take `⟨H, hH, -⟩` from `h.subgroup`. Take `⟨A, hAmul, -, hspan, hS⟩` from `h`. Establish `hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1` using `Formalism.REAL.Jm_mul_self ε`. Establish `hJt : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε` using `Formalism.REAL.Jm_conjTranspose ε`.

Establish `hJJ' : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, hJJ, Matrix.one_mul]`. Establish `hgU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε` using `g.2`. Establish `h1 : uMat g⁻¹ * uMat g = 1` using `by show (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * _ = 1`. Rewrite using `[Subgroup.coe_inv, Units.inv_mul]`.

Establish `h2 : uMat g * uMat g⁻¹ = 1` using `by show _ * (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1`. Rewrite using `[Subgroup.coe_inv, Units.mul_inv]`. Establish `hinv : uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by rw [h2, Matrix.mul_one]`. Establish `hgH : g ∈ H` using `by rw [← SetLike.mem_coe, hH]; exact hg`. Establish `hgi : g⁻¹ ∈ S` using `by rw [← hH]; exact H.inv_mem hgH`. Rewrite `hg`, `hgi` using `[hS]`. Establish `hXA : uMat g - 1 ∈ A` using `hg`.

Establish `hXsA : uMat g⁻¹ - 1 ∈ A` using `hgi`. Establish `hXs : Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε = uMat g⁻¹ - 1`. Rewrite using `[hinv]`. Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJJ]`. Establish `key : (uMat g⁻¹ - 1) * (uMat g - 1) = -((uMat g - 1) + (uMat g⁻¹ - 1))`.

Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, h1, Matrix.mul_one, Matrix.one_mul]`. Normalize the expressions using the abelian group laws. Establish `hG : Formalism.REAL.inG ε ((1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1)))`. Rewrite using `[← hXs]`. Generalize the expression as in `uMat g - 1 = X`.

Establish `h0 : (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) = 0`. Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJt, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJJ, hJJ', Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Unfold `Formalism.REAL.inG`. Rewrite using `[Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h0, smul_zero]`.

Establish `hY : (1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1)) ∈ Submodule.span ℝ (Set.range E)` using `(hspan _).1 ⟨A.smul_mem _ (A.sub_mem hXA hXsA), hG⟩`. Establish `hsq : nrm (uMat g⁻¹ - 1) = nrm (uMat g - 1)`. Rewrite using `[← hXs, nrm_conj_Jm, nrm_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[key]`.

Use `congr 1`. Use `module`. Use `_ = 1 / 2 * nrm ((uMat g⁻¹ - 1) * (uMat g - 1)) := by`. Rewrite using `[nrm_smul]`. Evaluate the numerical expressions.

Use `_ ≤ 1 / 2 * (nrm (uMat g⁻¹ - 1) * nrm (uMat g - 1)) := by gcongr`. Conclude with `nrm_mul_le _ _`. Use `_ ≤ nrm (uMat g - 1) ^ 2 := by`. Rewrite using `[hsq]`. Use polynomial arithmetic with `[sq_nonneg (nrm (uMat g - 1)), nrm_nonneg (uMat g - 1)]`.
-/
theorem nrm_sub_proj_le_sq (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (h : IsCut ε S E) (g : Formalism.REAL.UJ ε) (hg : g ∈ S) :
    nrm (uMat g - 1 - cmb E (crd E (uMat g - 1))) ≤ nrm (uMat g - 1) ^ 2 := by

  have hON : IsON E := h.isON
  obtain ⟨H, hH, -⟩ := h.subgroup
  obtain ⟨A, hAmul, -, hspan, hS⟩ := h
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJt : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJJ' : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hgU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : uMat g⁻¹ * uMat g = 1 := by
    show (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * _ = 1
    rw [Subgroup.coe_inv, Units.inv_mul]
  have h2 : uMat g * uMat g⁻¹ = 1 := by
    show _ * (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hinv : uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
    calc uMat g⁻¹ = Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * uMat g⁻¹ := by rw [hJJ, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) * uMat g⁻¹ := by rw [hgU]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by rw [h2, Matrix.mul_one]
  have hgH : g ∈ H := by rw [← SetLike.mem_coe, hH]; exact hg
  have hgi : g⁻¹ ∈ S := by rw [← hH]; exact H.inv_mem hgH
  rw [hS] at hg hgi
  have hXA : uMat g - 1 ∈ A := hg
  have hXsA : uMat g⁻¹ - 1 ∈ A := hgi
  have hXs : Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε = uMat g⁻¹ - 1 := by
    rw [hinv]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, hJJ]
  have key : (uMat g⁻¹ - 1) * (uMat g - 1) = -((uMat g - 1) + (uMat g⁻¹ - 1)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, h1, Matrix.mul_one, Matrix.one_mul]
    abel
  have hG : Formalism.REAL.inG ε ((1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1))) := by
    rw [← hXs]
    generalize uMat g - 1 = X
    have h0 : (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε +
        Formalism.REAL.Jm ε * (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) = 0 := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hJt, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJJ, hJJ', Matrix.mul_one]
      abel
    unfold Formalism.REAL.inG
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h0,
      smul_zero]
  have hY : (1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1)) ∈ Submodule.span ℝ (Set.range E) :=
    (hspan _).1 ⟨A.smul_mem _ (A.sub_mem hXA hXsA), hG⟩
  have hsq : nrm (uMat g⁻¹ - 1) = nrm (uMat g - 1) := by
    rw [← hXs, nrm_conj_Jm, nrm_conjTranspose]
  calc nrm (uMat g - 1 - cmb E (crd E (uMat g - 1)))
      ≤ nrm (uMat g - 1 - (1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1))) := nrm_sub_proj_le hON _ hY
    _ = nrm ((-(1 / 2 : ℝ)) • ((uMat g⁻¹ - 1) * (uMat g - 1))) := by
        rw [key]
        congr 1
        module
    _ = 1 / 2 * nrm ((uMat g⁻¹ - 1) * (uMat g - 1)) := by
        rw [nrm_smul]
        norm_num
    _ ≤ 1 / 2 * (nrm (uMat g⁻¹ - 1) * nrm (uMat g - 1)) := by
        gcongr
        exact nrm_mul_le _ _
    _ ≤ nrm (uMat g - 1) ^ 2 := by
        rw [hsq]
        nlinarith [sq_nonneg (nrm (uMat g - 1)), nrm_nonneg (uMat g - 1)]

end GlobalTheory.IwConstApprox
