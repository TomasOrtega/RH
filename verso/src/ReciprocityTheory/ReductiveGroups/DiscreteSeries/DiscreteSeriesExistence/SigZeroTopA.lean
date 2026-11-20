import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecALogLower
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.HermitianCurvature.StatementB

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def sztJd (ε : Fin n → Bool) : Fin n → ℂ := fun a => if ε a then 1 else -1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem szt_Jm_eq (ε : Fin n → Bool) : Jm ε = Matrix.diagonal (sztJd ε) := rfl

/- English proof (translation)
Unfold `sztJd`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem szt_jd_sq (ε : Fin n → Bool) (a : Fin n) : sztJd ε a * sztJd ε a = 1 := by
  unfold sztJd
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `S7.lead`. Use `split_ifs with h`. Establish `hsub : (Jm ε * z * Jm ε).submatrix (Fin.castLE h) (Fin.castLE h) = Matrix.diagonal (sztJd ε ∘ Fin.castLE h) * z.submatrix (Fin.castLE h) (Fin.castLE h) * Matrix.diagonal (sztJd ε ∘ Fin.castLE h)`. Rewrite using `[szt_Jm_eq]`. Use extensionality with `a b`.

Simplify using `only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply]`. Rewrite using `[hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]`. Establish `hA : (∏ a, (sztJd ε ∘ Fin.castLE h) a) * (∏ a, (sztJd ε ∘ Fin.castLE h) a) = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun a _ => szt_jd_sq ε _`.

Combine the equalities or inequalities in the displayed calculation. Both sides reduce to the same expression.
-/
theorem szt_lead_Jconj (ε : Fin n → Bool) (z : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) :
    S7.lead i (Jm ε * z * Jm ε) = S7.lead i z := by
  unfold S7.lead
  split_ifs with h
  · have hsub : (Jm ε * z * Jm ε).submatrix (Fin.castLE h) (Fin.castLE h) =
        Matrix.diagonal (sztJd ε ∘ Fin.castLE h) * z.submatrix (Fin.castLE h) (Fin.castLE h) *
          Matrix.diagonal (sztJd ε ∘ Fin.castLE h) := by
      rw [szt_Jm_eq]
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply]
    rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hA : (∏ a, (sztJd ε ∘ Fin.castLE h) a) * (∏ a, (sztJd ε ∘ Fin.castLE h) a) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun a _ => szt_jd_sq ε _
    calc (∏ a, (sztJd ε ∘ Fin.castLE h) a) * (z.submatrix (Fin.castLE h) (Fin.castLE h)).det *
          (∏ a, (sztJd ε ∘ Fin.castLE h) a)
        = ((∏ a, (sztJd ε ∘ Fin.castLE h) a) * (∏ a, (sztJd ε ∘ Fin.castLE h) a)) *
            (z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by ring
      _ = (z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by rw [hA, one_mul]
  · rfl

/- English proof (translation)
Unfold `S7.PhiM`. Simplify using `only [szt_lead_Jconj]`.
-/
theorem szt_phiM_Jconj (ε : Fin n → Bool) (μ : Fin n → ℤ) (z : Matrix (Fin n) (Fin n) ℂ) :
    S7.PhiM μ (Jm ε * z * Jm ε) = S7.PhiM μ z := by
  unfold S7.PhiM
  simp only [szt_lead_Jconj]

/- English proof (translation)
Take `⟨hY, hE⟩` from `S7.inP_conj k⁻¹ hX`. Simplify using `only [inv_inv] at hY hE`. Rewrite using `[← hE, Matrix.inv_eq_left_inv (PolarDecomposition.polar_exp_neg_mul _), ← S7.inP_JXJ hY, PolarDecomposition.polar_exp_Jconj, szt_phiM_Jconj]`.
-/
theorem szt_phiM_inv_conj {ε : Fin n → Bool} (μ : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X)
    (k : S7.KG ε) :
    S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹ =
      S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k) := by
  obtain ⟨hY, hE⟩ := S7.inP_conj k⁻¹ hX
  simp only [inv_inv] at hY hE
  rw [← hE, Matrix.inv_eq_left_inv (PolarDecomposition.polar_exp_neg_mul _), ← S7.inP_JXJ hY,
    PolarDecomposition.polar_exp_Jconj, szt_phiM_Jconj]

section Cayley

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

/- English proof (translation)
Establish `hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ` using `hP.2`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(Matrix.mem_unitaryGroup_iff' (A := P)).mp hPu` as an intermediate fact. Simplify `this` using `[Matrix.star_eq_conjTranspose]`. Use `(Matrix.mem_unitaryGroup_iff (A := P)).mp hPu` as an intermediate fact.

Simplify `this` using `[Matrix.star_eq_conjTranspose]`.
-/
theorem szt_unitary (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) : Pᴴ * P = 1 ∧ P * Pᴴ = 1 := by
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  refine ⟨?_, ?_⟩
  · have := (Matrix.mem_unitaryGroup_iff' (A := P)).mp hPu
    simpa [Matrix.star_eq_conjTranspose] using this
  · have := (Matrix.mem_unitaryGroup_iff (A := P)).mp hPu
    simpa [Matrix.star_eq_conjTranspose] using this

/- English proof (translation)
Rewrite using `[← mir_UJset_eq]`. Take `⟨e1, e2⟩` from `szt_unitary hP`. Establish `hinv : P⁻¹ = Pᴴ` using `Matrix.inv_eq_left_inv e1`. Establish `hc : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r` using `hP.1.2`. Establish `hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r` using `hg`.

Use `show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε`. Rewrite using `[hinv]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = P * Pᴴ * Formalism.REAL.Jm ε * (P * Pᴴ) := by`.

Rewrite using `[hc, hg', ← hc]`. Simplify using `[Matrix.mul_assoc]`. Use `_ = Formalism.REAL.Jm ε := by rw [e2]; simp`.
-/
theorem szt_conj_mem (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : P * g * P⁻¹ ∈ UJset ε := by
  rw [← mir_UJset_eq]
  obtain ⟨e1, e2⟩ := szt_unitary hP
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv e1
  have hc : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  rw [hinv]
  calc (P * g * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (P * g * Pᴴ)
      = P * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * Pᴴ := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = P * Pᴴ * Formalism.REAL.Jm ε * (P * Pᴴ) := by
        rw [hc, hg', ← hc]; simp [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [e2]; simp

/- English proof (translation)
Take `⟨e1, -⟩` from `szt_unitary hP`. Establish `hinv : P⁻¹ = Pᴴ` using `Matrix.inv_eq_left_inv e1`. Establish `h` using `S7.decA_hs_conj (K := Pᴴ) (by rw [Matrix.conjTranspose_conjTranspose]; exact e1) g`. Rewrite `h` using `[Matrix.conjTranspose_conjTranspose]`. Rewrite using `[hinv]`.

Conclude with `h`.
-/
theorem szt_hs_conj (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    S7.hs (P * g * P⁻¹) = S7.hs g := by
  obtain ⟨e1, -⟩ := szt_unitary hP
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv e1
  have h := S7.decA_hs_conj (K := Pᴴ) (by rw [Matrix.conjTranspose_conjTranspose]; exact e1) g
  rw [Matrix.conjTranspose_conjTranspose] at h
  rw [hinv]
  exact h

end Cayley

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.B.gN S7.hs`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `Complex.normSq_eq_norm_sq _`.
-/
theorem szt_gN_eq {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.FourierDecayAlt.B.gN g = Real.sqrt (S7.hs g) := by
  unfold Formalism.FourierDecayAlt.B.gN S7.hs
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact Complex.normSq_eq_norm_sq _

end ReciprocityTheory.ChartRestriction.DS
