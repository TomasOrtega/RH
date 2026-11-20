import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NonvanishingHypotheses
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.CayleyIndepA

open Matrix

namespace GlobalTheory.CayleyUnitaryQuotient

variable {n : ℕ}

/- English proof (translation)
Simplify `Matrix.mem_unitaryGroup_iff'.mp hP` using `[Matrix.star_eq_conjTranspose]`.
-/
lemma star_mul_self {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Pᴴ * P = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hP

/- English proof (translation)
Simplify `Matrix.mem_unitaryGroup_iff.mp hP` using `[Matrix.star_eq_conjTranspose]`.
-/
lemma mul_star_self {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    P * Pᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hP

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv (star_mul_self hP)`.
-/
lemma inv_eq_star {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    P⁻¹ = Pᴴ :=
  Matrix.inv_eq_left_inv (star_mul_self hP)

/- English proof (translation)
Establish `hQs : Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]`. Conclude with `star_mul_self hQ`. Use `⟨Submonoid.mul_mem _ hP hQs, ?_⟩` and prove the remaining obligations. Use `show P * Qᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (P * Qᴴ)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_star_self hQ, Matrix.mul_one]`. Use `_ = P * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qᴴ := by simp only [Matrix.mul_assoc]`. Use `_ = P * (Pᴴ * Formalism.REAL.Jm ε * P) * Qᴴ := by rw [h]`. Use `_ = (P * Pᴴ) * (Formalism.REAL.Jm ε * (P * Qᴴ)) := by simp only [Matrix.mul_assoc]`.

Use `_ = Formalism.REAL.Jm ε * (P * Qᴴ) := by rw [mul_star_self hP, Matrix.one_mul]`.
-/
lemma quotient_mem_K {ε : Fin n → Bool} {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = Qᴴ * Formalism.REAL.Jm ε * Q) :
    P * Qᴴ ∈ Formalism.REAL.Kset ε := by
  have hQs : Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact star_mul_self hQ
  refine ⟨Submonoid.mul_mem _ hP hQs, ?_⟩
  show P * Qᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (P * Qᴴ)
  calc P * Qᴴ * Formalism.REAL.Jm ε = P * Qᴴ * Formalism.REAL.Jm ε * (Q * Qᴴ) := by
        rw [mul_star_self hQ, Matrix.mul_one]
    _ = P * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qᴴ := by simp only [Matrix.mul_assoc]
    _ = P * (Pᴴ * Formalism.REAL.Jm ε * P) * Qᴴ := by rw [h]
    _ = (P * Pᴴ) * (Formalism.REAL.Jm ε * (P * Qᴴ)) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε * (P * Qᴴ) := by rw [mul_star_self hP, Matrix.one_mul]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
lemma quotient_mul {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (P * Qᴴ) * (Q * Pᴴ) = 1 := by
  calc (P * Qᴴ) * (Q * Pᴴ) = P * (Qᴴ * Q) * Pᴴ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [star_mul_self hQ, Matrix.mul_one, mul_star_self hP]

/- English proof (translation)
Rewrite using `[inv_eq_star hP, inv_eq_star hQ]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Pᴴ * g * P := by rw [star_mul_self hQ, Matrix.one_mul, Matrix.mul_one]`.
-/
lemma conj_eq {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    Q⁻¹ * (Q * Pᴴ * g * (P * Qᴴ)) * Q = P⁻¹ * g * P := by
  rw [inv_eq_star hP, inv_eq_star hQ]
  calc Qᴴ * (Q * Pᴴ * g * (P * Qᴴ)) * Q = (Qᴴ * Q) * (Pᴴ * g * P) * (Qᴴ * Q) := by
        simp only [Matrix.mul_assoc]
    _ = Pᴴ * g * P := by rw [star_mul_self hQ, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Introduce `k r ε lam H _ _ _ σ Q P hQ hP hds`. Establish `hPQ : Pᴴ * Formalism.REAL.Jm ε * P = Qᴴ * Formalism.REAL.Jm ε * Q` using `hP.1.2.trans hQ.1.2.symm`. Establish `ha` using `quotient_mem_K hP.2 hQ.2 hPQ`. Establish `hb` using `quotient_mem_K hQ.2 hP.2 hPQ.symm`. Establish `key` using `ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ds_conj (fun g => σ (Q⁻¹ * g * Q)) (quotient_mul hP.2 hQ.2) (quotient_mul hQ.2 hP.2) ha hb lam hds`.

Simplify using `only [conj_eq hP.2 hQ.2] at key`. Conclude with `key`.
-/
theorem cayley_independent : ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepStatement := by
  intro k r ε lam H _ _ _ σ Q P hQ hP hds
  have hPQ : Pᴴ * Formalism.REAL.Jm ε * P = Qᴴ * Formalism.REAL.Jm ε * Q := hP.1.2.trans hQ.1.2.symm
  have ha := quotient_mem_K hP.2 hQ.2 hPQ
  have hb := quotient_mem_K hQ.2 hP.2 hPQ.symm
  have key := ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ds_conj (fun g => σ (Q⁻¹ * g * Q))
    (quotient_mul hP.2 hQ.2) (quotient_mul hQ.2 hP.2) ha hb lam hds
  simp only [conj_eq hP.2 hQ.2] at key
  exact key

end GlobalTheory.CayleyUnitaryQuotient
