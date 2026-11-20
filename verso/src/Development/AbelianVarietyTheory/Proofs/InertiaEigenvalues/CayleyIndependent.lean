import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NonvanishingHypotheses
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.CayleyIndepA

open Matrix

namespace GlobalTheory.CayleyUnitaryQuotient

variable {n : ℕ}

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
lemma star_mul_self {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Pᴴ * P = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hP

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
lemma mul_star_self {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    P * Pᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hP

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma inv_eq_star {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    P⁻¹ = Pᴴ :=
  Matrix.inv_eq_left_inv (star_mul_self hP)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
Chain the equalities or inequalities of the calculation.
-/
lemma quotient_mul {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (P * Qᴴ) * (Q * Pᴴ) = 1 := by
  calc (P * Qᴴ) * (Q * Pᴴ) = P * (Qᴴ * Q) * Pᴴ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [star_mul_self hQ, Matrix.mul_one, mul_star_self hP]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
