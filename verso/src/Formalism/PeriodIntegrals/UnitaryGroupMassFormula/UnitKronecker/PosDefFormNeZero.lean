import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.Development
import Lemmata.GeneralBFactRightBis.Imports

namespace PI.UnitKronW

open Matrix Polynomial ComplexOrder

/- English proof (translation)
Use `conv_rhs => rw [← hG, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`.
-/
theorem form_pres {k : ℕ} {H G : Matrix (Fin k) (Fin k) ℂ} (hG : Gᴴ * H * G = H) (x y : Fin k → ℂ) :
    star (G *ᵥ x) ⬝ᵥ (H *ᵥ (G *ᵥ y)) = star x ⬝ᵥ (H *ᵥ y) := by
  conv_rhs => rw [← hG, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]

/- English proof (translation)
The claim follows from `((Matrix.posDef_iff_dotProduct_mulVec.mp hH).2 hv).ne'`.
-/
theorem posDef_form_ne_zero {k : ℕ} {H : Matrix (Fin k) (Fin k) ℂ} (hH : H.PosDef) {v : Fin k → ℂ}
    (hv : v ≠ 0) : star v ⬝ᵥ (H *ᵥ v) ≠ 0 :=
  ((Matrix.posDef_iff_dotProduct_mulVec.mp hH).2 hv).ne'

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_right_bis.goal1 .. | (apply Bl.general_b_fact_right_bis.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_bis.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_b …`.
-/
theorem exists_eigenvector {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (μ : ℂ) (hμ : G.charpoly.IsRoot μ) :
    ∃ v : Fin k → ℂ, v ≠ 0 ∧ G *ᵥ v = μ • v := by
  first | exact Bl.general_b_fact_right_bis.goal1 .. | (apply Bl.general_b_fact_right_bis.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_bis.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_bis.goal1 <;> first | assumption | infer_instance)

/- English proof (translation)
Introduce `k H G hH hG μ hμ`. Take `⟨v, hv0, hv⟩` from `exists_eigenvector G μ hμ`. Establish `h` using `form_pres hG v v`. Rewrite `h` using `[hv, Matrix.mulVec_smul, star_smul]`. Simplify using `only [smul_dotProduct, dotProduct_smul, smul_eq_mul] at h`.

Establish `hq` using `posDef_form_ne_zero hH hv0`. Establish `h1 : star μ * μ = 1`. Establish `: (star μ * μ) * (star v ⬝ᵥ (H *ᵥ v)) = 1 * (star v ⬝ᵥ (H *ᵥ v))`. Rewrite using `[one_mul]`. Take the linear combination `h`.

Conclude with `mul_right_cancel₀ hq this`. Establish `h2 : Complex.normSq μ = 1`. Use `congrArg Complex.re h1` as an intermediate fact. Rewrite `this` using `[Complex.star_def, mul_comm, Complex.mul_conj]`. Simplify using `using this`.

Rewrite `h2` using `[Complex.normSq_eq_norm_sq]`. Use polynomial arithmetic with `[norm_nonneg μ]`.
-/
theorem stepA : StepA := by
  intro k H G hH hG μ hμ
  obtain ⟨v, hv0, hv⟩ := exists_eigenvector G μ hμ
  have h := form_pres hG v v
  rw [hv, Matrix.mulVec_smul, star_smul] at h
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
  have hq := posDef_form_ne_zero hH hv0
  have h1 : star μ * μ = 1 := by
    have : (star μ * μ) * (star v ⬝ᵥ (H *ᵥ v)) = 1 * (star v ⬝ᵥ (H *ᵥ v)) := by
      rw [one_mul]; linear_combination h
    exact mul_right_cancel₀ hq this
  have h2 : Complex.normSq μ = 1 := by
    have := congrArg Complex.re h1
    rw [Complex.star_def, mul_comm, Complex.mul_conj] at this
    simpa using this
  rw [Complex.normSq_eq_norm_sq] at h2
  nlinarith [norm_nonneg μ]

end PI.UnitKronW
