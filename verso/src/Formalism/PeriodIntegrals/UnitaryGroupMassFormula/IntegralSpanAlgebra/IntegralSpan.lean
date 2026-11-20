import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralSpanAlgebra.Burnside

noncomputable section

namespace PI.UMultOne.GelfSpanWork

open MeasureTheory Matrix ComplexConjugate

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the argument to an intermediate assertion. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion repeatedly using the stated equalities. Establish an intermediate fact. Use symmetry to reverse the relation. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem intSpan' : IntSpan := by
  intro G _ _ _ _ _ _ _ _ μ _ N ρ hC hI T

  have hE : ∀ i j, Continuous (fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp hC)
  have hInt : ∀ f : G → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hIntP : ∀ f : G → ℂ, Continuous f → ∀ i j,
      Integrable (fun g => f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) μ :=
    fun f hf i j => hInt _ (hf.mul (hE i j))

  let S : Submodule ℂ (Matrix (Fin N) (Fin N) ℂ) :=
    { carrier := {T | ∃ f : G → ℂ, Continuous f ∧
        ∀ i j, T i j = ∫ g, f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ}
      add_mem' := by
        rintro A B ⟨f₁, hf₁, h₁⟩ ⟨f₂, hf₂, h₂⟩
        refine ⟨f₁ + f₂, hf₁.add hf₂, fun i j => ?_⟩
        simp only [Matrix.add_apply, Pi.add_apply, add_mul]
        rw [integral_add (hIntP f₁ hf₁ i j) (hIntP f₂ hf₂ i j), h₁, h₂]
      zero_mem' := ⟨0, continuous_const, fun i j => by simp⟩
      smul_mem' := by
        rintro c A ⟨f, hf, h⟩
        refine ⟨fun g => c * f g, continuous_const.mul hf, fun i j => ?_⟩
        simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc]
        rw [integral_const_mul, h] }
  suffices hS : S = ⊤ by
    have : T ∈ S := hS ▸ Submodule.mem_top
    exact this
  by_contra hne
  obtain ⟨ℓ, hℓ0, hℓS⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
  apply hℓ0
  apply functional_eq_zero ρ hI ℓ

  set h : G → ℂ := fun g => ℓ ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hh
  have hhc : Continuous h := (LinearMap.continuous_of_finiteDimensional ℓ).comp hC
  have hcoef : ∀ A : Matrix (Fin N) (Fin N) ℂ,
      ℓ A = ∑ i, ∑ j, A i j * ℓ (Matrix.single i j 1) := by
    intro A
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp only [map_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [show Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  let M : Matrix (Fin N) (Fin N) ℂ := fun i j =>
    ∫ g, conj (h g) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ
  have hM : M ∈ S := ⟨fun g => conj (h g), Complex.continuous_conj.comp hhc, fun i j => rfl⟩
  have hℓM : ℓ M = 0 := hℓS hM
  have hℓM' : ℓ M = ∫ g, ((Complex.normSq (h g) : ℝ) : ℂ) ∂μ := by
    rw [hcoef M]
    simp only [M]
    have : ∀ g, ((Complex.normSq (h g) : ℝ) : ℂ) = ∑ i, ∑ j,
        conj (h g) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j *
          ℓ (Matrix.single i j 1) := by
      intro g
      rw [Complex.normSq_eq_conj_mul_self, hh]
      simp only
      rw [hcoef ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    simp_rw [this]
    have hcj : Continuous (fun g => conj (h g)) := Complex.continuous_conj.comp hhc
    symm
    rw [integral_finsetSum _ (fun i _ => ?_)]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finsetSum _ (fun j _ => ?_)]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [integral_mul_const]
      · exact (hIntP (fun g => conj (h g)) hcj i j).mul_const _
    · exact integrable_finsetSum _ (fun j _ => (hIntP (fun g => conj (h g)) hcj i j).mul_const _)
  rw [hℓM, integral_complex_ofReal] at hℓM'
  have hR : ∫ g, Complex.normSq (h g) ∂μ = 0 := by exact_mod_cast hℓM'.symm
  intro g
  by_contra hg
  have hpos : 0 < ∫ x, Complex.normSq (h x) ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := g)
      (Complex.continuous_normSq.comp hhc) (HasCompactSupport.of_compactSpace _)
      (fun x => Complex.normSq_nonneg _) (by simpa [Complex.normSq_eq_zero] using hg)
  linarith

end PI.UMultOne.GelfSpanWork
