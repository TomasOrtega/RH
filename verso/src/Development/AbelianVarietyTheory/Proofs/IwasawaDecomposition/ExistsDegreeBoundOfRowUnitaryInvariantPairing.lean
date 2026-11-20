import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply

noncomputable section

open GlobalTheory.DefLift

namespace GlobalTheory.RowSupport

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Consider separately whether the proposition holds or fails. Substitute using the available equality. It suffices to derive a contradiction. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exp_I_pow_injective : Function.Injective fun e : ℕ => Complex.exp Complex.I ^ e := by
  intro a b h
  simp only [← Complex.exp_nat_mul] at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have h2 : (a : ℝ) = b + k * (2 * Real.pi) := by
    have := congrArg Complex.im hk
    simpa using this
  by_cases h0 : k = 0
  · subst h0
    exact_mod_cast (by simpa using h2 : (a : ℝ) = b)
  · exfalso
    have h3 : (2 * k : ℤ) ≠ 0 := mul_ne_zero two_ne_zero h0
    refine (irrational_pi.intCast_mul h3).ne_int ((a : ℤ) - b) ?_
    push_cast
    linarith

def scal (m : ℕ) : Matrix.unitaryGroup (Fin m) ℂ :=
  ⟨Complex.exp Complex.I • 1, by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, mul_one]
    have : Complex.exp Complex.I * star (Complex.exp Complex.I) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp
    rw [this, one_smul]⟩

open Classical in
/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem rowSub_scal {ι : Type} [Fintype ι] {m n : ℕ} (τ : ι) (α : ι × Fin m × Fin n →₀ ℕ) :
    rowSub n τ (scal m) (MvPolynomial.monomial α 1) =
      Complex.exp Complex.I ^ (∑ v, if v.1 = τ then α v else 0) • MvPolynomial.monomial α 1 := by
  have hv : ∀ v : ι × Fin m × Fin n,
      (∑ i, ∑ c, ((if v.1 = τ then (scal m : Matrix (Fin m) (Fin m) ℂ) else 1) i v.2.1 *
        (1 : Matrix (Fin n) (Fin n) ℂ) v.2.2 c) • (MvPolynomial.X (v.1, i, c) : Pol ι m n)) =
      (if v.1 = τ then Complex.exp Complex.I else 1) • MvPolynomial.X v := by
    rintro ⟨ρ, j, d⟩
    by_cases h : ρ = τ
    · simp [h, scal, Matrix.one_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp [h, Matrix.one_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']
  unfold rowSub subst
  rw [AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial, map_one, one_mul, MvPolynomial.monomial_eq, map_one, one_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp only [hv, smul_pow]
  rw [Finset.prod_smul, ← Finset.prod_pow_eq_pow_sum]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Apply an available result and prove the equalities needed to match it to the conclusion. A detailed English derivation is pending.
-/
theorem exists_degree_bound (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X) (β : Pol ι m n →ₗ[ℂ] X →ₗ[ℂ] ℂ)
    (h : ∀ τ u P x, β (rowSub n τ u P) (π τ u x) = β P x) :
    ∃ d : ℕ, ∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → β (MvPolynomial.monomial α 1) = 0 := by
  classical
  have hfin : ∀ τ, ∃ d : ℕ, ∀ e : ℕ,
      Module.End.HasEigenvalue (LinearMap.dualMap (π τ (scal m)) : Module.End ℂ (Module.Dual ℂ X))
        (Complex.exp Complex.I ^ e)⁻¹ → e ≤ d := by
    intro τ
    have h1 := Module.End.finite_hasEigenvalue (LinearMap.dualMap (π τ (scal m)) : Module.End ℂ (Module.Dual ℂ X))
    have h2 := h1.preimage (f := fun e : ℕ => (Complex.exp Complex.I ^ e)⁻¹)
      (inv_injective.comp exp_I_pow_injective).injOn
    obtain ⟨d, hd⟩ := h2.bddAbove
    exact ⟨d, fun e he => hd he⟩
  choose d hd using hfin
  refine ⟨∑ τ, d τ, fun α hα => ?_⟩
  by_contra hne
  have hdeg : α.degree = ∑ τ, ∑ v, if v.1 = τ then α v else 0 := by
    rw [Finset.sum_comm, Finsupp.degree_eq_sum]
    simp
  refine absurd hα (not_lt.2 ?_)
  rw [hdeg]
  refine Finset.sum_le_sum fun τ _ => hd τ _ ?_
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := β (MvPolynomial.monomial α 1)) ⟨?_, hne⟩
  rw [Module.End.mem_eigenspace_iff]
  ext x
  have := h τ (scal m) (MvPolynomial.monomial α 1) x
  rw [rowSub_scal, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  rw [LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ (Complex.exp_ne_zero _))]
  convert this

end GlobalTheory.RowSupport

end
