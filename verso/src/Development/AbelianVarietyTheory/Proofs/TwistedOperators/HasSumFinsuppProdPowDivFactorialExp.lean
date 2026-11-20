import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hasSum_pow_div_factorial_exp (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Apply an available result and prove the equalities needed to match it to the conclusion. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem hasSum_fin_prod_pow_div_factorial_exp : ∀ (n : ℕ) (x : Fin n → ℂ),
    HasSum (fun f : Fin n → ℕ => ∏ k, x k ^ f k / ((f k).factorial : ℂ))
      (Complex.exp (∑ k, x k)) := by
  intro n
  induction n with
  | zero =>
    intro x
    have := hasSum_unique (fun f : Fin 0 → ℕ => ∏ k, x k ^ f k / ((f k).factorial : ℂ))
    simpa using this
  | succ n ih =>
    intro x
    have h := hasSum_pow_div_factorial_exp (x 0)
    have ht := ih (Fin.tail x)
    have h1 : Summable (fun i => ‖x 0 ^ i / (i.factorial : ℂ)‖) :=
      (summable_norm_iff (E := ℂ)).2 h.summable
    have h2 : Summable (fun f : Fin n → ℕ => ‖∏ k, Fin.tail x k ^ f k / ((f k).factorial : ℂ)‖) :=
      (summable_norm_iff (E := ℂ)).2 ht.summable
    have h0 := summable_mul_of_summable_norm h1 h2
    have h3 := HasSum.mul h ht h0
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).hasSum_iff, Fin.sum_univ_succ,
      Complex.exp_add]
    convert h3 using 1
    all_goals first
      | rfl
      | (funext p; simp [Fin.prod_univ_succ, Fin.consEquiv, Fin.tail] <;> ring)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem hasSum_finsupp_prod_pow_div_factorial_exp : ∀ (κ : Type) [Fintype κ] (x : κ → ℂ),
    HasSum (fun m : κ →₀ ℕ => m.prod fun k n => x k ^ n / (n.factorial : ℂ))
      (Complex.exp (∑ k, x k)) := by
  intro κ _ x
  classical
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  have hA := hasSum_fin_prod_pow_div_factorial_exp (Fintype.card κ) (fun i => x (e.symm i))
  have hsum : (∑ i, x (e.symm i)) = ∑ k, x k := Equiv.sum_comp e.symm x
  rw [hsum] at hA
  have hB : HasSum (fun f : κ → ℕ => ∏ k, x k ^ f k / ((f k).factorial : ℂ))
      (Complex.exp (∑ k, x k)) := by
    rw [← ((Equiv.arrowCongr e (Equiv.refl ℕ)).symm).hasSum_iff]
    convert hA using 1
    funext g
    simp only [Function.comp_apply, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply,
      Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl, Function.comp_def, id]
    exact (Equiv.prod_comp e.symm (fun k => x k ^ g (e k) / ((g (e k)).factorial : ℂ))).symm.trans
      (by simp)
  rw [← (Finsupp.equivFunOnFinite (α := κ) (M := ℕ)).symm.hasSum_iff]
  convert hB using 1
  funext f
  simp only [Function.comp_apply]
  rw [Finsupp.prod_fintype]
  · simp
  · intro i; simp

end GlobalTheory
