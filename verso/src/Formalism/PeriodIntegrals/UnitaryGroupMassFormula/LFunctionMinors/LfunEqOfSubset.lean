import Mathlib
import Formalism.PeriodIntegrals.WwMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.FintypeColChoice

open MvPolynomial Finset

noncomputable section

namespace PI.WwMainW

open PI.WwMain PI.WwMain.KM

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Lfun_eq_of_subset {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (P : MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l])
    (s : Finset ((Lt × Fin N0 × Fin N1) →₀ ℕ)) (hs : P.support ⊆ s) :
    Lfun l N0 N1 Th P = ∑ α ∈ s, coeff α P * wt l N0 N1 Th α := by
  unfold Lfun
  exact Finset.sum_subset hs (fun α _ h => by
    rw [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, zero_mul])

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem lLin : LLin := by
  unfold LLin
  intro Lt l _ N0 N1 Th
  classical
  refine ⟨fun p q => ?_, ?_, fun c p => ?_⟩
  · rw [Lfun_eq_of_subset l N0 N1 Th (p + q) (p.support ∪ q.support) MvPolynomial.support_add,
      Lfun_eq_of_subset l N0 N1 Th p (p.support ∪ q.support) Finset.subset_union_left,
      Lfun_eq_of_subset l N0 N1 Th q (p.support ∪ q.support) Finset.subset_union_right]
    rw [← Finset.sum_add_distrib]
    simp only [MvPolynomial.coeff_add, add_mul]
  · rw [Lfun_eq_of_subset l N0 N1 Th 0 ∅ (by simp)]
    simp
  · have hsub : (MvPolynomial.C c * p).support ⊆ p.support := fun x hx => by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hx
      exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hx)
    rw [Lfun_eq_of_subset l N0 N1 Th (MvPolynomial.C c * p) p.support hsub,
      Lfun_eq_of_subset l N0 N1 Th p p.support subset_rfl, Finset.mul_sum]
    simp only [MvPolynomial.coeff_C_mul, mul_assoc]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem Lfun_monomial {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (α : (Lt × Fin N0 × Fin N1) →₀ ℕ) (c : ℂ_[l]) :
    Lfun l N0 N1 Th (monomial α c) = c * wt l N0 N1 Th α := by
  classical
  rw [Lfun_eq_of_subset l N0 N1 Th _ {α} MvPolynomial.support_monomial_subset]
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem Lfun_sum' {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    Lfun l N0 N1 Th (∑ i ∈ s, f i) = ∑ i ∈ s, Lfun l N0 N1 Th (f i) := by
  classical
  rw [Lfun_eq_of_subset l N0 N1 Th _ (s.biUnion fun i => (f i).support) MvPolynomial.support_sum]
  rw [Finset.sum_congr rfl (fun i hi => Lfun_eq_of_subset l N0 N1 Th (f i)
    (s.biUnion fun i => (f i).support) (Finset.subset_biUnion_of_mem (fun i => (f i).support) hi))]
  simp only [MvPolynomial.coeff_sum, Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem lH : LH := by
  unfold LH Hpol
  intro Lt _ _ l _ N0 N1 Th ph G
  rw [Lfun_sum']
  simp only [Lfun_monomial]
  unfold applyAt0
  have hm : ∀ (a : Lt × ℕ × Fin N0 →₀ ℕ) (c : ℂ_[l]),
      ph (MvPolynomial.monomial a c) = c * ph (MvPolynomial.monomial a 1) := fun a c => by
    rw [← smul_eq_mul, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  conv_rhs => rw [hm]
  unfold wt
  ring

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem sumElim_split {α β : Type} (μ : (α ⊕ β) →₀ ℕ) :
    μ = Finsupp.sumElim (Finsupp.sumFinsuppEquivProdFinsupp μ).1
      (Finsupp.sumFinsuppEquivProdFinsupp μ).2 := by
  ext x
  rcases x with x | x <;> simp

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem chi_monomial {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (z : Lt × Fin N0 × Fin N1 → ℂ_[l])
    (μ : (XZ Lt N0 N1) →₀ ℕ) (n : ℤ) :
    chi l N0 N1 z (monomial μ n) =
      C ((n : ℂ_[l]) * (Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun w e => z w ^ e) *
        monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1 1 := by
  unfold chi
  set p := Finsupp.sumFinsuppEquivProdFinsupp μ with hp
  have hμ : μ = Finsupp.sumElim p.1 p.2 := sumElim_split μ
  rw [hμ, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_sumElim]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, RingHom.coe_comp, Function.comp_apply,
    MvPolynomial.monomial_eq, map_one, one_mul, map_mul, Finsupp.prod, map_prod, map_pow, eq_intCast]
  simp only [map_intCast]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem evalH : EvalH := by
  unfold EvalH Hpol
  intro Lt _ _ l _ N0 N1 ph G z
  conv_rhs => rw [G.as_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [chi_monomial, MvPolynomial.eval_monomial, MvPolynomial.C_mul', map_smul, smul_eq_mul]
  ring

end PI.WwMainW
