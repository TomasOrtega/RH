import Mathlib
import Formalism.PeriodIntegrals.WwMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.FintypeColChoice

open MvPolynomial Finset

noncomputable section

namespace PI.WwMainW

open PI.WwMain PI.WwMain.KM

/- English proof (translation)
Unfold `Lfun`. Conclude with `Finset.sum_subset hs (fun α _ h => by`. Rewrite `h` using `[MvPolynomial.mem_support_iff, not_not]`. Rewrite using `[h, zero_mul])`.
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
Unfold `LLin`. Introduce `Lt l _ N0 N1 Th`. Use `⟨fun p q => ?_, ?_, fun c p => ?_⟩` and prove the remaining obligations. Rewrite using `[Lfun_eq_of_subset l N0 N1 Th (p + q) (p.support ∪ q.support) MvPolynomial.support_add, Lfun_eq_of_subset l N0 N1 Th p (p.support ∪ q.support) Finset.subset_union_left, Lfun_eq_of_subset l N0 N1 Th q (p.support ∪ q.support) Finset.subset_union_right]`. Rewrite using `[← Finset.sum_add_distrib]`.

Simplify using `only [MvPolynomial.coeff_add, add_mul]`. Rewrite using `[Lfun_eq_of_subset l N0 N1 Th 0 ∅ (by simp)]`. Simplify using the standard rewrite rules. Establish `hsub : (MvPolynomial.C c * p).support ⊆ p.support` using `fun x hx => by`. Rewrite `hx` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul]`.

Conclude with `MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hx)`. Rewrite using `[Lfun_eq_of_subset l N0 N1 Th (MvPolynomial.C c * p) p.support hsub, Lfun_eq_of_subset l N0 N1 Th p p.support subset_rfl, Finset.mul_sum]`. Simplify using `only [MvPolynomial.coeff_C_mul, mul_assoc]`.
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
Rewrite using `[Lfun_eq_of_subset l N0 N1 Th _ {α} MvPolynomial.support_monomial_subset]`. Simplify using the standard rewrite rules.
-/
theorem Lfun_monomial {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (α : (Lt × Fin N0 × Fin N1) →₀ ℕ) (c : ℂ_[l]) :
    Lfun l N0 N1 Th (monomial α c) = c * wt l N0 N1 Th α := by
  classical
  rw [Lfun_eq_of_subset l N0 N1 Th _ {α} MvPolynomial.support_monomial_subset]
  simp

/- English proof (translation)
Rewrite using `[Lfun_eq_of_subset l N0 N1 Th _ (s.biUnion fun i => (f i).support) MvPolynomial.support_sum]`. Rewrite using `[Finset.sum_congr rfl (fun i hi => Lfun_eq_of_subset l N0 N1 Th (f i) (s.biUnion fun i => (f i).support) (Finset.subset_biUnion_of_mem (fun i => (f i).support) hi))]`. Simplify using `only [MvPolynomial.coeff_sum, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
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
Unfold `LH Hpol`. Introduce `Lt _ _ l _ N0 N1 Th ph G`. Rewrite using `[Lfun_sum']`. Simplify using `only [Lfun_monomial]`. Unfold `applyAt0`.

Establish `hm : ∀ (a : Lt × ℕ × Fin N0 →₀ ℕ) (c : ℂ_[l]), ph (MvPolynomial.monomial a c) = c * ph (MvPolynomial.monomial a 1)` using `fun a c => by`. Rewrite using `[← smul_eq_mul, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl (fun μ _ => ?_)` and prove the remaining obligations. Use `conv_rhs => rw [hm]`.

Unfold `wt`. Expand and normalize the polynomial expressions, which then agree.
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
Use extensionality with `x`. Apply the tactic sequence `rcases x with x | x <;> simp`.
-/
theorem sumElim_split {α β : Type} (μ : (α ⊕ β) →₀ ℕ) :
    μ = Finsupp.sumElim (Finsupp.sumFinsuppEquivProdFinsupp μ).1
      (Finsupp.sumFinsuppEquivProdFinsupp μ).2 := by
  ext x
  rcases x with x | x <;> simp

/- English proof (translation)
Unfold `chi`. Use `set p := Finsupp.sumFinsuppEquivProdFinsupp μ with hp`. Establish `hμ : μ = Finsupp.sumElim p.1 p.2` using `sumElim_split μ`. Rewrite using `[hμ, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_sumElim]`. Simplify using `only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, RingHom.coe_comp, Function.comp_apply, MvPolynomial.monomial_eq, map_one, one_mul, map_mul, Finsupp.prod, map_prod, map_pow, eq_intCast]`.

Simplify using `only [map_intCast]`. Expand and normalize the polynomial expressions, which then agree.
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
Unfold `EvalH Hpol`. Introduce `Lt _ _ l _ N0 N1 ph G z`. Use `conv_rhs => rw [G.as_sum]`. Simplify using `only [map_sum]`. Use `Finset.sum_congr rfl (fun μ _ => ?_)` and prove the remaining obligations.

Rewrite using `[chi_monomial, MvPolynomial.eval_monomial, MvPolynomial.C_mul', map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
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
