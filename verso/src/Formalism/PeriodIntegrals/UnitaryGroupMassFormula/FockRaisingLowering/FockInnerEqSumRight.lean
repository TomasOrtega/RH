import Mathlib
import Formalism.PeriodIntegrals.JointBlockShapes.MinusPart
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.SameSign

noncomputable section

namespace FockRaiseLowInner

open MvPolynomial FockH1Action

variable {σ : Type*}

def wt (α : σ →₀ ℕ) : ℂ := α.prod (fun _ k => (k.factorial : ℂ))

/- English proof (translation)
Unfold `FockH1Action.fockInner`. Use `Finset.sum_congr rfl (fun α _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single α]`. Rewrite using `[if_pos rfl]`. Both sides reduce to the same expression.

Introduce `β _ hβ`. Rewrite using `[if_neg (Ne.symm hβ), mul_zero]`. Introduce `hα`. Establish `h : coeff α Q = 0` using `by simpa [MvPolynomial.mem_support_iff] using hα`. Rewrite using `[h]`.

Simplify using the standard rewrite rules.
-/
theorem fockInner_eq_support (P Q : MvPolynomial σ ℂ) :
    fockInner P Q = ∑ α ∈ P.support, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
  unfold FockH1Action.fockInner
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Finset.sum_eq_single α]
  · rw [if_pos rfl]
    rfl
  · intro β _ hβ
    rw [if_neg (Ne.symm hβ), mul_zero]
  · intro hα
    have h : coeff α Q = 0 := by simpa [MvPolynomial.mem_support_iff] using hα
    rw [h]
    simp

/- English proof (translation)
Rewrite using `[fockInner_eq_support]`. Establish `h1 : (∑ α ∈ P.support, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α) = ∑ α ∈ P.support ∪ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α`. Use `Finset.sum_subset (fun x hx => Finset.mem_union_left _ hx) (fun α _ hα => ?_)` and prove the remaining obligations. Establish `h : coeff α P = 0` using `by simpa [MvPolynomial.mem_support_iff] using hα`. Rewrite using `[h]`.

Simplify using the standard rewrite rules. Establish `h2 : (∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α) = ∑ α ∈ P.support ∪ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α`. Use `Finset.sum_subset (fun x hx => Finset.mem_union_right _ hx) (fun α _ hα => ?_)` and prove the remaining obligations. Rewrite using `[hS α hα, zero_mul]`. Rewrite using `[h1, h2]`.
-/
theorem fockInner_eq_sum (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : ∀ α, α ∉ S → (starRingEnd ℂ) (coeff α P) * coeff α Q = 0) :
    fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
  classical
  rw [fockInner_eq_support]
  have h1 : (∑ α ∈ P.support, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α) =
      ∑ α ∈ P.support ∪ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
    refine Finset.sum_subset (fun x hx => Finset.mem_union_left _ hx) (fun α _ hα => ?_)
    have h : coeff α P = 0 := by simpa [MvPolynomial.mem_support_iff] using hα
    rw [h]
    simp
  have h2 : (∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α) =
      ∑ α ∈ P.support ∪ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
    refine Finset.sum_subset (fun x hx => Finset.mem_union_right _ hx) (fun α _ hα => ?_)
    rw [hS α hα, zero_mul]
  rw [h1, h2]

/- English proof (translation)
Use `fockInner_eq_sum P Q S (fun α hα => ?_)` and prove the remaining obligations. Establish `h : coeff α P = 0`. Assume the negation of the conclusion as `h'`. Conclude with `hα (hS (MvPolynomial.mem_support_iff.mpr h'))`. Rewrite using `[h]`.

Simplify using the standard rewrite rules.
-/
theorem fockInner_eq_sum_left (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) :
    fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
  refine fockInner_eq_sum P Q S (fun α hα => ?_)
  have h : coeff α P = 0 := by
    by_contra h'
    exact hα (hS (MvPolynomial.mem_support_iff.mpr h'))
  rw [h]
  simp

/- English proof (translation)
Use `fockInner_eq_sum P Q S (fun α hα => ?_)` and prove the remaining obligations. Establish `h : coeff α Q = 0`. Assume the negation of the conclusion as `h'`. Conclude with `hα (hS (MvPolynomial.mem_support_iff.mpr h'))`. Rewrite using `[h, mul_zero]`.
-/
theorem fockInner_eq_sum_right (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : Q.support ⊆ S) :
    fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
  refine fockInner_eq_sum P Q S (fun α hα => ?_)
  have h : coeff α Q = 0 := by
    by_contra h'
    exact hα (hS (MvPolynomial.mem_support_iff.mpr h'))
  rw [h, mul_zero]

/- English proof (translation)
Rewrite using `[fockInner_eq_support]`. Simplify using the standard rewrite rules.
-/
theorem fockInner_zero_left (Q : MvPolynomial σ ℂ) : fockInner 0 Q = 0 := by
  rw [fockInner_eq_support]
  simp

/- English proof (translation)
Rewrite using `[fockInner_eq_support]`. Simplify using the standard rewrite rules.
-/
theorem fockInner_zero_right (P : MvPolynomial σ ℂ) : fockInner P 0 = 0 := by
  rw [fockInner_eq_support]
  simp

/- English proof (translation)
Rewrite using `[fockInner_eq_support P (Q₁ + Q₂), fockInner_eq_support P Q₁, fockInner_eq_support P Q₂, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun α _ => ?_)` and prove the remaining obligations. Rewrite using `[coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockInner_add_right (P Q₁ Q₂ : MvPolynomial σ ℂ) :
    fockInner P (Q₁ + Q₂) = fockInner P Q₁ + fockInner P Q₂ := by
  rw [fockInner_eq_support P (Q₁ + Q₂), fockInner_eq_support P Q₁,
    fockInner_eq_support P Q₂, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_add]
  ring

/- English proof (translation)
Rewrite using `[fockInner_eq_support P (c • Q), fockInner_eq_support P Q, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun α _ => ?_)` and prove the remaining obligations. Rewrite using `[coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockInner_smul_right (P Q : MvPolynomial σ ℂ) (c : ℂ) :
    fockInner P (c • Q) = c * fockInner P Q := by
  rw [fockInner_eq_support P (c • Q), fockInner_eq_support P Q, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[fockInner_eq_support P (-Q), fockInner_eq_support P Q, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl (fun α _ => ?_)` and prove the remaining obligations. Rewrite using `[coeff_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockInner_neg_right (P Q : MvPolynomial σ ℂ) :
    fockInner P (-Q) = - fockInner P Q := by
  rw [fockInner_eq_support P (-Q), fockInner_eq_support P Q, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_neg]
  ring

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, fockInner_add_right, fockInner_neg_right, ← sub_eq_add_neg]`.
-/
theorem fockInner_sub_right (P Q₁ Q₂ : MvPolynomial σ ℂ) :
    fockInner P (Q₁ - Q₂) = fockInner P Q₁ - fockInner P Q₂ := by
  rw [sub_eq_add_neg, fockInner_add_right, fockInner_neg_right, ← sub_eq_add_neg]

/- English proof (translation)
The claim follows from `fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _)`.
-/
private theorem fockInner_eq_sum_support_right (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P Q = ∑ α ∈ Q.support, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α :=
  fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _)

/- English proof (translation)
Rewrite using `[fockInner_eq_sum_support_right (P₁ + P₂) Q, fockInner_eq_sum_support_right P₁ Q, fockInner_eq_sum_support_right P₂ Q, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun α _ => ?_)` and prove the remaining obligations. Rewrite using `[coeff_add, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockInner_add_left (P₁ P₂ Q : MvPolynomial σ ℂ) :
    fockInner (P₁ + P₂) Q = fockInner P₁ Q + fockInner P₂ Q := by
  rw [fockInner_eq_sum_support_right (P₁ + P₂) Q, fockInner_eq_sum_support_right P₁ Q,
    fockInner_eq_sum_support_right P₂ Q, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_add, map_add]
  ring

/- English proof (translation)
Rewrite using `[fockInner_eq_sum_support_right (c • P) Q, fockInner_eq_sum_support_right P Q, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun α _ => ?_)` and prove the remaining obligations. Rewrite using `[coeff_smul, smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockInner_smul_left (P Q : MvPolynomial σ ℂ) (c : ℂ) :
    fockInner (c • P) Q = (starRingEnd ℂ) c * fockInner P Q := by
  rw [fockInner_eq_sum_support_right (c • P) Q, fockInner_eq_sum_support_right P Q, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_smul, smul_eq_mul, map_mul]
  ring

/- English proof (translation)
Rewrite using `[fockInner_eq_sum_support_right (-P) Q, fockInner_eq_sum_support_right P Q, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl (fun α _ => ?_)` and prove the remaining obligations. Rewrite using `[coeff_neg, map_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockInner_neg_left (P Q : MvPolynomial σ ℂ) :
    fockInner (-P) Q = - fockInner P Q := by
  rw [fockInner_eq_sum_support_right (-P) Q, fockInner_eq_sum_support_right P Q,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_neg, map_neg]
  ring

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_empty, Finset.sum_empty, fockInner_zero_right]`. Introduce `a t ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, fockInner_add_right, ih]`.
-/
theorem fockInner_sum_right {ι : Type*} (s : Finset ι) (P : MvPolynomial σ ℂ)
    (f : ι → MvPolynomial σ ℂ) :
    fockInner P (∑ i ∈ s, f i) = ∑ i ∈ s, fockInner P (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, fockInner_zero_right]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockInner_add_right, ih]

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_empty, Finset.sum_empty, fockInner_zero_left]`. Introduce `a t ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, fockInner_add_left, ih]`.
-/
theorem fockInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (Q : MvPolynomial σ ℂ) :
    fockInner (∑ i ∈ s, f i) Q = ∑ i ∈ s, fockInner (f i) Q := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, fockInner_zero_left]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockInner_add_left, ih]

/- English proof (translation)
Unfold `wt Finsupp.prod`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Conclude with `map_natCast _ _`.
-/
theorem wt_conj (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) = wt α := by
  unfold wt Finsupp.prod
  rw [map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact map_natCast _ _

/- English proof (translation)
Rewrite using `[fockInner_eq_support Q P, fockInner_eq_sum_support_right P Q, map_sum]`. Use `Finset.sum_congr rfl (fun α _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, Complex.conj_conj, wt_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockInner_swap (P Q : MvPolynomial σ ℂ) :
    fockInner Q P = (starRingEnd ℂ) (fockInner P Q) := by
  rw [fockInner_eq_support Q P, fockInner_eq_sum_support_right P Q, map_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [map_mul, map_mul, Complex.conj_conj, wt_conj]
  ring

/- English proof (translation)
Establish `hl : l ∈ insert l α.support` using `Finset.mem_insert_self l α.support`. Establish `hsub1 : (Finsupp.single l 1 + α).support ⊆ insert l α.support`. Introduce `i hi`. Rewrite `hi` using `[Finsupp.mem_support_iff, Finsupp.add_apply]`. Distinguish the cases in `h : i = l`.

Rewrite using `[h]`. Conclude with `hl`. Rewrite `hi` using `[Finsupp.single_apply, if_neg (Ne.symm h), zero_add]`. Conclude with `Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hi)`. Establish `hsub2 : α.support ⊆ insert l α.support` using `fun i hi => Finset.mem_insert_of_mem hi`.

Unfold `wt`. Rewrite using `[Finsupp.prod_of_support_subset _ hsub1 _ (fun _ _ => by simp), Finsupp.prod_of_support_subset _ hsub2 _ (fun _ _ => by simp)]`. Establish `e1` using `Finset.mul_prod_erase (insert l α.support) (fun i => (((Finsupp.single l 1 + α : σ →₀ ℕ) i).factorial : ℂ)) hl`. Establish `e2` using `Finset.mul_prod_erase (insert l α.support) (fun i => ((α i).factorial : ℂ)) hl`. Apply the tactic sequence `try beta_reduce at e1 e2`.

Rewrite using `[← e1, ← e2]`. Establish `hrest : ∏ x ∈ (insert l α.support).erase l, (((Finsupp.single l 1 + α : σ →₀ ℕ) x).factorial : ℂ) = ∏ x ∈ (insert l α.support).erase l, ((α x).factorial : ℂ)`. Use `Finset.prod_congr rfl (fun i hi => ?_)` and prove the remaining obligations. Establish `hil : i ≠ l` using `Finset.ne_of_mem_erase hi`. Rewrite using `[Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hil), zero_add]`.

Rewrite using `[hrest, Finsupp.add_apply, Finsupp.single_eq_same, show (1 + α l).factorial = (α l + 1) * (α l).factorial from by`. Rewrite using `[add_comm]`. Conclude with `Nat.factorial_succ _]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wt_single_add (l : σ) (α : σ →₀ ℕ) :
    wt (Finsupp.single l 1 + α) = ((α l : ℂ) + 1) * wt α := by
  classical
  have hl : l ∈ insert l α.support := Finset.mem_insert_self l α.support
  have hsub1 : (Finsupp.single l 1 + α).support ⊆ insert l α.support := by
    intro i hi
    rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hi
    by_cases h : i = l
    · rw [h]
      exact hl
    · rw [Finsupp.single_apply, if_neg (Ne.symm h), zero_add] at hi
      exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hi)
  have hsub2 : α.support ⊆ insert l α.support := fun i hi => Finset.mem_insert_of_mem hi
  unfold wt
  rw [Finsupp.prod_of_support_subset _ hsub1 _ (fun _ _ => by simp),
    Finsupp.prod_of_support_subset _ hsub2 _ (fun _ _ => by simp)]
  have e1 := Finset.mul_prod_erase (insert l α.support)
    (fun i => (((Finsupp.single l 1 + α : σ →₀ ℕ) i).factorial : ℂ)) hl
  have e2 := Finset.mul_prod_erase (insert l α.support) (fun i => ((α i).factorial : ℂ)) hl
  try beta_reduce at e1 e2
  rw [← e1, ← e2]
  have hrest : ∏ x ∈ (insert l α.support).erase l, (((Finsupp.single l 1 + α : σ →₀ ℕ) x).factorial : ℂ) =
      ∏ x ∈ (insert l α.support).erase l, ((α x).factorial : ℂ) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hil : i ≠ l := Finset.ne_of_mem_erase hi
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hil), zero_add]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same,
    show (1 + α l).factorial = (α l + 1) * (α l).factorial from by
      rw [add_comm]
      exact Nat.factorial_succ _]
  push_cast
  ring

/- English proof (translation)
Use `MvPolynomial.induction_on' Q (fun β b => ?_) (fun Q₁ Q₂ h₁ h₂ => ?_)` and prove the remaining obligations. Rewrite using `[pderiv_monomial, fockInner_eq_sum_right (X l * P) (monomial β b) {β} support_monomial_subset, fockInner_eq_sum_right P (monomial (β - Finsupp.single l 1) (b * (β l : ℂ))) {β - Finsupp.single l 1} support_monomial_subset, Finset.sum_singleton, Finset.sum_singleton, coeff_monomial …`. Distinguish the cases in `h : β l = 0`. Establish `hl : l ∉ β.support`. Rewrite using `[Finsupp.mem_support_iff, not_not]`.

Conclude with `h`. Rewrite using `[coeff_X_mul', if_neg hl, h]`. Simplify using the standard rewrite rules. Establish `hβ : β = Finsupp.single l 1 + (β - Finsupp.single l 1)`. Use extensionality with `i`.

Simplify using `only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]`. Use `split_ifs with hli`. Substitute `hli` using the available equality. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.

Take `⟨γ, rfl⟩ : ∃ γ, β = Finsupp.single l 1 + γ` from `⟨_, hβ⟩`. Rewrite using `[add_tsub_cancel_left, coeff_X_mul, wt_single_add, Finsupp.add_apply, Finsupp.single_eq_same]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_add, fockInner_add_right, fockInner_add_right, h₁, h₂]`.
-/
theorem fockInner_X_mul (l : σ) (P Q : MvPolynomial σ ℂ) :
    fockInner (X l * P) Q = fockInner P (pderiv l Q) := by
  classical
  refine MvPolynomial.induction_on' Q (fun β b => ?_) (fun Q₁ Q₂ h₁ h₂ => ?_)
  · rw [pderiv_monomial,
      fockInner_eq_sum_right (X l * P) (monomial β b) {β} support_monomial_subset,
      fockInner_eq_sum_right P (monomial (β - Finsupp.single l 1) (b * (β l : ℂ)))
        {β - Finsupp.single l 1} support_monomial_subset,
      Finset.sum_singleton, Finset.sum_singleton, coeff_monomial, coeff_monomial, if_pos rfl, if_pos rfl]
    by_cases h : β l = 0
    · have hl : l ∉ β.support := by
        rw [Finsupp.mem_support_iff, not_not]
        exact h
      rw [coeff_X_mul', if_neg hl, h]
      simp
    · have hβ : β = Finsupp.single l 1 + (β - Finsupp.single l 1) := by
        ext i
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
        split_ifs with hli
        · subst hli
          omega
        · omega
      obtain ⟨γ, rfl⟩ : ∃ γ, β = Finsupp.single l 1 + γ := ⟨_, hβ⟩
      rw [add_tsub_cancel_left, coeff_X_mul, wt_single_add, Finsupp.add_apply,
        Finsupp.single_eq_same]
      push_cast
      ring
  · rw [map_add, fockInner_add_right, fockInner_add_right, h₁, h₂]

/- English proof (translation)
Rewrite using `[fockInner_swap (X l * Q) P, fockInner_X_mul, ← fockInner_swap]`.
-/
theorem fockInner_mul_X (l : σ) (P Q : MvPolynomial σ ℂ) :
    fockInner P (X l * Q) = fockInner (pderiv l P) Q := by
  rw [fockInner_swap (X l * Q) P, fockInner_X_mul, ← fockInner_swap]

/- English proof (translation)
Introduce `τ c P₁ P₂ Q`. Rewrite using `[fockInner_add_left, fockInner_smul_left]`.
-/
theorem fischerConjLinearLeft : FockRL.FockLinL := by
  intro τ c P₁ P₂ Q
  rw [fockInner_add_left, fockInner_smul_left]

/- English proof (translation)
Introduce `τ c P Q₁ Q₂`. Rewrite using `[fockInner_add_right, fockInner_smul_right]`.
-/
theorem fischerLinearRight : FockRL.FockLinR := by
  intro τ c P Q₁ Q₂
  rw [fockInner_add_right, fockInner_smul_right]

/- English proof (translation)
Introduce `τ l P Q`. Conclude with `fockInner_X_mul l P Q`.
-/
theorem fischerXAdjoint : FockRL.FockXAdj := by
  intro τ l P Q
  exact fockInner_X_mul l P Q

end FockRaiseLowInner
