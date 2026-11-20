import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarExist

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QPK

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Establish `hF : Measurable fun x : (i : _) → E i => ∏ i, f i (x i)` using `Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)`. Distinguish the cases in `hne : Nonempty ((i : _) → E i)`. Take `⟨x0⟩` from `hne`. Establish `key : ∀ s : Finset _, ∀ x : (i : _) → E i, lmarginal μ s (fun x : (i : _) → E i => ∏ i, f i (x i)) x = ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i))`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `x`. Simplify using `[lmarginal_empty]`. Consider the case `insert a s ha ih`.

Introduce `x`. Rewrite using `[lmarginal_insert _ hF ha]`. Repeatedly rewrite using `[ih]`. Establish `hC : ∀ t, ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (Function.update x a t i)) = f a t * ∏ i ∈ Finset.univ.erase a, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i))`. Introduce `t`.

Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]`. Use `congr 1`. Simplify using `[ha]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Simplify using `[Function.update_apply, Finset.ne_of_mem_erase hi]`.

Repeatedly rewrite using `[hC]`. Rewrite using `[lintegral_mul_const _ (hf a), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]`. Use `congr 1`. Simplify using the standard rewrite rules. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations.

Simplify using `[Finset.mem_insert, Finset.ne_of_mem_erase hi]`. Rewrite using `[lintegral_eq_lmarginal_univ x0, key]`. Simplify using the standard rewrite rules. Establish `hj : ∃ j, IsEmpty (E j)`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hne ⟨fun i => (h i).some⟩`. Take `⟨j, hj⟩` from `hj`. Use `haveI : IsEmpty ((i : _) → E i) := not_nonempty_iff.1 hne`. Rewrite using `[lintegral_of_isEmpty]`.

Use `(Finset.prod_eq_zero (Finset.mem_univ j) ?_).symm` and prove the remaining obligations. Use `haveI := hj`. Conclude with `lintegral_of_isEmpty _ _`.
-/
theorem lintegral_fin_prod {n : ℕ} {E : Fin n → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  have hF : Measurable fun x : (i : _) → E i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  by_cases hne : Nonempty ((i : _) → E i)
  · obtain ⟨x0⟩ := hne
    have key : ∀ s : Finset _, ∀ x : (i : _) → E i,
        lmarginal μ s (fun x : (i : _) → E i => ∏ i, f i (x i)) x =
          ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro x
        simp [lmarginal_empty]
      | insert a s ha ih =>
        intro x
        rw [lmarginal_insert _ hF ha]
        simp_rw [ih]
        have hC : ∀ t, ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (Function.update x a t i)) =
            f a t * ∏ i ∈ Finset.univ.erase a, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i)) := by
          intro t
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
          congr 1
          · simp [ha]
          · refine Finset.prod_congr rfl fun i hi => ?_
            simp [Function.update_apply, Finset.ne_of_mem_erase hi]
        simp_rw [hC]
        rw [lintegral_mul_const _ (hf a), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
        congr 1
        · simp
        · refine Finset.prod_congr rfl fun i hi => ?_
          simp [Finset.mem_insert, Finset.ne_of_mem_erase hi]
    rw [lintegral_eq_lmarginal_univ x0, key]
    simp
  · have hj : ∃ j, IsEmpty (E j) := by
      by_contra h
      push_neg at h
      exact hne ⟨fun i => (h i).some⟩
    obtain ⟨j, hj⟩ := hj
    haveI : IsEmpty ((i : _) → E i) := not_nonempty_iff.1 hne
    rw [lintegral_of_isEmpty]
    refine (Finset.prod_eq_zero (Finset.mem_univ j) ?_).symm
    haveI := hj
    exact lintegral_of_isEmpty _ _

/- English proof (translation)
Establish `hF : Measurable fun x : (i : _) → E i => ∏ i, f i (x i)` using `Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)`. Distinguish the cases in `hne : Nonempty ((i : _) → E i)`. Take `⟨x0⟩` from `hne`. Establish `key : ∀ s : Finset _, ∀ x : (i : _) → E i, lmarginal μ s (fun x : (i : _) → E i => ∏ i, f i (x i)) x = ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i))`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `x`. Simplify using `[lmarginal_empty]`. Consider the case `insert a s ha ih`.

Introduce `x`. Rewrite using `[lmarginal_insert _ hF ha]`. Repeatedly rewrite using `[ih]`. Establish `hC : ∀ t, ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (Function.update x a t i)) = f a t * ∏ i ∈ Finset.univ.erase a, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i))`. Introduce `t`.

Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]`. Use `congr 1`. Simplify using `[ha]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Simplify using `[Function.update_apply, Finset.ne_of_mem_erase hi]`.

Repeatedly rewrite using `[hC]`. Rewrite using `[lintegral_mul_const _ (hf a), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]`. Use `congr 1`. Simplify using the standard rewrite rules. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations.

Simplify using `[Finset.mem_insert, Finset.ne_of_mem_erase hi]`. Rewrite using `[lintegral_eq_lmarginal_univ x0, key]`. Simplify using the standard rewrite rules. Establish `hj : ∃ j, IsEmpty (E j)`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hne ⟨fun i => (h i).some⟩`. Take `⟨j, hj⟩` from `hj`. Use `haveI : IsEmpty ((i : _) → E i) := not_nonempty_iff.1 hne`. Rewrite using `[lintegral_of_isEmpty]`.

Use `(Finset.prod_eq_zero (Finset.mem_univ j) ?_).symm` and prove the remaining obligations. Use `haveI := hj`. Conclude with `lintegral_of_isEmpty _ _`.
-/
theorem lintegral_fintype_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  have hF : Measurable fun x : (i : _) → E i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  by_cases hne : Nonempty ((i : _) → E i)
  · obtain ⟨x0⟩ := hne
    have key : ∀ s : Finset _, ∀ x : (i : _) → E i,
        lmarginal μ s (fun x : (i : _) → E i => ∏ i, f i (x i)) x =
          ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro x
        simp [lmarginal_empty]
      | insert a s ha ih =>
        intro x
        rw [lmarginal_insert _ hF ha]
        simp_rw [ih]
        have hC : ∀ t, ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (Function.update x a t i)) =
            f a t * ∏ i ∈ Finset.univ.erase a, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i)) := by
          intro t
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
          congr 1
          · simp [ha]
          · refine Finset.prod_congr rfl fun i hi => ?_
            simp [Function.update_apply, Finset.ne_of_mem_erase hi]
        simp_rw [hC]
        rw [lintegral_mul_const _ (hf a), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
        congr 1
        · simp
        · refine Finset.prod_congr rfl fun i hi => ?_
          simp [Finset.mem_insert, Finset.ne_of_mem_erase hi]
    rw [lintegral_eq_lmarginal_univ x0, key]
    simp
  · have hj : ∃ j, IsEmpty (E j) := by
      by_contra h
      push_neg at h
      exact hne ⟨fun i => (h i).some⟩
    obtain ⟨j, hj⟩ := hj
    haveI : IsEmpty ((i : _) → E i) := not_nonempty_iff.1 hne
    rw [lintegral_of_isEmpty]
    refine (Finset.prod_eq_zero (Finset.mem_univ j) ?_).symm
    haveI := hj
    exact lintegral_of_isEmpty _ _

end QPK
