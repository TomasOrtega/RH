import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotent

set_option autoImplicit false

namespace GlobalTheory.PeriodFamily

/- English proof (translation)
Introduce `I _ _ D _ _ J N hJ r`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `n _ _ K f _`. Use `⟨fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun a ↦ ?_⟩` and prove the remaining obligations.

Establish `h` using `taylor_sub_value_mem_span N (fun i ↦ ∑ j, n j i) (f a)`. Establish `h0 : Ideal.span (Set.range (fun i ↦ ∑ j, n j i)) = ⊥`. Rewrite using `[Ideal.span_eq_bot]`. Introduce and unpack `x ⟨i, rfl⟩`. Simplify using the standard rewrite rules.

Rewrite `h` using `[h0, Ideal.mem_bot]`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Consider the case `succ r ih`. Introduce `n hn hsq K f hf`.

Take `⟨n', h1, h2, h3⟩` from `ih (fun j ↦ n j.succ) (fun j i ↦ hn _ _) (fun j i i' ↦ hsq _ _ _) f hf`. Use `⟨Fin.cons (fun a ↦ ∑ i, taylor N (fun i ↦ ∑ j : Fin r, n j.succ i) (fun z ↦ fderiv ℂ (f a) z (Pi.single i 1)) * n 0 i) n', ?_, ?_, fun a ↦ ?_⟩` and prove the remaining obligations. Introduce `j a`. Use `Fin.cases ?_ (fun j ↦ ?_) j` and prove the remaining obligations. Simplify using `only [Fin.cons_zero]`.

Conclude with `Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hn _ _)`. Simplify `h1 j a` using `only [Fin.cons_succ]`. Introduce `j a b`. Use `Fin.cases ?_ (fun j ↦ ?_) j` and prove the remaining obligations. Simplify using `only [Fin.cons_zero]`.

Rewrite using `[Finset.sum_mul_sum]`. Use `Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun i' _ ↦ ?_` and prove the remaining obligations. Rewrite using `[mul_mul_mul_comm, hsq, mul_zero]`. Simplify `h2 j a b` using `only [Fin.cons_succ]`. Establish `he : (fun i ↦ ∑ j, n j i) = fun i ↦ (∑ j : Fin r, n j.succ i) + n 0 i`.

Use function extensionality and compare the values at `i`. Rewrite using `[Fin.sum_univ_succ, add_comm]`. Establish `hle : Ideal.span (Set.range (fun i ↦ ∑ j : Fin r, n j.succ i) ∪ Set.range (n 0)) ≤ J`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `x (⟨i, rfl⟩ | ⟨i, rfl⟩)`.

Conclude with `Ideal.sum_mem _ fun j _ ↦ hn _ _`. Conclude with `hn _ _`. Rewrite using `[he, taylor_add_of_mul_eq_zero N (fun i ↦ ∑ j : Fin r, n j.succ i) (n 0) (fun s hs ↦ hJ s fun a ↦ hle (hs a)) (hsq 0) (f a) (hf a), Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[← h3 a]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem taylor_sum_sub_value_eq_sum_sqZero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (n : Fin r → I → D), (∀ j i, n j i ∈ J) → (∀ j i i', n j i * n j i' = 0) → ∀ {K : Type} (f : K → (I → ℂ) → ℂ), (∀ a, AnalyticAt ℂ (f a) 0) → ∃ n' : Fin r → K → D, (∀ j a, n' j a ∈ J) ∧ (∀ j a b, n' j a * n' j b = 0) ∧ ∀ a, GlobalTheory.PeriodFamily.taylor N (fun i ↦ ∑ j, n j i) (f a) - algebraMap ℂ D (f a 0) = ∑ j, n' j a := by
  intro I _ _ D _ _ J N hJ r
  induction r with
  | zero =>
    intro n _ _ K f _
    refine ⟨fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun a ↦ ?_⟩
    have h := taylor_sub_value_mem_span N (fun i ↦ ∑ j, n j i) (f a)
    have h0 : Ideal.span (Set.range (fun i ↦ ∑ j, n j i)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro x ⟨i, rfl⟩
      simp
    rw [h0, Ideal.mem_bot] at h
    rw [h]
    simp
  | succ r ih =>
    intro n hn hsq K f hf
    obtain ⟨n', h1, h2, h3⟩ := ih (fun j ↦ n j.succ) (fun j i ↦ hn _ _) (fun j i i' ↦ hsq _ _ _) f hf
    refine ⟨Fin.cons (fun a ↦ ∑ i, taylor N (fun i ↦ ∑ j : Fin r, n j.succ i)
      (fun z ↦ fderiv ℂ (f a) z (Pi.single i 1)) * n 0 i) n', ?_, ?_, fun a ↦ ?_⟩
    · intro j a
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simp only [Fin.cons_zero]
        exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hn _ _)
      · simpa only [Fin.cons_succ] using h1 j a
    · intro j a b
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simp only [Fin.cons_zero]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun i' _ ↦ ?_
        rw [mul_mul_mul_comm, hsq, mul_zero]
      · simpa only [Fin.cons_succ] using h2 j a b
    · have he : (fun i ↦ ∑ j, n j i) = fun i ↦ (∑ j : Fin r, n j.succ i) + n 0 i := by
        funext i
        rw [Fin.sum_univ_succ, add_comm]
      have hle : Ideal.span (Set.range (fun i ↦ ∑ j : Fin r, n j.succ i) ∪ Set.range (n 0)) ≤ J := by
        rw [Ideal.span_le]
        rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact Ideal.sum_mem _ fun j _ ↦ hn _ _
        · exact hn _ _
      rw [he, taylor_add_of_mul_eq_zero N (fun i ↦ ∑ j : Fin r, n j.succ i) (n 0)
        (fun s hs ↦ hJ s fun a ↦ hle (hs a)) (hsq 0) (f a) (hf a), Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← h3 a]
      ring

end GlobalTheory.PeriodFamily
