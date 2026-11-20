import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSubmoduleOfComplexPolyValuesMemStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap

open Matrix Formalism.REAL GlobalTheory.TorFin

/- English proof (translation)
Proceed by induction on `m generalizing a b with`. Consider the case `zero`. Rewrite using `[epow.eq_1, pow_zero, Matrix.one_apply]`. Consider the case `succ k ih`. Rewrite using `[epow.eq_2, pow_succ, Matrix.mul_apply]`.

Simplify using `only [ih, Matrix.of_apply]`.
-/
private theorem epow_eq_matrix_pow {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (m : ℕ) (a b : Fin n) :
    epow E m a b = (Matrix.of E ^ m) a b := by
  induction m generalizing a b with
  | zero =>
    rw [epow.eq_1, pow_zero, Matrix.one_apply]
  | succ k ih =>
    rw [epow.eq_2, pow_succ, Matrix.mul_apply]
    simp only [ih, Matrix.of_apply]

/- English proof (translation)
Take `⟨v, hv0, hv⟩` from `hf`. Use `⟨fun l => a * v l, by simp [hv0], fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[hv u, Finset.mul_sum]`. Simplify using `only [mul_smul_comm]`.
-/
private theorem exists_coeff_vanishing_mul_left {A : Type} [Ring A] [Algebra ℂ A] (K p : ℕ) (a : A) {f : ℂ → A}
    (hf : ∃ v : ℕ → A, v p = 0 ∧ ∀ u, f u = ∑ l ∈ Finset.range K, u ^ l • v l) :
    ∃ v : ℕ → A, v p = 0 ∧ ∀ u, a * f u = ∑ l ∈ Finset.range K, u ^ l • v l := by
  obtain ⟨v, hv0, hv⟩ := hf
  refine ⟨fun l => a * v l, by simp [hv0], fun u => ?_⟩
  rw [hv u, Finset.mul_sum]
  simp only [mul_smul_comm]

/- English proof (translation)
Take `⟨v, hv0, hv⟩` from `hf`. Use `⟨fun l => v l * a, by simp [hv0], fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[hv u, Finset.sum_mul]`. Simplify using `only [smul_mul_assoc]`.
-/
private theorem exists_coeff_vanishing_mul_right {A : Type} [Ring A] [Algebra ℂ A] (K p : ℕ) (a : A) {f : ℂ → A}
    (hf : ∃ v : ℕ → A, v p = 0 ∧ ∀ u, f u = ∑ l ∈ Finset.range K, u ^ l • v l) :
    ∃ v : ℕ → A, v p = 0 ∧ ∀ u, f u * a = ∑ l ∈ Finset.range K, u ^ l • v l := by
  obtain ⟨v, hv0, hv⟩ := hf
  refine ⟨fun l => v l * a, by simp [hv0], fun u => ?_⟩
  rw [hv u, Finset.sum_mul]
  simp only [smul_mul_assoc]

/- English proof (translation)
Use `choose v hv0 hv using hf`. Use `⟨fun l => ∑ i, v i l, by simp [hv0], fun u => ?_⟩` and prove the remaining obligations. Simplify using `only [hv, Finset.smul_sum]`. Conclude with `Finset.sum_comm`.
-/
private theorem exists_coeff_vanishing_sum {A : Type} [Ring A] [Algebra ℂ A] (K p : ℕ) {ι : Type} [Fintype ι]
    {f : ι → ℂ → A}
    (hf : ∀ i, ∃ v : ℕ → A, v p = 0 ∧ ∀ u, f i u = ∑ l ∈ Finset.range K, u ^ l • v l) :
    ∃ v : ℕ → A, v p = 0 ∧ ∀ u, ∑ i, f i u = ∑ l ∈ Finset.range K, u ^ l • v l := by
  choose v hv0 hv using hf
  refine ⟨fun l => ∑ i, v i l, by simp [hv0], fun u => ?_⟩
  simp only [hv, Finset.smul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Use `set S := Algebra.adjoin ℂ (Set.range (qdet E)) with hS`. Establish `hq : ∀ u, qdet E u ∈ S` using `fun u => Algebra.subset_adjoin ⟨u, rfl⟩`. Take `⟨c, hc1, hc⟩` from `GlobalTheory.T.exists_monic_poly_eq_qdet A (m + 1) E`. Establish `hp : ∀ i j : Fin (m + 1), ∃ v : ℕ → A, v (m + 1) = 0 ∧ ∀ u : ℂ, qminor E j.succAbove i.succAbove u = ∑ l ∈ Finset.range (m + 1 + 1), u ^ l • v l`. Introduce `i j`.

Take `⟨d, hd⟩` from `GlobalTheory.qminor_polyMap A (m + 1) m E j.succAbove i.succAbove 0`. Use `⟨fun l => if l < m + 1 then d l else 0, by simp, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_range_succ]`. Simplify using `only [lt_irrefl, ↓reduceIte, smul_zero, add_zero]`. Establish `e` using `hd u`.

Rewrite `e` using `[sub_zero]`. Rewrite using `[e]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[if_pos (Finset.mem_range.mp hl)]`. Use `Nat.strong_induction_on N ?_` and prove the remaining obligations.

Introduce `N ih`. Establish `hgS : ∀ u : ℂ, algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E j.succAbove i.succAbove u * epow E (N + 1) j i - qdet E u * (algebraMap ℂ A ((-1) ^ N) * etr E N) ∈ S`. Introduce `u`. Establish `key` using `GlobalTheory.T.traced_qminor_comatrix_truncated_inverse A m E hE u N`. Rewrite `key` using `[Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_add]`.

Rewrite using `[eq_sub_of_add_eq' key, sub_right_comm, add_sub_cancel_right]`. Use `S.sub_mem (S.mul_mem (hq u) (S.sum_mem fun k hk => S.mul_mem (S.algebraMap_mem _) (ih k (Finset.mem_range.mp hk)))) (S.mul_mem (S.algebraMap_mem _) ?_)` and prove the remaining obligations. Rewrite using `[← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor' A m E u]`. Conclude with `S.sub_mem (hq _) (hq _)`. Establish `h1 : ∀ i j : Fin (m + 1), ∃ v : ℕ → A, v (m + 1) = 0 ∧ ∀ u : ℂ, (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E j.succAbove i.succAbove u * epow E (N + 1) j i = ∑ l ∈ Finset.range (m + 1 + 1), u ^ l • v l` using `fun i j => exists_coeff_vanishing_mul_right _ _ _ (exists_coeff_vanishing_mul_left _ _ _ (hp i j))`.

Take `⟨v, hv0, hv⟩` from `exists_coeff_vanishing_mul_left _ _ (algebraMap ℂ A ((-1) ^ N)) (exists_coeff_vanishing_sum _ _ fun i => exists_coeff_vanishing_sum _ _ (h1 i))`. Establish `hall : ∀ u : ℂ, ∑ l ∈ Finset.range (m + 1 + 1), u ^ l • (v l - c l * (algebraMap ℂ A ((-1) ^ N) * etr E N)) ∈ Subalgebra.toSubmodule S`. Introduce `u`. Establish `e : ∑ l ∈ Finset.range (m + 1 + 1), u ^ l • (v l - c l * (algebraMap ℂ A ((-1) ^ N) * etr E N)) = algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E j.succAbove i.succAbove u * epow E (N + 1) j i - qdet E u * (a …`. Rewrite using `[hv u, hc u, Finset.sum_mul, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_sub, smul_mul_assoc]`. Rewrite using `[e]`. Conclude with `hgS u`. Establish `hm` using `GlobalTheory.T.coeff_mem_submodule_of_complex_poly_values_mem A (Subalgebra.toSubmodule S) (m + 1 + 1) _ hall (m + 1) (by omega)`.

Simplify using `only [hv0, hc1, zero_sub, one_mul] at hm`. Establish `hm' : algebraMap ℂ A ((-1) ^ N) * etr E N ∈ S`. Establish `h` using `(Subalgebra.toSubmodule S).neg_mem hm`. Rewrite `h` using `[neg_neg]`. Conclude with `(Subalgebra.mem_toSubmodule S).1 h`.

Establish `h` using `S.mul_mem (S.algebraMap_mem ((-1 : ℂ) ^ N)) hm'`. Rewrite `h` using `[← mul_assoc, ← map_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, map_one, one_mul]`. Then use the resulting hypothesis.
-/
private theorem etr_mem_adjoin_range_qdet (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A)
    (hE : GlRel E) (N : ℕ) : etr E N ∈ Algebra.adjoin ℂ (Set.range (qdet E)) := by
  set S := Algebra.adjoin ℂ (Set.range (qdet E)) with hS
  have hq : ∀ u, qdet E u ∈ S := fun u => Algebra.subset_adjoin ⟨u, rfl⟩
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet A (m + 1) E
  have hp : ∀ i j : Fin (m + 1), ∃ v : ℕ → A, v (m + 1) = 0 ∧
      ∀ u : ℂ, qminor E j.succAbove i.succAbove u = ∑ l ∈ Finset.range (m + 1 + 1), u ^ l • v l := by
    intro i j
    obtain ⟨d, hd⟩ := GlobalTheory.qminor_polyMap A (m + 1) m E j.succAbove i.succAbove 0
    refine ⟨fun l => if l < m + 1 then d l else 0, by simp, fun u => ?_⟩
    rw [Finset.sum_range_succ]
    simp only [lt_irrefl, ↓reduceIte, smul_zero, add_zero]
    have e := hd u
    rw [sub_zero] at e
    rw [e]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [if_pos (Finset.mem_range.mp hl)]
  refine Nat.strong_induction_on N ?_
  intro N ih
  have hgS : ∀ u : ℂ, algebraMap ℂ A ((-1) ^ N) *
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) *
        qminor E j.succAbove i.succAbove u * epow E (N + 1) j i
      - qdet E u * (algebraMap ℂ A ((-1) ^ N) * etr E N) ∈ S := by
    intro u
    have key := GlobalTheory.T.traced_qminor_comatrix_truncated_inverse A m E hE u N
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_add] at key
    rw [eq_sub_of_add_eq' key, sub_right_comm, add_sub_cancel_right]
    refine S.sub_mem (S.mul_mem (hq u) (S.sum_mem fun k hk => S.mul_mem (S.algebraMap_mem _)
      (ih k (Finset.mem_range.mp hk)))) (S.mul_mem (S.algebraMap_mem _) ?_)
    rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor' A m E u]
    exact S.sub_mem (hq _) (hq _)
  have h1 : ∀ i j : Fin (m + 1), ∃ v : ℕ → A, v (m + 1) = 0 ∧ ∀ u : ℂ,
      (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E j.succAbove i.succAbove u * epow E (N + 1) j i
        = ∑ l ∈ Finset.range (m + 1 + 1), u ^ l • v l :=
    fun i j => exists_coeff_vanishing_mul_right _ _ _ (exists_coeff_vanishing_mul_left _ _ _ (hp i j))
  obtain ⟨v, hv0, hv⟩ := exists_coeff_vanishing_mul_left _ _ (algebraMap ℂ A ((-1) ^ N))
    (exists_coeff_vanishing_sum _ _ fun i => exists_coeff_vanishing_sum _ _ (h1 i))
  have hall : ∀ u : ℂ, ∑ l ∈ Finset.range (m + 1 + 1),
      u ^ l • (v l - c l * (algebraMap ℂ A ((-1) ^ N) * etr E N)) ∈ Subalgebra.toSubmodule S := by
    intro u
    have e : ∑ l ∈ Finset.range (m + 1 + 1), u ^ l • (v l - c l * (algebraMap ℂ A ((-1) ^ N) * etr E N))
        = algebraMap ℂ A ((-1) ^ N) *
          ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) *
            qminor E j.succAbove i.succAbove u * epow E (N + 1) j i
          - qdet E u * (algebraMap ℂ A ((-1) ^ N) * etr E N) := by
      rw [hv u, hc u, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_sub, smul_mul_assoc]
    rw [e]
    exact hgS u
  have hm := GlobalTheory.T.coeff_mem_submodule_of_complex_poly_values_mem A (Subalgebra.toSubmodule S) (m + 1 + 1) _ hall (m + 1) (by omega)
  simp only [hv0, hc1, zero_sub, one_mul] at hm
  have hm' : algebraMap ℂ A ((-1) ^ N) * etr E N ∈ S := by
    have h := (Subalgebra.toSubmodule S).neg_mem hm
    rw [neg_neg] at h
    exact (Subalgebra.mem_toSubmodule S).1 h
  have h := S.mul_mem (S.algebraMap_mem ((-1 : ℂ) ^ N)) hm'
  rwa [← mul_assoc, ← map_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, map_one, one_mul] at h

/- English proof (translation)
Introduce `A _ _ n X hX k`. Rewrite using `[GlobalTheory.SmoothForms.gelfA_eq_sum_pow]`. Establish `h : (∑ c, (Matrix.of X ^ (k + 1)) c c) = etr X (k + 1)`. Simplify using `only [etr, epow_eq_matrix_pow]`. Rewrite using `[h]`.

Consider the cases of `n with`. Consider the case `zero`. Establish `h0 : etr X (k + 1) = 0` using `by simp [etr]`. Rewrite using `[h0]`. Conclude with `Subalgebra.zero_mem _`.

Consider the case `succ m => exact etr_mem_adjoin_range_qdet A m X hX (k + 1)`.
-/
theorem UpperTheory.gelfandElement_mem_adjoin_capelliCoeffs :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), GlRel X → ∀ k : ℕ, GlobalTheory.SmoothForms.gelfA X k ∈ Algebra.adjoin ℂ (Set.range (qdet X)) := by
  intro A _ _ n X hX k
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow]
  have h : (∑ c, (Matrix.of X ^ (k + 1)) c c) = etr X (k + 1) := by
    simp only [etr, epow_eq_matrix_pow]
  rw [h]
  cases n with
  | zero =>
    have h0 : etr X (k + 1) = 0 := by simp [etr]
    rw [h0]
    exact Subalgebra.zero_mem _
  | succ m => exact etr_mem_adjoin_range_qdet A m X hX (k + 1)
