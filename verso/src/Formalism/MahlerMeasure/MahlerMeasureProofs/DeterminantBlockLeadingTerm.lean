import Formalism.MahlerMeasure.Statement

namespace Formalism.GM

open Finset Polynomial

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using the standard rewrite rules. Introduce `a s ha ih h`.

Establish `ha' : (f a).natDegree ≤ d a` using `h a (Finset.mem_insert_self a s)`. Take `⟨ih1, ih2⟩` from `ih (fun i hi => h i (Finset.mem_insert_of_mem hi))`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]`. Conclude with `⟨Polynomial.natDegree_mul_le.trans (add_le_add ha' ih1), by rw [Polynomial.coeff_mul_add_eq_of_natDegree_le ha' ih1, ih2]⟩`.
-/
theorem prod_natDegree_coeff {K ι : Type*} [CommRing K] (s : Finset ι) (f : ι → K[X]) (d : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ha ih h
    have ha' : (f a).natDegree ≤ d a := h a (Finset.mem_insert_self a s)
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact ⟨Polynomial.natDegree_mul_le.trans (add_le_add ha' ih1),
      by rw [Polynomial.coeff_mul_add_eq_of_natDegree_le ha' ih1, ih2]⟩

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.smul_def]`. Conclude with `(Polynomial.natDegree_smul_le _ _).trans hp`. Rewrite using `[Units.smul_def, Units.smul_def, Polynomial.coeff_smul]`.
-/
theorem term_natDegree_coeff {K : Type*} [CommRing K] (u : ℤˣ) (p : K[X]) (N : ℕ)
    (hp : p.natDegree ≤ N) :
    (u • p).natDegree ≤ N ∧ (u • p).coeff N = u • p.coeff N := by
  refine ⟨?_, ?_⟩
  · rw [Units.smul_def]
    exact (Polynomial.natDegree_smul_le _ _).trans hp
  · rw [Units.smul_def, Units.smul_def, Polynomial.coeff_smul]

/- English proof (translation)
Establish `key : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ • ∏ i, A (σ i) i).natDegree ≤ N ∧ (Equiv.Perm.sign σ • ∏ i, A (σ i) i).coeff N = Equiv.Perm.sign σ • ∏ i, (A (σ i) i).coeff (c σ i)`. Introduce `σ`. Take `⟨h1, h2⟩` from `prod_natDegree_coeff univ (fun i => A (σ i) i) (c σ) (fun i _ => hA σ i)`. Rewrite `h1`, `h2` using `[hc σ]`. Take `⟨k1, k2⟩` from `term_natDegree_coeff (Equiv.Perm.sign σ) _ N h1`.

Conclude with `⟨k1, by rw [k2, h2]⟩`. Rewrite using `[Matrix.det_apply]`. Use `⟨natDegree_sum_le_of_forall_le _ _ (fun σ _ => (key σ).1), ?_⟩` and prove the remaining obligations. Rewrite using `[finsetSum_coeff]`. Conclude with `sum_congr rfl (fun σ _ => (key σ).2)`.
-/
theorem det_natDegree_coeff {K : Type*} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K[X]) (N : ℕ)
    (c : Equiv.Perm (Fin n) → Fin n → ℕ) (hc : ∀ σ, ∑ i, c σ i = N)
    (hA : ∀ σ i, (A (σ i) i).natDegree ≤ c σ i) :
    A.det.natDegree ≤ N ∧
      A.det.coeff N = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, (A (σ i) i).coeff (c σ i) := by
  have key : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ • ∏ i, A (σ i) i).natDegree ≤ N ∧
      (Equiv.Perm.sign σ • ∏ i, A (σ i) i).coeff N =
        Equiv.Perm.sign σ • ∏ i, (A (σ i) i).coeff (c σ i) := by
    intro σ
    obtain ⟨h1, h2⟩ := prod_natDegree_coeff univ (fun i => A (σ i) i) (c σ) (fun i _ => hA σ i)
    rw [hc σ] at h1 h2
    obtain ⟨k1, k2⟩ := term_natDegree_coeff (Equiv.Perm.sign σ) _ N h1
    exact ⟨k1, by rw [k2, h2]⟩
  rw [Matrix.det_apply]
  refine ⟨natDegree_sum_le_of_forall_le _ _ (fun σ _ => (key σ).1), ?_⟩
  rw [finsetSum_coeff]
  exact sum_congr rfl (fun σ _ => (key σ).2)

/- English proof (translation)
Unfold `DetBlockLead`. Introduce `K _ n A D e he hA`. Use `set M : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0 with hM`. Establish `hdeg : ∀ σ : Equiv.Perm (Fin n), ∀ i, (A (σ i) i).natDegree ≤ D - e i`. Introduce `σ i`.

Establish `h3` using `hA (σ i) i`. Establish `h4 : e i ≤ max (e (σ i)) (e i)` using `le_max_right _ _`. Use linear arithmetic over natural numbers and integers. Take `⟨h1, h2⟩` from `det_natDegree_coeff A (∑ i, (D - e i)) (fun _ i => D - e i) (fun _ => rfl) hdeg`. Establish `hprod : ∀ σ : Equiv.Perm (Fin n), ∏ i, (A (σ i) i).coeff (D - e i) = ∏ i, M (σ i) i`.

Introduce `σ`. Distinguish the cases in `hall : ∀ i, e (σ i) = e i`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Simplify using `[hM, Matrix.of_apply, hall i]`. Use `push_neg at hall`.

Establish `hex : ∃ j, e j < e (σ j)`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `hsum : ∑ j, e (σ j) = ∑ j, e j` using `Equiv.sum_comp σ e`. Establish `hall'` using `(Finset.sum_eq_sum_iff_of_le (fun j _ => hno j)).1 hsum`.

Take `⟨i, hi⟩` from `hall`. Conclude with `hi (hall' i (Finset.mem_univ i))`. Take `⟨j, hj⟩` from `hex`. Establish `hne : e (σ j) ≠ e j` using `ne_of_gt hj`. Establish `hL : (A (σ j) j).coeff (D - e j) = 0`.

Apply `Polynomial.coeff_eq_zero_of_natDegree_lt` to reduce the goal to its premises. Establish `h3` using `hA (σ j) j`. Establish `h4 : e (σ j) ≤ max (e (σ j)) (e j)` using `le_max_left _ _`. Establish `h5` using `he (σ j)`. Use linear arithmetic over natural numbers and integers.

Establish `hR : M (σ j) j = 0` using `by simp [hM, Matrix.of_apply, hne]`. Rewrite using `[Finset.prod_eq_zero (f := fun i => (A (σ i) i).coeff (D - e i)) (Finset.mem_univ j) hL, Finset.prod_eq_zero (f := fun i => M (σ i) i) (Finset.mem_univ j) hR]`. Establish `hdet : A.det.coeff (∑ i, (D - e i)) = M.det`. Rewrite using `[h2, Matrix.det_apply]`. Conclude with `Finset.sum_congr rfl (fun σ _ => by rw [hprod σ])`.

Use `⟨h1, hdet, fun hne => ?_⟩` and prove the remaining obligations. Establish `hN : A.det.natDegree = ∑ i, (D - e i)` using `le_antisymm h1 (Polynomial.le_natDegree_of_ne_zero (by rw [hdet]; exact hne))`. Use `⟨hN, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.leadingCoeff, hN, hdet]`.
-/
theorem determinant_block_leading_term : DetBlockLead := by
  unfold DetBlockLead
  intro K _ n A D e he hA
  set M : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0 with hM
  have hdeg : ∀ σ : Equiv.Perm (Fin n), ∀ i, (A (σ i) i).natDegree ≤ D - e i := by
    intro σ i
    have h3 := hA (σ i) i
    have h4 : e i ≤ max (e (σ i)) (e i) := le_max_right _ _
    omega
  obtain ⟨h1, h2⟩ := det_natDegree_coeff A (∑ i, (D - e i)) (fun _ i => D - e i)
    (fun _ => rfl) hdeg
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      ∏ i, (A (σ i) i).coeff (D - e i) = ∏ i, M (σ i) i := by
    intro σ
    by_cases hall : ∀ i, e (σ i) = e i
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      simp [hM, Matrix.of_apply, hall i]
    · push_neg at hall
      have hex : ∃ j, e j < e (σ j) := by
        by_contra hno
        push_neg at hno
        have hsum : ∑ j, e (σ j) = ∑ j, e j := Equiv.sum_comp σ e
        have hall' := (Finset.sum_eq_sum_iff_of_le (fun j _ => hno j)).1 hsum
        obtain ⟨i, hi⟩ := hall
        exact hi (hall' i (Finset.mem_univ i))
      obtain ⟨j, hj⟩ := hex
      have hne : e (σ j) ≠ e j := ne_of_gt hj
      have hL : (A (σ j) j).coeff (D - e j) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have h3 := hA (σ j) j
        have h4 : e (σ j) ≤ max (e (σ j)) (e j) := le_max_left _ _
        have h5 := he (σ j)
        omega
      have hR : M (σ j) j = 0 := by simp [hM, Matrix.of_apply, hne]
      rw [Finset.prod_eq_zero (f := fun i => (A (σ i) i).coeff (D - e i)) (Finset.mem_univ j) hL,
        Finset.prod_eq_zero (f := fun i => M (σ i) i) (Finset.mem_univ j) hR]
  have hdet : A.det.coeff (∑ i, (D - e i)) = M.det := by
    rw [h2, Matrix.det_apply]
    exact Finset.sum_congr rfl (fun σ _ => by rw [hprod σ])
  refine ⟨h1, hdet, fun hne => ?_⟩
  have hN : A.det.natDegree = ∑ i, (D - e i) :=
    le_antisymm h1 (Polynomial.le_natDegree_of_ne_zero (by rw [hdet]; exact hne))
  refine ⟨hN, ?_⟩
  rw [Polynomial.leadingCoeff, hN, hdet]

end Formalism.GM
