import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simp [AddMonoidAlgebra.one_def]`. Consider the case `insert i T hi ih`. Rewrite using `[Finset.prod_insert hi, ih, AddMonoidAlgebra.single_mul_single, Finset.sum_insert hi, Finset.prod_insert hi]`.
-/
private theorem prod_single_eq_single_sum {k A ι : Type} [CommRing k] [AddCommGroup A] [DecidableEq ι]
    (T : Finset ι) (f : ι → A) (c : k) :
    ∏ j ∈ T, (AddMonoidAlgebra.single (f j) c : AddMonoidAlgebra k A)
      = AddMonoidAlgebra.single (∑ j ∈ T, f j) (∏ _j ∈ T, c) := by
  induction T using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert i T hi ih =>
    rw [Finset.prod_insert hi, ih, AddMonoidAlgebra.single_mul_single, Finset.sum_insert hi,
      Finset.prod_insert hi]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `h` to reduce the goal to its premises. Rewrite using `[AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]`. Conclude with `Finset.sum_eq_zero hc`.
-/
private theorem coeff_monic_poly_sum {k A ι : Type} [CommRing k] [AddCommGroup A]
    (T : Finset ι) (f : ι → AddMonoidAlgebra k A) (a : A) (h : (∑ j ∈ T, f j).coeff a ≠ 0) :
    ∃ j ∈ T, (f j).coeff a ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  exact Finset.sum_eq_zero hc

/- English proof (translation)
Introduce `A ι _ _ _ η N`. Use `⟨(Finset.univ ×ˢ (Finset.range N ×ˢ (Finset.univ : Finset ι).powerset)).image (fun p : ι × ℕ × Finset ι => p.2.1 • η p.1 + ∑ j ∈ p.2.2, N • η j), ?_⟩` and prove the remaining obligations. Introduce `k _ P a ha`. Simplify using `only [sinE] at ha`. Take `⟨i, -, hi⟩` from `coeff_monic_poly_sum _ _ a ha`.

Establish `hprod : ∏ j ∈ Finset.univ.erase i, (1 - AddMonoidAlgebra.single (N • η j) (1 : k)) = ∑ t ∈ (Finset.univ.erase i).powerset, AddMonoidAlgebra.single (∑ j ∈ t, N • η j) (∏ _j ∈ t, (-1 : k))`. Establish `e : ∀ j, (1 - AddMonoidAlgebra.single (N • η j) (1 : k)) = AddMonoidAlgebra.single (N • η j) (-1 : k) + 1`. Introduce `j`. Rewrite using `[AddMonoidAlgebra.single_neg]`. Normalize the expressions using the abelian group laws.

Repeatedly rewrite using `[e]`. Rewrite using `[Finset.prod_add]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `t _`. Rewrite using `[Finset.prod_const_one, mul_one, prod_single_eq_single_sum]`.

Rewrite `hi` using `[hprod, Finset.sum_mul]`. Take `⟨s, hs, hs2⟩` from `coeff_monic_poly_sum _ _ a hi`. Rewrite `hs2` using `[Finset.mul_sum]`. Take `⟨t, ht, ht2⟩` from `coeff_monic_poly_sum _ _ a hs2`. Rewrite `ht2` using `[AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single_apply]`.

Use `split_ifs at ht2 with hEq`. Rewrite using `[Finset.mem_image]`. Use `⟨(i, s, t), ?_, hEq⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_product, Finset.mem_univ, Finset.mem_powerset, true_and]`. Conclude with `⟨hs, Finset.subset_univ _⟩`.

Conclude with `absurd rfl ht2`.
-/
theorem UpperTheory.V.FW.sinSupp :
    ∀ (A ι : Type) [AddCommGroup A] [Fintype ι] [DecidableEq ι] (η : ι → A) (N : ℕ), ∃ S : Finset A, ∀ (k : Type) [CommRing k] (P : ℕ → k) (a : A), (sinE η N P).coeff a ≠ 0 → a ∈ S := by
  intro A ι _ _ _ η N
  classical
  refine ⟨(Finset.univ ×ˢ (Finset.range N ×ˢ (Finset.univ : Finset ι).powerset)).image
    (fun p : ι × ℕ × Finset ι => p.2.1 • η p.1 + ∑ j ∈ p.2.2, N • η j), ?_⟩
  intro k _ P a ha
  simp only [sinE] at ha
  obtain ⟨i, -, hi⟩ := coeff_monic_poly_sum _ _ a ha
  have hprod : ∏ j ∈ Finset.univ.erase i, (1 - AddMonoidAlgebra.single (N • η j) (1 : k))
      = ∑ t ∈ (Finset.univ.erase i).powerset,
          AddMonoidAlgebra.single (∑ j ∈ t, N • η j) (∏ _j ∈ t, (-1 : k)) := by
    have e : ∀ j, (1 - AddMonoidAlgebra.single (N • η j) (1 : k))
        = AddMonoidAlgebra.single (N • η j) (-1 : k) + 1 := by
      intro j
      rw [AddMonoidAlgebra.single_neg]
      abel
    simp_rw [e]
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.prod_const_one, mul_one, prod_single_eq_single_sum]
  rw [hprod, Finset.sum_mul] at hi
  obtain ⟨s, hs, hs2⟩ := coeff_monic_poly_sum _ _ a hi
  rw [Finset.mul_sum] at hs2
  obtain ⟨t, ht, ht2⟩ := coeff_monic_poly_sum _ _ a hs2
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single_apply] at ht2
  split_ifs at ht2 with hEq
  · rw [Finset.mem_image]
    refine ⟨(i, s, t), ?_, hEq⟩
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_powerset, true_and]
    exact ⟨hs, Finset.subset_univ _⟩
  · exact absurd rfl ht2
