import Mathlib

noncomputable def UpperTheory.Reformulated.B.BoxBounds.box :
    {K : Type} → [inst : Field K] → {i : ℕ} → K → Submodule (NumberField.RingOfIntegers K) (Fin i → K) :=
    fun {K : Type} [Field K] {i : ℕ} (c : K) ↦ Submodule.pi Set.univ fun (x : Fin i) ↦ NumberField.RingOfIntegers K ∙ c

/- English proof (translation)
Introduce `K _ _ i L hL`. Establish `h : ∀ j : Fin i, ∃ t : nonZeroDivisors (NumberField.RingOfIntegers K), (t : NumberField.RingOfIntegers K) • (Pi.single j (1 : K) : Fin i → K) ∈ L`. Introduce `j`. Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (NumberField.RingOfIntegers K)) K (↑L : Set (Fin i → K)) (Pi.single j (1 : K)) (hL ▸ Submodule.mem_top)`. Rewrite `ht` using `[Submodule.span_eq]`.

Conclude with `⟨t, ht⟩`. Use `choose t ht using h`. Use `⟨∏ j, (t j : NumberField.RingOfIntegers K), Finset.prod_ne_zero_iff.mpr fun j _ => nonZeroDivisors.coe_ne_zero (t j), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[← Finset.univ_sum_single x]`.

Use `L.sum_mem fun j _ => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.mp (Submodule.mem_pi.mp hx j (Set.mem_univ j))`. Take `⟨u, hu⟩ : (t j : NumberField.RingOfIntegers K) ∣ ∏ k, (t k : NumberField.RingOfIntegers K)` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ j)`. Establish `hj : (Pi.single j (x j) : Fin i → K) = (a * u) • (t j : NumberField.RingOfIntegers K) • (Pi.single j (1 : K) : Fin i → K)`. Rewrite using `[← ha, hu, smul_smul, ← Pi.single_smul, Algebra.algebraMap_eq_smul_one, smul_smul]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hj]`. Conclude with `L.smul_mem _ (ht j)`.
-/
theorem UpperTheory.Reformulated.B.BoxBounds.exists_box_le :
    ∀ {K : Type} [inst : Field K] [NumberField K] {i : ℕ} (L : Submodule (NumberField.RingOfIntegers K) (Fin i → K)),
      Submodule.span K (↑L : Set (Fin i → K)) = ⊤ →
        ∃ (e : NumberField.RingOfIntegers K),
          e ≠ (0 : NumberField.RingOfIntegers K) ∧
            UpperTheory.Reformulated.B.BoxBounds.box
                ((Algebra.algebraMap (NumberField.RingOfIntegers K) K : NumberField.RingOfIntegers K → K) e) ≤
              L := by
  intro K _ _ i L hL
  classical
  have h : ∀ j : Fin i, ∃ t : nonZeroDivisors (NumberField.RingOfIntegers K),
      (t : NumberField.RingOfIntegers K) • (Pi.single j (1 : K) : Fin i → K) ∈ L := by
    intro j
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
      (nonZeroDivisors (NumberField.RingOfIntegers K)) K (↑L : Set (Fin i → K))
      (Pi.single j (1 : K)) (hL ▸ Submodule.mem_top)
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using h
  refine ⟨∏ j, (t j : NumberField.RingOfIntegers K),
    Finset.prod_ne_zero_iff.mpr fun j _ => nonZeroDivisors.coe_ne_zero (t j), ?_⟩
  intro x hx
  rw [← Finset.univ_sum_single x]
  refine L.sum_mem fun j _ => ?_
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_pi.mp hx j (Set.mem_univ j))
  obtain ⟨u, hu⟩ : (t j : NumberField.RingOfIntegers K) ∣ ∏ k, (t k : NumberField.RingOfIntegers K) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have hj : (Pi.single j (x j) : Fin i → K)
      = (a * u) • (t j : NumberField.RingOfIntegers K) • (Pi.single j (1 : K) : Fin i → K) := by
    rw [← ha, hu, smul_smul, ← Pi.single_smul, Algebra.algebraMap_eq_smul_one, smul_smul]
    congr 2
    ring
  rw [hj]
  exact L.smul_mem _ (ht j)
