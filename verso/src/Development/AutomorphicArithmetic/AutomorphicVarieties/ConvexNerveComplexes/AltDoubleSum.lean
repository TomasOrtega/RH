import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed

open Set UpperTheory.V.ConeExtensionAcyclic

/- English proof (translation)
Distinguish the cases in `h : (j : ℕ) < i`. Establish `h' : j.castSucc < i`. Rewrite using `[Fin.lt_def, Fin.coe_castSucc]`. Conclude with `h`. Rewrite using `[Fin.succAbove_of_castSucc_lt _ _ h', Fin.predAbove_of_castSucc_lt _ _ h']`.

Simplify using `[h]`. Establish `h' : i ≤ j.castSucc`. Rewrite using `[Fin.le_def, Fin.coe_castSucc]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Fin.succAbove_of_le_castSucc _ _ h', Fin.predAbove_of_le_castSucc _ _ h']`.

Simplify using `[h]`.
-/
private theorem UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    ((i.succAbove j : ℕ) = if (j : ℕ) < i then (j : ℕ) else j + 1) ∧
      ((j.predAbove i : ℕ) = if (j : ℕ) < i then (i : ℕ) - 1 else i) := by
  by_cases h : (j : ℕ) < i
  · have h' : j.castSucc < i := by
      rw [Fin.lt_def, Fin.coe_castSucc]
      exact h
    rw [Fin.succAbove_of_castSucc_lt _ _ h', Fin.predAbove_of_castSucc_lt _ _ h']
    simp [h]
  · have h' : i ≤ j.castSucc := by
      rw [Fin.le_def, Fin.coe_castSucc]
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ h', Fin.predAbove_of_le_castSucc _ _ h']
    simp [h]

/- English proof (translation)
Set `φ : Fin (n + 2) × Fin (n + 1) → Fin (n + 2) × Fin (n + 1)` to `fun p => (p.1.succAbove p.2, p.2.predAbove p.1)`. Establish `hinv : ∀ p, φ (φ p) = p`. Introduce and unpack `⟨i, j⟩`. Take `⟨h1, h2⟩` from `UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val n i j`. Take `⟨h3, h4⟩` from `UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val n (i.succAbove j) (j.predAbove i)`.

Simplify using `only [φ, Prod.mk.injEq, Fin.ext_iff]`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Apply the tactic sequence `split_ifs at h1 h2 h3 h4 <;> omega`. Establish `hsign : ∀ p : Fin (n + 2) × Fin (n + 1), ((-1 : ℤ) ^ (((φ p).1 : ℕ) + ((φ p).2 : ℕ))) = -((-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)))`.

Introduce and unpack `⟨i, j⟩`. Take `⟨h1, h2⟩` from `UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val n i j`. Simplify using `only [φ]`. Rewrite using `[h1, h2]`. Use `split_ifs with h`.

Establish `e : (j : ℕ) + ((i : ℕ) - 1) + 1 = (i : ℕ) + j` using `by omega`. Rewrite using `[← neg_one_mul ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))), ← e, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[show (j : ℕ) + 1 + i = (i : ℕ) + j + 1 by omega, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Set `e : Fin (n + 2) × Fin (n + 1) ≃ Fin (n + 2) × Fin (n + 1)` to `{ toFun := φ, invFun := φ, left_inv := hinv, right_inv := hinv }`. Use `set S := ∑ i : Fin (n + 2), ∑ j : Fin (n + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) • f i j with hS`. Establish `hneg : S = -S`. Rewrite using `[hS, ← Finset.sum_neg_distrib]`. Simplify using `only [← Finset.sum_neg_distrib]`.

Rewrite using `[← Fintype.sum_prod_type', ← Fintype.sum_prod_type']`. Use `Fintype.sum_equiv e _ _ ?_` and prove the remaining obligations. Introduce `p`. Use `show _ = -(((-1 : ℤ) ^ (((φ p).1 : ℕ) + ((φ p).2 : ℕ))) • f (φ p).1 (φ p).2)`. Rewrite using `[hsign p]`.

Establish `hfp : f (φ p).1 (φ p).2 = f p.1 p.2` using `hf p.1 p.2`. Rewrite using `[hfp, neg_smul, neg_neg]`. Establish `h2 : (2 : ℕ) • S = (2 : ℕ) • (0 : M)`. Rewrite using `[two_nsmul, smul_zero]`. Use `nth_rewrite 1 [hneg]`.

Conclude with `neg_add_cancel S`. Conclude with `nsmul_right_injective (by norm_num) h2`.
-/
private theorem UpperTheory.V.ConeExtensionAcyclic.alt_double_sum {M : Type*} [AddCommGroup M] [IsAddTorsionFree M]
    (n : ℕ) (f : Fin (n + 2) → Fin (n + 1) → M)
    (hf : ∀ i j, f (i.succAbove j) (j.predAbove i) = f i j) :
    ∑ i : Fin (n + 2), ∑ j : Fin (n + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) • f i j = 0 := by
  let φ : Fin (n + 2) × Fin (n + 1) → Fin (n + 2) × Fin (n + 1) :=
    fun p => (p.1.succAbove p.2, p.2.predAbove p.1)
  have hinv : ∀ p, φ (φ p) = p := by
    rintro ⟨i, j⟩
    obtain ⟨h1, h2⟩ := UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val n i j
    obtain ⟨h3, h4⟩ := UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val n (i.succAbove j) (j.predAbove i)
    simp only [φ, Prod.mk.injEq, Fin.ext_iff]
    have hi := i.isLt
    have hj := j.isLt
    split_ifs at h1 h2 h3 h4 <;> omega
  have hsign : ∀ p : Fin (n + 2) × Fin (n + 1),
      ((-1 : ℤ) ^ (((φ p).1 : ℕ) + ((φ p).2 : ℕ))) = -((-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ))) := by
    rintro ⟨i, j⟩
    obtain ⟨h1, h2⟩ := UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val n i j
    simp only [φ]
    rw [h1, h2]
    split_ifs with h
    · have e : (j : ℕ) + ((i : ℕ) - 1) + 1 = (i : ℕ) + j := by omega
      rw [← neg_one_mul ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))), ← e, pow_succ]
      ring
    · rw [show (j : ℕ) + 1 + i = (i : ℕ) + j + 1 by omega, pow_succ]
      ring
  let e : Fin (n + 2) × Fin (n + 1) ≃ Fin (n + 2) × Fin (n + 1) :=
    { toFun := φ, invFun := φ, left_inv := hinv, right_inv := hinv }
  set S := ∑ i : Fin (n + 2), ∑ j : Fin (n + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) • f i j with hS
  have hneg : S = -S := by
    rw [hS, ← Finset.sum_neg_distrib]
    simp only [← Finset.sum_neg_distrib]
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv e _ _ ?_
    intro p
    show _ = -(((-1 : ℤ) ^ (((φ p).1 : ℕ) + ((φ p).2 : ℕ))) • f (φ p).1 (φ p).2)
    rw [hsign p]
    have hfp : f (φ p).1 (φ p).2 = f p.1 p.2 := hf p.1 p.2
    rw [hfp, neg_smul, neg_neg]
  have h2 : (2 : ℕ) • S = (2 : ℕ) • (0 : M) := by
    rw [two_nsmul, smul_zero]
    nth_rewrite 1 [hneg]
    exact neg_add_cancel S
  exact nsmul_right_injective (by norm_num) h2

/- English proof (translation)
Introduce `I n c`. Establish `hlin : (bd I n).comp (bd I (n + 1)) = 0`. Apply `Finsupp.lhom_ext` to reduce the goal to its premises. Introduce `t a`. Simplify using `only [LinearMap.comp_apply, LinearMap.zero_apply, bd, Finsupp.linearCombination_single, map_smul, map_sum, one_smul, smul_smul, Finset.smul_sum]`.

Establish `hterm : ∀ (i : Fin (n + 2)) (j : Fin (n + 1)), (a * (-1) ^ (i : ℕ) * (1 * (-1) ^ (j : ℕ))) • (Finsupp.single ((t ∘ i.succAbove) ∘ j.succAbove) (1 : ℤ)) = a • (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) • Finsupp.single ((t ∘ i.succAbove) ∘ j.succAbove) (1 : ℤ))`. Introduce `i j`. Rewrite using `[smul_smul, pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hterm, ← Finset.smul_sum]`. Rewrite using `[UpperTheory.V.ConeExtensionAcyclic.alt_double_sum n (fun i j => Finsupp.single ((t ∘ i.succAbove) ∘ j.succAbove) (1 : ℤ)), smul_zero]`. Introduce `i j`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Simplify using `only [Function.comp_apply]`. Rewrite using `[Fin.succAbove_succAbove_succAbove_predAbove]`. Conclude with `LinearMap.congr_fun hlin c`.
-/
theorem UpperTheory.V.ConeExtensionAcyclic.bd_bd :
    ∀ (I : Type) (n : ℕ) (c : Ch I (n + 2)), bd I n (bd I (n + 1) c) = 0 := by
  intro I n c
  have hlin : (bd I n).comp (bd I (n + 1)) = 0 := by
    apply Finsupp.lhom_ext
    intro t a
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, bd, Finsupp.linearCombination_single,
      map_smul, map_sum, one_smul, smul_smul, Finset.smul_sum]
    have hterm : ∀ (i : Fin (n + 2)) (j : Fin (n + 1)),
        (a * (-1) ^ (i : ℕ) * (1 * (-1) ^ (j : ℕ))) •
            (Finsupp.single ((t ∘ i.succAbove) ∘ j.succAbove) (1 : ℤ)) =
          a • (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
            Finsupp.single ((t ∘ i.succAbove) ∘ j.succAbove) (1 : ℤ)) := by
      intro i j
      rw [smul_smul, pow_add]
      congr 1
      ring
    simp only [hterm, ← Finset.smul_sum]
    rw [UpperTheory.V.ConeExtensionAcyclic.alt_double_sum n (fun i j => Finsupp.single ((t ∘ i.succAbove) ∘ j.succAbove) (1 : ℤ)), smul_zero]
    intro i j
    congr 1
    funext k
    simp only [Function.comp_apply]
    rw [Fin.succAbove_succAbove_succAbove_predAbove]
  exact LinearMap.congr_fun hlin c
