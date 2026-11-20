import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear

noncomputable section

open Formalism.BasicNotions GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[tor_coe]`. Conclude with `Matrix.diagonal_apply_ne _ (ne_of_gt hij)`.
-/
private theorem tor_isUp (a k : ℕ) (z : Circle) : IsUp (tor a k z) := by
  intro i j hij
  rw [tor_coe]
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)

/- English proof (translation)
Rewrite using `[← Complex.normSq_eq_conj_mul_self]`. Simplify using the standard rewrite rules.
-/
private theorem circ_mul_conj (z : Circle) : (starRingEnd ℂ) (z : ℂ) * (z : ℂ) = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

/- English proof (translation)
Use `set d : Fin a → ℂ := fun i => if (i : ℕ) < k then (z : ℂ) else 1 with hd`. Establish `hdd : ∀ i, d i * (starRingEnd ℂ) (d i) = 1`. Introduce `i`. Simplify using `only [hd]`. Use `split_ifs`.

Rewrite using `[mul_comm]`. Conclude with `circ_mul_conj z`. Simplify using the standard rewrite rules. Establish `hmem : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin a) ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]`.

Rewrite using `[← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hdd i`. Use `⟨⟨Matrix.diagonal d, hmem⟩, ?_⟩` and prove the remaining obligations.

Use extensionality with `: 1`. Rewrite using `[unitaryIncl_coe, tor_coe]`.
-/
private theorem tor_unitary (a k : ℕ) (z : Circle) :
    ∃ u : Matrix.unitaryGroup (Fin a) ℂ, unitaryIncl a u = tor a k z := by
  set d : Fin a → ℂ := fun i => if (i : ℕ) < k then (z : ℂ) else 1 with hd
  have hdd : ∀ i, d i * (starRingEnd ℂ) (d i) = 1 := by
    intro i
    simp only [hd]
    split_ifs
    · rw [mul_comm]
      exact circ_mul_conj z
    · simp
  have hmem : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact hdd i
  refine ⟨⟨Matrix.diagonal d, hmem⟩, ?_⟩
  ext : 1
  rw [unitaryIncl_coe, tor_coe]

/- English proof (translation)
Establish `hz : (z : ℂ) ≠ 0` using `by simp`. Simplify using `only [chi, psum, tor_coe, Matrix.diagonal_apply_eq]`. Rewrite using `[Finset.sum_filter]`. Establish `key : ∀ s : Finset (Fin a), ∏ i ∈ s, (if (i : ℕ) < k then (z : ℂ) else 1) ^ κ.w i = (z : ℂ) ^ ∑ i ∈ s, (if (i : ℕ) < k then κ.w i else 0)`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hz]`. Apply the tactic sequence `split_ifs <;> simp`.

Conclude with `key _`.
-/
private theorem tor_chi {a : ℕ} (k : ℕ) (z : Circle) (κ : DomWeight a) :
    chi κ (tor a k z) = (z : ℂ) ^ psum κ k := by
  have hz : (z : ℂ) ≠ 0 := by simp
  simp only [chi, psum, tor_coe, Matrix.diagonal_apply_eq]
  rw [Finset.sum_filter]
  have key : ∀ s : Finset (Fin a), ∏ i ∈ s, (if (i : ℕ) < k then (z : ℂ) else 1) ^ κ.w i =
      (z : ℂ) ^ ∑ i ∈ s, (if (i : ℕ) < k then κ.w i else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hz]
      split_ifs <;> simp
  exact key _

/- English proof (translation)
Establish `hinv : (starRingEnd ℂ) (z : ℂ) = ((z⁻¹ : Circle) : ℂ)`. Rewrite using `[Circle.coe_inv]`. Conclude with `eq_inv_of_mul_eq_one_left (circ_mul_conj z)`. Use extensionality with `i j`. Simplify using `only [Matrix.GeneralLinearGroup.map_apply, tor_coe, Matrix.map_apply, Matrix.diagonal_apply]`.

Apply the tactic sequence `split_ifs <;> simp [hinv]`.
-/
private theorem tor_conj (a k : ℕ) (z : Circle) :
    Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (tor a k z) = tor a k z⁻¹ := by
  have hinv : (starRingEnd ℂ) (z : ℂ) = ((z⁻¹ : Circle) : ℂ) := by
    rw [Circle.coe_inv]
    exact eq_inv_of_mul_eq_one_left (circ_mul_conj z)
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, tor_coe, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [hinv]

/- English proof (translation)
Introduce `a k z` and use `⟨tor_isUp a k z, tor_unitary a k z, fun κ => tor_chi k z κ, tor_conj a k z⟩`.
-/
theorem torFacts_of : TorFacts := fun a k z =>
  ⟨tor_isUp a k z, tor_unitary a k z, fun κ => tor_chi k z κ, tor_conj a k z⟩

end UpperTheory.Gal.Wt

end
