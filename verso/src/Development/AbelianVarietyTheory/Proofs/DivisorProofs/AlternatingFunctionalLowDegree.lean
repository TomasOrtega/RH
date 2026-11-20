import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
open MvPolynomial GlobalTheory.CovTest GlobalTheory.ArInt GlobalTheory.BlockPoint

namespace GlobalTheory.AltLowDeg

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro S _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `S hS`.

Establish `hne : S.Nonempty` using `Finset.card_pos.1 (by omega)`. Establish `hmem` using `S.max'_mem hne`. Establish `hM : n ≤ S.max' hne`. Establish `hsub : S ⊆ Finset.range (S.max' hne + 1)` using `fun x hx => Finset.mem_range.2 (Nat.lt_succ_of_le (S.le_max' x hx))`. Use `Finset.card_le_card hsub` as an intermediate fact.

Simplify using `only [Finset.card_range] at this`. Use linear arithmetic over natural numbers and integers. Establish `hc : (S.erase (S.max' hne)).card = n`. Rewrite using `[Finset.card_erase_of_mem hmem]`. Use linear arithmetic over natural numbers and integers.

Use `ih _ hc` as an intermediate fact. Rewrite using `[Finset.sum_range_succ, ← Finset.add_sum_erase S _ hmem]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_range_le_sum_of_card (n : ℕ) : ∀ S : Finset ℕ, S.card = n → ∑ i ∈ Finset.range n, i ≤ ∑ s ∈ S, s := by
  induction n with
  | zero => intro S _; simp
  | succ n ih =>
    intro S hS
    have hne : S.Nonempty := Finset.card_pos.1 (by omega)
    have hmem := S.max'_mem hne
    have hM : n ≤ S.max' hne := by
      have hsub : S ⊆ Finset.range (S.max' hne + 1) := fun x hx =>
        Finset.mem_range.2 (Nat.lt_succ_of_le (S.le_max' x hx))
      have := Finset.card_le_card hsub
      simp only [Finset.card_range] at this
      omega
    have hc : (S.erase (S.max' hne)).card = n := by
      rw [Finset.card_erase_of_mem hmem]; omega
    have := ih _ hc
    rw [Finset.sum_range_succ, ← Finset.add_sum_erase S _ hmem]
    omega

/- English proof (translation)
Establish `h` using `sum_range_le_sum_of_card n (Finset.univ.image f) (by rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin])`. Rewrite `h` using `[Finset.sum_image (fun x _ y _ h => hf h)]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => i) n]` and apply the resulting hypothesis.
-/
theorem sum_fin_le_sum_of_injective {n : ℕ} {f : Fin n → ℕ} (hf : Function.Injective f) :
    ∑ i : Fin n, (i : ℕ) ≤ ∑ i, f i := by
  have h := sum_range_le_sum_of_card n (Finset.univ.image f)
    (by rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin])
  rw [Finset.sum_image (fun x _ y _ h => hf h)] at h
  rwa [Fin.sum_univ_eq_sum_range (fun i => i) n]

/- English proof (translation)
Establish `h1 : MvPolynomial.rename (Equiv.swap i j) (monomial α c) = monomial α c`. Establish `hα : Finsupp.mapDomain (Equiv.swap i j) α = α`. Use extensionality with `k`. Rewrite using `[Finsupp.mapDomain_equiv_apply, Equiv.symm_swap]`. Break down `eq_or_ne k i with rfl | hki` into its components or cases.

Rewrite using `[Equiv.swap_apply_left, he]`. Break down `eq_or_ne k j with rfl | hkj` into its components or cases. Rewrite using `[Equiv.swap_apply_right, he]`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne hki hkj]`. Rewrite using `[rename_monomial, hα]`.

Establish `h2` using `hψ (Equiv.swap i j) (monomial α c)`. Rewrite `h2` using `[h1, Equiv.Perm.sign_swap hij]`. Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem alt_monomial_eq_zero {n : ℕ} (ψ : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ)
    (hψ : ∀ (σ : Equiv.Perm (Fin n)) (P : MvPolynomial (Fin n) ℝ),
      ψ (MvPolynomial.rename σ P) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ψ P)
    (α : Fin n →₀ ℕ) (c : ℝ) {i j : Fin n} (hij : i ≠ j) (he : α i = α j) :
    ψ (monomial α c) = 0 := by
  have h1 : MvPolynomial.rename (Equiv.swap i j) (monomial α c) = monomial α c := by
    have hα : Finsupp.mapDomain (Equiv.swap i j) α = α := by
      ext k
      rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap]
      rcases eq_or_ne k i with rfl | hki
      · rw [Equiv.swap_apply_left, he]
      rcases eq_or_ne k j with rfl | hkj
      · rw [Equiv.swap_apply_right, he]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    rw [rename_monomial, hα]
  have h2 := hψ (Equiv.swap i j) (monomial α c)
  rw [h1, Equiv.Perm.sign_swap hij] at h2
  push_cast at h2
  linarith

/- English proof (translation)
Rewrite using `[P.as_sum, map_sum]`. Use `Finset.sum_eq_zero fun α hα => ?_` and prove the remaining obligations. Distinguish the cases in `h : ∃ i j, i ≠ j ∧ α i = α j`. Take `⟨i, j, hij, he⟩` from `h`. Conclude with `alt_monomial_eq_zero ψ hψ α _ hij he`.

Use `exfalso push_neg at h`. Establish `hinj : Function.Injective (α : Fin n → ℕ)` using `fun i j e => by`. Assume the negation of the conclusion as `hne`. Conclude with `h i j hne e`. Establish `hw` using `hP (mem_support_iff.1 hα)`.

Establish `hdeg : ∑ i, α i = d`. Rewrite using `[← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]`. Conclude with `hw`. Use `sum_fin_le_sum_of_injective hinj` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem alt_eq_zero_of_lt (n : ℕ) (ψ : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ)
    (hψ : ∀ (σ : Equiv.Perm (Fin n)) (P : MvPolynomial (Fin n) ℝ),
      ψ (MvPolynomial.rename σ P) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ψ P)
    (P : MvPolynomial (Fin n) ℝ) (d : ℕ) (hP : P.IsHomogeneous d) (hd : d < ∑ i : Fin n, (i : ℕ)) :
    ψ P = 0 := by
  rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun α hα => ?_
  by_cases h : ∃ i j, i ≠ j ∧ α i = α j
  · obtain ⟨i, j, hij, he⟩ := h
    exact alt_monomial_eq_zero ψ hψ α _ hij he
  · exfalso
    push_neg at h
    have hinj : Function.Injective (α : Fin n → ℕ) := fun i j e => by
      by_contra hne; exact h i j hne e
    have hw := hP (mem_support_iff.1 hα)
    have hdeg : ∑ i, α i = d := by
      rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]; exact hw
    have := sum_fin_le_sum_of_injective hinj
    omega

end GlobalTheory.AltLowDeg
