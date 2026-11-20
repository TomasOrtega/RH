import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.BinomLeft

variable {R : Type} [CommRing R] {d : ℕ}

/- English proof (translation)
Rewrite using `[monomial_zero_eq_C_apply, map_natCast]`.
-/
theorem natCast_eq_monomial {σ : Type} (n : ℕ) : ((n : ℕ) : MvPowerSeries σ R) = monomial 0 (n : R) := by
  rw [monomial_zero_eq_C_apply, map_natCast]

/- English proof (translation)
Rewrite using `[add_pow]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [x1, x2, X_pow_eq, monomial_mul_monomial, one_mul, natCast_eq_monomial, add_zero, mul_one]`.
-/
theorem pow_threeGroupsFirst_add_second_expansion (i : Fin d) (k : ℕ) :
    ((x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) ^ k =
      ∑ j ∈ Finset.range (k + 1),
        monomial (Finsupp.single (Sum.inl i) j + Finsupp.single (Sum.inr (Sum.inl i)) (k - j)) (k.choose j : R) := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [x1, x2, X_pow_eq, monomial_mul_monomial, one_mul, natCast_eq_monomial, add_zero, mul_one]

/- English proof (translation)
Establish `hv : ∀ s, ((∑ i, (Finsupp.single (Sum.inl i) (p i) + Finsupp.single (Sum.inr (Sum.inl i)) (α (Sum.inl i) - p i))) + ∑ i, Finsupp.single (Sum.inr (Sum.inr i)) (α (Sum.inr i)) : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ) s = Sum.elim p (Sum.elim (fun i => α (Sum.inl i) - p i) (fun i => α (Sum.i …`. Introduce `s`. Break down `s with i | i | i` into its components or cases. Simplify using `[Finsupp.finsetSum_apply, Finsupp.single_apply]`. Simplify using `only [Finsupp.coe_add, Pi.add_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]`.

Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by simp [hj, Ne.symm hj]) (by simp)]`. Simplify using the standard rewrite rules. Simplify using `[Finsupp.finsetSum_apply, Finsupp.single_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h1 : ∀ i, a i = p i` using `fun i => by`. Use `DFunLike.congr_fun h (Sum.inl i)` as an intermediate fact. Rewrite `this` using `[hv]`. Simplify using `using this`. Establish `h2 : ∀ i, b i = α (Sum.inl i) - p i` using `fun i => by`.

Use `DFunLike.congr_fun h (Sum.inr (Sum.inl i))` as an intermediate fact. Rewrite `this` using `[hv]`. Simplify using `using this`. Establish `h3 : ∀ i, e i = α (Sum.inr i)` using `fun i => by`. Use `DFunLike.congr_fun h (Sum.inr (Sum.inr i))` as an intermediate fact.

Rewrite `this` using `[hv]`. Simplify using `using this`. Use `⟨?_, funext fun i => (h1 i).symm⟩` and prove the remaining obligations. Use extensionality with `s`. Break down `s with i | i` into its components or cases.

Use `hp i` as an intermediate fact. Use `h1 i` as an intermediate fact. Use `h2 i` as an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Simplify using `[h3 i]`. Introduce and unpack `⟨rfl, rfl⟩`. Use extensionality with `s`. Rewrite using `[hv]`. Apply the tactic sequence `rcases s with i | i | i <;> simp`.
-/
theorem expo_iff (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ) (p : Fin d → ℕ)
    (hp : ∀ i, p i ≤ α (Sum.inl i)) :
    Finsupp.sumElim a (Finsupp.sumElim b e) =
        (∑ i, (Finsupp.single (Sum.inl i) (p i) + Finsupp.single (Sum.inr (Sum.inl i)) (α (Sum.inl i) - p i))) +
          ∑ i, Finsupp.single (Sum.inr (Sum.inr i)) (α (Sum.inr i)) ↔
      α = Finsupp.sumElim (a + b) e ∧ p = ⇑a := by
  classical
  have hv : ∀ s, ((∑ i, (Finsupp.single (Sum.inl i) (p i) + Finsupp.single (Sum.inr (Sum.inl i)) (α (Sum.inl i) - p i))) +
          ∑ i, Finsupp.single (Sum.inr (Sum.inr i)) (α (Sum.inr i)) : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ) s =
        Sum.elim p (Sum.elim (fun i => α (Sum.inl i) - p i) (fun i => α (Sum.inr i))) s := by
    intro s
    rcases s with i | i | i
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj, Ne.symm hj]) (by simp)]
      simp
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  constructor
  · intro h
    have h1 : ∀ i, a i = p i := fun i => by
      have := DFunLike.congr_fun h (Sum.inl i); rw [hv] at this; simpa using this
    have h2 : ∀ i, b i = α (Sum.inl i) - p i := fun i => by
      have := DFunLike.congr_fun h (Sum.inr (Sum.inl i)); rw [hv] at this; simpa using this
    have h3 : ∀ i, e i = α (Sum.inr i) := fun i => by
      have := DFunLike.congr_fun h (Sum.inr (Sum.inr i)); rw [hv] at this; simpa using this
    refine ⟨?_, funext fun i => (h1 i).symm⟩
    ext s
    rcases s with i | i
    · have := hp i; have := h1 i; have := h2 i; simp; omega
    · simp [h3 i]
  · rintro ⟨rfl, rfl⟩
    ext s
    rw [hv]
    rcases s with i | i | i <;> simp

/- English proof (translation)
Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, pow_threeGroupsFirst_add_second_expansion]`. Rewrite using `[Finset.prod_univ_sum]`. Simplify using `only [x3, X_pow_eq, prod_monomial, Finset.sum_mul, monomial_mul_monomial, mul_one, map_sum, coeff_monomial, Finset.prod_const_one]`. Establish `hmem : ∀ p ∈ Fintype.piFinset fun i => Finset.range (α (Sum.inl i) + 1), ∀ i, p i ≤ α (Sum.inl i)`.

Introduce `p hp i`. Use `Fintype.mem_piFinset.1 hp i` as an intermediate fact. Rewrite `this` using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Use `split_ifs with hα`.

Rewrite using `[Finset.sum_congr rfl fun p hp => by rw [if_congr (expo_iff α a b e p (hmem p hp)) rfl rfl]]`. Simplify using `only [hα, true_and]`. Rewrite using `[Finset.sum_ite_eq']`. Rewrite using `[if_pos]`. Simplify using the standard rewrite rules.

Rewrite using `[Fintype.mem_piFinset]`. Introduce `i`. Simplify using `only [Finset.mem_range, Finsupp.sumElim_apply, Sum.elim_inl, Finsupp.coe_add, Pi.add_apply]`. Use linear arithmetic over natural numbers and integers. Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations.

Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hα ((expo_iff α a b e p (hmem p hp)).1 h).1`.
-/
theorem coeff_prod_pow_add (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e))
        (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) =
      if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := by
  classical
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, pow_threeGroupsFirst_add_second_expansion]
  rw [Finset.prod_univ_sum]
  simp only [x3, X_pow_eq, prod_monomial, Finset.sum_mul, monomial_mul_monomial, mul_one, map_sum,
    coeff_monomial, Finset.prod_const_one]
  have hmem : ∀ p ∈ Fintype.piFinset fun i => Finset.range (α (Sum.inl i) + 1), ∀ i, p i ≤ α (Sum.inl i) := by
    intro p hp i
    have := Fintype.mem_piFinset.1 hp i
    rw [Finset.mem_range] at this
    omega
  split_ifs with hα
  · rw [Finset.sum_congr rfl fun p hp => by rw [if_congr (expo_iff α a b e p (hmem p hp)) rfl rfl]]
    simp only [hα, true_and]
    rw [Finset.sum_ite_eq']
    rw [if_pos]
    · simp
    · rw [Fintype.mem_piFinset]
      intro i
      simp only [Finset.mem_range, Finsupp.sumElim_apply, Sum.elim_inl, Finsupp.coe_add, Pi.add_apply]
      omega
  · refine Finset.sum_eq_zero fun p hp => ?_
    rw [if_neg]
    intro h
    exact hα ((expo_iff α a b e p (hmem p hp)).1 h).1

end GlobalTheory.BinomLeft
