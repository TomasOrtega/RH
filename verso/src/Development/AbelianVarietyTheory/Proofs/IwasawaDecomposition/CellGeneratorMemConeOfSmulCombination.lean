import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

/- English proof (translation)
Introduce `O _ bar φ X _ _ _ m m' δ γ i k a hδ hγ hk he j hj`. Take `⟨N, ℓ, hN, h1, h2, h3⟩` from `hδ.strict`. Establish `eδ : φ.evalZ (k • δ i) = k * φ.evalZ (δ i)`. Use `hδ.linear (Pi.single i (k : ℝ)) fun l => by` as an intermediate fact. Distinguish the cases in `h : l = i`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`. Simplify using `only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`. Rewrite using `[InvFun.evalZ]`.

Use `this using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x y`. Simplify using the standard rewrite rules. Establish `eγ : φ.evalZ (∑ j, a j • γ j) = ∑ j, (a j : ℝ) * φ.evalZ (γ j)`. Use `hγ.linear (fun j => (a j : ℝ)) fun j => by positivity` as an intermediate fact.

Rewrite using `[InvFun.evalZ]`. Use `this using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x y`. Simplify using `[LinearMap.sum_apply]`. Establish `ℓδ : (ℓ (k • δ i) : ℝ) = k * (N * φ.evalZ (δ i))`.

Rewrite using `[map_nsmul, ← h1 i, nsmul_eq_mul]`. Use `push_cast`. Both sides reduce to the same expression. Establish `ℓγ : (ℓ (∑ j, a j • γ j) : ℝ) = ∑ j, (a j : ℝ) * ℓ (γ j)`. Rewrite using `[map_sum]`.

Use `push_cast`. Simplify using `[map_nsmul]`. Establish `key : ∑ j, (a j : ℝ) * ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j)) = 0`. Establish `e1 : (ℓ (∑ j, a j • γ j) : ℝ) = N * φ.evalZ (∑ j, a j • γ j)`. Rewrite using `[← he, ℓδ, eδ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `e1` using `[ℓγ, eγ, Finset.mul_sum]`. Simplify using `only [mul_sub, Finset.sum_sub_distrib, e1]`. Rewrite using `[sub_eq_zero]`. Use `Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.

Establish `nn : ∀ j ∈ Finset.univ, 0 ≤ (a j : ℝ) * ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j))` using `fun j _ => mul_nonneg (by positivity) (sub_nonneg.2 (h2 _ (hγ.mem j) (hγ.nonneg j)))`. Establish `z` using `(Finset.sum_eq_zero_iff_of_nonneg nn).1 key j (Finset.mem_univ _)`. Establish `ha : (a j : ℝ) ≠ 0` using `by exact_mod_cast hj.ne'`. Establish `heq : (N : ℝ) * φ.evalZ (γ j) = ℓ (γ j)`. Use `(mul_eq_zero.1 z).resolve_left ha` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h3 _ (hγ.mem j) (hγ.nonneg j) heq`.
-/
theorem cell_gen_mem_cone_of_smul : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (i : Fin m) (k : ℕ) (a : Fin m' → ℕ), IsCell bar φ δ → IsCell bar φ γ → 0 < k → k • δ i = ∑ j, a j • γ j →
    ∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l := by
  intro O _ bar φ X _ _ _ m m' δ γ i k a hδ hγ hk he j hj
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hδ.strict

  have eδ : φ.evalZ (k • δ i) = k * φ.evalZ (δ i) := by
    have := hδ.linear (Pi.single i (k : ℝ)) fun l => by
      by_cases h : l = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [InvFun.evalZ]
    convert this using 2
    funext x y
    simp
  have eγ : φ.evalZ (∑ j, a j • γ j) = ∑ j, (a j : ℝ) * φ.evalZ (γ j) := by
    have := hγ.linear (fun j => (a j : ℝ)) fun j => by positivity
    rw [InvFun.evalZ]
    convert this using 2
    funext x y
    simp [LinearMap.sum_apply]
  have ℓδ : (ℓ (k • δ i) : ℝ) = k * (N * φ.evalZ (δ i)) := by
    rw [map_nsmul, ← h1 i, nsmul_eq_mul]; push_cast; rfl
  have ℓγ : (ℓ (∑ j, a j • γ j) : ℝ) = ∑ j, (a j : ℝ) * ℓ (γ j) := by
    rw [map_sum]; push_cast; simp [map_nsmul]
  have key : ∑ j, (a j : ℝ) * ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j)) = 0 := by
    have e1 : (ℓ (∑ j, a j • γ j) : ℝ) = N * φ.evalZ (∑ j, a j • γ j) := by
      rw [← he, ℓδ, eδ]; ring
    rw [ℓγ, eγ, Finset.mul_sum] at e1
    simp only [mul_sub, Finset.sum_sub_distrib, e1]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => by ring
  have nn : ∀ j ∈ Finset.univ, 0 ≤ (a j : ℝ) * ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j)) := fun j _ =>
    mul_nonneg (by positivity) (sub_nonneg.2 (h2 _ (hγ.mem j) (hγ.nonneg j)))
  have z := (Finset.sum_eq_zero_iff_of_nonneg nn).1 key j (Finset.mem_univ _)
  have ha : (a j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have heq : (N : ℝ) * φ.evalZ (γ j) = ℓ (γ j) := by
    have := (mul_eq_zero.1 z).resolve_left ha
    linarith
  exact h3 _ (hγ.mem j) (hγ.nonneg j) heq

end GlobalTheory.PolFan
