import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [shear, Matrix.add_apply, Matrix.of_apply]`. Rewrite using `[if_neg, add_zero]`. Introduce and unpack `⟨h1, -⟩`. Conclude with `h (congrArg Sigma.fst h1)`.
-/
theorem shear_apply_of_ne {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {K : Type} [CommRing K] (t : K)
    {σ : ι} (h : σ ≠ τ) : shear τ a b t σ = 1 := by
  ext i k
  simp only [shear, Matrix.add_apply, Matrix.of_apply]
  rw [if_neg, add_zero]
  rintro ⟨h1, -⟩
  exact h (congrArg Sigma.fst h1)

/- English proof (translation)
Establish `e : ∀ k, shear τ a b t τ i k = (1 : Matrix (Fin (m τ)) (Fin (m τ)) K) i k + if i = a ∧ k = b then t else 0`. Introduce `k`. Simplify using `only [shear, Matrix.add_apply, Matrix.of_apply]`. Use `congr 1`. Apply the tactic sequence `by_cases h1 : i = a <;> by_cases h2 : k = b <;> simp [h1, h2]`.

Rewrite using `[Matrix.mul_apply]`. Simplify using `only [e, add_mul, Finset.sum_add_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Apply the tactic sequence `by_cases h1 : i = a <;> simp [h1]`.
-/
theorem shear_self_mul_apply {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {K : Type} [CommRing K] (t : K)
    (A : Matrix (Fin (m τ)) (Fin (m τ)) K) (i c : Fin (m τ)) :
    (shear τ a b t τ * A) i c = A i c + if i = a then t * A b c else 0 := by
  have e : ∀ k, shear τ a b t τ i k = (1 : Matrix (Fin (m τ)) (Fin (m τ)) K) i k + if i = a ∧ k = b then t else 0 := by
    intro k
    simp only [shear, Matrix.add_apply, Matrix.of_apply]
    congr 1
    by_cases h1 : i = a <;> by_cases h2 : k = b <;> simp [h1, h2]
  rw [Matrix.mul_apply]
  simp only [e, add_mul, Finset.sum_add_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h1 : i = a <;> simp [h1]

/- English proof (translation)
Introduce `ι m τ a b hab L K _ _ j t ht C hP`. Establish `hmap : ∀ σ i c, (C.map j) σ i c = j (C σ i c)` using `fun _ _ _ => rfl`. Establish `hL : ∀ σ, shear τ a b t σ * (C.map j) σ = (shear τ a b t * C.map j) σ` using `fun _ => rfl`. Establish `hz : ∀ σ (i c : Fin (m σ)), i < c → (shear τ a b t σ * (C.map j) σ) i c = 0` using `fun σ i c h => by`. Rewrite using `[hL]`.

Conclude with `(hP σ).2.2.2 i c i.isLt h`. Establish `hd : ∀ σ, (shear τ a b t σ * (C.map j) σ).det ≠ 0` using `fun σ => by rw [hL]; exact (hP σ).2.1`. Establish `hdiag : ∀ σ (i : Fin (m σ)), (shear τ a b t σ * (C.map j) σ) i i ≠ 0` using `fun σ i => by`. Establish `hbt : (shear τ a b t σ * (C.map j) σ).BlockTriangular OrderDual.toDual` using `fun p q hpq => hz σ p q (OrderDual.toDual_lt_toDual.1 hpq)`. Use `hd σ` as an intermediate fact.

Rewrite `this` using `[Matrix.det_of_lowerTriangular _ hbt]`. Conclude with `Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ _)`. Establish `hab' : a < b` using `by rw [Fin.lt_def]; omega`. Establish `hba : b ≠ a` using `ne_of_gt hab'`. Use `⟨fun σ hσ => hd σ ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_mul, Mat.det_map, hσ, map_zero, mul_zero]`. Introduce `h0`. Establish `h1` using `hz τ a b hab'`. Establish `h2` using `hdiag τ b`. Rewrite `h1`, `h2` using `[shear_self_mul_apply]`.

Rewrite `h1` using `[if_pos rfl, hmap, h0, map_zero, zero_add]`. Rewrite `h2` using `[if_neg hba, add_zero]`. Conclude with `h2 ((mul_eq_zero.1 h1).resolve_left ht)`. Introduce `σ i c hic hn`. Use `(map_eq_zero j).1 ?_` and prove the remaining obligations.

Rewrite using `[← hmap]`. Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality. Establish `hn' : ¬ (i = a ∧ c = b)` using `fun h => hn ⟨by rw [h.1], by rw [h.2]⟩`. Establish `h1` using `hz σ i c hic`.

Rewrite `h1` using `[shear_self_mul_apply]`. Distinguish the cases in `hi : i = a`. Substitute `hi` using the available equality. Establish `hcb : c ≠ b` using `fun h => hn' ⟨rfl, h⟩`. Establish `hbc : b < c`.

Rewrite `hic`, the goal using `[Fin.lt_def]`. Establish `: (c : ℕ) ≠ b` using `fun h => hcb (Fin.ext h)`. Use linear arithmetic over natural numbers and integers. Establish `h2` using `hz σ b c hbc`. Rewrite `h2` using `[shear_self_mul_apply, if_neg hba, add_zero]`.

Rewrite `h1` using `[if_pos rfl, h2, mul_zero, add_zero]`. Conclude with `h1`. Rewrite `h1` using `[if_neg hi, add_zero]`. Conclude with `h1`. Establish `h1` using `hz σ i c hic`.

Rewrite `h1` using `[shear_apply_of_ne τ a b t hσ, one_mul]`. Conclude with `h1`.
-/
theorem almostLow_of_shear : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 →
    ∀ (L K : Type) [Field L] [Field K] (j : L →+* K) (t : K), t ≠ 0 → ∀ C : Mat m L,
      Par m ⊤ (shear τ a b t * C.map j) → AlmostLow τ a b C := by
  intro ι m τ a b hab L K _ _ j t ht C hP
  have hmap : ∀ σ i c, (C.map j) σ i c = j (C σ i c) := fun _ _ _ => rfl
  have hL : ∀ σ, shear τ a b t σ * (C.map j) σ = (shear τ a b t * C.map j) σ := fun _ => rfl
  have hz : ∀ σ (i c : Fin (m σ)), i < c → (shear τ a b t σ * (C.map j) σ) i c = 0 := fun σ i c h => by
    rw [hL]; exact (hP σ).2.2.2 i c i.isLt h
  have hd : ∀ σ, (shear τ a b t σ * (C.map j) σ).det ≠ 0 := fun σ => by rw [hL]; exact (hP σ).2.1
  have hdiag : ∀ σ (i : Fin (m σ)), (shear τ a b t σ * (C.map j) σ) i i ≠ 0 := fun σ i => by
    have hbt : (shear τ a b t σ * (C.map j) σ).BlockTriangular OrderDual.toDual := fun p q hpq =>
      hz σ p q (OrderDual.toDual_lt_toDual.1 hpq)
    have := hd σ
    rw [Matrix.det_of_lowerTriangular _ hbt] at this
    exact Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ _)
  have hab' : a < b := by rw [Fin.lt_def]; omega
  have hba : b ≠ a := ne_of_gt hab'
  refine ⟨fun σ hσ => hd σ ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Mat.det_map, hσ, map_zero, mul_zero]
  · intro h0
    have h1 := hz τ a b hab'
    have h2 := hdiag τ b
    rw [shear_self_mul_apply] at h1 h2
    rw [if_pos rfl, hmap, h0, map_zero, zero_add] at h1
    rw [if_neg hba, add_zero] at h2
    exact h2 ((mul_eq_zero.1 h1).resolve_left ht)
  · intro σ i c hic hn
    refine (map_eq_zero j).1 ?_
    rw [← hmap]
    by_cases hσ : σ = τ
    · subst hσ
      have hn' : ¬ (i = a ∧ c = b) := fun h => hn ⟨by rw [h.1], by rw [h.2]⟩
      have h1 := hz σ i c hic
      rw [shear_self_mul_apply] at h1
      by_cases hi : i = a
      · subst hi
        have hcb : c ≠ b := fun h => hn' ⟨rfl, h⟩
        have hbc : b < c := by
          rw [Fin.lt_def] at hic ⊢
          have : (c : ℕ) ≠ b := fun h => hcb (Fin.ext h)
          omega
        have h2 := hz σ b c hbc
        rw [shear_self_mul_apply, if_neg hba, add_zero] at h2
        rw [if_pos rfl, h2, mul_zero, add_zero] at h1
        exact h1
      · rw [if_neg hi, add_zero] at h1
        exact h1
    · have h1 := hz σ i c hic
      rw [shear_apply_of_ne τ a b t hσ, one_mul] at h1
      exact h1

end GlobalTheory.FlagPush
