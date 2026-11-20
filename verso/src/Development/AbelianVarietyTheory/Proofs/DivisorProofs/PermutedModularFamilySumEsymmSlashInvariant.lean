import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in

/- English proof (translation)
Establish `hi` using `congrFun (h i γ) τ`. Rewrite `hi` using `[ModularForm.SL_slash_apply]`. Conclude with `hi`.
-/
theorem _root_.GlobalTheory.QFam.IsFam.value_mul_denom {ι : Type} {act : ι → SL(2, ℤ) → ι}
    {w : ℤ} {f : ι → ℍ → ℂ}
    (h : _root_.GlobalTheory.QFam.IsFam act w f) (i : ι) (γ : SL(2, ℤ)) (τ : ℍ) :
    f i (γ • τ) * UpperHalfPlane.denom γ τ ^ (-w) = f (act i γ) τ := by
  have hi := congrFun (h i γ) τ
  rw [ModularForm.SL_slash_apply] at hi
  exact hi

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in

/- English proof (translation)
Set `e : ι ≃ ι` to `Equiv.ofBijective _ (hb γ)`. Use extensionality with `τ`. Rewrite using `[ModularForm.SL_slash_apply, Finset.sum_mul]`. Establish `key : ∀ t ∈ Finset.powersetCard k (Finset.univ : Finset ι), (∏ i ∈ t, f i (γ • τ)) * UpperHalfPlane.denom γ τ ^ (-(k * w : ℤ)) = ∏ i ∈ t, f (e i) τ`. Introduce `t ht`.

Rewrite `ht` using `[Finset.mem_powersetCard]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, ht.2, ← zpow_natCast, ← zpow_mul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = ∏ i ∈ t, f (e i) τ := Finset.prod_congr rfl fun i _ => h.value_mul_denom i γ τ`. Rewrite using `[Finset.sum_congr rfl key]`. Use `Finset.sum_nbij' (fun t => t.map e.toEmbedding) (fun t => t.map e.symm.toEmbedding) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `t ht`. Simplify using `only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.card_map] at ht ⊢`.

Conclude with `ht`. Introduce `t ht`. Simplify using `only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.card_map] at ht ⊢`. Conclude with `ht`. Introduce `t _`.

Simplify using `[Finset.map_map]`. Introduce `t _`. Simplify using `[Finset.map_map]`. Introduce `t _`. Rewrite using `[Finset.prod_map]`.

Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.QFam.IsFam.esymm_slash {ι : Type} [Fintype ι]
    {act : ι → SL(2, ℤ) → ι} {w : ℤ} {f : ι → ℍ → ℂ}
    (hb : _root_.GlobalTheory.QFam.ActBij act) (h : _root_.GlobalTheory.QFam.IsFam act w f)
    (γ : SL(2, ℤ)) (k : ℕ) :
    (fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) ∣[(k * w : ℤ)] γ =
      fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ := by
  let e : ι ≃ ι := Equiv.ofBijective _ (hb γ)
  ext τ
  rw [ModularForm.SL_slash_apply, Finset.sum_mul]
  have key : ∀ t ∈ Finset.powersetCard k (Finset.univ : Finset ι),
      (∏ i ∈ t, f i (γ • τ)) * UpperHalfPlane.denom γ τ ^ (-(k * w : ℤ)) =
        ∏ i ∈ t, f (e i) τ := by
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    calc (∏ i ∈ t, f i (γ • τ)) * UpperHalfPlane.denom γ τ ^ (-(k * w : ℤ))
        = ∏ i ∈ t, (f i (γ • τ) * UpperHalfPlane.denom γ τ ^ (-w)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, ht.2, ← zpow_natCast, ← zpow_mul]
          congr 2
          ring
      _ = ∏ i ∈ t, f (e i) τ := Finset.prod_congr rfl fun i _ => h.value_mul_denom i γ τ
  rw [Finset.sum_congr rfl key]
  refine Finset.sum_nbij' (fun t => t.map e.toEmbedding) (fun t => t.map e.symm.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.card_map] at ht ⊢
    exact ht
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.card_map] at ht ⊢
    exact ht
  · intro t _
    simp [Finset.map_map]
  · intro t _
    simp [Finset.map_map]
  · intro t _
    rw [Finset.prod_map]
    rfl

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in

/- English proof (translation)
Introduce `ι _ act w f hb h γ`. Use `⟨?_, fun k => h.esymm_slash hb γ k⟩` and prove the remaining obligations. Set `e : ι ≃ ι` to `Equiv.ofBijective _ (hb γ)`. Use extensionality with `τ`. Rewrite using `[ModularForm.SL_slash_apply, Finset.sum_mul]`.

Rewrite using `[Finset.sum_congr rfl fun i _ => h.value_mul_denom i γ τ]`. Conclude with `e.sum_comp (fun i => f i τ)`.
-/
theorem _root_.GlobalTheory.QFam.sum_esymm_slash : ∀ (ι : Type) [Fintype ι]
    (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ),
    _root_.GlobalTheory.QFam.ActBij act → _root_.GlobalTheory.QFam.IsFam act w f → ∀ γ : SL(2, ℤ),
      ((fun τ => ∑ i, f i τ) ∣[w] γ = fun τ => ∑ i, f i τ) ∧
      ∀ k : ℕ, ((fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) ∣[(k * w : ℤ)] γ =
        fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) := by
  intro ι _ act w f hb h γ
  refine ⟨?_, fun k => h.esymm_slash hb γ k⟩
  let e : ι ≃ ι := Equiv.ofBijective _ (hb γ)
  ext τ
  rw [ModularForm.SL_slash_apply, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => h.value_mul_denom i γ τ]
  exact e.sum_comp (fun i => f i τ)

end GlobalTheory.QFam
