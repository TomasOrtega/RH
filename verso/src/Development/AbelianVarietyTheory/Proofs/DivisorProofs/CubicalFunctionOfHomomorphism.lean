import Mathlib

namespace GlobalTheory

def evenDefectTriangle (n : ℤ) : ℤ := n * (n - 1) / 2

/- English proof (translation)
Unfold `evenDefectTriangle`. Conclude with `Int.mul_ediv_cancel' (Int.even_mul_pred_self n).two_dvd`.
-/
lemma two_mul_evenDefectTriangle (n : ℤ) : 2 * evenDefectTriangle n = n * (n - 1) := by
  unfold evenDefectTriangle
  exact Int.mul_ediv_cancel' (Int.even_mul_pred_self n).two_dvd

/- English proof (translation)
Establish `h1` using `two_mul_evenDefectTriangle (-n)`. Establish `h2` using `two_mul_evenDefectTriangle n`. Establish `: 2 * evenDefectTriangle (-n) = 2 * (evenDefectTriangle n + n)`. Rewrite using `[h1, mul_add, h2]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) this`.
-/
lemma evenDefectTriangle_neg (n : ℤ) : evenDefectTriangle (-n) = evenDefectTriangle n + n := by
  have h1 := two_mul_evenDefectTriangle (-n)
  have h2 := two_mul_evenDefectTriangle n
  have : 2 * evenDefectTriangle (-n) = 2 * (evenDefectTriangle n + n) := by
    rw [h1, mul_add, h2]; ring
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) this

/- English proof (translation)
Establish `h1` using `two_mul_evenDefectTriangle (a + a' + b)`. Establish `h2` using `two_mul_evenDefectTriangle a`. Establish `h3` using `two_mul_evenDefectTriangle a'`. Establish `h4` using `two_mul_evenDefectTriangle b`. Establish `h5` using `two_mul_evenDefectTriangle (a + a')`.

Establish `h6` using `two_mul_evenDefectTriangle (a + b)`. Establish `h7` using `two_mul_evenDefectTriangle (a' + b)`. Apply `mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)` to reduce the goal to its premises. Take the linear combination `h1 + h2 + h3 + h4 - h5 - h6 - h7`.
-/
lemma evenDefectTriangle_cube (a a' b : ℤ) :
    evenDefectTriangle (a + a' + b) + evenDefectTriangle a + evenDefectTriangle a'
      + evenDefectTriangle b
      = evenDefectTriangle (a + a') + evenDefectTriangle (a + b) + evenDefectTriangle (a' + b) := by
  have h1 := two_mul_evenDefectTriangle (a + a' + b)
  have h2 := two_mul_evenDefectTriangle a
  have h3 := two_mul_evenDefectTriangle a'
  have h4 := two_mul_evenDefectTriangle b
  have h5 := two_mul_evenDefectTriangle (a + a')
  have h6 := two_mul_evenDefectTriangle (a + b)
  have h7 := two_mul_evenDefectTriangle (a' + b)
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
  linear_combination h1 + h2 + h3 + h4 - h5 - h6 - h7

/- English proof (translation)
Set `e` to `Module.Free.chooseBasis ℤ X`. Set `ψ : Multiplicative X →* A` to `MonoidHom.mk' (fun x => h x.toAdd) (fun x y => hh _ _)`. Establish `hrep : ∀ x, h x = ∏ i, h (e i) ^ (e.repr x i)`. Introduce `x`. Use `conv_lhs => rw [← e.sum_repr x]`.

Express the relevant statement in the definitionally equal form `ψ (Multiplicative.ofAdd (∑ i, e.repr x i • e i)) = _`. Rewrite using `[ofAdd_sum, map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ofAdd_zsmul, map_zpow]`. Both sides reduce to the same expression.

Use `⟨fun x => ∏ i, h (e i) ^ evenDefectTriangle (e.repr x i), ?_, ?_⟩` and prove the remaining obligations. Introduce `a a' c`. Simplify using `only [map_add, Finsupp.add_apply, ← Finset.prod_mul_distrib, ← zpow_add]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[evenDefectTriangle_cube]`.

Introduce `a`. Simplify using `only [map_neg, Finsupp.neg_apply, evenDefectTriangle_neg]`. Rewrite using `[hrep a, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add, add_comm]`.
-/
theorem hom_eq_evenness_defect_of_cube (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (A : Type) [CommGroup A] (h : X → A)
    (hh : ∀ a b, h (a + b) = h a * h b) :
    ∃ k : X → A, (∀ a a' b : X, k (a + a' + b) * k a * k a' * k b
        = k (a + a') * k (a + b) * k (a' + b)) ∧ ∀ a, k (-a) = h a * k a := by
  classical
  let e := Module.Free.chooseBasis ℤ X
  let ψ : Multiplicative X →* A := MonoidHom.mk' (fun x => h x.toAdd) (fun x y => hh _ _)
  have hrep : ∀ x, h x = ∏ i, h (e i) ^ (e.repr x i) := by
    intro x
    conv_lhs => rw [← e.sum_repr x]
    change ψ (Multiplicative.ofAdd (∑ i, e.repr x i • e i)) = _
    rw [ofAdd_sum, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ofAdd_zsmul, map_zpow]
    rfl
  refine ⟨fun x => ∏ i, h (e i) ^ evenDefectTriangle (e.repr x i), ?_, ?_⟩
  · intro a a' c
    simp only [map_add, Finsupp.add_apply, ← Finset.prod_mul_distrib, ← zpow_add]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [evenDefectTriangle_cube]
  · intro a
    simp only [map_neg, Finsupp.neg_apply, evenDefectTriangle_neg]
    rw [hrep a, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_add, add_comm]

end GlobalTheory
