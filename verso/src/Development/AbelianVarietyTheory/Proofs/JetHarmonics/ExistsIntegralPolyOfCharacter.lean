import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

/- English proof (translation)
Use `choose c hc1 hc2 using hc`. Establish `van : ∀ v : Fin (Fintype.card G) → K, (∀ i, ∑ a, v a * x i ^ (a : ℕ) = 0) → v = 0`. Introduce `v hv`. Conclude with `Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero (f := fun j => x ((Fintype.equivFin G).symm j)) (hx.comp (Fintype.equivFin G).symm.injective) (fun j => hv _)`. Use `set g : Polynomial K := Lagrange.interpolate Finset.univ x χ with hg`.

Establish `hinj : Set.InjOn x (Finset.univ : Finset G)` using `hx.injOn`. Establish `hdeg : g.degree < (Fintype.card G : ℕ)`. Conclude with `Lagrange.degree_interpolate_lt (r := χ) hinj`. Establish `hev : ∀ i, g.eval (x i) = χ i` using `fun i => Lagrange.eval_interpolate_at_node χ hinj (Finset.mem_univ i)`. Establish `hpos : 0 < Fintype.card G` using `Fintype.card_pos`.

Establish `hnat : g.natDegree < Fintype.card G`. Distinguish the cases in `h0 : g = 0`. Simplify `hpos` using `[h0]`. Conclude with `(Polynomial.natDegree_lt_iff_degree_lt h0).2 hdeg`. Establish `hsum : ∀ i, χ i = ∑ a : Fin (Fintype.card G), g.coeff a * x i ^ (a : ℕ)`.

Introduce `i`. Rewrite using `[← hev i, Polynomial.eval_eq_sum_range' hnat, Fin.sum_univ_eq_sum_range (fun a => g.coeff a * x i ^ a)]`. Establish `key : ∀ a b : Fin (Fintype.card G), g.coeff a * g.coeff b = ∑ k : Fin (Fintype.card G), g.coeff k * c k a b`. Establish `h1 : ∀ j, (fun a : Fin (Fintype.card G) => ∑ b : Fin (Fintype.card G), (g.coeff a * g.coeff b - ∑ k : Fin (Fintype.card G), g.coeff k * c k a b) * x j ^ (b : ℕ)) = 0`. Introduce `j`.

Apply `van` to reduce the goal to its premises. Introduce `i`. Establish `e1 : χ i * χ j = ∑ a : Fin (Fintype.card G), ∑ b : Fin (Fintype.card G), g.coeff a * g.coeff b * x j ^ (b : ℕ) * x i ^ (a : ℕ)`. Rewrite using `[hsum i, hsum j, Finset.sum_mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`.

Establish `e2 : χ (i + j) = ∑ a : Fin (Fintype.card G), ∑ b : Fin (Fintype.card G), (∑ k : Fin (Fintype.card G), g.coeff k * c k a b) * x j ^ (b : ℕ) * x i ^ (a : ℕ)`. Rewrite using `[hsum (i + j)]`. Repeatedly rewrite using `[hc2, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring`. Establish `e3` using `hχ i j`. Rewrite `e3` using `[e1, e2]`. Repeatedly rewrite using `[Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]`.

Rewrite using `[sub_eq_zero]`. Conclude with `e3.symm`. Introduce `a b`. Establish `h2` using `van _ (fun j => congrFun (h1 j) a)`. Conclude with `sub_eq_zero.1 (congrFun h2 b)`.

Use `haveI : Nonempty (Fin (Fintype.card G)) := ⟨⟨0, hpos⟩⟩`. Take `⟨m, -, hm⟩` from `Finset.exists_max_image Finset.univ (fun a : Fin (Fintype.card G) => ‖g.coeff a‖) Finset.univ_nonempty`. Establish `hM : ‖g.coeff m‖ * ‖g.coeff m‖ ≤ ‖g.coeff m‖`. Rewrite using `[← norm_mul, key]`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)` to reduce the goal to its premises.

Introduce `k _`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hM1 : ‖g.coeff m‖ ≤ 1` using `by nlinarith [norm_nonneg (g.coeff m)]`. Use `⟨g, fun k => ?_, hev⟩` and prove the remaining obligations.

Distinguish the cases in `hk : k < Fintype.card G`. Conclude with `(hm ⟨k, hk⟩ (Finset.mem_univ _)).trans hM1`. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem exists_integral_poly_of_character (K : Type) [NormedField K] [IsUltrametricDist K]
    (G : Type) [AddCommGroup G] [Fintype G] (x χ : G → K) (hx : Function.Injective x)
    (hχ : ∀ i j, χ (i + j) = χ i * χ j)
    (hc : ∀ k : Fin (Fintype.card G), ∃ c : Fin (Fintype.card G) → Fin (Fintype.card G) → K,
      (∀ a b, ‖c a b‖ ≤ 1) ∧
        ∀ i j, x (i + j) ^ (k : ℕ) = ∑ a, ∑ b, c a b * x i ^ (a : ℕ) * x j ^ (b : ℕ)) :
    ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧ ∀ i, g.eval (x i) = χ i := by
  classical
  choose c hc1 hc2 using hc
  have van : ∀ v : Fin (Fintype.card G) → K, (∀ i, ∑ a, v a * x i ^ (a : ℕ) = 0) → v = 0 := by
    intro v hv
    exact Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      (f := fun j => x ((Fintype.equivFin G).symm j))
      (hx.comp (Fintype.equivFin G).symm.injective) (fun j => hv _)
  set g : Polynomial K := Lagrange.interpolate Finset.univ x χ with hg
  have hinj : Set.InjOn x (Finset.univ : Finset G) := hx.injOn
  have hdeg : g.degree < (Fintype.card G : ℕ) := by
    exact Lagrange.degree_interpolate_lt (r := χ) hinj
  have hev : ∀ i, g.eval (x i) = χ i := fun i =>
    Lagrange.eval_interpolate_at_node χ hinj (Finset.mem_univ i)
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  have hnat : g.natDegree < Fintype.card G := by
    by_cases h0 : g = 0
    · simpa [h0] using hpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hdeg
  have hsum : ∀ i, χ i = ∑ a : Fin (Fintype.card G), g.coeff a * x i ^ (a : ℕ) := by
    intro i
    rw [← hev i, Polynomial.eval_eq_sum_range' hnat,
      Fin.sum_univ_eq_sum_range (fun a => g.coeff a * x i ^ a)]
  have key : ∀ a b : Fin (Fintype.card G),
      g.coeff a * g.coeff b = ∑ k : Fin (Fintype.card G), g.coeff k * c k a b := by
    have h1 : ∀ j, (fun a : Fin (Fintype.card G) => ∑ b : Fin (Fintype.card G),
        (g.coeff a * g.coeff b - ∑ k : Fin (Fintype.card G), g.coeff k * c k a b)
          * x j ^ (b : ℕ)) = 0 := by
      intro j
      apply van
      intro i
      have e1 : χ i * χ j = ∑ a : Fin (Fintype.card G), ∑ b : Fin (Fintype.card G),
          g.coeff a * g.coeff b * x j ^ (b : ℕ) * x i ^ (a : ℕ) := by
        rw [hsum i, hsum j, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      have e2 : χ (i + j) = ∑ a : Fin (Fintype.card G), ∑ b : Fin (Fintype.card G),
          (∑ k : Fin (Fintype.card G), g.coeff k * c k a b) * x j ^ (b : ℕ) * x i ^ (a : ℕ) := by
        rw [hsum (i + j)]
        simp_rw [hc2, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring
      have e3 := hχ i j
      rw [e1, e2] at e3
      simp_rw [Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      exact e3.symm
    intro a b
    have h2 := van _ (fun j => congrFun (h1 j) a)
    exact sub_eq_zero.1 (congrFun h2 b)
  haveI : Nonempty (Fin (Fintype.card G)) := ⟨⟨0, hpos⟩⟩
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ
    (fun a : Fin (Fintype.card G) => ‖g.coeff a‖) Finset.univ_nonempty
  have hM : ‖g.coeff m‖ * ‖g.coeff m‖ ≤ ‖g.coeff m‖ := by
    rw [← norm_mul, key]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro k _
    rw [norm_mul]
    calc ‖g.coeff k‖ * ‖c k m m‖ ≤ ‖g.coeff k‖ * 1 :=
          mul_le_mul_of_nonneg_left (hc1 k m m) (norm_nonneg _)
      _ ≤ ‖g.coeff m‖ := by simpa using hm k (Finset.mem_univ k)
  have hM1 : ‖g.coeff m‖ ≤ 1 := by nlinarith [norm_nonneg (g.coeff m)]
  refine ⟨g, fun k => ?_, hev⟩
  by_cases hk : k < Fintype.card G
  · exact (hm ⟨k, hk⟩ (Finset.mem_univ _)).trans hM1
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

end GlobalTheory.ConvSer
