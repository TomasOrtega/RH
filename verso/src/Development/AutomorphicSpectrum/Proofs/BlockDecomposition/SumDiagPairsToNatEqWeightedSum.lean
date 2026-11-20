import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagPairs

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical

namespace GlobalTheory.CompanionTheory.IwJac

/- English proof (translation)
Establish `h1 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), x p.1 = ∑ i : Fin n, ∑ j : Fin n, if i < j then x i else 0`. Rewrite using `[Finset.sum_filter, Fintype.sum_prod_type]`. Establish `h2 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), x p.2 = ∑ i : Fin n, ∑ j : Fin n, if j < i then x i else 0`. Rewrite using `[Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]`. Rewrite using `[Finset.sum_sub_distrib, h1, h2, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `a1 : (∑ j : Fin n, if i < j then x i else 0) = ((n : ℤ) - 1 - (i : ℕ)) * x i`. Rewrite using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`. Establish `: (Finset.univ.filter fun j : Fin n => i < j) = Finset.Ioi i` using `by ext j; simp`. Rewrite using `[this, Fin.card_Ioi]`.

Use `i.isLt` as an intermediate fact. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `a2 : (∑ j : Fin n, if j < i then x i else 0) = ((i : ℕ) : ℤ) * x i`. Rewrite using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`.

Establish `: (Finset.univ.filter fun j : Fin n => j < i) = Finset.Iio i` using `by ext j; simp`. Rewrite using `[this, Fin.card_Iio]`. Rewrite using `[a1, a2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_pairs_sub (n : ℕ) (x : Fin n → ℤ) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), (x p.1 - x p.2) =
      ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i := by
  have h1 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), x p.1 =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then x i else 0 := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  have h2 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), x p.2 =
      ∑ i : Fin n, ∑ j : Fin n, if j < i then x i else 0 := by
    rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_sub_distrib, h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have a1 : (∑ j : Fin n, if i < j then x i else 0) = ((n : ℤ) - 1 - (i : ℕ)) * x i := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have : (Finset.univ.filter fun j : Fin n => i < j) = Finset.Ioi i := by ext j; simp
    rw [this, Fin.card_Ioi]
    have := i.isLt
    congr 1
    omega
  have a2 : (∑ j : Fin n, if j < i then x i else 0) = ((i : ℕ) : ℤ) * x i := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have : (Finset.univ.filter fun j : Fin n => j < i) = Finset.Iio i := by ext j; simp
    rw [this, Fin.card_Iio]
  rw [a1, a2]
  ring

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)) (t := Finset.range n) (g := fun p => p.2.val - p.1.val - 1)]`. Use `Finset.sum_congr rfl fun d hd => Finset.sum_congr ?_ fun _ _ => rfl` and prove the remaining obligations. Use extensionality with `p`. Establish `h1` using `p.1.isLt`. Establish `h2` using `p.2.isLt`.

Simplify using `only [diagPairs, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Introduce `p hp`. Establish `h2` using `p.2.isLt`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hp`.

Rewrite using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_diagPairs (n : ℕ) (f : Fin n × Fin n → ℤ) :
    ∑ d ∈ Finset.range n, ∑ p ∈ diagPairs n d, f p =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), f p := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (t := Finset.range n) (g := fun p => p.2.val - p.1.val - 1)]
  · refine Finset.sum_congr rfl fun d hd => Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    simp only [diagPairs, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    omega
  · intro p hp
    have h2 := p.2.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hp
    rw [Finset.mem_range]
    omega

/- English proof (translation)
Rewrite using `[← sum_pairs_sub, ← sum_diagPairs]`. Use `push_cast`. Use `Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hlt : p.1 < p.2`. Simplify using `only [diagPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp`.

Rewrite using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Use `hx hlt` as an intermediate fact. Conclude with `Int.toNat_of_nonneg (by omega)`.
-/
theorem sum_diagPairs_toNat (n : ℕ) (x : Fin n → ℤ) (hx : StrictAnti x) :
    ((∑ d ∈ Finset.range n, ∑ p ∈ diagPairs n d, (x p.1 - x p.2).toNat : ℕ) : ℤ) =
      ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i := by
  rw [← sum_pairs_sub, ← sum_diagPairs]
  push_cast
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun p hp => ?_
  have hlt : p.1 < p.2 := by
    simp only [diagPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [Fin.lt_def]
    omega
  have := hx hlt
  exact Int.toNat_of_nonneg (by omega)

end GlobalTheory.CompanionTheory.IwJac

end
