import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL Finset

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons a L ih`. Simplify using `only [List.map_cons, List.prod_cons, abs_mul]`. Establish `h1` using `h a (by simp)`.

Establish `h2` using `ih (fun b hb => h b (by simp [hb]))`. Conclude with `mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)`.
-/
theorem abs_list_prod_map_le_of_abs_le {α : Type} (L : List α) (f n : α → ℝ)
    (h : ∀ a ∈ L, |f a| ≤ n a) : |(L.map f).prod| ≤ (L.map n).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, abs_mul]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image k) (g := k) (fun i _ => Finset.mem_image_of_mem k (Finset.mem_univ i)), Complex.re_sum]`. Use `Finset.sum_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[← Complex.re_ofReal_mul, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun i hi => ?_)` and prove the remaining obligations.

Establish `hi' : k i = t` using `(Finset.mem_filter.mp hi).2`. Rewrite using `[← Finset.mul_sum, hi', Finset.sum_filter]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Use `split_ifs with h`.

Both sides reduce to the same expression. Conclude with `hB i j (fun e => h (e ▸ hi'))`.
-/
theorem sum_weight_blockDiagonal_eq {ι κ : Type} [Fintype ι] [DecidableEq κ] (B : ι → ι → ℂ)
    (k : ι → κ) (hB : ∀ i j, k i ≠ k j → B i j = 0) (f : κ → ℝ) :
    (∑ i, ∑ j, ((f (k i) : ℝ) : ℂ) * B i j).re =
      ∑ t ∈ Finset.univ.image k, f t *
        (∑ i ∈ Finset.univ.filter (fun i => k i = t),
          ∑ j ∈ Finset.univ.filter (fun j => k j = t), B i j).re := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image k) (g := k)
    (fun i _ => Finset.mem_image_of_mem k (Finset.mem_univ i)), Complex.re_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Complex.re_ofReal_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : k i = t := (Finset.mem_filter.mp hi).2
  rw [← Finset.mul_sum, hi', Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs with h
  · rfl
  · exact hB i j (fun e => h (e ▸ hi'))

/- English proof (translation)
Introduce `ι α _ B c L n hpos hzero hbd`. Establish `hB : ∀ i j, L.map (c i) ≠ L.map (c j) → B i j = 0`. Introduce `i j hij`. Assume the negation of the conclusion as `hne`. Apply `hij` to reduce the goal to its premises.

Use `List.map_congr_left (fun a ha => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hne (hzero i j a ha h)`. Establish `e1` using `sum_weight_blockDiagonal_eq B (fun i => L.map (c i)) hB List.prod`. Establish `e2` using `sum_weight_blockDiagonal_eq B (fun i => L.map (c i)) hB (fun _ => 1)`.

Simplify using `only [Complex.ofReal_one, one_mul] at e2`. Rewrite using `[e1, e2, Finset.mul_sum]`. Use `Finset.sum_le_sum (fun t ht => ?_)` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `Finset.mem_image.mp ht`. Conclude with `mul_le_mul_of_nonneg_right ((le_abs_self _).trans (abs_list_prod_map_le_of_abs_le L (c i) n (hbd i))) (hpos _)`.
-/
theorem gram_blockDiagonal_energy_bound :
    ∀ (ι α : Type) [Fintype ι] (B : ι → ι → ℂ) (c : ι → α → ℝ) (L : List α) (n : α → ℝ), (∀ S : Finset ι, 0 ≤ (∑ i ∈ S, ∑ j ∈ S, B i j).re) → (∀ i j, ∀ a ∈ L, c i a ≠ c j a → B i j = 0) → (∀ i, ∀ a ∈ L, |c i a| ≤ n a) → (∑ i, ∑ j, (((L.map (c i)).prod : ℝ) : ℂ) * B i j).re ≤ (L.map n).prod * (∑ i, ∑ j, B i j).re := by
  intro ι α _ B c L n hpos hzero hbd
  classical
  have hB : ∀ i j, L.map (c i) ≠ L.map (c j) → B i j = 0 := by
    intro i j hij
    by_contra hne
    apply hij
    refine List.map_congr_left (fun a ha => ?_)
    by_contra h
    exact hne (hzero i j a ha h)
  have e1 := sum_weight_blockDiagonal_eq B (fun i => L.map (c i)) hB List.prod
  have e2 := sum_weight_blockDiagonal_eq B (fun i => L.map (c i)) hB (fun _ => 1)
  simp only [Complex.ofReal_one, one_mul] at e2
  rw [e1, e2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun t ht => ?_)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
  exact mul_le_mul_of_nonneg_right
    ((le_abs_self _).trans (abs_list_prod_map_le_of_abs_le L (c i) n (hbd i))) (hpos _)

end GlobalTheory
