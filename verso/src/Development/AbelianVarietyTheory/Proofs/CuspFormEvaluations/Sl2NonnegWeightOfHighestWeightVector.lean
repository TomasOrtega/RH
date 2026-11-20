import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `key : ∀ i j, e i j (e j i v) = ((if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ) : K) • v`. Introduce `i j`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Establish `h1` using `congrArg (fun f : Module.End K V => f v) (he i j j i)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, ↓reduceIte] at h1`.

Rewrite `h1` using `[hv i j h, map_zero, sub_zero, hκ, hκ]`. Rewrite using `[h1, if_pos h]`. Use `push_cast`. Rewrite using `[sub_smul]`. Substitute `h` using the available equality.

Rewrite using `[if_neg (lt_irrefl i), if_pos rfl, hκ, map_smul, hκ, smul_smul]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hv j i h, map_zero, if_neg (lt_asymm h), if_neg h.ne']`. Simplify using the standard rewrite rules.

Establish `hsum : (∑ i : Fin m, ∑ j : Fin m, (if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ)) = ∑ i : Fin m, κ i * (κ i + m - 1 - 2 * (i : ℕ))`. Establish `h2 : ∀ i j : Fin m, (if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ) = ((if i = j then κ i * κ i else 0) + (if i < j then κ i else 0)) - (if i < j then κ j else 0)`. Introduce `i j`. Distinguish the cases in `h : i < j`. Simplify using `[h, h.ne]`.

Simplify using `[h]`. Repeatedly rewrite using `[h2, Finset.sum_sub_distrib, Finset.sum_add_distrib]`. Rewrite using `[Finset.sum_comm (f := fun i j => if i < j then κ j else 0)]`. Rewrite using `[← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio, nsmul_eq_mul, nsmul_eq_mul]`. Establish `hi` using `i.isLt`. Establish `hc : ((m - 1 - (i : ℕ) : ℕ) : ℤ) = m - 1 - (i : ℕ)` using `by omega`. Rewrite using `[hc]`.

Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[key]`. Rewrite using `[← hsum, Int.cast_sum, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Int.cast_sum, Finset.sum_smul]`.
-/
theorem casimir_on_highest {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] {m : ℕ} (e : Fin m → Fin m → Module.End K V)
    (he : ∀ i j k l, e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0))
    (v : V) (κ : Fin m → ℤ) (hv : ∀ i j, i < j → e i j v = 0) (hκ : ∀ i, e i i v = (κ i : K) • v) :
    ∑ i, ∑ j, e i j (e j i v) = ((∑ i, κ i * (κ i + m - 1 - 2 * (i : ℕ)) : ℤ) : K) • v := by
  have key : ∀ i j, e i j (e j i v) =
      ((if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ) : K) • v := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · have h1 := congrArg (fun f : Module.End K V => f v) (he i j j i)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, ↓reduceIte] at h1
      rw [hv i j h, map_zero, sub_zero, hκ, hκ] at h1
      rw [h1, if_pos h]
      push_cast
      rw [sub_smul]
    · subst h
      rw [if_neg (lt_irrefl i), if_pos rfl, hκ, map_smul, hκ, smul_smul]
      push_cast
      rfl
    · rw [hv j i h, map_zero, if_neg (lt_asymm h), if_neg h.ne']
      simp
  have hsum : (∑ i : Fin m, ∑ j : Fin m,
      (if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ)) =
      ∑ i : Fin m, κ i * (κ i + m - 1 - 2 * (i : ℕ)) := by
    have h2 : ∀ i j : Fin m, (if i < j then κ i - κ j else if i = j then κ i * κ i else 0 : ℤ) =
        ((if i = j then κ i * κ i else 0) + (if i < j then κ i else 0)) -
          (if i < j then κ j else 0) := by
      intro i j
      by_cases h : i < j
      · simp [h, h.ne]
      · simp [h]
    simp_rw [h2, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => if i < j then κ j else 0)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
      Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio,
      nsmul_eq_mul, nsmul_eq_mul]
    have hi := i.isLt
    have hc : ((m - 1 - (i : ℕ) : ℕ) : ℤ) = m - 1 - (i : ℕ) := by omega
    rw [hc]
    ring
  simp_rw [key]
  rw [← hsum, Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_sum, Finset.sum_smul]

/- English proof (translation)
Establish `hHFk : ∀ k : ℕ, H ((F ^ k) v) = ((l : K) - 2 * k) • (F ^ k) v`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [hH]`. Consider the case `succ k ih`.

Establish `h1` using `congrArg (fun f : Module.End K V => f ((F ^ k) v)) hHF`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply, LinearMap.add_apply] at h1`. Rewrite `h1` using `[sub_eq_iff_eq_add]`. Rewrite using `[pow_succ', Module.End.mul_apply, h1, ih, map_smul]`. Use `push_cast`.

Use `module`. Establish `hEFk : ∀ k : ℕ, E ((F ^ (k + 1)) v) = (((k : K) + 1) * ((l : K) - k)) • (F ^ k) v`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Establish `h1` using `congrArg (fun f : Module.End K V => f v) hEF`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hE, map_zero, sub_zero] at h1`. Simplify using `[h1, hH]`. Consider the case `succ k ih`. Establish `h1` using `congrArg (fun f : Module.End K V => f ((F ^ (k + 1)) v)) hEF`.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h1`. Rewrite `h1` using `[sub_eq_iff_eq_add]`. Establish `hp : (F ^ (k + 1 + 1)) v = F ((F ^ (k + 1)) v)`. Rewrite using `[pow_succ' F (k + 1), Module.End.mul_apply]`. Establish `hq : F ((F ^ k) v) = (F ^ (k + 1)) v`.

Rewrite using `[pow_succ' F k, Module.End.mul_apply]`. Rewrite using `[hp, h1, ih, map_smul, hq, hHFk, ← add_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Assume the negation of the conclusion as `hl0`. Establish `hl : l < 0` using `not_le.mp hl0`. Establish `hne : ∀ k : ℕ, (F ^ k) v ≠ 0`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simpa using hv0`. Consider the case `succ k ih`. Introduce `h0`. Establish `h1` using `hEFk k`. Rewrite `h1` using `[h0, map_zero]`.

Establish `hc : ((k : K) + 1) * ((l : K) - k) ≠ 0`. Use `mul_ne_zero (Nat.cast_add_one_ne_zero k) ?_` and prove the remaining obligations. Introduce `h`. Establish `h3 : ((l : ℤ) : K) = ((k : ℤ) : K)`. Rewrite `h` using `[sub_eq_zero]`.

Rewrite using `[h]`. Use `push_cast`. Both sides reduce to the same expression. Establish `h4 : l = (k : ℤ)` using `Int.cast_injective h3`. Use linear arithmetic over natural numbers and integers.

Conclude with `ih ((smul_eq_zero.mp h1.symm).resolve_left hc)`. Establish `hmem : ∀ k : ℕ, (F ^ k) v ∈ W`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hvW`.

Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `hW _ ih`. Establish `hli : LinearIndependent K (fun k : Fin (Module.finrank K W + 1) => (F ^ (k : ℕ)) v)`. Use `Module.End.eigenvectors_linearIndependent' H (fun k : Fin (Module.finrank K W + 1) => (l : K) - 2 * ((k : ℕ) : K)) ?_ _ (fun k => ⟨Module.End.mem_eigenspace_iff.2 (hHFk k), hne k⟩)` and prove the remaining obligations.

Introduce `a b hab`. Establish `h1 : (2 : K) * ((a : ℕ) : K) = 2 * ((b : ℕ) : K)` using `sub_right_injective hab`. Establish `h2 : ((a : ℕ) : K) = ((b : ℕ) : K)` using `mul_left_cancel₀ two_ne_zero h1`. Conclude with `Fin.ext (Nat.cast_injective h2)`. Establish `hw : LinearIndependent K (fun k : Fin (Module.finrank K W + 1) => (⟨(F ^ (k : ℕ)) v, hmem k⟩ : W))` using `LinearIndependent.of_comp W.subtype hli`.

Establish `h5` using `hw.fintype_card_le_finrank`. Simplify using `at h5`.
-/
theorem sl2_nonneg_weight_of_highest_weight_vector {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (E F H : Module.End K V) (hEF : E * F - F * E = H) (hHF : H * F - F * H = -(F + F))
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ w ∈ W, F w ∈ W)
    (v : V) (hvW : v ∈ W) (hv0 : v ≠ 0) (l : ℤ) (hE : E v = 0) (hH : H v = (l : K) • v) : 0 ≤ l := by
  have hHFk : ∀ k : ℕ, H ((F ^ k) v) = ((l : K) - 2 * k) • (F ^ k) v := by
    intro k
    induction k with
    | zero => simp [hH]
    | succ k ih =>
      have h1 := congrArg (fun f : Module.End K V => f ((F ^ k) v)) hHF
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
        LinearMap.add_apply] at h1
      rw [sub_eq_iff_eq_add] at h1
      rw [pow_succ', Module.End.mul_apply, h1, ih, map_smul]
      push_cast
      module
  have hEFk : ∀ k : ℕ, E ((F ^ (k + 1)) v) = (((k : K) + 1) * ((l : K) - k)) • (F ^ k) v := by
    intro k
    induction k with
    | zero =>
      have h1 := congrArg (fun f : Module.End K V => f v) hEF
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hE, map_zero, sub_zero] at h1
      simp [h1, hH]
    | succ k ih =>
      have h1 := congrArg (fun f : Module.End K V => f ((F ^ (k + 1)) v)) hEF
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
      rw [sub_eq_iff_eq_add] at h1
      have hp : (F ^ (k + 1 + 1)) v = F ((F ^ (k + 1)) v) := by
        rw [pow_succ' F (k + 1), Module.End.mul_apply]
      have hq : F ((F ^ k) v) = (F ^ (k + 1)) v := by
        rw [pow_succ' F k, Module.End.mul_apply]
      rw [hp, h1, ih, map_smul, hq, hHFk, ← add_smul]
      congr 1
      push_cast
      ring
  by_contra hl0
  have hl : l < 0 := not_le.mp hl0
  have hne : ∀ k : ℕ, (F ^ k) v ≠ 0 := by
    intro k
    induction k with
    | zero => simpa using hv0
    | succ k ih =>
      intro h0
      have h1 := hEFk k
      rw [h0, map_zero] at h1
      have hc : ((k : K) + 1) * ((l : K) - k) ≠ 0 := by
        refine mul_ne_zero (Nat.cast_add_one_ne_zero k) ?_
        intro h
        have h3 : ((l : ℤ) : K) = ((k : ℤ) : K) := by
          rw [sub_eq_zero] at h
          rw [h]
          push_cast
          rfl
        have h4 : l = (k : ℤ) := Int.cast_injective h3
        omega
      exact ih ((smul_eq_zero.mp h1.symm).resolve_left hc)
  have hmem : ∀ k : ℕ, (F ^ k) v ∈ W := by
    intro k
    induction k with
    | zero => simpa using hvW
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hW _ ih
  have hli : LinearIndependent K (fun k : Fin (Module.finrank K W + 1) => (F ^ (k : ℕ)) v) := by
    refine Module.End.eigenvectors_linearIndependent' H
      (fun k : Fin (Module.finrank K W + 1) => (l : K) - 2 * ((k : ℕ) : K)) ?_ _
      (fun k => ⟨Module.End.mem_eigenspace_iff.2 (hHFk k), hne k⟩)
    intro a b hab
    have h1 : (2 : K) * ((a : ℕ) : K) = 2 * ((b : ℕ) : K) := sub_right_injective hab
    have h2 : ((a : ℕ) : K) = ((b : ℕ) : K) := mul_left_cancel₀ two_ne_zero h1
    exact Fin.ext (Nat.cast_injective h2)
  have hw : LinearIndependent K
      (fun k : Fin (Module.finrank K W + 1) => (⟨(F ^ (k : ℕ)) v, hmem k⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hli
  have h5 := hw.fintype_card_le_finrank
  simp at h5

/- English proof (translation)
Introduce `a b hab`. Break down `hab.lt_or_eq with h | h` into its components or cases. Establish `hne : a ≠ b` using `h.ne`. Establish `hEF : e a b * e b a - e b a * e a b = e a a - e b b`. Simplify `he a b b a` using `only [↓reduceIte]`.

Establish `hHF : (e a a - e b b) * e b a - e b a * (e a a - e b b) = -(e b a + e b a)`. Establish `h1` using `he a a b a`. Establish `h2` using `he b b b a`. Simplify using `only [if_neg hne, ↓reduceIte, zero_sub, sub_zero] at h1 h2`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[sub_mul, mul_sub]`. Normalize the expressions using the abelian group laws. Use `_ = -(e b a + e b a) := by`. Rewrite using `[h1, h2]`. Normalize the expressions using the abelian group laws.

Establish `hHv : (e a a - e b b) v = (((κ a - κ b : ℤ)) : K) • v`. Rewrite using `[LinearMap.sub_apply, hκ, hκ]`. Use `push_cast`. Rewrite using `[sub_smul]`. Establish `h0` using `sl2_nonneg_weight_of_highest_weight_vector (e a b) (e b a) (e a a - e b b) hEF hHF W (hW b a) v hvW hv0 (κ a - κ b) (hv a b h) hHv`.

Combine the linear equalities and inequalities to obtain the conclusion. Substitute `h` using the available equality. Conclude with `le_rfl`.
-/
theorem highest_weight_antitone {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {m : ℕ} (e : Fin m → Fin m → Module.End K V)
    (he : ∀ i j k l, e i j * e k l - e k l * e i j = (if j = k then e i l else 0) - (if l = i then e k j else 0))
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ i j, ∀ w ∈ W, e i j w ∈ W)
    (v : V) (hvW : v ∈ W) (hv0 : v ≠ 0) (κ : Fin m → ℤ) (hv : ∀ i j, i < j → e i j v = 0) (hκ : ∀ i, e i i v = (κ i : K) • v) : Antitone κ := by
  intro a b hab
  rcases hab.lt_or_eq with h | h
  · have hne : a ≠ b := h.ne
    have hEF : e a b * e b a - e b a * e a b = e a a - e b b := by
      simpa only [↓reduceIte] using he a b b a
    have hHF : (e a a - e b b) * e b a - e b a * (e a a - e b b) = -(e b a + e b a) := by
      have h1 := he a a b a
      have h2 := he b b b a
      simp only [if_neg hne, ↓reduceIte, zero_sub, sub_zero] at h1 h2
      calc (e a a - e b b) * e b a - e b a * (e a a - e b b)
          = (e a a * e b a - e b a * e a a) - (e b b * e b a - e b a * e b b) := by
            rw [sub_mul, mul_sub]
            abel
        _ = -(e b a + e b a) := by
            rw [h1, h2]
            abel
    have hHv : (e a a - e b b) v = (((κ a - κ b : ℤ)) : K) • v := by
      rw [LinearMap.sub_apply, hκ, hκ]
      push_cast
      rw [sub_smul]
    have h0 := sl2_nonneg_weight_of_highest_weight_vector (e a b) (e b a) (e a a - e b b) hEF hHF W
      (hW b a) v hvW hv0 (κ a - κ b) (hv a b h) hHv
    linarith
  · subst h
    exact le_rfl

end GlobalTheory
