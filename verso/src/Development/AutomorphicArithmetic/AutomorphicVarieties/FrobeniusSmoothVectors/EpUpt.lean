import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `C _ n h T T' hT hT' hu hc`. It suffices to establish `key : ∀ m, ∀ i j : Fin n, j.val + (n - i.val) = m → j < i → h i j = 0 by`. Introduce `i j hji`. Conclude with `key _ i j rfl hji`. Introduce `m`.

Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `i j hm hji`. Establish `e` using `congrFun (congrFun hc i) j`. Simplify using `only [Matrix.mul_apply] at e`.

Establish `hji'` using `Fin.lt_iff_val_lt_val.mp hji`. Establish `L : ∑ k, h i k * T k j = h i j * T j j`. Rewrite using `[Finset.sum_eq_single j]`. Introduce `k _ hkj`. Break down `lt_or_gt_of_ne hkj with hk | hk` into its components or cases.

Establish `hk'` using `Fin.lt_iff_val_lt_val.mp hk`. Rewrite using `[ih (k.val + (n - i.val)) (by omega) i k rfl (hk.trans hji), zero_mul]`. Rewrite using `[hT k j hk, mul_zero]`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ j) hn`.

Establish `R : ∑ k, T' i k * h k j = T' i i * h i j`. Rewrite using `[Finset.sum_eq_single i]`. Introduce `k _ hki`. Break down `lt_or_gt_of_ne hki with hk | hk` into its components or cases. Rewrite using `[hT' i k hk, zero_mul]`.

Establish `hk'` using `Fin.lt_iff_val_lt_val.mp hk`. Establish `hkn` using `k.isLt`. Rewrite using `[ih (j.val + (n - k.val)) (by omega) k j rfl (hji.trans hk), mul_zero]`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ i) hn`.

Rewrite `e` using `[L, R]`. Establish `e2 : h i j * (T j j - T' i i) = 0`. Rewrite using `[mul_sub, e, mul_comm]`. Conclude with `sub_self _`. Conclude with `(hu i j hji).mul_left_eq_zero.mp e2`.
-/
theorem UpperTheory.V.Fr.ep_upt :
    ∀ {C : Type} [CommRing C] {n : ℕ} (h T T' : Matrix (Fin n) (Fin n) C), UpT T → UpT T' → (∀ i j, j < i → IsUnit (T j j - T' i i)) → h * T = T' * h → UpT h := by
  intro C _ n h T T' hT hT' hu hc
  suffices key : ∀ m, ∀ i j : Fin n, j.val + (n - i.val) = m → j < i → h i j = 0 by
    intro i j hji
    exact key _ i j rfl hji
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i j hm hji
    have e := congrFun (congrFun hc i) j
    simp only [Matrix.mul_apply] at e
    have hji' := Fin.lt_iff_val_lt_val.mp hji
    have L : ∑ k, h i k * T k j = h i j * T j j := by
      rw [Finset.sum_eq_single j]
      · intro k _ hkj
        rcases lt_or_gt_of_ne hkj with hk | hk
        · have hk' := Fin.lt_iff_val_lt_val.mp hk
          rw [ih (k.val + (n - i.val)) (by omega) i k rfl (hk.trans hji), zero_mul]
        · rw [hT k j hk, mul_zero]
      · intro hn
        exact absurd (Finset.mem_univ j) hn
    have R : ∑ k, T' i k * h k j = T' i i * h i j := by
      rw [Finset.sum_eq_single i]
      · intro k _ hki
        rcases lt_or_gt_of_ne hki with hk | hk
        · rw [hT' i k hk, zero_mul]
        · have hk' := Fin.lt_iff_val_lt_val.mp hk
          have hkn := k.isLt
          rw [ih (j.val + (n - k.val)) (by omega) k j rfl (hji.trans hk), mul_zero]
      · intro hn
        exact absurd (Finset.mem_univ i) hn
    rw [L, R] at e
    have e2 : h i j * (T j j - T' i i) = 0 := by
      rw [mul_sub, e, mul_comm]
      exact sub_self _
    exact (hu i j hji).mul_left_eq_zero.mp e2
