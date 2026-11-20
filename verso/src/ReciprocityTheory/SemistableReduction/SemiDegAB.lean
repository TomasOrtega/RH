import ReciprocityTheory.SemistableReduction.SemiDegAA

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Module

/- English proof (translation)
Break down `Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩` into its components or cases. Conclude with `Or.inl h`. Use `right`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => left`.

Simplify using the standard rewrite rules. Consider the case `cast j => right`. Conclude with `⟨j, rfl⟩`.
-/
theorem wa_cases3 {n : ℕ} (i : Fin (n + 2)) :
    i = 0 ∨ i = Fin.last (n + 1) ∨ ∃ j : Fin n, i = (Fin.castSucc j).succ := by
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · exact Or.inl h
  · right
    induction j using Fin.lastCases with
    | last => left; simp
    | cast j => right; exact ⟨j, rfl⟩

def waExt {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) : Fin (n + 2) → α :=
  Fin.cons x (Fin.snoc f y : Fin (n + 1) → α)

/- English proof (translation)
Simplify using `[waExt]`.
-/
@[simp] theorem waExt_zero {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) :
    waExt x y f 0 = x := by
  simp [waExt]

/- English proof (translation)
Rewrite using `[waExt, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]`.
-/
@[simp] theorem waExt_last {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) :
    waExt x y f (Fin.last (n + 1)) = y := by
  rw [waExt, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]

/- English proof (translation)
Rewrite using `[waExt, Fin.cons_succ, Fin.snoc_castSucc]`.
-/
@[simp] theorem waExt_mid {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) (j : Fin n) :
    waExt x y f (Fin.castSucc j).succ = f j := by
  rw [waExt, Fin.cons_succ, Fin.snoc_castSucc]

/- English proof (translation)
Unfold `wittMat`. Simplify using `only [Matrix.of_apply, Fin.val_inj]`.
-/
theorem wa_witt_apply {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i j : Fin r) :
    wittMat r m g i j = if (i : ℕ) + j + 1 = r ∧ ((i : ℕ) < m ∨ (j : ℕ) < m) then 1
      else if (i : ℕ) = j ∧ m ≤ (i : ℕ) ∧ (i : ℕ) + m < r then g i else 0 := by
  unfold wittMat
  simp only [Matrix.of_apply, Fin.val_inj]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `W hW hnd`. Distinguish the cases in `hiso : ∃ x ∈ W, x ≠ 0 ∧ S.h x x = 0`.

Take `⟨x, hxW, hx0, hxx⟩` from `hiso`. Take `⟨y, hyW, hxy, hyy⟩` from `wa_hyp S W hnd x hxW hx0 hxx`. Establish `hyx : S.h y x = 1` using `by rw [wa_symm, hxy, map_one]`. Establish `hf1` using `wa_finrank_inf_ker W (waR S x) y hyW (by rw [waR_apply, hxy]; exact one_ne_zero)`. Establish `hf2` using `wa_finrank_inf_ker (W ⊓ LinearMap.ker (waR S x)) (waR S y) x (Submodule.mem_inf.mpr ⟨hxW, by rw [LinearMap.mem_ker, waR_apply, hxx]⟩) (by rw [waR_apply, hyx]; exact one_ne_zero)`.

Take `⟨n', rfl⟩ : ∃ n', n = n' + 2` from `⟨finrank K ↥(W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y)), by omega⟩`. Take `⟨m', b', g', hb'W, hm', hgram', hani'⟩` from `ih n' (by omega) (W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y)) (by omega) (wa_perp_nondeg S W hnd x y hxW hyW hxx hxy hyy)`. Establish `hmem : ∀ j, b' j ∈ W ∧ S.h x (b' j) = 0 ∧ S.h y (b' j) = 0` using `fun j => by`. Establish `h` using `hb'W j`. Rewrite `h` using `[Submodule.mem_inf, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, waR_apply, waR_apply]`.

Conclude with `⟨h.1.1, h.1.2, h.2⟩`. Establish `hbx : ∀ j, S.h (b' j) x = 0` using `fun j => by rw [wa_symm, (hmem j).2.1, map_zero]`. Establish `hby : ∀ j, S.h (b' j) y = 0` using `fun j => by rw [wa_symm, (hmem j).2.2, map_zero]`. Use `⟨m' + 1, waExt x y b', waExt 0 0 g', fun i => ?_, by omega, fun i j => ?_, fun t ht hsum => ?_⟩` and prove the remaining obligations. Break down `wa_cases3 i with rfl | rfl | ⟨j, rfl⟩` into its components or cases.

Simplify using `using hxW`. Simplify using `using hyW`. Simplify using `using (hmem j).1`. Rewrite using `[wa_witt_apply]`. Apply the tactic sequence `rcases wa_cases3 i with rfl | rfl | ⟨i, rfl⟩ <;>`.

Apply the tactic sequence `rcases wa_cases3 j with rfl | rfl | ⟨j, rfl⟩ <;>`. Apply the tactic sequence `simp only [waExt_zero, waExt_last, waExt_mid, Fin.val_zero, Fin.val_last, Fin.val_succ, Fin.val_castSucc] <;>`. Apply the tactic sequence `try simp only [true_and]`. Rewrite using `[hxx, if_neg (by omega), if_neg (by omega)]`. Rewrite using `[hxy, if_pos (by omega)]`.

Use `j.2` as an intermediate fact. Rewrite using `[(hmem j).2.1, if_neg (by omega), if_neg (by omega)]`. Rewrite using `[hyx, if_pos (by omega)]`. Rewrite using `[hyy, if_neg (by omega), if_neg (by omega)]`. Use `j.2` as an intermediate fact.

Rewrite using `[(hmem j).2.2, if_neg (by omega), if_neg (by omega)]`. Use `i.2` as an intermediate fact. Rewrite using `[hbx, if_neg (by omega), if_neg (by omega)]`. Use `i.2` as an intermediate fact. Rewrite using `[hby, if_neg (by omega), if_neg (by omega)]`.

Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Rewrite using `[hgram', wa_witt_apply]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Establish `ht0 : t 0 = 0` using `ht 0 (Or.inl (by simp))`.

Establish `htl : t (Fin.last (n' + 1)) = 0` using `ht _ (Or.inr (by simp only [Fin.val_last]; omega))`. Establish `ht' : (fun j : Fin n' => t (Fin.castSucc j).succ) = 0`. Use `hani' _ (fun j hj => ht _ ?_) ?_` and prove the remaining obligations. Simplify using `only [Fin.val_succ, Fin.val_castSucc]`. Use linear arithmetic over natural numbers and integers.

Rewrite `hsum` using `[Fin.sum_univ_succ, Fin.sum_univ_castSucc]`. Simplify `hsum` using `[ht0, htl, Fin.succ_last]`. Use function extensionality and compare the values at `i`. Break down `wa_cases3 i with rfl | rfl | ⟨j, rfl⟩` into its components or cases. Conclude with `ht0`.

Conclude with `htl`. Conclude with `congrFun ht' j`. Establish `han : ∀ x ∈ W, S.h x x = 0 → x = 0` using `fun x hx hxx => by`. Assume the negation of the conclusion as `h0`. Conclude with `hiso ⟨x, hx, h0, hxx⟩`.

Take `⟨b, hbW, hb0, hbo⟩` from `wa_diag S n W hW han`. Establish `hg : ∀ k, S.h (b k) (b k) ≠ 0` using `fun k h => hb0 k (han _ (hbW k) h)`. Use `⟨0, b, fun k => S.h (b k) (b k), hbW, by omega, fun i j => ?_, fun t _ hsum => ?_⟩` and prove the remaining obligations. Rewrite using `[wa_witt_apply]`. Use `i.2` as an intermediate fact.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[if_neg (by omega), if_pos ⟨rfl, by omega, by omega⟩]`. Rewrite using `[hbo i j hij, if_neg (by omega), if_neg (fun h => hij (Fin.ext h.1))]`. Establish `hz : ∀ k, S.h (b k) (∑ i, t i • b i) = t k * S.h (b k) (b k)` using `fun k => by`.

Rewrite using `[wa_sum_right, Finset.sum_eq_single k (fun i _ hik => by rw [hbo k i (Ne.symm hik), mul_zero]) (by simp)]`. Establish `hzz : S.h (∑ i, t i • b i) (∑ i, t i • b i) = 0`. Rewrite using `[wa_sum_left]`. Simplify using `only [hz]`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum` and prove the remaining obligations.

Use `beta_reduce`. Expand and normalize the polynomial expressions, which then agree. Establish `hz0` using `han _ (W.sum_mem fun i _ => W.smul_mem _ (hbW i)) hzz`. Use function extensionality and compare the values at `k`. Establish `h` using `hz k`.

Rewrite `h` using `[hz0, wa_zero_right]`. Conclude with `(mul_eq_zero.mp h.symm).resolve_right (hg k)`.
-/
theorem wa_main {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) :
    ∀ (n : ℕ) (W : Submodule K (Fin r → K)), finrank K W = n →
      (∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0) →
      ∃ (m : ℕ) (b : Fin n → Fin r → K) (g : Fin n → K), (∀ i, b i ∈ W) ∧ 2 * m ≤ n ∧
        (∀ i j, S.h (b i) (b j) = wittMat n m g i j) ∧
        ∀ t : Fin n → K, (∀ i : Fin n, (i : ℕ) < m ∨ n ≤ (i : ℕ) + m → t i = 0) →
          ∑ i, S.c (t i) * g i * t i = 0 → t = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hW hnd
  by_cases hiso : ∃ x ∈ W, x ≠ 0 ∧ S.h x x = 0
  · obtain ⟨x, hxW, hx0, hxx⟩ := hiso
    obtain ⟨y, hyW, hxy, hyy⟩ := wa_hyp S W hnd x hxW hx0 hxx
    have hyx : S.h y x = 1 := by rw [wa_symm, hxy, map_one]
    have hf1 := wa_finrank_inf_ker W (waR S x) y hyW
      (by rw [waR_apply, hxy]; exact one_ne_zero)
    have hf2 := wa_finrank_inf_ker (W ⊓ LinearMap.ker (waR S x)) (waR S y) x
      (Submodule.mem_inf.mpr ⟨hxW, by rw [LinearMap.mem_ker, waR_apply, hxx]⟩)
      (by rw [waR_apply, hyx]; exact one_ne_zero)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 :=
      ⟨finrank K ↥(W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y)), by omega⟩
    obtain ⟨m', b', g', hb'W, hm', hgram', hani'⟩ := ih n' (by omega)
      (W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y)) (by omega)
      (wa_perp_nondeg S W hnd x y hxW hyW hxx hxy hyy)
    have hmem : ∀ j, b' j ∈ W ∧ S.h x (b' j) = 0 ∧ S.h y (b' j) = 0 := fun j => by
      have h := hb'W j
      rw [Submodule.mem_inf, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, waR_apply,
        waR_apply] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
    have hbx : ∀ j, S.h (b' j) x = 0 := fun j => by rw [wa_symm, (hmem j).2.1, map_zero]
    have hby : ∀ j, S.h (b' j) y = 0 := fun j => by rw [wa_symm, (hmem j).2.2, map_zero]
    refine ⟨m' + 1, waExt x y b', waExt 0 0 g', fun i => ?_, by omega, fun i j => ?_,
      fun t ht hsum => ?_⟩
    · rcases wa_cases3 i with rfl | rfl | ⟨j, rfl⟩
      · simpa using hxW
      · simpa using hyW
      · simpa using (hmem j).1
    · rw [wa_witt_apply]
      rcases wa_cases3 i with rfl | rfl | ⟨i, rfl⟩ <;>
        rcases wa_cases3 j with rfl | rfl | ⟨j, rfl⟩ <;>
        simp only [waExt_zero, waExt_last, waExt_mid, Fin.val_zero, Fin.val_last, Fin.val_succ,
          Fin.val_castSucc] <;>
        try simp only [true_and]
      · rw [hxx, if_neg (by omega), if_neg (by omega)]
      · rw [hxy, if_pos (by omega)]
      · have := j.2
        rw [(hmem j).2.1, if_neg (by omega), if_neg (by omega)]
      · rw [hyx, if_pos (by omega)]
      · rw [hyy, if_neg (by omega), if_neg (by omega)]
      · have := j.2
        rw [(hmem j).2.2, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        rw [hbx, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        rw [hby, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        have := j.2
        rw [hgram', wa_witt_apply]
        split_ifs <;> first | rfl | (exfalso; omega)
    · have ht0 : t 0 = 0 := ht 0 (Or.inl (by simp))
      have htl : t (Fin.last (n' + 1)) = 0 := ht _ (Or.inr (by simp only [Fin.val_last]; omega))
      have ht' : (fun j : Fin n' => t (Fin.castSucc j).succ) = 0 := by
        refine hani' _ (fun j hj => ht _ ?_) ?_
        · simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        · rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hsum
          simpa [ht0, htl, Fin.succ_last] using hsum
      funext i
      rcases wa_cases3 i with rfl | rfl | ⟨j, rfl⟩
      · exact ht0
      · exact htl
      · exact congrFun ht' j
  · have han : ∀ x ∈ W, S.h x x = 0 → x = 0 := fun x hx hxx => by
      by_contra h0
      exact hiso ⟨x, hx, h0, hxx⟩
    obtain ⟨b, hbW, hb0, hbo⟩ := wa_diag S n W hW han
    have hg : ∀ k, S.h (b k) (b k) ≠ 0 := fun k h => hb0 k (han _ (hbW k) h)
    refine ⟨0, b, fun k => S.h (b k) (b k), hbW, by omega, fun i j => ?_, fun t _ hsum => ?_⟩
    · rw [wa_witt_apply]
      have := i.2
      by_cases hij : i = j
      · subst hij
        rw [if_neg (by omega), if_pos ⟨rfl, by omega, by omega⟩]
      · rw [hbo i j hij, if_neg (by omega), if_neg (fun h => hij (Fin.ext h.1))]
    · have hz : ∀ k, S.h (b k) (∑ i, t i • b i) = t k * S.h (b k) (b k) := fun k => by
        rw [wa_sum_right, Finset.sum_eq_single k
          (fun i _ hik => by rw [hbo k i (Ne.symm hik), mul_zero]) (by simp)]
      have hzz : S.h (∑ i, t i • b i) (∑ i, t i • b i) = 0 := by
        rw [wa_sum_left]
        simp only [hz]
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
        beta_reduce
        ring
      have hz0 := han _ (W.sum_mem fun i _ => W.smul_mem _ (hbW i)) hzz
      funext k
      have h := hz k
      rw [hz0, wa_zero_right] at h
      exact (mul_eq_zero.mp h.symm).resolve_right (hg k)

end ReciprocityTheory.MultiplicativeHeights
