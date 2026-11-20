import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `N _ p Φ M D F hDM hΦM hΦD hΦF hFmono hpM hpD hFcomp hFclosed hnil hpcomp hpclosed`. Establish `hiterM : ∀ (i : ℕ) (x : N), x ∈ M → Φ^[i] x ∈ M`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro x hx`.

Simplify using `using hx`. Consider the case `succ i ih => intro x hx`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `hΦM _ (ih x hx)`. Establish `htel : ∀ (x : N) (m : ℕ), Φ (∑ i ∈ Finset.range m, Φ^[i] x) - ∑ i ∈ Finset.range m, Φ^[i] x = Φ^[m] x - x`.

Introduce `x m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[Finset.sum_range_succ, map_add, Function.iterate_succ_apply']`.

Establish `hsplit : ∀ a b : N, Φ a + Φ b - (a + b) = (Φ a - a) + (Φ b - b)` using `fun a b => by abel`. Rewrite using `[hsplit, ih]`. Normalize the expressions using the abelian group laws. Establish `step : ∀ z ∈ M, Φ z - z ∈ D → ∃ d ∈ D, ∃ r, z - d = p • r ∧ r ∈ M ∧ Φ r - r ∈ D`. Introduce `z hzM hzD`.

Establish `hiter : ∀ j : ℕ, Φ^[j] z - z ∈ D`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`.

Rewrite using `[Function.iterate_succ_apply']`. Establish `h : Φ (Φ^[j] z) - z = Φ (Φ^[j] z - z) + (Φ z - z)` using `by rw [map_sub]; abel`. Rewrite using `[h]`. Conclude with `D.add_mem (hΦD _ ih) hzD`. Establish `happrox : ∀ m, ∃ d ∈ D, z - d ∈ F m`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Take `⟨j, d, hd, hj⟩` from `hnil z hzM`. Use `⟨d - (Φ^[j] z - z), D.sub_mem hd (hiter j), ?_⟩` and prove the remaining obligations.

Establish `h : z - (d - (Φ^[j] z - z)) = Φ^[j] z - d` using `by abel`. Rewrite using `[h]`. Conclude with `hj`. Consider the case `succ m ih`. Take `⟨d, hd, hm⟩` from `ih`.

Use `⟨Φ d - (Φ z - z), D.sub_mem (hΦD d hd) hzD, ?_⟩` and prove the remaining obligations. Establish `h : z - (Φ d - (Φ z - z)) = Φ (z - d)` using `by rw [map_sub]; abel`. Rewrite using `[h]`. Conclude with `hΦF m _ hm`. Take `⟨d, hd, r, hr⟩` from `hFclosed z happrox`.

Establish `hpr : p • r ∈ M` using `by rw [← hr]; exact M.sub_mem hzM (hDM hd)`. Use `⟨d, hd, r, hr, hpM r hpr, hpD _ ?_⟩` and prove the remaining obligations. Establish `h : p • (Φ r - r) = (Φ z - z) - (Φ d - d)`. Rewrite using `[smul_sub, ← map_nsmul, ← hr, map_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[h]`. Conclude with `D.sub_mem hzD (D.sub_mem (hΦD d hd) hd)`. Establish `hinj : ∀ z ∈ M, Φ z - z ∈ D → z ∈ D`. Introduce `z hzM hzD`. Establish `key : ∀ k : ℕ, ∃ d ∈ D, ∃ r, z - d = p ^ k • r ∧ r ∈ M ∧ Φ r - r ∈ D`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, D.zero_mem, z, by simp, hzM, hzD⟩`. Consider the case `succ k ih`. Take `⟨d, hd, r, hr, hrM, hrD⟩` from `ih`.

Take `⟨d', hd', r', hr', hr'M, hr'D⟩` from `step r hrM hrD`. Use `⟨d + p ^ k • d', D.add_mem hd (nsmul_mem hd' _), r', ?_, hr'M, hr'D⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Apply `hpclosed` to reduce the goal to its premises. Introduce `k`.

Take `⟨d, hd, r, hr, -, -⟩` from `key k`. Conclude with `⟨d, hd, r, hr⟩`. Establish `step1 : ∀ y ∈ M, ∃ z ∈ M, ∃ d ∈ D, ∃ r, y - (Φ z - z) - d = p • r`. Introduce `y hyM`. Take `⟨j, d, hd, hj⟩` from `hnil y hyM`.

Take `⟨e, he⟩ : ∃ e, e = Φ^[j] y - d` from `⟨_, rfl⟩`. Rewrite `hj` using `[← he]`. Establish `heM : e ∈ M` using `by rw [he]; exact M.sub_mem (hiterM j y hyM) (hDM hd)`. Establish `hfF : ∀ i, Φ^[i] e ∈ F i`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero => simpa using hj`. Consider the case `succ i ih => rw [Function.iterate_succ_apply']`. Conclude with `hΦF i _ ih`. Take `⟨s, hsM, hs⟩` from `hFcomp (fun i => Φ^[i] e) (fun i => hiterM i e heM) hfF`.

Establish `hx : ∀ m, Φ s - s + e ∈ F m`. Introduce `m`. Establish `hsm : s - ∑ i ∈ Finset.range m, Φ^[i] e ∈ F m` using `hs m`. Establish `ht` using `htel e m`. Generalize the expression as in `∑ i ∈ Finset.range m, Φ^[i] e = S at hsm ht`.

Establish `h : Φ s - s + e = (Φ (s - S) - (s - S)) + Φ^[m] e`. Rewrite using `[map_sub, ← sub_add_cancel (Φ^[m] e) e, ← ht]`. Normalize the expressions using the abelian group laws. Rewrite using `[h]`. Conclude with `add_mem (sub_mem (hFmono m (hΦF m _ hsm)) hsm) (hfF m)`.

Take `⟨d', hd', r, hr⟩` from `hFclosed (Φ s - s + e) (fun m => ⟨0, D.zero_mem, by rw [sub_zero]; exact hx m⟩)`. Use `⟨-(∑ i ∈ Finset.range j, Φ^[i] y + s), M.neg_mem (M.add_mem (sum_mem fun i _ => hiterM i y hyM) hsM), d + d', D.add_mem hd hd', r, ?_⟩` and prove the remaining obligations. Establish `hT` using `htel y j`. Generalize the expression as in `∑ i ∈ Finset.range j, Φ^[i] y = T at hT ⊢`. Rewrite using `[← hr, map_neg, map_add, he, show Φ^[j] y = Φ T - T + y by rw [hT]; abel]`.

Normalize the expressions using the abelian group laws. Use `choose! Z hZM Dd hDd R hR using step1`. Establish `hRM : ∀ y ∈ M, R y ∈ M`. Introduce `y hy`. Apply `hpM` to reduce the goal to its premises.

Rewrite using `[← hR y hy]`. Conclude with `M.sub_mem (M.sub_mem hy (M.sub_mem (hΦM _ (hZM y hy)) (hZM y hy))) (hDM (hDd y hy))`. Establish `hsurj : ∀ y ∈ M, ∃ z ∈ M, y - (Φ z - z) ∈ D`. Introduce `y hyM`. Establish `hys : ∀ k, R^[k] y ∈ M`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hyM`. Consider the case `succ k ih => rw [Function.iterate_succ_apply']`. Conclude with `hRM _ ih`.

Establish `hexp : ∀ k, y - ∑ i ∈ Finset.range k, p ^ i • (Φ (Z (R^[i] y)) - Z (R^[i] y)) - ∑ i ∈ Finset.range k, p ^ i • Dd (R^[i] y) = p ^ k • R^[k] y`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ, Function.iterate_succ_apply', pow_succ, mul_smul, ← hR _ (hys k), smul_sub (p ^ k) (R^[k] y - _), smul_sub (p ^ k) (R^[k] y), ← ih]`. Normalize the expressions using the abelian group laws. Take `⟨W, hWM, hW⟩` from `hpcomp (fun i => Z (R^[i] y)) (fun i => hZM _ (hys i))`. Use `⟨W, hWM, hpclosed _ ?_⟩` and prove the remaining obligations. Introduce `k`.

Take `⟨r, hr⟩` from `hW k`. Use `⟨∑ i ∈ Finset.range k, p ^ i • Dd (R^[i] y), sum_mem fun i _ => nsmul_mem (hDd _ (hys i)) _, R^[k] y - (Φ r - r), ?_⟩` and prove the remaining obligations. Establish `hsum : Φ (∑ i ∈ Finset.range k, p ^ i • Z (R^[i] y)) - ∑ i ∈ Finset.range k, p ^ i • Z (R^[i] y) = ∑ i ∈ Finset.range k, p ^ i • (Φ (Z (R^[i] y)) - Z (R^[i] y))`. Rewrite using `[map_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_nsmul, smul_sub]`. Establish `hWe : W = ∑ i ∈ Finset.range k, p ^ i • Z (R^[i] y) + p ^ k • r` using `by rw [← hr]; abel`. Rewrite using `[hWe, map_add, map_nsmul, smul_sub (p ^ k) (R^[k] y), smul_sub (p ^ k) (Φ r), ← hexp k, ← hsum]`. Normalize the expressions using the abelian group laws. Conclude with `⟨hsurj, hinj⟩`.
-/
theorem sub_one_bijective_quotient_of_topNilpotent :
    ∀ (N : Type) [AddCommGroup N] (p : ℕ) (Φ : N →+ N) (M D : AddSubgroup N) (F : ℕ → AddSubgroup N), D ≤ M → (∀ x ∈ M, Φ x ∈ M) → (∀ x ∈ D, Φ x ∈ D) → (∀ m, ∀ x ∈ F m, Φ x ∈ F (m + 1)) → (∀ m, F (m + 1) ≤ F m) → (∀ x, p • x ∈ M → x ∈ M) → (∀ x, p • x ∈ D → x ∈ D) → (∀ f : ℕ → N, (∀ i, f i ∈ M) → (∀ i, f i ∈ F i) → ∃ s ∈ M, ∀ m, s - ∑ i ∈ Finset.range m, f i ∈ F m) → (∀ x, (∀ m, ∃ d ∈ D, x - d ∈ F m) → ∃ d ∈ D, ∃ r, x - d = p • r) → (∀ y ∈ M, ∃ j : ℕ, ∃ d ∈ D, Φ^[j] y - d ∈ F 0) → (∀ x : ℕ → N, (∀ i, x i ∈ M) → ∃ s ∈ M, ∀ k, ∃ r, s - ∑ i ∈ Finset.range k, p ^ i • x i = p ^ k • r) → (∀ x, (∀ k : ℕ, ∃ d ∈ D, ∃ r, x - d = p ^ k • r) → x ∈ D) → (∀ y ∈ M, ∃ z ∈ M, y - (Φ z - z) ∈ D) ∧ (∀ z ∈ M, Φ z - z ∈ D → z ∈ D) := by
  intro N _ p Φ M D F hDM hΦM hΦD hΦF hFmono hpM hpD hFcomp hFclosed hnil hpcomp hpclosed
  have hiterM : ∀ (i : ℕ) (x : N), x ∈ M → Φ^[i] x ∈ M := by
    intro i
    induction i with
    | zero => intro x hx; simpa using hx
    | succ i ih => intro x hx; rw [Function.iterate_succ_apply']; exact hΦM _ (ih x hx)
  have htel : ∀ (x : N) (m : ℕ), Φ (∑ i ∈ Finset.range m, Φ^[i] x) - ∑ i ∈ Finset.range m, Φ^[i] x = Φ^[m] x - x := by
    intro x m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, map_add, Function.iterate_succ_apply']
      have hsplit : ∀ a b : N, Φ a + Φ b - (a + b) = (Φ a - a) + (Φ b - b) := fun a b => by abel
      rw [hsplit, ih]
      abel
  have step : ∀ z ∈ M, Φ z - z ∈ D → ∃ d ∈ D, ∃ r, z - d = p • r ∧ r ∈ M ∧ Φ r - r ∈ D := by
    intro z hzM hzD
    have hiter : ∀ j : ℕ, Φ^[j] z - z ∈ D := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        have h : Φ (Φ^[j] z) - z = Φ (Φ^[j] z - z) + (Φ z - z) := by rw [map_sub]; abel
        rw [h]
        exact D.add_mem (hΦD _ ih) hzD
    have happrox : ∀ m, ∃ d ∈ D, z - d ∈ F m := by
      intro m
      induction m with
      | zero =>
        obtain ⟨j, d, hd, hj⟩ := hnil z hzM
        refine ⟨d - (Φ^[j] z - z), D.sub_mem hd (hiter j), ?_⟩
        have h : z - (d - (Φ^[j] z - z)) = Φ^[j] z - d := by abel
        rw [h]
        exact hj
      | succ m ih =>
        obtain ⟨d, hd, hm⟩ := ih
        refine ⟨Φ d - (Φ z - z), D.sub_mem (hΦD d hd) hzD, ?_⟩
        have h : z - (Φ d - (Φ z - z)) = Φ (z - d) := by rw [map_sub]; abel
        rw [h]
        exact hΦF m _ hm
    obtain ⟨d, hd, r, hr⟩ := hFclosed z happrox
    have hpr : p • r ∈ M := by rw [← hr]; exact M.sub_mem hzM (hDM hd)
    refine ⟨d, hd, r, hr, hpM r hpr, hpD _ ?_⟩
    have h : p • (Φ r - r) = (Φ z - z) - (Φ d - d) := by
      rw [smul_sub, ← map_nsmul, ← hr, map_sub]
      abel
    rw [h]
    exact D.sub_mem hzD (D.sub_mem (hΦD d hd) hd)
  have hinj : ∀ z ∈ M, Φ z - z ∈ D → z ∈ D := by
    intro z hzM hzD
    have key : ∀ k : ℕ, ∃ d ∈ D, ∃ r, z - d = p ^ k • r ∧ r ∈ M ∧ Φ r - r ∈ D := by
      intro k
      induction k with
      | zero => exact ⟨0, D.zero_mem, z, by simp, hzM, hzD⟩
      | succ k ih =>
        obtain ⟨d, hd, r, hr, hrM, hrD⟩ := ih
        obtain ⟨d', hd', r', hr', hr'M, hr'D⟩ := step r hrM hrD
        refine ⟨d + p ^ k • d', D.add_mem hd (nsmul_mem hd' _), r', ?_, hr'M, hr'D⟩
        calc z - (d + p ^ k • d') = p ^ k • (r - d') := by rw [smul_sub, ← hr]; abel
          _ = p ^ (k + 1) • r' := by rw [hr', pow_succ, mul_smul]
    apply hpclosed
    intro k
    obtain ⟨d, hd, r, hr, -, -⟩ := key k
    exact ⟨d, hd, r, hr⟩
  have step1 : ∀ y ∈ M, ∃ z ∈ M, ∃ d ∈ D, ∃ r, y - (Φ z - z) - d = p • r := by
    intro y hyM
    obtain ⟨j, d, hd, hj⟩ := hnil y hyM
    obtain ⟨e, he⟩ : ∃ e, e = Φ^[j] y - d := ⟨_, rfl⟩
    rw [← he] at hj
    have heM : e ∈ M := by rw [he]; exact M.sub_mem (hiterM j y hyM) (hDM hd)
    have hfF : ∀ i, Φ^[i] e ∈ F i := by
      intro i
      induction i with
      | zero => simpa using hj
      | succ i ih => rw [Function.iterate_succ_apply']; exact hΦF i _ ih
    obtain ⟨s, hsM, hs⟩ := hFcomp (fun i => Φ^[i] e) (fun i => hiterM i e heM) hfF
    have hx : ∀ m, Φ s - s + e ∈ F m := by
      intro m
      have hsm : s - ∑ i ∈ Finset.range m, Φ^[i] e ∈ F m := hs m
      have ht := htel e m
      generalize ∑ i ∈ Finset.range m, Φ^[i] e = S at hsm ht
      have h : Φ s - s + e = (Φ (s - S) - (s - S)) + Φ^[m] e := by
        rw [map_sub, ← sub_add_cancel (Φ^[m] e) e, ← ht]
        abel
      rw [h]
      exact add_mem (sub_mem (hFmono m (hΦF m _ hsm)) hsm) (hfF m)
    obtain ⟨d', hd', r, hr⟩ := hFclosed (Φ s - s + e) (fun m => ⟨0, D.zero_mem, by rw [sub_zero]; exact hx m⟩)
    refine ⟨-(∑ i ∈ Finset.range j, Φ^[i] y + s),
      M.neg_mem (M.add_mem (sum_mem fun i _ => hiterM i y hyM) hsM), d + d', D.add_mem hd hd', r, ?_⟩
    have hT := htel y j
    generalize ∑ i ∈ Finset.range j, Φ^[i] y = T at hT ⊢
    rw [← hr, map_neg, map_add, he, show Φ^[j] y = Φ T - T + y by rw [hT]; abel]
    abel
  choose! Z hZM Dd hDd R hR using step1
  have hRM : ∀ y ∈ M, R y ∈ M := by
    intro y hy
    apply hpM
    rw [← hR y hy]
    exact M.sub_mem (M.sub_mem hy (M.sub_mem (hΦM _ (hZM y hy)) (hZM y hy))) (hDM (hDd y hy))
  have hsurj : ∀ y ∈ M, ∃ z ∈ M, y - (Φ z - z) ∈ D := by
    intro y hyM
    have hys : ∀ k, R^[k] y ∈ M := by
      intro k
      induction k with
      | zero => simpa using hyM
      | succ k ih => rw [Function.iterate_succ_apply']; exact hRM _ ih
    have hexp : ∀ k, y - ∑ i ∈ Finset.range k, p ^ i • (Φ (Z (R^[i] y)) - Z (R^[i] y))
        - ∑ i ∈ Finset.range k, p ^ i • Dd (R^[i] y) = p ^ k • R^[k] y := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Function.iterate_succ_apply', pow_succ,
          mul_smul, ← hR _ (hys k), smul_sub (p ^ k) (R^[k] y - _), smul_sub (p ^ k) (R^[k] y), ← ih]
        abel
    obtain ⟨W, hWM, hW⟩ := hpcomp (fun i => Z (R^[i] y)) (fun i => hZM _ (hys i))
    refine ⟨W, hWM, hpclosed _ ?_⟩
    intro k
    obtain ⟨r, hr⟩ := hW k
    refine ⟨∑ i ∈ Finset.range k, p ^ i • Dd (R^[i] y),
      sum_mem fun i _ => nsmul_mem (hDd _ (hys i)) _, R^[k] y - (Φ r - r), ?_⟩
    have hsum : Φ (∑ i ∈ Finset.range k, p ^ i • Z (R^[i] y)) - ∑ i ∈ Finset.range k, p ^ i • Z (R^[i] y)
        = ∑ i ∈ Finset.range k, p ^ i • (Φ (Z (R^[i] y)) - Z (R^[i] y)) := by
      rw [map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_nsmul, smul_sub]
    have hWe : W = ∑ i ∈ Finset.range k, p ^ i • Z (R^[i] y) + p ^ k • r := by rw [← hr]; abel
    rw [hWe, map_add, map_nsmul, smul_sub (p ^ k) (R^[k] y), smul_sub (p ^ k) (Φ r), ← hexp k, ← hsum]
    abel
  exact ⟨hsurj, hinj⟩

end GlobalTheory
