import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.T0.SpanTopOfComplete

/- English proof (translation)
Use `choose c y hcy using hS`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Set `xs : ℕ → N` to `fun k => Nat.rec x (fun _ z => y z) k`. Establish `hxs : ∀ k, xs (k + 1) = y (xs k)` using `fun k => rfl`.

Set `a : ℕ → Fin n → O` to `fun k i => ∑ j ∈ Finset.range k, ϖ ^ j * c (xs j) i`. Establish `hxa : ∀ k, x = ∑ i, a k i • S i + ϖ ^ k • xs k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [a, xs]`.

Consider the case `succ k ih`. Establish `hk` using `hcy (xs k)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hxs]`. Simplify using `only [a, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum, smul_smul, pow_succ]`.

Normalize the expressions using the abelian group laws. Establish `hmem : ∀ m k, m ≤ k → ∀ i, a k i - a m i ∈ Ideal.span {ϖ ^ m}`. Introduce `m k hmk i`. Establish `: a k i - a m i = ∑ j ∈ Finset.Ico m k, ϖ ^ j * c (xs j) i`. Simplify using `only [a]`.

Rewrite using `[← Finset.sum_range_add_sum_Ico _ hmk]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `Ideal.sum_mem _ fun j hj => ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_span_singleton]`.

Conclude with `Dvd.dvd.mul_right (pow_dvd_pow ϖ (Finset.mem_Ico.1 hj).1) _`. Establish `hpow : ∀ m : ℕ, (Ideal.span {ϖ} ^ m • ⊤ : Submodule O O) = Ideal.span {ϖ ^ m}`. Introduce `m`. Rewrite using `[Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top]`. Establish `hlim : ∀ i, ∃ L : O, ∀ k, a k i - L ∈ Ideal.span {ϖ ^ k}`.

Introduce `i`. Take `⟨L, hL⟩` from `IsPrecomplete.prec' (I := Ideal.span {ϖ}) (fun k => a k i) (fun {m k} hmk => by`. Rewrite using `[SModEq.sub_mem, hpow]`. Use `hmem m k hmk i` as an intermediate fact. Rewrite using `[← neg_sub]`.

Conclude with `(Ideal.neg_mem_iff _).2 this)`. Conclude with `⟨L, fun k => by have := hL k; rwa [SModEq.sub_mem, hpow] at this⟩`. Use `choose L hL using hlim`. Establish `hx : x = ∑ i, L i • S i`. Rewrite using `[← sub_eq_zero]`.

Use `hsep _ fun k => ?_` and prove the remaining obligations. Establish `ht : ∀ i, ∃ t : O, a k i - L i = ϖ ^ k * t` using `fun i => Ideal.mem_span_singleton'.1 (hL i k) |>.imp fun t ht => by rw [← ht, mul_comm]`. Use `choose t ht using ht`. Use `⟨∑ i, t i • S i + xs k, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [hxa k]`.

Establish `e : ∀ i, a k i • S i = L i • S i + ϖ ^ k • t i • S i`. Introduce `i`. Rewrite using `[smul_smul, ← ht i, sub_smul]`. Normalize the expressions using the abelian group laws. Simplify using `only [e, Finset.sum_add_distrib, smul_add, Finset.smul_sum]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hx]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem span_eq_top_of_complete {O N : Type*} [CommRing O] [AddCommGroup N] [Module O N] (ϖ : O)
    [IsPrecomplete (Ideal.span {ϖ}) O]
    (hsep : ∀ x : N, (∀ k : ℕ, ∃ y : N, x = ϖ ^ k • y) → x = 0) {n : ℕ} (S : Fin n → N)
    (hS : ∀ x : N, ∃ c : Fin n → O, ∃ y : N, x = ∑ i, c i • S i + ϖ • y) :
    Submodule.span O (Set.range S) = ⊤ := by
  classical
  choose c y hcy using hS
  rw [eq_top_iff]
  intro x _
  let xs : ℕ → N := fun k => Nat.rec x (fun _ z => y z) k
  have hxs : ∀ k, xs (k + 1) = y (xs k) := fun k => rfl
  let a : ℕ → Fin n → O := fun k i => ∑ j ∈ Finset.range k, ϖ ^ j * c (xs j) i
  have hxa : ∀ k, x = ∑ i, a k i • S i + ϖ ^ k • xs k := by
    intro k
    induction k with
    | zero => simp [a, xs]
    | succ k ih =>
      have hk := hcy (xs k)
      calc x = ∑ i, a k i • S i + ϖ ^ k • xs k := ih
        _ = ∑ i, a k i • S i + ϖ ^ k • (∑ i, c (xs k) i • S i + ϖ • y (xs k)) := by rw [← hk]
        _ = ∑ i, a (k + 1) i • S i + ϖ ^ (k + 1) • xs (k + 1) := by
          rw [hxs]
          simp only [a, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum,
            smul_smul, pow_succ]
          abel

  have hmem : ∀ m k, m ≤ k → ∀ i, a k i - a m i ∈ Ideal.span {ϖ ^ m} := by
    intro m k hmk i
    have : a k i - a m i = ∑ j ∈ Finset.Ico m k, ϖ ^ j * c (xs j) i := by
      simp only [a]
      rw [← Finset.sum_range_add_sum_Ico _ hmk]
      ring
    rw [this]
    refine Ideal.sum_mem _ fun j hj => ?_
    rw [Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_right (pow_dvd_pow ϖ (Finset.mem_Ico.1 hj).1) _
  have hpow : ∀ m : ℕ, (Ideal.span {ϖ} ^ m • ⊤ : Submodule O O) = Ideal.span {ϖ ^ m} := by
    intro m
    rw [Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top]
  have hlim : ∀ i, ∃ L : O, ∀ k, a k i - L ∈ Ideal.span {ϖ ^ k} := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {ϖ}) (fun k => a k i) (fun {m k} hmk => by
      rw [SModEq.sub_mem, hpow]
      have := hmem m k hmk i
      rw [← neg_sub]
      exact (Ideal.neg_mem_iff _).2 this)
    exact ⟨L, fun k => by have := hL k; rwa [SModEq.sub_mem, hpow] at this⟩
  choose L hL using hlim
  have hx : x = ∑ i, L i • S i := by
    rw [← sub_eq_zero]
    refine hsep _ fun k => ?_
    have ht : ∀ i, ∃ t : O, a k i - L i = ϖ ^ k * t := fun i => Ideal.mem_span_singleton'.1 (hL i k) |>.imp
      fun t ht => by rw [← ht, mul_comm]
    choose t ht using ht
    refine ⟨∑ i, t i • S i + xs k, ?_⟩
    conv_lhs => rw [hxa k]
    have e : ∀ i, a k i • S i = L i • S i + ϖ ^ k • t i • S i := by
      intro i
      rw [smul_smul, ← ht i, sub_smul]
      abel
    simp only [e, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
    abel
  rw [hx]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end ReciprocityTheory.ChartRestriction.G.T0.SpanTopOfComplete
