import Mathlib

/- English proof (translation)
Introduce `O S _ _ _ _ m hm n`. Proceed by induction on `n with`. Consider the case `zero`. Use `⟨⊥, Submodule.fg_bot, fun x => ⟨0, Submodule.zero_mem _, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[pow_zero, Ideal.one_eq_top]`.

Conclude with `Submodule.mem_top`. Consider the case `succ n ih`. Take `⟨N, hN, hx⟩` from `ih`. Take `⟨s, hs⟩ : (m ^ n).FG` from `IsNoetherian.noetherian (m ^ n)`. Establish `key : ∀ z : S, z ∈ Submodule.span S (s : Set S) → ∃ w ∈ Submodule.span O (s : Set S), z - w ∈ m ^ (n + 1)`.

Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Conclude with `⟨z, Submodule.subset_span hz, by rw [sub_self]; exact Submodule.zero_mem _⟩`. Consider the case `zero`.

Conclude with `⟨0, Submodule.zero_mem _, by rw [sub_self]; exact Submodule.zero_mem _⟩`. Consider the case `add z z' _ _ h h'`. Take `⟨w, hw, h⟩` from `h`. Take `⟨w', hw', h'⟩` from `h'`. Use `⟨w + w', Submodule.add_mem _ hw hw', ?_⟩` and prove the remaining obligations.

Establish `e : z + z' - (w + w') = (z - w) + (z' - w')` using `by ring`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ h h'`. Consider the case `smul c z hz h`. Take `⟨w, hw, h⟩` from `h`.

Take `⟨a, ha⟩` from `hm c`. Use `⟨a • w, Submodule.smul_mem _ a hw, ?_⟩` and prove the remaining obligations. Establish `hz' : z ∈ m ^ n`. Rewrite using `[← hs]`. Conclude with `hz`.

Establish `e : c • z - a • w = algebraMap O S a * (z - w) + z * (c - algebraMap O S a)`. Rewrite using `[Algebra.smul_def a w, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `Submodule.add_mem _ (Ideal.mul_mem_left _ _ h) ?_` and prove the remaining obligations.

Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul hz' ha`. Use `⟨N ⊔ Submodule.span O (s : Set S), hN.sup ⟨s, rfl⟩, fun x => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hxy⟩` from `hx x`. Rewrite `hxy` using `[← hs]`.

Take `⟨w, hw, h⟩` from `key (x - y) hxy`. Use `⟨y + w, Submodule.add_mem_sup hy hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_sub]`. Conclude with `h`.
-/
theorem UpperTheory.Reformulated.B.PointFinitePower.ptFin_pow :
    ∀ {O S : Type} [inst : CommRing O] [inst_1 : CommRing S]
    [inst_2 : Algebra O S] [IsNoetherianRing S] (m : Ideal S),
    (∀ (x : S), ∃ (a : O), x - (Algebra.algebraMap O S : O → S) a ∈ m) →
      ∀ (n : ℕ), ∃ (N : Submodule O S), N.FG ∧ ∀ (x : S), ∃ y ∈ N, x - y ∈ m ^ n := by
  intro O S _ _ _ _ m hm n
  induction n with
  | zero =>
    refine ⟨⊥, Submodule.fg_bot, fun x => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    obtain ⟨N, hN, hx⟩ := ih
    obtain ⟨s, hs⟩ : (m ^ n).FG := IsNoetherian.noetherian (m ^ n)
    have key : ∀ z : S, z ∈ Submodule.span S (s : Set S) →
        ∃ w ∈ Submodule.span O (s : Set S), z - w ∈ m ^ (n + 1) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        exact ⟨z, Submodule.subset_span hz, by rw [sub_self]; exact Submodule.zero_mem _⟩
      | zero =>
        exact ⟨0, Submodule.zero_mem _, by rw [sub_self]; exact Submodule.zero_mem _⟩
      | add z z' _ _ h h' =>
        obtain ⟨w, hw, h⟩ := h
        obtain ⟨w', hw', h'⟩ := h'
        refine ⟨w + w', Submodule.add_mem _ hw hw', ?_⟩
        have e : z + z' - (w + w') = (z - w) + (z' - w') := by ring
        rw [e]
        exact Submodule.add_mem _ h h'
      | smul c z hz h =>
        obtain ⟨w, hw, h⟩ := h
        obtain ⟨a, ha⟩ := hm c
        refine ⟨a • w, Submodule.smul_mem _ a hw, ?_⟩
        have hz' : z ∈ m ^ n := by
          rw [← hs]
          exact hz
        have e : c • z - a • w
            = algebraMap O S a * (z - w) + z * (c - algebraMap O S a) := by
          rw [Algebra.smul_def a w, smul_eq_mul]
          ring
        rw [e]
        refine Submodule.add_mem _ (Ideal.mul_mem_left _ _ h) ?_
        rw [pow_succ]
        exact Ideal.mul_mem_mul hz' ha
    refine ⟨N ⊔ Submodule.span O (s : Set S), hN.sup ⟨s, rfl⟩, fun x => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hx x
    rw [← hs] at hxy
    obtain ⟨w, hw, h⟩ := key (x - y) hxy
    refine ⟨y + w, Submodule.add_mem_sup hy hw, ?_⟩
    rw [← sub_sub]
    exact h
