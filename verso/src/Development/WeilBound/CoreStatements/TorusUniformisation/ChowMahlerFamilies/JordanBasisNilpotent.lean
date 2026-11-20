import Mathlib

namespace PositivityTheory.Xgn.JordanBasis

/- English proof (translation)
Establish `hd : Module.finrank k (W ⧸ LinearMap.range π) ≤ r`. Establish `h1` using `Submodule.finrank_quotient_add_finrank (LinearMap.range π)`. Establish `h2` using `LinearMap.finrank_range_add_finrank_ker π`. Use linear arithmetic over natural numbers and integers. Take `⟨g, hg⟩ : ∃ g : W ⧸ LinearMap.range π → W, ∀ q, (LinearMap.range π).mkQ (g q) = q` from `⟨_, Function.surjInv_eq (LinearMap.range π).mkQ_surjective⟩`.

Set `b` to `Module.finBasis k (W ⧸ LinearMap.range π)`. Set `x : Fin r → W` to `fun i => if h : (i : ℕ) < Module.finrank k (W ⧸ LinearMap.range π) then g (b ⟨i, h⟩) else 0`. Establish `hspan : ∀ j, g (b j) ∈ Submodule.span k (Set.range x)`. Introduce `j`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨⟨j, lt_of_lt_of_le j.2 hd⟩, ?_⟩` and prove the remaining obligations. Simplify using `[x, j.2]`. Use `⟨x, fun v => ?_⟩` and prove the remaining obligations. Use `⟨∑ j, b.repr ((LinearMap.range π).mkQ v) j • g (b j), Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hspan j), ?_⟩` and prove the remaining obligations. Establish `hq : (LinearMap.range π).mkQ (v - ∑ j, b.repr ((LinearMap.range π).mkQ v) j • g (b j)) = 0`.

Rewrite using `[map_sub, map_sum]`. Simplify using `only [map_smul, hg]`. Rewrite using `[b.sum_repr, sub_self]`. Rewrite `hq` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨u, hu⟩` from `LinearMap.mem_range.mp hq`.

Conclude with `⟨u, by rw [hu]; abel⟩`.
-/
theorem exists_span_sup_range {k W : Type} [Field k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (π : Module.End k W) (r : ℕ)
    (h : Module.finrank k (LinearMap.ker π) ≤ r) :
    ∃ x : Fin r → W, ∀ v : W, ∃ a ∈ Submodule.span k (Set.range x), ∃ u : W, v = a + π u := by
  classical
  have hd : Module.finrank k (W ⧸ LinearMap.range π) ≤ r := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range π)
    have h2 := LinearMap.finrank_range_add_finrank_ker π
    omega
  obtain ⟨g, hg⟩ : ∃ g : W ⧸ LinearMap.range π → W, ∀ q, (LinearMap.range π).mkQ (g q) = q :=
    ⟨_, Function.surjInv_eq (LinearMap.range π).mkQ_surjective⟩
  let b := Module.finBasis k (W ⧸ LinearMap.range π)
  let x : Fin r → W := fun i =>
    if h : (i : ℕ) < Module.finrank k (W ⧸ LinearMap.range π) then g (b ⟨i, h⟩) else 0
  have hspan : ∀ j, g (b j) ∈ Submodule.span k (Set.range x) := by
    intro j
    apply Submodule.subset_span
    refine ⟨⟨j, lt_of_lt_of_le j.2 hd⟩, ?_⟩
    simp [x, j.2]
  refine ⟨x, fun v => ?_⟩
  refine ⟨∑ j, b.repr ((LinearMap.range π).mkQ v) j • g (b j),
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hspan j), ?_⟩
  have hq : (LinearMap.range π).mkQ
      (v - ∑ j, b.repr ((LinearMap.range π).mkQ v) j • g (b j)) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_smul, hg]
    rw [b.sum_repr, sub_self]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hq
  exact ⟨u, by rw [hu]; abel⟩

/- English proof (translation)
Use `set S := Submodule.span k (Set.range fun q : Fin r × Fin e => (π ^ (q.2 : ℕ)) (x q.1)) with hS`. Break down `Nat.eq_zero_or_pos e with he | he` into its components or cases. Substitute `he` using the available equality. Rewrite `hπ` using `[pow_zero]`. Use `Submodule.eq_top_iff'.2 fun v => ?_` and prove the remaining obligations.

Establish `hv : v = 0` using `by simpa using LinearMap.congr_fun hπ v`. Rewrite using `[hv]`. Conclude with `S.zero_mem`. Establish `hinv : ∀ s ∈ S, π s ∈ S`. Introduce `s hs`.

Use `Submodule.span_induction (p := fun s _ => π s ∈ S) ?_ ?_ ?_ ?_ hs` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨i, j⟩, rfl⟩`. Distinguish the cases in `hj : (j : ℕ) + 1 < e`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨(i, ⟨(j : ℕ) + 1, hj⟩), ?_⟩` and prove the remaining obligations.

Simplify using `[pow_succ', Module.End.mul_apply]`. Establish `hje : (j : ℕ) + 1 = e` using `by omega`. Establish `h0 : π ((π ^ (j : ℕ)) (x i)) = 0`. Establish `h1 : (π ^ ((j : ℕ) + 1)) (x i) = π ((π ^ (j : ℕ)) (x i))`. Rewrite using `[pow_succ', Module.End.mul_apply]`.

Rewrite using `[← h1, hje, hπ, LinearMap.zero_apply]`. Use `show π ((π ^ (j : ℕ)) (x i)) ∈ S`. Rewrite using `[h0]`. Conclude with `S.zero_mem`. Simplify using the standard rewrite rules.

Introduce `a c _ _ ha hc`. Rewrite using `[map_add]`. Conclude with `S.add_mem ha hc`. Introduce `c a _ ha`. Rewrite using `[map_smul]`.

Conclude with `S.smul_mem c ha`. Establish `hxS : ∀ a ∈ Submodule.span k (Set.range x), a ∈ S`. Introduce `a ha`. Use `Submodule.span_le.2 ?_ ha` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨(i, ⟨0, he⟩), by simp⟩`. Establish `hpow : ∀ n : ℕ, ∀ s ∈ S, (π ^ n) s ∈ S`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro s hs`. Simplify using `using hs`. Consider the case `succ n ih`. Introduce `s hs`. Rewrite using `[pow_succ', Module.End.mul_apply]`.

Conclude with `hinv _ (ih s hs)`. Establish `key : ∀ n : ℕ, ∀ v : W, ∃ s ∈ S, ∃ u : W, v = s + (π ^ n) u`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro v; exact ⟨0, S.zero_mem, v, by simp⟩`.

Consider the case `succ n ih`. Introduce `v`. Take `⟨s, hs, u, rfl⟩` from `ih v`. Take `⟨a, ha, u', rfl⟩` from `hx u`. Use `⟨s + (π ^ n) a, S.add_mem hs (hpow n a (hxS a ha)), u', ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, pow_succ, Module.End.mul_apply, add_assoc]`. Use `Submodule.eq_top_iff'.2 fun v => ?_` and prove the remaining obligations. Take `⟨s, hs, u, rfl⟩` from `key e v`. Rewrite using `[hπ, LinearMap.zero_apply, add_zero]`. Conclude with `hs`.
-/
theorem span_eq_top {k W : Type} [Field k] [AddCommGroup W] [Module k W]
    (π : Module.End k W) (e r : ℕ) (hπ : π ^ e = 0) (x : Fin r → W)
    (hx : ∀ v : W, ∃ a ∈ Submodule.span k (Set.range x), ∃ u : W, v = a + π u) :
    Submodule.span k (Set.range fun q : Fin r × Fin e => (π ^ (q.2 : ℕ)) (x q.1)) = ⊤ := by
  classical
  set S := Submodule.span k (Set.range fun q : Fin r × Fin e => (π ^ (q.2 : ℕ)) (x q.1)) with hS
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    rw [pow_zero] at hπ
    refine Submodule.eq_top_iff'.2 fun v => ?_
    have hv : v = 0 := by simpa using LinearMap.congr_fun hπ v
    rw [hv]
    exact S.zero_mem
  have hinv : ∀ s ∈ S, π s ∈ S := by
    intro s hs
    refine Submodule.span_induction (p := fun s _ => π s ∈ S) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨⟨i, j⟩, rfl⟩
      by_cases hj : (j : ℕ) + 1 < e
      · apply Submodule.subset_span
        refine ⟨(i, ⟨(j : ℕ) + 1, hj⟩), ?_⟩
        simp [pow_succ', Module.End.mul_apply]
      · have hje : (j : ℕ) + 1 = e := by omega
        have h0 : π ((π ^ (j : ℕ)) (x i)) = 0 := by
          have h1 : (π ^ ((j : ℕ) + 1)) (x i) = π ((π ^ (j : ℕ)) (x i)) := by
            rw [pow_succ', Module.End.mul_apply]
          rw [← h1, hje, hπ, LinearMap.zero_apply]
        show π ((π ^ (j : ℕ)) (x i)) ∈ S
        rw [h0]
        exact S.zero_mem
    · simp
    · intro a c _ _ ha hc
      rw [map_add]
      exact S.add_mem ha hc
    · intro c a _ ha
      rw [map_smul]
      exact S.smul_mem c ha
  have hxS : ∀ a ∈ Submodule.span k (Set.range x), a ∈ S := by
    intro a ha
    refine Submodule.span_le.2 ?_ ha
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    exact ⟨(i, ⟨0, he⟩), by simp⟩
  have hpow : ∀ n : ℕ, ∀ s ∈ S, (π ^ n) s ∈ S := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ n ih =>
      intro s hs
      rw [pow_succ', Module.End.mul_apply]
      exact hinv _ (ih s hs)
  have key : ∀ n : ℕ, ∀ v : W, ∃ s ∈ S, ∃ u : W, v = s + (π ^ n) u := by
    intro n
    induction n with
    | zero => intro v; exact ⟨0, S.zero_mem, v, by simp⟩
    | succ n ih =>
      intro v
      obtain ⟨s, hs, u, rfl⟩ := ih v
      obtain ⟨a, ha, u', rfl⟩ := hx u
      refine ⟨s + (π ^ n) a, S.add_mem hs (hpow n a (hxS a ha)), u', ?_⟩
      rw [map_add, pow_succ, Module.End.mul_apply, add_assoc]
  refine Submodule.eq_top_iff'.2 fun v => ?_
  obtain ⟨s, hs, u, rfl⟩ := key e v
  rw [hπ, LinearMap.zero_apply, add_zero]
  exact hs

end PositivityTheory.Xgn.JordanBasis
