import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNormOneOfPair
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomFix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

structure IsSelfDualMod (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) (M : AddSubgroup V) : Prop where
  smul_mem : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M
  int : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ S
  dual : ∀ x : V, (∀ m ∈ M, h m x ∈ S) → x ∈ M
  span : ∀ x : V, ∃ t : K, t ≠ 0 ∧ t • x ∈ M

variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}

/- English proof (translation)
Establish `hl : ∀ (c : K) (u w : V), h (c • u) w = star c * h u w`. Introduce `c u w`. Rewrite using `[LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]`. Establish `hr : ∀ (c : K) (u w : V), h u (c • w) = c * h u w`. Introduce `c u w`.

Simplify using the standard rewrite rules. Establish `hsym : ∀ u w : V, star (h u w) = h w u`. Introduce `u w`. Establish `hsu` using `hs.eq u w`. Rewrite `hsu` using `[starRingEnd_apply]`. Then use the resulting hypothesis.

Establish `hxx : h (x j) (x j) = 1`. Rewrite using `[hx]`. Simplify using the standard rewrite rules. Establish `hxj : ∀ i ∈ s, h (x i) (x j) = 0`. Introduce `i hi`.

Establish `hij : i ≠ j` using `fun e => hj (e ▸ hi)`. Rewrite using `[hx]`. Simplify using `[hij]`. Establish `hjx : ∀ i ∈ s, h (x j) (x i) = 0`. Introduce `i hi`.

Rewrite using `[← hsym, hxj i hi, star_zero]`. Take `⟨t, ht0, htM⟩` from `hM.span (x j)`. Establish `hmemA : ∀ a : K, a ∈ M.map (h (x j)).toAddMonoidHom ↔ ∃ m ∈ M, h (x j) m = a`. Introduce `a`. Rewrite using `[AddSubgroup.mem_map]`.

Both sides reduce to the same expression. Take `⟨α, hαA, hα0, hαS⟩` from `hS.principal (M.map (h (x j)).toAddMonoidHom) (by`. Introduce `r hr' a ha`. Take `⟨m, hm, rfl⟩` from `(hmemA a).1 ha`. Conclude with `(hmemA _).2 ⟨r • m, hM.smul_mem r hr' m hm, hr r _ _⟩)`.

Use the proof step `⟨t, (hmemA t).2 ⟨t • x j, htM, by rw [hr, hxx, mul_one]⟩, ht0⟩`. Use the proof step `⟨star t, star_ne_zero.2 ht0, fun a ha => by`. Take `⟨m, hm, rfl⟩` from `(hmemA a).1 ha`. Rewrite using `[← hl]`. Conclude with `hM.int _ htM m hm⟩`.

Take `⟨w1, hw1M, hw1⟩` from `(hmemA α).1 hαA`. Take `⟨a2, ha2⟩ : ∃ a2 : K, a2 = star α⁻¹` from `⟨_, rfl⟩`. Establish `ha20 : a2 ≠ 0`. Rewrite using `[ha2]`. Conclude with `star_ne_zero.2 (inv_ne_zero hα0)`.

Establish `hvM : a2 • x j ∈ M`. Apply `hM.dual` to reduce the goal to its premises. Introduce `m hm`. Rewrite using `[hr, ← hsym]`. Establish `h1` using `hS.star_mem _ (hαS _ ((hmemA _).2 ⟨m, hm, rfl⟩))`.

Rewrite `h1` using `[star_mul', ← ha2, mul_comm]`. Conclude with `h1`. Establish `hcM : ∀ i ∈ s, (h (x i) w1) • x i ∈ M` using `fun i hi => hM.smul_mem _ (hM.int _ (hxM i hi) _ hw1M) _ (hxM i hi)`. Establish `hw0M : w1 - ∑ i ∈ s, (h (x i) w1) • x i ∈ M` using `M.sub_mem hw1M (M.sum_mem hcM)`. Establish `hw0o : ∀ k ∈ s, h (x k) (w1 - ∑ i ∈ s, (h (x i) w1) • x i) = 0`.

Introduce `k hk`. Rewrite using `[map_sub, map_sum]`. Simplify using `only [hr, hx]`. Simplify using `[Finset.sum_ite_eq, Finset.sum_ite_eq', hk]`. Establish `hvw : h (a2 • x j) (w1 - ∑ i ∈ s, (h (x i) w1) • x i) = 1`.

Rewrite using `[map_sub, map_sum, Finset.sum_eq_zero, sub_zero, hl, hw1, ha2, star_star, inv_mul_cancel₀ hα0]`. Introduce `i hi`. Rewrite using `[hr, hl, hjx i hi, mul_zero, mul_zero]`. Establish `hvvS : star a2 * a2 ∈ S`. Use `hM.int _ hvM _ hvM` as an intermediate fact.

Rewrite `this` using `[hl, hr, hxx, mul_one]`. Then use the resulting hypothesis. Take `⟨b, hb1, hbS⟩` from `exists_norm_one_mul_mem hS hvvS`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hb1`.

Take `⟨c, hc, d, hd, hcd⟩` from `exists_norm_one_of_pair hS hs (y := b • a2 • x j) (w := b • (w1 - ∑ i ∈ s, (h (x i) w1) • x i)) (a := a2 * b) hbS (mul_ne_zero ha20 hb0) (by rw [hl, hr, hl, hr, hxx, star_mul']; ring) (by rw [hl, hr, hvw, mul_one, hb1]) (by rw [hl, hr, ← mul_assoc, hb1, one_mul]; exact hM.int _ h …`. Use `⟨c • (w1 - ∑ i ∈ s, (h (x i) w1) • x i) + d • a2 • x j, M.add_mem (hM.smul_mem c hc _ hw0M) (hM.smul_mem d hd _ hvM), ?_, ?_⟩` and prove the remaining obligations. Rewrite `hcd` using `[smul_comm c b, smul_comm d b, ← smul_add, hl, hr, ← mul_assoc, hb1, one_mul]`. Conclude with `hcd`. Introduce `i hi`.

Rewrite using `[map_add, hr, hr, hw0o i hi, hr, hxj i hi]`. Simplify using the standard rewrite rules.
-/
theorem exists_next (hS : IsHermSemilocal S) (hs : h.IsSymm) (hM : IsSelfDualMod S h M)
    {ι : Type*} [DecidableEq ι] (x : ι → V) (hx : ∀ i j, h (x i) (x j) = if i = j then 1 else 0)
    (s : Finset ι) (hxM : ∀ i ∈ s, x i ∈ M) (j : ι) (hj : j ∉ s) :
    ∃ z ∈ M, h z z = 1 ∧ ∀ i ∈ s, h (x i) z = 0 := by
  have hl : ∀ (c : K) (u w : V), h (c • u) w = star c * h u w := by
    intro c u w
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]
  have hr : ∀ (c : K) (u w : V), h u (c • w) = c * h u w := by
    intro c u w
    simp
  have hsym : ∀ u w : V, star (h u w) = h w u := by
    intro u w
    have hsu := hs.eq u w
    rwa [starRingEnd_apply] at hsu
  have hxx : h (x j) (x j) = 1 := by
    rw [hx]
    simp
  have hxj : ∀ i ∈ s, h (x i) (x j) = 0 := by
    intro i hi
    have hij : i ≠ j := fun e => hj (e ▸ hi)
    rw [hx]
    simp [hij]
  have hjx : ∀ i ∈ s, h (x j) (x i) = 0 := by
    intro i hi
    rw [← hsym, hxj i hi, star_zero]
  obtain ⟨t, ht0, htM⟩ := hM.span (x j)
  have hmemA : ∀ a : K, a ∈ M.map (h (x j)).toAddMonoidHom ↔ ∃ m ∈ M, h (x j) m = a := by
    intro a
    rw [AddSubgroup.mem_map]
    rfl
  obtain ⟨α, hαA, hα0, hαS⟩ := hS.principal (M.map (h (x j)).toAddMonoidHom)
    (by
      intro r hr' a ha
      obtain ⟨m, hm, rfl⟩ := (hmemA a).1 ha
      exact (hmemA _).2 ⟨r • m, hM.smul_mem r hr' m hm, hr r _ _⟩)
    ⟨t, (hmemA t).2 ⟨t • x j, htM, by rw [hr, hxx, mul_one]⟩, ht0⟩
    ⟨star t, star_ne_zero.2 ht0, fun a ha => by
      obtain ⟨m, hm, rfl⟩ := (hmemA a).1 ha
      rw [← hl]
      exact hM.int _ htM m hm⟩
  obtain ⟨w1, hw1M, hw1⟩ := (hmemA α).1 hαA
  obtain ⟨a2, ha2⟩ : ∃ a2 : K, a2 = star α⁻¹ := ⟨_, rfl⟩
  have ha20 : a2 ≠ 0 := by
    rw [ha2]
    exact star_ne_zero.2 (inv_ne_zero hα0)
  have hvM : a2 • x j ∈ M := by
    apply hM.dual
    intro m hm
    rw [hr, ← hsym]
    have h1 := hS.star_mem _ (hαS _ ((hmemA _).2 ⟨m, hm, rfl⟩))
    rw [star_mul', ← ha2, mul_comm] at h1
    exact h1
  have hcM : ∀ i ∈ s, (h (x i) w1) • x i ∈ M := fun i hi =>
    hM.smul_mem _ (hM.int _ (hxM i hi) _ hw1M) _ (hxM i hi)
  have hw0M : w1 - ∑ i ∈ s, (h (x i) w1) • x i ∈ M :=
    M.sub_mem hw1M (M.sum_mem hcM)
  have hw0o : ∀ k ∈ s, h (x k) (w1 - ∑ i ∈ s, (h (x i) w1) • x i) = 0 := by
    intro k hk
    rw [map_sub, map_sum]
    simp only [hr, hx]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', hk]
  have hvw : h (a2 • x j) (w1 - ∑ i ∈ s, (h (x i) w1) • x i) = 1 := by
    rw [map_sub, map_sum, Finset.sum_eq_zero, sub_zero, hl, hw1, ha2, star_star,
      inv_mul_cancel₀ hα0]
    intro i hi
    rw [hr, hl, hjx i hi, mul_zero, mul_zero]
  have hvvS : star a2 * a2 ∈ S := by
    have := hM.int _ hvM _ hvM
    rwa [hl, hr, hxx, mul_one] at this
  obtain ⟨b, hb1, hbS⟩ := exists_norm_one_mul_mem hS hvvS
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb1
  obtain ⟨c, hc, d, hd, hcd⟩ := exists_norm_one_of_pair hS hs (y := b • a2 • x j)
    (w := b • (w1 - ∑ i ∈ s, (h (x i) w1) • x i)) (a := a2 * b) hbS (mul_ne_zero ha20 hb0)
    (by rw [hl, hr, hl, hr, hxx, star_mul']; ring)
    (by rw [hl, hr, hvw, mul_one, hb1])
    (by rw [hl, hr, ← mul_assoc, hb1, one_mul]; exact hM.int _ hw0M _ hw0M)
  refine ⟨c • (w1 - ∑ i ∈ s, (h (x i) w1) • x i) + d • a2 • x j,
    M.add_mem (hM.smul_mem c hc _ hw0M) (hM.smul_mem d hd _ hvM), ?_, ?_⟩
  · rw [smul_comm c b, smul_comm d b, ← smul_add, hl, hr, ← mul_assoc, hb1, one_mul] at hcd
    exact hcd
  · intro i hi
    rw [map_add, hr, hr, hw0o i hi, hr, hxj i hi]
    simp

/- English proof (translation)
Establish `hsym : ∀ u w : V, star (h u w) = h w u`. Introduce `u w`. Establish `hsu` using `hs.eq u w`. Rewrite `hsu` using `[starRingEnd_apply]`. Then use the resulting hypothesis. Establish `key : ∀ k : ℕ, k ≤ n → ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i : Fin n, (i : ℕ) < k → g (e i) ∈ M`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_`. Conclude with `⟨1, (Formalism.HermitianLatticesTheory.isom h).one_mem, fun i hi => absurd hi (Nat.not_lt_zero _)⟩`.

Consider the case `succ k ih`. Introduce `hk`. Take `⟨g, hg, hgM⟩` from `ih (Nat.le_of_succ_le hk)`. Establish `hgi : ∀ u w : V, h (g u) (g w) = h u w` using `hg`. Take `⟨kk, hkk⟩ : ∃ kk : Fin n, (kk : ℕ) = k` from `⟨⟨k, Nat.lt_of_succ_le hk⟩, rfl⟩`.

Establish `hxx : ∀ i j : Fin n, h (g (e i)) (g (e j)) = if i = j then 1 else 0`. Introduce `i j`. Rewrite using `[hgi, he]`. Take `⟨z, hzM, hzz, hzo⟩` from `exists_next hS hs hM (fun i => g (e i)) hxx (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)) (fun i hi => hgM i (Finset.mem_filter.1 hi).2) kk (by simp [hkk])`. Establish `hzo' : ∀ i : Fin n, (i : ℕ) < k → h (g (e i)) z = 0` using `fun i hi => hzo i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)`.

Establish `hk1 : h (g (e kk)) (g (e kk)) = 1`. Rewrite using `[hxx]`. Simplify using the standard rewrite rules. Take `⟨τ, hτ, hτk, hτfix⟩` from `exists_isom_fix hs hd hk1 hzz`. Use `⟨τ * g, (Formalism.HermitianLatticesTheory.isom h).mul_mem hτ hg, ?_⟩` and prove the remaining obligations.

Introduce `i hi`. Use `show τ (g (e i)) ∈ M`. Break down `Nat.lt_or_ge (i : ℕ) k with hlt | hge` into its components or cases. Establish `h1 : h (g (e kk)) (g (e i)) = 0`. Rewrite using `[hxx]`.

Establish `hne : kk ≠ i`. Introduce `h'`. Rewrite `hlt` using `[← h', hkk]`. Conclude with `lt_irrefl _ hlt`. Simplify using `[hne]`.

Establish `h2 : h z (g (e i)) = 0`. Rewrite using `[← hsym, hzo' i hlt, star_zero]`. Rewrite using `[hτfix _ h1 h2]`. Conclude with `hgM i hlt`. Establish `hik : i = kk` using `Fin.ext (by omega)`.

Rewrite using `[hik, hτk]`. Conclude with `hzM`. Take `⟨g, hg, hgM⟩` from `key n le_rfl`. Conclude with `⟨g, hg, fun i => hgM i i.isLt⟩`.
-/
theorem exists_isom_frame (hS : IsHermSemilocal S) (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0)
    (hM : IsSelfDualMod S h M) {n : ℕ} (e : Fin n → V)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i, g (e i) ∈ M := by
  have hsym : ∀ u w : V, star (h u w) = h w u := by
    intro u w
    have hsu := hs.eq u w
    rwa [starRingEnd_apply] at hsu
  have key : ∀ k : ℕ, k ≤ n → ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i : Fin n, (i : ℕ) < k → g (e i) ∈ M := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨1, (Formalism.HermitianLatticesTheory.isom h).one_mem, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨g, hg, hgM⟩ := ih (Nat.le_of_succ_le hk)
      have hgi : ∀ u w : V, h (g u) (g w) = h u w := hg
      obtain ⟨kk, hkk⟩ : ∃ kk : Fin n, (kk : ℕ) = k := ⟨⟨k, Nat.lt_of_succ_le hk⟩, rfl⟩
      have hxx : ∀ i j : Fin n, h (g (e i)) (g (e j)) = if i = j then 1 else 0 := by
        intro i j
        rw [hgi, he]
      obtain ⟨z, hzM, hzz, hzo⟩ := exists_next hS hs hM (fun i => g (e i)) hxx
        (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k))
        (fun i hi => hgM i (Finset.mem_filter.1 hi).2) kk (by simp [hkk])
      have hzo' : ∀ i : Fin n, (i : ℕ) < k → h (g (e i)) z = 0 := fun i hi =>
        hzo i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      have hk1 : h (g (e kk)) (g (e kk)) = 1 := by
        rw [hxx]
        simp
      obtain ⟨τ, hτ, hτk, hτfix⟩ := exists_isom_fix hs hd hk1 hzz
      refine ⟨τ * g, (Formalism.HermitianLatticesTheory.isom h).mul_mem hτ hg, ?_⟩
      intro i hi
      show τ (g (e i)) ∈ M
      rcases Nat.lt_or_ge (i : ℕ) k with hlt | hge
      · have h1 : h (g (e kk)) (g (e i)) = 0 := by
          rw [hxx]
          have hne : kk ≠ i := by
            intro h'
            rw [← h', hkk] at hlt
            exact lt_irrefl _ hlt
          simp [hne]
        have h2 : h z (g (e i)) = 0 := by
          rw [← hsym, hzo' i hlt, star_zero]
        rw [hτfix _ h1 h2]
        exact hgM i hlt
      · have hik : i = kk := Fin.ext (by omega)
        rw [hik, hτk]
        exact hzM
  obtain ⟨g, hg, hgM⟩ := key n le_rfl
  exact ⟨g, hg, fun i => hgM i i.isLt⟩

end Formalism.HermitianLattices.Ext.L3.WA
