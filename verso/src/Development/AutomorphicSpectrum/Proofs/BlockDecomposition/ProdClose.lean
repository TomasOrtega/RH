import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

open Filter Topology
open GlobalTheory.CompanionTheory.EGlue PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.MCl

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `zero => exact Multiset.nodup_zero`. Consider the case `@cons a b as bs hab hrel ih`. Establish `hgn : (b ::ₘ bs).Nodup` using `hg.1`. Establish `hb : b ∉ bs` using `(Multiset.nodup_cons.1 hgn).1`.

Establish `hg' : GapM bs`. Use `⟨(Multiset.nodup_cons.1 hgn).2, fun x hx y hy hxy => ?_⟩` and prove the remaining obligations. Conclude with `hg.2 x (Multiset.mem_cons_of_mem hx) y (Multiset.mem_cons_of_mem hy) hxy`. Use `Multiset.nodup_cons.2 ⟨fun ha => ?_, ih hg'⟩` and prove the remaining obligations. Take `⟨y, hy, hay⟩` from `Multiset.exists_mem_of_rel_of_mem hrel ha`.

Establish `hne : b ≠ y` using `fun e => hb (e ▸ hy)`. Establish `h1` using `hg.2 b (Multiset.mem_cons_self b bs) y (Multiset.mem_cons_of_mem hy) hne`. Establish `h2 : ‖b - y‖ ≤ ‖a - b‖ + ‖a - y‖`. Establish `: b - y = (a - y) - (a - b)` using `by ring`. Rewrite using `[this]`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nodup_of_close {ε : ℝ} (hε : ε < 1 / 4) {m n : Multiset ℂ}
    (h : Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε) m n) (hg : GapM n) : m.Nodup := by
  induction h with
  | zero => exact Multiset.nodup_zero
  | @cons a b as bs hab hrel ih =>
    have hgn : (b ::ₘ bs).Nodup := hg.1
    have hb : b ∉ bs := (Multiset.nodup_cons.1 hgn).1
    have hg' : GapM bs := by
      refine ⟨(Multiset.nodup_cons.1 hgn).2, fun x hx y hy hxy => ?_⟩
      exact hg.2 x (Multiset.mem_cons_of_mem hx) y (Multiset.mem_cons_of_mem hy) hxy
    refine Multiset.nodup_cons.2 ⟨fun ha => ?_, ih hg'⟩
    obtain ⟨y, hy, hay⟩ := Multiset.exists_mem_of_rel_of_mem hrel ha
    have hne : b ≠ y := fun e => hb (e ▸ hy)
    have h1 := hg.2 b (Multiset.mem_cons_self b bs) y (Multiset.mem_cons_of_mem hy) hne
    have h2 : ‖b - y‖ ≤ ‖a - b‖ + ‖a - y‖ := by
      have : b - y = (a - y) - (a - b) := by ring
      rw [this]
      calc ‖(a - y) - (a - b)‖ ≤ ‖a - y‖ + ‖a - b‖ := norm_sub_le _ _
        _ = ‖a - b‖ + ‖a - y‖ := add_comm _ _
    linarith

/- English proof (translation)
Proceed by induction on `n using Multiset.induction_on with`. Consider the case `empty`. Introduce `δ hδ`. Use `⟨1, one_pos, fun m hm => ?_⟩` and prove the remaining obligations. Establish `: m = 0` using `Multiset.rel_zero_right.1 hm`.

Substitute `this` using the available equality. Simplify using `using hδ`. Consider the case `cons b bs ih`. Introduce `δ hδ`. Establish `hc : ContinuousAt (fun p : ℂ × ℂ => p.1 * p.2) (u + b, (bs.map (u + ·)).prod)` using `continuous_mul.continuousAt`.

Take `⟨δ', hδ', H⟩` from `Metric.continuousAt_iff.1 hc δ hδ`. Take `⟨ε₁, hε₁, H₁⟩` from `ih δ' hδ'`. Use `⟨min ε₁ (δ' / 2), lt_min hε₁ (half_pos hδ'), fun m hm => ?_⟩` and prove the remaining obligations. Take `⟨a, as, hab, has, rfl⟩` from `Multiset.rel_cons_right.1 hm`. Establish `has' : Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε₁) as bs` using `has.mono fun x _ y _ hxy => hxy.trans (min_le_left _ _)`.

Establish `h1 : ‖(u + a) - (u + b)‖ < δ'`. Establish `e : (u + a) - (u + b) = a - b` using `by ring`. Rewrite using `[e]`. Use `hab.trans (min_le_right _ _)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2` using `H₁ as has'`. Establish `hd : dist ((u + a, (as.map (u + ·)).prod) : ℂ × ℂ) (u + b, (bs.map (u + ·)).prod) < δ'`. Rewrite using `[Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]`. Conclude with `⟨h1, h2⟩`. Establish `h3` using `H hd`.

Rewrite `h3` using `[dist_eq_norm]`. Simplify `h3` using `[Multiset.map_cons, Multiset.prod_cons]`.
-/
theorem prod_close (u : ℂ) (n : Multiset ℂ) : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ m : Multiset ℂ,
    Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε) m n →
      ‖(m.map (u + ·)).prod - (n.map (u + ·)).prod‖ < δ := by
  induction n using Multiset.induction_on with
  | empty =>
    intro δ hδ
    refine ⟨1, one_pos, fun m hm => ?_⟩
    have : m = 0 := Multiset.rel_zero_right.1 hm
    subst this
    simpa using hδ
  | cons b bs ih =>
    intro δ hδ
    have hc : ContinuousAt (fun p : ℂ × ℂ => p.1 * p.2) (u + b, (bs.map (u + ·)).prod) :=
      continuous_mul.continuousAt
    obtain ⟨δ', hδ', H⟩ := Metric.continuousAt_iff.1 hc δ hδ
    obtain ⟨ε₁, hε₁, H₁⟩ := ih δ' hδ'
    refine ⟨min ε₁ (δ' / 2), lt_min hε₁ (half_pos hδ'), fun m hm => ?_⟩
    obtain ⟨a, as, hab, has, rfl⟩ := Multiset.rel_cons_right.1 hm
    have has' : Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε₁) as bs :=
      has.mono fun x _ y _ hxy => hxy.trans (min_le_left _ _)
    have h1 : ‖(u + a) - (u + b)‖ < δ' := by
      have e : (u + a) - (u + b) = a - b := by ring
      rw [e]
      have := hab.trans (min_le_right _ _)
      linarith
    have h2 := H₁ as has'
    have hd : dist ((u + a, (as.map (u + ·)).prod) : ℂ × ℂ) (u + b, (bs.map (u + ·)).prod) < δ' := by
      rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
      exact ⟨h1, h2⟩
    have h3 := H hd
    rw [dist_eq_norm] at h3
    simpa [Multiset.map_cons, Multiset.prod_cons] using h3

end GlobalTheory.CompanionTheory.EGlue.MCl

namespace GlobalTheory.CompanionTheory.EGlue

/- English proof (translation)
Use `⟨fun ε m n B h hB x hx => ?_, fun ε m n hε h hg => MCl.nodup_of_close hε h hg, fun m n hm u => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hxy⟩` from `Multiset.exists_mem_of_rel_of_mem h hx`. Establish `h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖`. Simplify using `using norm_add_le (x - y) y`. Establish `h2` using `hB y hy`.

Establish `h3 : ‖x - y‖ ≤ ε` using `hxy`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Metric.tendsto_nhds]`. Introduce `δ hδ`. Take `⟨ε, hε, H⟩` from `MCl.prod_close u n δ hδ`.

Use `filter_upwards [hm ε hε] with k hk`. Rewrite using `[dist_eq_norm]`. Conclude with `H _ hk`.
-/
theorem mCloseFacts_holds : MCloseFacts := by
  refine ⟨fun ε m n B h hB x hx => ?_, fun ε m n hε h hg => MCl.nodup_of_close hε h hg,
    fun m n hm u => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := Multiset.exists_mem_of_rel_of_mem h hx
    have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      simpa using norm_add_le (x - y) y
    have h2 := hB y hy
    have h3 : ‖x - y‖ ≤ ε := hxy
    linarith
  · rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨ε, hε, H⟩ := MCl.prod_close u n δ hδ
    filter_upwards [hm ε hε] with k hk
    rw [dist_eq_norm]
    exact H _ hk

end GlobalTheory.CompanionTheory.EGlue
