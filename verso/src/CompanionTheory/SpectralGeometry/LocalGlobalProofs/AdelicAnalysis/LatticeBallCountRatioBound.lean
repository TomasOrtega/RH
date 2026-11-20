import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteInterClosedBallOfSeparated

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.Packing

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Λ : Type} [AddCommGroup Λ]

def Sep (e : Λ →+ V) (r R : ℝ) (s : Finset Λ) : Prop :=
  (∀ l ∈ s, ‖e l‖ ≤ R) ∧ (s : Set Λ).Pairwise fun a b => r ≤ ‖e a - e b‖

/- English proof (translation)
Establish `hinj : Set.InjOn e (s : Set Λ)`. Introduce `a ha b hb hab`. Assume the negation of the conclusion as `hne`. Establish `: r ≤ ‖e a - e b‖` using `hs.2 ha hb hne`. Rewrite `this` using `[hab, sub_self, norm_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcard : (s.image e).card = s.card` using `Finset.card_image_of_injOn hinj`. Establish `h1` using `GlobalTheory.finset_card_le_of_separated (s.image e) hr (hr.le.trans hrR) (0 : V) (by`. Introduce `a ha`. Take `⟨l, hl, rfl⟩` from `Finset.mem_image.1 ha`.

Simplify using `using hs.1 l hl)`. Use the proof step `(by`. Introduce `a ha b hb hab`. Take `⟨l, hl, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 ha)`. Take `⟨m, hm, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hb)`.

Establish `hlm : l ≠ m` using `fun h => hab (by rw [h])`. Rewrite using `[dist_eq_norm]`. Conclude with `hs.2 hl hm hlm)`. Rewrite `h1` using `[hcard]`. Conclude with `h1.trans (GlobalTheory.one_add_two_mul_div_pow_le hr hrR _)`.
-/
theorem Sep.card_le {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {s : Finset Λ}
    (hs : Sep e r R s) : (s.card : ℝ) ≤ (3 * R / r) ^ Module.finrank ℝ V := by
  classical
  have hinj : Set.InjOn e (s : Set Λ) := by
    intro a ha b hb hab
    by_contra hne
    have : r ≤ ‖e a - e b‖ := hs.2 ha hb hne
    rw [hab, sub_self, norm_zero] at this
    linarith
  have hcard : (s.image e).card = s.card := Finset.card_image_of_injOn hinj
  have h1 := GlobalTheory.finset_card_le_of_separated (s.image e) hr (hr.le.trans hrR) (0 : V)
    (by
      intro a ha
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 ha
      simpa using hs.1 l hl)
    (by
      intro a ha b hb hab
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
      have hlm : l ≠ m := fun h => hab (by rw [h])
      rw [dist_eq_norm]
      exact hs.2 hl hm hlm)
  rw [hcard] at h1
  exact h1.trans (GlobalTheory.one_add_two_mul_div_pow_le hr hrR _)

/- English proof (translation)
Set `S : Set ℕ` to `{n | ∃ s : Finset Λ, Sep e r R s ∧ s.card = n}`. Establish `hne : S.Nonempty` using `⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩`. Establish `hbd : BddAbove S`. Use `⟨⌊(3 * R / r) ^ Module.finrank ℝ V⌋₊, ?_⟩` and prove the remaining obligations. Introduce and unpack `n ⟨s, hs, rfl⟩`.

Conclude with `Nat.le_floor (Sep.card_le hr hrR hs)`. Take `⟨s, hs, hc⟩` from `Nat.sSup_mem hne hbd`. Conclude with `⟨s, hs, fun t ht => hc ▸ le_csSup hbd ⟨t, ht, rfl⟩⟩`.
-/
theorem exists_max_sep (e : Λ →+ V) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∃ s : Finset Λ, Sep e r R s ∧ ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card := by
  let S : Set ℕ := {n | ∃ s : Finset Λ, Sep e r R s ∧ s.card = n}
  have hne : S.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hbd : BddAbove S := by
    refine ⟨⌊(3 * R / r) ^ Module.finrank ℝ V⌋₊, ?_⟩
    rintro n ⟨s, hs, rfl⟩
    exact Nat.le_floor (Sep.card_le hr hrR hs)
  obtain ⟨s, hs, hc⟩ := Nat.sSup_mem hne hbd
  exact ⟨s, hs, fun t ht => hc ▸ le_csSup hbd ⟨t, ht, rfl⟩⟩

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hns : l ∉ s` using `fun h => by`. Use `hcon l h` as an intermediate fact. Simplify using `only [sub_self, map_zero, norm_zero] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hins : Sep e r R (insert l s)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `m hm`. Break down `Finset.mem_insert.1 hm with rfl | hm` into its components or cases.

Conclude with `hl`. Conclude with `hs.1 m hm`. Rewrite using `[Finset.coe_insert]`. Use `Set.pairwise_insert.2 ⟨hs.2, ?_⟩` and prove the remaining obligations. Introduce `b hb _`.

Establish `h` using `hcon b hb`. Rewrite `h` using `[map_sub]`. Conclude with `⟨h.le, by rw [norm_sub_rev]; exact h.le⟩`. Use `hmax _ hins` as an intermediate fact. Rewrite `this` using `[Finset.card_insert_of_notMem hns]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem Sep.exists_near {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) {s : Finset Λ}
    (hs : Sep e r R s) (hmax : ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card)
    {l : Λ} (hl : ‖e l‖ ≤ R) : ∃ t ∈ s, ‖e (l - t)‖ ≤ r := by
  classical
  by_contra hcon
  push_neg at hcon
  have hns : l ∉ s := fun h => by
    have := hcon l h
    simp only [sub_self, map_zero, norm_zero] at this
    linarith
  have hins : Sep e r R (insert l s) := by
    refine ⟨?_, ?_⟩
    · intro m hm
      rcases Finset.mem_insert.1 hm with rfl | hm
      · exact hl
      · exact hs.1 m hm
    · rw [Finset.coe_insert]
      refine Set.pairwise_insert.2 ⟨hs.2, ?_⟩
      intro b hb _
      have h := hcon b hb
      rw [map_sub] at h
      exact ⟨h.le, by rw [norm_sub_rev]; exact h.le⟩
  have := hmax _ hins
  rw [Finset.card_insert_of_notMem hns] at this
  omega

end GlobalTheory.CompanionTheory.Adelic.Packing

open GlobalTheory.CompanionTheory.Adelic.Packing in

/- English proof (translation)
Introduce `V _ _ _ Λ _ e r R hr hrR`. Take `⟨s, hs, hmax⟩` from `exists_max_sep e hr hrR`. Use `set f : Λ → ℝ≥0∞ := Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) with hf`. Establish `hpt : ∀ l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤ ∑ t ∈ s, f (l - t)`. Introduce `l`.

Distinguish the cases in `hl : ‖e l‖ ≤ R`. Take `⟨t, ht, hlt⟩` from `hs.exists_near hr hmax hl`. Establish `h1 : f (l - t) = 1` using `Set.indicator_of_mem (s := {l : Λ | ‖e l‖ ≤ r}) hlt _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Set.indicator_of_notMem (by simpa using hl)]`.

Conclude with `zero_le`. Establish `hshift : ∀ t : Λ, ∑' l : Λ, f (l - t) = ∑' l : Λ, f l` using `fun t => (Equiv.subRight t).tsum_eq f`. Establish `hcard : (s.card : ℝ≥0∞) ≤ ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V)`. Establish `h3 : (s.card : ℝ) ≤ (5 * R / r) ^ Module.finrank ℝ V`. Use `(Sep.card_le hr hrR hs).trans (pow_le_pow_left₀ (by have := hr.le.trans hrR; positivity) ?_ _)` and prove the remaining obligations.

Use `hr.le.trans hrR` as an intermediate fact. Use `gcongr`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]`. Use `_ = (s.card : ℝ≥0∞) * ∑' l : Λ, f l := by`. Simplify using `only [hshift, Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ _ := by gcongr`.
-/
theorem GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Type)
      [AddCommGroup Λ] (e : Λ →+ V) (r R : ℝ), 0 < r → r ≤ R →
      ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
        ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) *
          ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) l := by
  intro V _ _ _ Λ _ e r R hr hrR
  classical
  obtain ⟨s, hs, hmax⟩ := exists_max_sep e hr hrR
  set f : Λ → ℝ≥0∞ := Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) with hf
  have hpt : ∀ l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
      ∑ t ∈ s, f (l - t) := by
    intro l
    by_cases hl : ‖e l‖ ≤ R
    · obtain ⟨t, ht, hlt⟩ := hs.exists_near hr hmax hl
      have h1 : f (l - t) = 1 := Set.indicator_of_mem (s := {l : Λ | ‖e l‖ ≤ r}) hlt _
      calc Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤ 1 :=
            Set.indicator_le_self' (fun _ _ => zero_le) l
        _ = f (l - t) := h1.symm
        _ ≤ ∑ t ∈ s, f (l - t) :=
            Finset.single_le_sum (f := fun t => f (l - t)) (fun _ _ => zero_le) ht
    · rw [Set.indicator_of_notMem (by simpa using hl)]
      exact zero_le
  have hshift : ∀ t : Λ, ∑' l : Λ, f (l - t) = ∑' l : Λ, f l := fun t =>
    (Equiv.subRight t).tsum_eq f
  have hcard : (s.card : ℝ≥0∞) ≤ ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) := by
    have h3 : (s.card : ℝ) ≤ (5 * R / r) ^ Module.finrank ℝ V := by
      refine (Sep.card_le hr hrR hs).trans (pow_le_pow_left₀ (by have := hr.le.trans hrR; positivity) ?_ _)
      have := hr.le.trans hrR
      gcongr
      norm_num
    calc (s.card : ℝ≥0∞) = ENNReal.ofReal (s.card : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h3
  calc ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l
      ≤ ∑' l : Λ, ∑ t ∈ s, f (l - t) := ENNReal.tsum_le_tsum hpt
    _ = ∑ t ∈ s, ∑' l : Λ, f (l - t) := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = (s.card : ℝ≥0∞) * ∑' l : Λ, f l := by
        simp only [hshift, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr
