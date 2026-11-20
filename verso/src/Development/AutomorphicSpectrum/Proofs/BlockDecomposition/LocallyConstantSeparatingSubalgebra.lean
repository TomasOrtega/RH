import Mathlib

namespace GlobalTheory.CompanionTheory.LocConstSW

open Set Topology

variable {B : Type} [TopologicalSpace B]

/- English proof (translation)
Establish `hfin : (Set.range f).Finite` using `hlc.range_finite`. Use `set S : Finset ℂ := hfin.toFinset with hS`. Establish `hprod : ∀ T : Finset ℂ, (∏ w ∈ T, ((v - w)⁻¹ • (f - w • (1 : B → ℂ)))) ∈ V`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`.

Consider the case `empty => simpa using h1`. Consider the case `insert a T ha ih`. Rewrite using `[Finset.prod_insert ha]`. Conclude with `hmul _ (V.smul_mem _ (V.sub_mem hf (V.smul_mem _ h1))) _ ih`. Distinguish the cases in `hv : v ∈ S`.

Establish `key : ({x | f x = v} : Set B).indicator (1 : B → ℂ) = ∏ w ∈ S.erase v, ((v - w)⁻¹ • (f - w • (1 : B → ℂ)))`. Use function extensionality and compare the values at `x`. Simplify using `only [Finset.prod_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]`. Distinguish the cases in `hx : f x = v`. Rewrite using `[Set.indicator_of_mem (by simpa using hx)]`.

Simplify using `only [Pi.one_apply]`. Use `symm`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `w hw`. Establish `hwv : v - w ≠ 0` using `sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hw))`.

Rewrite using `[hx]`. Conclude with `inv_mul_cancel₀ hwv`. Rewrite using `[Set.indicator_of_notMem (by simpa using hx)]`. Use `symm`. Apply `Finset.prod_eq_zero (i := f x)` to reduce the goal to its premises.

Use `Finset.mem_erase.mpr ⟨hx, ?_⟩` and prove the remaining obligations. Simplify using `[hS]`. Simplify using the standard rewrite rules. Rewrite using `[key]`. Conclude with `hprod _`.

Establish `: ({x | f x = v} : Set B) = ∅`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]`. Introduce `hx`. Apply `hv` to reduce the goal to its premises.

Simplify using `[hS, ← hx]`. Rewrite using `[this, Set.indicator_empty]`. Conclude with `V.zero_mem`.
-/
theorem indicator_level_mem [CompactSpace B] (V : Submodule ℂ (B → ℂ)) (h1 : (1 : B → ℂ) ∈ V)
    (hmul : ∀ f ∈ V, ∀ g ∈ V, f * g ∈ V) {f : B → ℂ} (hf : f ∈ V)
    (hlc : IsLocallyConstant f) (v : ℂ) :
    ({x | f x = v} : Set B).indicator (1 : B → ℂ) ∈ V := by
  classical
  have hfin : (Set.range f).Finite := hlc.range_finite
  set S : Finset ℂ := hfin.toFinset with hS
  have hprod : ∀ T : Finset ℂ,
      (∏ w ∈ T, ((v - w)⁻¹ • (f - w • (1 : B → ℂ)))) ∈ V := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using h1
    | insert a T ha ih =>
      rw [Finset.prod_insert ha]
      exact hmul _ (V.smul_mem _ (V.sub_mem hf (V.smul_mem _ h1))) _ ih
  by_cases hv : v ∈ S
  · have key : ({x | f x = v} : Set B).indicator (1 : B → ℂ)
        = ∏ w ∈ S.erase v, ((v - w)⁻¹ • (f - w • (1 : B → ℂ))) := by
      funext x
      simp only [Finset.prod_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul,
        mul_one]
      by_cases hx : f x = v
      · rw [Set.indicator_of_mem (by simpa using hx)]
        simp only [Pi.one_apply]
        symm
        apply Finset.prod_eq_one
        intro w hw
        have hwv : v - w ≠ 0 := sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hw))
        rw [hx]
        exact inv_mul_cancel₀ hwv
      · rw [Set.indicator_of_notMem (by simpa using hx)]
        symm
        apply Finset.prod_eq_zero (i := f x)
        · refine Finset.mem_erase.mpr ⟨hx, ?_⟩
          simp [hS]
        · simp
    rw [key]
    exact hprod _
  · have : ({x | f x = v} : Set B) = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      apply hv
      simp [hS, ← hx]
    rw [this, Set.indicator_empty]
    exact V.zero_mem

/- English proof (translation)
Introduce `B _ _ V h1 hmul hlc Φ hΦ hsep`. Set `P : Set B → Prop` to `fun C => C.indicator (1 : B → ℂ) ∈ V`. Establish `hPinter : ∀ C D, P C → P D → P (C ∩ D)`. Introduce `C D hC hD`. Establish `: (C ∩ D).indicator (1 : B → ℂ) = C.indicator 1 * D.indicator 1`.

Use function extensionality and compare the values at `x`. Apply the tactic sequence `by_cases hx : x ∈ C <;> by_cases hy : x ∈ D <;> simp [Set.indicator, hx, hy]`. Use `show (C ∩ D).indicator (1 : B → ℂ) ∈ V`. Rewrite using `[this]`. Conclude with `hmul _ hC _ hD`.

Establish `hPcompl : ∀ C, P C → P Cᶜ`. Introduce `C hC`. Establish `: (Cᶜ).indicator (1 : B → ℂ) = 1 - C.indicator 1`. Use function extensionality and compare the values at `x`. Apply the tactic sequence `by_cases hx : x ∈ C <;> simp [Set.indicator, hx]`.

Use `show (Cᶜ).indicator (1 : B → ℂ) ∈ V`. Rewrite using `[this]`. Conclude with `V.sub_mem h1 hC`. Establish `hPunion : ∀ C D, P C → P D → P (C ∪ D)`. Introduce `C D hC hD`.

Use `hPcompl _ (hPinter _ _ (hPcompl C hC) (hPcompl D hD))` as an intermediate fact. Rewrite `this` using `[Set.compl_inter, compl_compl, compl_compl]`. Then use the resulting hypothesis. Establish `hPuniv : P Set.univ` using `by show (Set.univ : Set B).indicator (1 : B → ℂ) ∈ V`. Rewrite using `[Set.indicator_univ]`. Conclude with `h1`.

Establish `hPempty : P ∅` using `by show (∅ : Set B).indicator (1 : B → ℂ) ∈ V`. Rewrite using `[Set.indicator_empty]`. Conclude with `V.zero_mem`. Establish `hPopen : ∀ C, P C → IsOpen C`. Introduce `C hC`.

Use `(hlc _ hC).isOpen_fiber (1 : ℂ)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Apply the tactic sequence `by_cases hx : x ∈ C <;> simp [Set.indicator, hx]`. Establish `hlevel : ∀ v : ℂ, P (Φ ⁻¹' {v})`.

Introduce `v`. Use `set K : Set B := Φ ⁻¹' {v} with hK`. Establish `hKopen : IsOpen K` using `hΦ.isOpen_fiber v`. Establish `hKclosed : IsClosed K` using `hΦ.isClosed_fiber v`. Establish `hstep : ∀ p ∈ K, ∃ C, P C ∧ p ∈ C ∧ C ∩ Kᶜ = ∅`.

Introduce `p hp`. Establish `hcomp : IsCompact (Kᶜ)` using `hKopen.isClosed_compl.isCompact`. Establish `: ∃ C, P C ∧ p ∈ C ∧ C ∩ Kᶜ = ∅`. Use `hcomp.induction_on (p := fun s => ∃ C, P C ∧ p ∈ C ∧ C ∩ s = ∅) ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `⟨Set.univ, hPuniv, trivial, by simp⟩`.

Introduce and unpack `s t hst ⟨C, hC, hpC, hCt⟩`. Use `⟨C, hC, hpC, ?_⟩` and prove the remaining obligations. Conclude with `Set.subset_empty_iff.mp (hCt ▸ Set.inter_subset_inter_right C hst)`. Introduce and unpack `s t ⟨C, hC, hpC, hCs⟩ ⟨D, hD, hpD, hDt⟩`. Use `⟨C ∩ D, hPinter _ _ hC hD, ⟨hpC, hpD⟩, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Simplify using `only [Set.mem_inter_iff, Set.mem_union, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨⟨hxC, hxD⟩, hxs | hxt⟩`. Conclude with `(Set.eq_empty_iff_forall_notMem.mp hCs x) ⟨hxC, hxs⟩`. Conclude with `(Set.eq_empty_iff_forall_notMem.mp hDt x) ⟨hxD, hxt⟩`.

Introduce `q hq`. Establish `hne : Φ p ≠ Φ q`. Establish `hp' : Φ p = v` using `hp`. Establish `hq' : Φ q ≠ v` using `hq`. Rewrite using `[hp']`.

Conclude with `Ne.symm hq'`. Take `⟨f, hfV, hfpq⟩` from `hsep p q hne`. Establish `hC : P {x | f x = f p}` using `indicator_level_mem V h1 hmul hfV (hlc f hfV) (f p)`. Establish `hopen : IsOpen ({x | f x = f p}ᶜ : Set B)` using `(hlc f hfV).isClosed_fiber (f p) |>.isOpen_compl`. Use `⟨{x | f x = f p}ᶜ, mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds ?_), _, hC, rfl, ?_⟩` and prove the remaining obligations.

Conclude with `fun h => hfpq h.symm`. Simplify using the standard rewrite rules. Conclude with `this`. Establish `hKcomp : IsCompact K` using `hKclosed.isCompact`. Establish `: ∃ C, P C ∧ K ⊆ C ∧ C ⊆ K`.

Use `hKcomp.induction_on (p := fun s => ∃ C, P C ∧ s ⊆ C ∧ C ⊆ K) ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `⟨∅, hPempty, subset_rfl, Set.empty_subset _⟩`. Introduce and unpack `s t hst ⟨C, hC, htC, hCK⟩`. Conclude with `⟨C, hC, hst.trans htC, hCK⟩`. Introduce and unpack `s t ⟨C, hC, hsC, hCK⟩ ⟨D, hD, htD, hDK⟩`.

Conclude with `⟨C ∪ D, hPunion _ _ hC hD, Set.union_subset_union hsC htD, Set.union_subset hCK hDK⟩`. Introduce `p hp`. Take `⟨C, hC, hpC, hCK⟩` from `hstep p hp`. Use `⟨C, mem_nhdsWithin_of_mem_nhds ((hPopen C hC).mem_nhds hpC), C, hC, subset_rfl, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Assume the negation of the conclusion as `hxK`. Conclude with `(Set.eq_empty_iff_forall_notMem.mp hCK x) ⟨hx, hxK⟩`. Take `⟨C, hC, hKC, hCK⟩` from `this`. Establish `: C = K` using `Set.Subset.antisymm hCK hKC`. Rewrite using `[← this]`.

Conclude with `hC`. Establish `hfin : (Set.range Φ).Finite` using `hΦ.range_finite`. Establish `hsum : Φ = ∑ v ∈ hfin.toFinset, v • (Φ ⁻¹' {v}).indicator (1 : B → ℂ)`. Use function extensionality and compare the values at `x`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single (Φ x)]`.

Simplify using `[Set.indicator]`. Introduce `b _ hb`. Establish `: x ∉ Φ ⁻¹' {b}` using `fun h => hb (by simpa using h.symm)`. Simplify using `[Set.indicator_of_notMem this]`. Introduce `h`.

Conclude with `absurd (by simp) h`. Rewrite using `[hsum]`. Conclude with `V.sum_mem fun v _ => V.smul_mem _ (hlevel v)`.
-/
theorem mem_of_separates : ∀ (B : Type) [TopologicalSpace B] [CompactSpace B]
    (V : Submodule ℂ (B → ℂ)), (1 : B → ℂ) ∈ V → (∀ f ∈ V, ∀ g ∈ V, f * g ∈ V) →
    (∀ f ∈ V, IsLocallyConstant f) → ∀ Φ : B → ℂ, IsLocallyConstant Φ →
    (∀ p q, Φ p ≠ Φ q → ∃ f ∈ V, f p ≠ f q) → Φ ∈ V := by
  intro B _ _ V h1 hmul hlc Φ hΦ hsep
  classical

  let P : Set B → Prop := fun C => C.indicator (1 : B → ℂ) ∈ V
  have hPinter : ∀ C D, P C → P D → P (C ∩ D) := by
    intro C D hC hD
    have : (C ∩ D).indicator (1 : B → ℂ) = C.indicator 1 * D.indicator 1 := by
      funext x
      by_cases hx : x ∈ C <;> by_cases hy : x ∈ D <;> simp [Set.indicator, hx, hy]
    show (C ∩ D).indicator (1 : B → ℂ) ∈ V
    rw [this]
    exact hmul _ hC _ hD
  have hPcompl : ∀ C, P C → P Cᶜ := by
    intro C hC
    have : (Cᶜ).indicator (1 : B → ℂ) = 1 - C.indicator 1 := by
      funext x
      by_cases hx : x ∈ C <;> simp [Set.indicator, hx]
    show (Cᶜ).indicator (1 : B → ℂ) ∈ V
    rw [this]
    exact V.sub_mem h1 hC
  have hPunion : ∀ C D, P C → P D → P (C ∪ D) := by
    intro C D hC hD
    have := hPcompl _ (hPinter _ _ (hPcompl C hC) (hPcompl D hD))
    rwa [Set.compl_inter, compl_compl, compl_compl] at this
  have hPuniv : P Set.univ := by
    show (Set.univ : Set B).indicator (1 : B → ℂ) ∈ V
    rw [Set.indicator_univ]
    exact h1
  have hPempty : P ∅ := by
    show (∅ : Set B).indicator (1 : B → ℂ) ∈ V
    rw [Set.indicator_empty]
    exact V.zero_mem

  have hPopen : ∀ C, P C → IsOpen C := by
    intro C hC
    have := (hlc _ hC).isOpen_fiber (1 : ℂ)
    convert this using 1
    ext x
    by_cases hx : x ∈ C <;> simp [Set.indicator, hx]
  have hlevel : ∀ v : ℂ, P (Φ ⁻¹' {v}) := by
    intro v
    set K : Set B := Φ ⁻¹' {v} with hK
    have hKopen : IsOpen K := hΦ.isOpen_fiber v
    have hKclosed : IsClosed K := hΦ.isClosed_fiber v

    have hstep : ∀ p ∈ K, ∃ C, P C ∧ p ∈ C ∧ C ∩ Kᶜ = ∅ := by
      intro p hp
      have hcomp : IsCompact (Kᶜ) := hKopen.isClosed_compl.isCompact
      have : ∃ C, P C ∧ p ∈ C ∧ C ∩ Kᶜ = ∅ := by
        refine hcomp.induction_on (p := fun s => ∃ C, P C ∧ p ∈ C ∧ C ∩ s = ∅) ?_ ?_ ?_ ?_
        · exact ⟨Set.univ, hPuniv, trivial, by simp⟩
        · rintro s t hst ⟨C, hC, hpC, hCt⟩
          refine ⟨C, hC, hpC, ?_⟩
          exact Set.subset_empty_iff.mp (hCt ▸ Set.inter_subset_inter_right C hst)
        · rintro s t ⟨C, hC, hpC, hCs⟩ ⟨D, hD, hpD, hDt⟩
          refine ⟨C ∩ D, hPinter _ _ hC hD, ⟨hpC, hpD⟩, ?_⟩
          ext x
          simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_empty_iff_false, iff_false]
          rintro ⟨⟨hxC, hxD⟩, hxs | hxt⟩
          · exact (Set.eq_empty_iff_forall_notMem.mp hCs x) ⟨hxC, hxs⟩
          · exact (Set.eq_empty_iff_forall_notMem.mp hDt x) ⟨hxD, hxt⟩
        · intro q hq
          have hne : Φ p ≠ Φ q := by
            have hp' : Φ p = v := hp
            have hq' : Φ q ≠ v := hq
            rw [hp']
            exact Ne.symm hq'
          obtain ⟨f, hfV, hfpq⟩ := hsep p q hne
          have hC : P {x | f x = f p} := indicator_level_mem V h1 hmul hfV (hlc f hfV) (f p)
          have hopen : IsOpen ({x | f x = f p}ᶜ : Set B) := (hlc f hfV).isClosed_fiber (f p) |>.isOpen_compl
          refine ⟨{x | f x = f p}ᶜ, mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds ?_), _, hC, rfl, ?_⟩
          · exact fun h => hfpq h.symm
          · simp
      exact this
    have hKcomp : IsCompact K := hKclosed.isCompact
    have : ∃ C, P C ∧ K ⊆ C ∧ C ⊆ K := by
      refine hKcomp.induction_on (p := fun s => ∃ C, P C ∧ s ⊆ C ∧ C ⊆ K) ?_ ?_ ?_ ?_
      · exact ⟨∅, hPempty, subset_rfl, Set.empty_subset _⟩
      · rintro s t hst ⟨C, hC, htC, hCK⟩
        exact ⟨C, hC, hst.trans htC, hCK⟩
      · rintro s t ⟨C, hC, hsC, hCK⟩ ⟨D, hD, htD, hDK⟩
        exact ⟨C ∪ D, hPunion _ _ hC hD, Set.union_subset_union hsC htD,
          Set.union_subset hCK hDK⟩
      · intro p hp
        obtain ⟨C, hC, hpC, hCK⟩ := hstep p hp
        refine ⟨C, mem_nhdsWithin_of_mem_nhds ((hPopen C hC).mem_nhds hpC), C, hC, subset_rfl, ?_⟩
        intro x hx
        by_contra hxK
        exact (Set.eq_empty_iff_forall_notMem.mp hCK x) ⟨hx, hxK⟩
    obtain ⟨C, hC, hKC, hCK⟩ := this
    have : C = K := Set.Subset.antisymm hCK hKC
    rw [← this]
    exact hC

  have hfin : (Set.range Φ).Finite := hΦ.range_finite
  have hsum : Φ = ∑ v ∈ hfin.toFinset, v • (Φ ⁻¹' {v}).indicator (1 : B → ℂ) := by
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single (Φ x)]
    · simp [Set.indicator]
    · intro b _ hb
      have : x ∉ Φ ⁻¹' {b} := fun h => hb (by simpa using h.symm)
      simp [Set.indicator_of_notMem this]
    · intro h
      exact absurd (by simp) h
  rw [hsum]
  exact V.sum_mem fun v _ => V.smul_mem _ (hlevel v)

end GlobalTheory.CompanionTheory.LocConstSW
