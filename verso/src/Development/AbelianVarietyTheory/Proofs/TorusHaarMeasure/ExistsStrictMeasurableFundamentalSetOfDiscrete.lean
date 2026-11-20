import Mathlib

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ ⟨U, hU, hΓU⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨t, htU, ht, h1t⟩` from `mem_nhds_iff.1 hU`. Establish `hopen : IsOpen ({1} : Set Γ)`. Rewrite using `[isOpen_induced_iff]`.

Use `⟨t, ht, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `Subtype.ext (hΓU x x.2 (htU hx))`. Introduce and unpack `rfl`. Conclude with `h1t`. Use `haveI : DiscreteTopology Γ := discreteTopology_of_isOpen_singleton_one hopen`. Conclude with `TopologicalSpace.separableSpace_iff_countable.1 inferInstance`.

Take `⟨V, hVo, hV1, hVU⟩` from `exists_open_nhds_one_split hU`. Set `C : G → Set G` to `fun x => {y | y * x⁻¹ ∈ V ∧ x * y⁻¹ ∈ V}`. Establish `hCo : ∀ x, IsOpen (C x)` using `fun x => (hVo.preimage (continuous_id.mul continuous_const)).inter (hVo.preimage (continuous_const.mul continuous_inv))`. Establish `hCx : ∀ x, x ∈ C x` using `fun x => by simp [C, hV1]`. Take `⟨T, hTc, hT⟩` from `TopologicalSpace.isOpen_iUnion_countable C hCo`.

Establish `hTne : T.Nonempty`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Set.not_nonempty_iff_eq_empty]`. Establish `h1 : (1 : G) ∈ ⋃ x, C x` using `Set.mem_iUnion.2 ⟨1, hCx 1⟩`. Rewrite `h1` using `[← hT, h]`.

Simplify using `at h1`. Take `⟨c, hc⟩` from `hTc.exists_eq_range hTne`. Set `W : ℕ → Set G` to `fun n => C (c n)`. Establish `hWo : ∀ n, IsOpen (W n)` using `fun n => hCo _`. Establish `hcover : ∀ x, ∃ n, x ∈ W n`.

Introduce `x`. Establish `hx : x ∈ ⋃ y ∈ T, C y` using `by rw [hT]; exact Set.mem_iUnion.2 ⟨x, hCx x⟩`. Rewrite `hx` using `[hc]`. Simplify using `only [Set.biUnion_range, Set.mem_iUnion] at hx`. Conclude with `hx`.

Establish `hsep : ∀ n (x : G) (γ : Γ), x ∈ W n → (γ : G) * x ∈ W n → γ = 1`. Introduce `n x γ hx hγx`. Establish `h` using `hVU _ hγx.1 _ hx.2`. Establish `he : (γ : G) * x * (c n)⁻¹ * (c n * x⁻¹) = γ` using `by group`. Rewrite `h` using `[he]`.

Conclude with `Subtype.ext (hΓU γ γ.2 h)`. Set `S : ℕ → Set G` to `fun m => ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' W m`. Establish `hSo : ∀ m, IsOpen (S m)` using `fun m => isOpen_iUnion fun γ => (hWo m).preimage (continuous_const.mul continuous_id)`. Establish `hmemS : ∀ m x, x ∈ S m ↔ ∃ γ : Γ, (γ : G) * x ∈ W m` using `fun m x => by`. Simplify using `only [S, Set.mem_iUnion, Set.mem_preimage]`.

Use `⟨⋃ n : ℕ, W n \ ⋃ m : Fin n, S m, ?_, ?_⟩` and prove the remaining obligations. Conclude with `MeasurableSet.iUnion fun n => (hWo n).measurableSet.diff (MeasurableSet.iUnion fun m => (hSo m).measurableSet)`. Introduce `g`. Establish `hmemF : ∀ y, y ∈ (⋃ n : ℕ, W n \ ⋃ m : Fin n, S m) ↔ ∃ n, y ∈ W n ∧ ∀ m < n, y ∉ S m`. Introduce `y`.

Simplify using `only [Set.mem_iUnion, Set.mem_diff, not_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hy, hm⟩`. Conclude with `⟨n, hy, fun m hm' => hm ⟨m, hm'⟩⟩`. Introduce and unpack `⟨n, hy, hm⟩`.

Conclude with `⟨n, hy, fun m => hm m m.2⟩`. Establish `hex : ∃ n, g ∈ S n`. Take `⟨n, hn⟩` from `hcover g`. Conclude with `⟨n, (hmemS n g).2 ⟨1, by simpa using hn⟩⟩`. Take `⟨γ, hγ⟩` from `(hmemS _ g).1 (Nat.find_spec hex)`.

Use `⟨γ, (hmemF _).2 ⟨Nat.find hex, hγ, fun m hm hS => ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨δ, hδ⟩` from `(hmemS m _).1 hS`. Conclude with `Nat.find_min hex hm ((hmemS m g).2 ⟨δ * γ, by simpa [mul_assoc] using hδ⟩)`. Introduce `γ' hγ'`. Take `⟨k, hk, hkS⟩` from `(hmemF _).1 hγ'`.

Establish `hkN : k = Nat.find hex`. Use `le_antisymm ?_ (Nat.find_min' hex ((hmemS k g).2 ⟨γ', hk⟩))` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Conclude with `hkS _ hlt ((hmemS _ _).2 ⟨γ * γ'⁻¹, by simpa [mul_assoc] using hγ⟩)`.

Rewrite `hk` using `[hkN]`. Establish `h1` using `hsep _ _ (γ' * γ⁻¹) hγ (by simpa [mul_assoc] using hk)`. Conclude with `mul_inv_eq_one.1 h1`.
-/
theorem _root_.GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → Countable Γ ∧ ∃ F : Set G, MeasurableSet F ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) := by
  intro G _ _ _ _ _ _ _ _ Γ ⟨U, hU, hΓU⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨t, htU, ht, h1t⟩ := mem_nhds_iff.1 hU
    have hopen : IsOpen ({1} : Set Γ) := by
      rw [isOpen_induced_iff]
      refine ⟨t, ht, ?_⟩
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact Subtype.ext (hΓU x x.2 (htU hx))
      · rintro rfl
        exact h1t
    haveI : DiscreteTopology Γ := discreteTopology_of_isOpen_singleton_one hopen
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  · obtain ⟨V, hVo, hV1, hVU⟩ := exists_open_nhds_one_split hU
    let C : G → Set G := fun x => {y | y * x⁻¹ ∈ V ∧ x * y⁻¹ ∈ V}
    have hCo : ∀ x, IsOpen (C x) := fun x =>
      (hVo.preimage (continuous_id.mul continuous_const)).inter
        (hVo.preimage (continuous_const.mul continuous_inv))
    have hCx : ∀ x, x ∈ C x := fun x => by simp [C, hV1]
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable C hCo
    have hTne : T.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have h1 : (1 : G) ∈ ⋃ x, C x := Set.mem_iUnion.2 ⟨1, hCx 1⟩
      rw [← hT, h] at h1
      simp at h1
    obtain ⟨c, hc⟩ := hTc.exists_eq_range hTne
    let W : ℕ → Set G := fun n => C (c n)
    have hWo : ∀ n, IsOpen (W n) := fun n => hCo _
    have hcover : ∀ x, ∃ n, x ∈ W n := by
      intro x
      have hx : x ∈ ⋃ y ∈ T, C y := by rw [hT]; exact Set.mem_iUnion.2 ⟨x, hCx x⟩
      rw [hc] at hx
      simp only [Set.biUnion_range, Set.mem_iUnion] at hx
      exact hx
    have hsep : ∀ n (x : G) (γ : Γ), x ∈ W n → (γ : G) * x ∈ W n → γ = 1 := by
      intro n x γ hx hγx
      have h := hVU _ hγx.1 _ hx.2
      have he : (γ : G) * x * (c n)⁻¹ * (c n * x⁻¹) = γ := by group
      rw [he] at h
      exact Subtype.ext (hΓU γ γ.2 h)
    let S : ℕ → Set G := fun m => ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' W m
    have hSo : ∀ m, IsOpen (S m) := fun m =>
      isOpen_iUnion fun γ => (hWo m).preimage (continuous_const.mul continuous_id)
    have hmemS : ∀ m x, x ∈ S m ↔ ∃ γ : Γ, (γ : G) * x ∈ W m := fun m x => by
      simp only [S, Set.mem_iUnion, Set.mem_preimage]
    refine ⟨⋃ n : ℕ, W n \ ⋃ m : Fin n, S m, ?_, ?_⟩
    · exact MeasurableSet.iUnion fun n =>
        (hWo n).measurableSet.diff (MeasurableSet.iUnion fun m => (hSo m).measurableSet)
    · intro g
      have hmemF : ∀ y, y ∈ (⋃ n : ℕ, W n \ ⋃ m : Fin n, S m) ↔
          ∃ n, y ∈ W n ∧ ∀ m < n, y ∉ S m := by
        intro y
        simp only [Set.mem_iUnion, Set.mem_diff, not_exists]
        constructor
        · rintro ⟨n, hy, hm⟩
          exact ⟨n, hy, fun m hm' => hm ⟨m, hm'⟩⟩
        · rintro ⟨n, hy, hm⟩
          exact ⟨n, hy, fun m => hm m m.2⟩
      have hex : ∃ n, g ∈ S n := by
        obtain ⟨n, hn⟩ := hcover g
        exact ⟨n, (hmemS n g).2 ⟨1, by simpa using hn⟩⟩
      classical
      obtain ⟨γ, hγ⟩ := (hmemS _ g).1 (Nat.find_spec hex)
      refine ⟨γ, (hmemF _).2 ⟨Nat.find hex, hγ, fun m hm hS => ?_⟩, ?_⟩
      · obtain ⟨δ, hδ⟩ := (hmemS m _).1 hS
        exact Nat.find_min hex hm ((hmemS m g).2 ⟨δ * γ, by simpa [mul_assoc] using hδ⟩)
      · intro γ' hγ'
        obtain ⟨k, hk, hkS⟩ := (hmemF _).1 hγ'
        have hkN : k = Nat.find hex := by
          refine le_antisymm ?_ (Nat.find_min' hex ((hmemS k g).2 ⟨γ', hk⟩))
          by_contra hlt
          push_neg at hlt
          exact hkS _ hlt ((hmemS _ _).2 ⟨γ * γ'⁻¹, by simpa [mul_assoc] using hγ⟩)
        rw [hkN] at hk
        have h1 := hsep _ _ (γ' * γ⁻¹) hγ (by simpa [mul_assoc] using hk)
        exact mul_inv_eq_one.1 h1

end GlobalTheory
