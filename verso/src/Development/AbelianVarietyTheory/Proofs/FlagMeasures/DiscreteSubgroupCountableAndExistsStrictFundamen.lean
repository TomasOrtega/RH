import Mathlib

open MeasureTheory Set TopologicalSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `G _ _ _ _ _ _ Γ _`. Use `⟨TopologicalSpace.separableSpace_iff_countable.1 inferInstance, ?_⟩` and prove the remaining obligations. Take `⟨U, hUo, hU⟩` from `isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))`. Establish `hU1 : (1 : G) ∈ U`. Establish `: (1 : Γ) ∈ Subtype.val ⁻¹' U` using `by rw [hU]; rfl`.

Simplify using `using this`. Establish `hUΓ : ∀ x : G, x ∈ U → x ∈ Γ → x = 1`. Introduce `x hx hxΓ`. Establish `: (⟨x, hxΓ⟩ : Γ) ∈ Subtype.val ⁻¹' U` using `hx`. Rewrite `this` using `[hU]`.

Simplify using `using congrArg Subtype.val (show (⟨x, hxΓ⟩ : Γ) = 1 from this)`. Take `⟨V, hVo, hV1, hVU⟩` from `exists_open_nhds_one_split (hUo.mem_nhds hU1)`. Set `P : Set G → Prop` to `fun W => ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ Γ → x = y`. Set `S : Set (Set G)` to `{W | W ∈ countableBasis G ∧ P W}`. Establish `hcover : ∀ g : G, ∃ W ∈ S, g ∈ W`.

Introduce `g`. Set `N : Set G` to `(fun x => x * g⁻¹) ⁻¹' (V ∩ V⁻¹)`. Establish `hNo : IsOpen N` using `(hVo.inter hVo.inv).preimage (continuous_mul_right _)`. Establish `hgN : g ∈ N` using `by simp [N, hV1]`. Take `⟨W, hWb, hgW, hWN⟩` from `(isBasis_countableBasis G).exists_subset_of_mem_open hgN hNo`.

Use `⟨W, ⟨hWb, ?_⟩, hgW⟩` and prove the remaining obligations. Introduce `x hx y hy hxy`. Establish `hx'` using `hWN hx`. Establish `hy'` using `hWN hy`. Simplify using `only [N, mem_preimage, mem_inter_iff, Set.mem_inv] at hx' hy'`.

Establish `h1 : (x * g⁻¹) * (y * g⁻¹)⁻¹ ∈ U` using `hVU _ hx'.1 _ hy'.2`. Establish `h2 : (x * g⁻¹) * (y * g⁻¹)⁻¹ = x * y⁻¹` using `by group`. Rewrite `h1` using `[h2]`. Use `hUΓ _ h1 hxy` as an intermediate fact. Conclude with `mul_inv_eq_one.1 this`.

Establish `hSc : S.Countable` using `(countable_countableBasis G).mono fun W hW => hW.1`. Establish `hSne : S.Nonempty`. Take `⟨W, hW, -⟩` from `hcover 1`. Conclude with `⟨W, hW⟩`. Take `⟨f, hf⟩` from `hSc.exists_eq_range hSne`.

Establish `hfS : ∀ n, f n ∈ S` using `fun n => hf ▸ mem_range_self n`. Set `Sat : ℕ → Set G` to `fun m => {x | ∃ γ : Γ, (γ : G) * x ∈ f m}`. Establish `hSat : ∀ m, IsOpen (Sat m)`. Introduce `m`. Establish `: Sat m = ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' f m`.

Use extensionality with `x`. Simplify using `[Sat]`. Rewrite using `[this]`. Conclude with `isOpen_iUnion fun γ => ((isBasis_countableBasis G).isOpen (hfS m).1).preimage (continuous_mul_left _)`. Set `D : Set G` to `⋃ n, (f n ∩ ⋂ m ∈ Finset.range n, (Sat m)ᶜ)`.

Use `⟨D, ?_, ?_⟩` and prove the remaining obligations. Use `MeasurableSet.iUnion fun n => ?_` and prove the remaining obligations. Use `(((isBasis_countableBasis G).isOpen (hfS n).1).measurableSet).inter ?_` and prove the remaining obligations. Conclude with `Finset.measurableSet_biInter _ fun m _ => (hSat m).measurableSet.compl`. Introduce `g`.

Establish `hex : ∃ n, ∃ γ : Γ, (γ : G) * g ∈ f n`. Take `⟨W, hW, hgW⟩` from `hcover g`. Rewrite `hW` using `[hf]`. Take `⟨n, rfl⟩` from `hW`. Conclude with `⟨n, 1, by simpa using hgW⟩`.

Take `⟨γ, hγ⟩` from `Nat.find_spec hex`. Establish `hmem : ∀ (δ : Γ) n, (δ : G) * g ∈ f n → (∀ m < n, (δ : G) * g ∉ Sat m) → (δ : G) * g ∈ D`. Introduce `δ n h1 h2`. Use `mem_iUnion.2 ⟨n, h1, ?_⟩` and prove the remaining obligations. Simplify using `only [mem_iInter, Finset.mem_range, mem_compl_iff]`.

Conclude with `h2`. Use `⟨γ, hmem γ _ hγ fun m hm hS => ?_, ?_⟩` and prove the remaining obligations. Take `⟨δ, hδ⟩` from `hS`. Use `Nat.find_min hex hm ⟨δ * γ, ?_⟩` and prove the remaining obligations. Simplify `hδ` using `[mul_assoc]`.

Introduce `δ hδ`. Establish `hD : ∀ (ε : Γ), (ε : G) * g ∈ D → ∃ n, (ε : G) * g ∈ f n ∧ ∀ m < n, (ε : G) * g ∉ Sat m`. Introduce `ε hε`. Take `⟨n, h1, h2⟩` from `mem_iUnion.1 hε`. Use `⟨n, h1, fun m hm => ?_⟩` and prove the remaining obligations.

Simplify using `only [mem_iInter, Finset.mem_range, mem_compl_iff] at h2`. Conclude with `h2 m hm`. Take `⟨n1, h11, h12⟩` from `hD δ hδ`. Take `⟨n2, h21, h22⟩` from `hD γ (hmem γ _ hγ fun m hm hS => by`. Take `⟨δ', hδ'⟩` from `hS`.

Conclude with `Nat.find_min hex hm ⟨δ' * γ, by simpa [mul_assoc] using hδ'⟩)`. Establish `hn : n1 = n2`. Break down `lt_trichotomy n1 n2 with h | h | h` into its components or cases. Conclude with `absurd ⟨δ * γ⁻¹, by simpa [mul_assoc] using h11⟩ (h22 n1 h)`. Conclude with `h`.

Conclude with `absurd ⟨γ * δ⁻¹, by simpa [mul_assoc] using h21⟩ (h12 n2 h)`. Substitute `hn` using the available equality. Establish `hP` using `(hfS n1).2 _ h11 _ h21 (by`. Establish `: ((δ : G) * g) * ((γ : G) * g)⁻¹ = ((δ * γ⁻¹ : Γ) : G)` using `by simp [mul_assoc]`. Rewrite using `[this]`.

Conclude with `(δ * γ⁻¹).2)`. Conclude with `Subtype.ext (mul_right_cancel hP)`.
-/
theorem discreteSubgroup_countable_and_exists_strict_fundamentalDomain : ∀ {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ],
    Countable Γ ∧ ∃ D : Set G, MeasurableSet D ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ D := by
  intro G _ _ _ _ _ _ Γ _
  refine ⟨TopologicalSpace.separableSpace_iff_countable.1 inferInstance, ?_⟩

  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
  have hU1 : (1 : G) ∈ U := by
    have : (1 : Γ) ∈ Subtype.val ⁻¹' U := by rw [hU]; rfl
    simpa using this
  have hUΓ : ∀ x : G, x ∈ U → x ∈ Γ → x = 1 := by
    intro x hx hxΓ
    have : (⟨x, hxΓ⟩ : Γ) ∈ Subtype.val ⁻¹' U := hx
    rw [hU] at this
    simpa using congrArg Subtype.val (show (⟨x, hxΓ⟩ : Γ) = 1 from this)
  obtain ⟨V, hVo, hV1, hVU⟩ := exists_open_nhds_one_split (hUo.mem_nhds hU1)

  let P : Set G → Prop := fun W => ∀ x ∈ W, ∀ y ∈ W, x * y⁻¹ ∈ Γ → x = y
  let S : Set (Set G) := {W | W ∈ countableBasis G ∧ P W}
  have hcover : ∀ g : G, ∃ W ∈ S, g ∈ W := by
    intro g
    let N : Set G := (fun x => x * g⁻¹) ⁻¹' (V ∩ V⁻¹)
    have hNo : IsOpen N := (hVo.inter hVo.inv).preimage (continuous_mul_right _)
    have hgN : g ∈ N := by simp [N, hV1]
    obtain ⟨W, hWb, hgW, hWN⟩ := (isBasis_countableBasis G).exists_subset_of_mem_open hgN hNo
    refine ⟨W, ⟨hWb, ?_⟩, hgW⟩
    intro x hx y hy hxy
    have hx' := hWN hx
    have hy' := hWN hy
    simp only [N, mem_preimage, mem_inter_iff, Set.mem_inv] at hx' hy'
    have h1 : (x * g⁻¹) * (y * g⁻¹)⁻¹ ∈ U := hVU _ hx'.1 _ hy'.2
    have h2 : (x * g⁻¹) * (y * g⁻¹)⁻¹ = x * y⁻¹ := by group
    rw [h2] at h1
    have := hUΓ _ h1 hxy
    exact mul_inv_eq_one.1 this
  have hSc : S.Countable := (countable_countableBasis G).mono fun W hW => hW.1
  have hSne : S.Nonempty := by
    obtain ⟨W, hW, -⟩ := hcover 1
    exact ⟨W, hW⟩
  obtain ⟨f, hf⟩ := hSc.exists_eq_range hSne
  have hfS : ∀ n, f n ∈ S := fun n => hf ▸ mem_range_self n

  let Sat : ℕ → Set G := fun m => {x | ∃ γ : Γ, (γ : G) * x ∈ f m}
  have hSat : ∀ m, IsOpen (Sat m) := by
    intro m
    have : Sat m = ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' f m := by
      ext x; simp [Sat]
    rw [this]
    exact isOpen_iUnion fun γ => ((isBasis_countableBasis G).isOpen (hfS m).1).preimage
      (continuous_mul_left _)
  let D : Set G := ⋃ n, (f n ∩ ⋂ m ∈ Finset.range n, (Sat m)ᶜ)
  refine ⟨D, ?_, ?_⟩
  · refine MeasurableSet.iUnion fun n => ?_
    refine (((isBasis_countableBasis G).isOpen (hfS n).1).measurableSet).inter ?_
    exact Finset.measurableSet_biInter _ fun m _ => (hSat m).measurableSet.compl
  · intro g
    have hex : ∃ n, ∃ γ : Γ, (γ : G) * g ∈ f n := by
      obtain ⟨W, hW, hgW⟩ := hcover g
      rw [hf] at hW
      obtain ⟨n, rfl⟩ := hW
      exact ⟨n, 1, by simpa using hgW⟩
    classical
    obtain ⟨γ, hγ⟩ := Nat.find_spec hex
    have hmem : ∀ (δ : Γ) n, (δ : G) * g ∈ f n → (∀ m < n, (δ : G) * g ∉ Sat m) → (δ : G) * g ∈ D := by
      intro δ n h1 h2
      refine mem_iUnion.2 ⟨n, h1, ?_⟩
      simp only [mem_iInter, Finset.mem_range, mem_compl_iff]
      exact h2
    refine ⟨γ, hmem γ _ hγ fun m hm hS => ?_, ?_⟩
    · obtain ⟨δ, hδ⟩ := hS
      refine Nat.find_min hex hm ⟨δ * γ, ?_⟩
      simpa [mul_assoc] using hδ
    · intro δ hδ
      have hD : ∀ (ε : Γ), (ε : G) * g ∈ D → ∃ n, (ε : G) * g ∈ f n ∧ ∀ m < n, (ε : G) * g ∉ Sat m := by
        intro ε hε
        obtain ⟨n, h1, h2⟩ := mem_iUnion.1 hε
        refine ⟨n, h1, fun m hm => ?_⟩
        simp only [mem_iInter, Finset.mem_range, mem_compl_iff] at h2
        exact h2 m hm
      obtain ⟨n1, h11, h12⟩ := hD δ hδ
      obtain ⟨n2, h21, h22⟩ := hD γ (hmem γ _ hγ fun m hm hS => by
        obtain ⟨δ', hδ'⟩ := hS
        exact Nat.find_min hex hm ⟨δ' * γ, by simpa [mul_assoc] using hδ'⟩)
      have hn : n1 = n2 := by
        rcases lt_trichotomy n1 n2 with h | h | h
        · exact absurd ⟨δ * γ⁻¹, by simpa [mul_assoc] using h11⟩ (h22 n1 h)
        · exact h
        · exact absurd ⟨γ * δ⁻¹, by simpa [mul_assoc] using h21⟩ (h12 n2 h)
      subst hn
      have hP := (hfS n1).2 _ h11 _ h21 (by
        have : ((δ : G) * g) * ((γ : G) * g)⁻¹ = ((δ * γ⁻¹ : Γ) : G) := by simp [mul_assoc]
        rw [this]; exact (δ * γ⁻¹).2)
      exact Subtype.ext (mul_right_cancel hP)

end GlobalTheory
