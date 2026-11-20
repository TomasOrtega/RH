import Mathlib

open MeasureTheory Set Topology

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Establish `h1 : IsOpen ({1} : Set Γ)` using `isOpen_discrete _`. Take `⟨W, hW, hWeq⟩` from `isOpen_induced_iff.mp h1`. Use `⟨W, hW, ?_, ?_⟩` and prove the remaining obligations. Establish `: (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' W` using `by rw [hWeq]; rfl`. Simplify using `using this`.

Introduce `γ hγ hγW`. Establish `: (⟨γ, hγ⟩ : Γ) ∈ ((↑) : Γ → G) ⁻¹' W` using `hγW`. Rewrite `this` using `[hWeq]`. Simplify using `using congrArg Subtype.val (Set.mem_singleton_iff.mp this)`.
-/
theorem exists_isOpen_inter_subgroup_eq_one (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧ ∀ γ ∈ Γ, γ ∈ W → γ = 1 := by
  have h1 : IsOpen ({1} : Set Γ) := isOpen_discrete _
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp h1
  refine ⟨W, hW, ?_, ?_⟩
  · have : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' W := by rw [hWeq]; rfl
    simpa using this
  · intro γ hγ hγW
    have : (⟨γ, hγ⟩ : Γ) ∈ ((↑) : Γ → G) ⁻¹' W := hγW
    rw [hWeq] at this
    simpa using congrArg Subtype.val (Set.mem_singleton_iff.mp this)

variable [LocallyCompactSpace G]

/- English proof (translation)
Take `⟨W, hWo, hW1, hWΓ⟩` from `exists_isOpen_inter_subgroup_eq_one Γ`. Establish `hcont : Continuous fun p : G × G => p.1 * p.2⁻¹` using `by fun_prop`. Establish `hmem : (c, c) ∈ (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' W` using `by simpa using hW1`. Take `⟨U₁, U₂, hU₁, hU₂, hc₁, hc₂, hsub⟩` from `isOpen_prod_iff.mp (hWo.preimage hcont) c c hmem`. Take `⟨L, hL, hLn⟩` from `exists_compact_mem_nhds c`.

Use `⟨U₁ ∩ U₂ ∩ interior L, (hU₁.inter hU₂).inter isOpen_interior, ⟨⟨hc₁, hc₂⟩, mem_interior_iff_mem_nhds.mpr hLn⟩, ⟨L, hL, fun x hx => interior_subset hx.2⟩, ?_⟩` and prove the remaining obligations. Introduce `γ hγ x hx hγx`. Apply `hWΓ γ hγ` to reduce the goal to its premises. Establish `: (γ * x, x) ∈ U₁ ×ˢ U₂` using `⟨hγx.1.1, hx.1.2⟩`. Simplify using `using hsub this`.
-/
theorem exists_isOpen_small (Γ : Subgroup G) [DiscreteTopology Γ] (c : G) :
    ∃ V : Set G, IsOpen V ∧ c ∈ V ∧ (∃ L, IsCompact L ∧ V ⊆ L) ∧
      ∀ γ ∈ Γ, ∀ x ∈ V, γ * x ∈ V → γ = 1 := by
  obtain ⟨W, hWo, hW1, hWΓ⟩ := exists_isOpen_inter_subgroup_eq_one Γ
  have hcont : Continuous fun p : G × G => p.1 * p.2⁻¹ := by fun_prop
  have hmem : (c, c) ∈ (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' W := by simpa using hW1
  obtain ⟨U₁, U₂, hU₁, hU₂, hc₁, hc₂, hsub⟩ :=
    isOpen_prod_iff.mp (hWo.preimage hcont) c c hmem
  obtain ⟨L, hL, hLn⟩ := exists_compact_mem_nhds c
  refine ⟨U₁ ∩ U₂ ∩ interior L, (hU₁.inter hU₂).inter isOpen_interior,
    ⟨⟨hc₁, hc₂⟩, mem_interior_iff_mem_nhds.mpr hLn⟩, ⟨L, hL, fun x hx => interior_subset hx.2⟩, ?_⟩
  intro γ hγ x hx hγx
  apply hWΓ γ hγ
  have : (γ * x, x) ∈ U₁ ×ˢ U₂ := ⟨hγx.1.1, hx.1.2⟩
  simpa using hsub this

def saturate (Γ : Subgroup G) (A : Set G) : Set G := {y | ∃ γ ∈ Γ, γ⁻¹ * y ∈ A}

/- English proof (translation)
Establish `: saturate Γ A = ⋃ γ : Γ, (fun y => (γ : G)⁻¹ * y) ⁻¹' A`. Use extensionality with `y`. Simplify using `[saturate]`. Rewrite using `[this]`. Conclude with `isOpen_iUnion fun γ => hA.preimage (by fun_prop)`.
-/
theorem isOpen_saturate (Γ : Subgroup G) {A : Set G} (hA : IsOpen A) : IsOpen (saturate Γ A) := by
  have : saturate Γ A = ⋃ γ : Γ, (fun y => (γ : G)⁻¹ * y) ⁻¹' A := by
    ext y; simp [saturate]
  rw [this]
  exact isOpen_iUnion fun γ => hA.preimage (by fun_prop)

def firstHit (Γ : Subgroup G) (A : ℕ → Set G) : Set G :=
  ⋃ i, (A i \ saturate Γ (⋃ j < i, A j))

/- English proof (translation)
Use `MeasurableSet.iUnion fun i => (hA i).measurableSet.diff ?_` and prove the remaining obligations. Conclude with `(isOpen_saturate Γ (isOpen_biUnion fun j _ => hA j)).measurableSet`.
-/
theorem measurableSet_firstHit [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    {A : ℕ → Set G} (hA : ∀ i, IsOpen (A i)) : MeasurableSet (firstHit Γ A) := by
  refine MeasurableSet.iUnion fun i => (hA i).measurableSet.diff ?_
  exact (isOpen_saturate Γ (isOpen_biUnion fun j _ => hA j)).measurableSet

/- English proof (translation)
Establish `hex : ∃ i, ∃ γ ∈ Γ, γ * x ∈ A i` using `hcov x`. Set `i₀` to `Nat.find hex`. Take `⟨γ, hγ, hγx⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ j < i₀, ∀ δ ∈ Γ, δ * x ∉ A j` using `fun j hj δ hδ hδx => Nat.find_min hex hj ⟨δ, hδ, hδx⟩`. Establish `hγF : (γ : G) * x ∈ firstHit Γ A`.

Use `mem_iUnion.mpr ⟨i₀, hγx, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨δ, hδ, hδy⟩`. Take `⟨j, hj⟩` from `mem_iUnion.mp hδy`. Take `⟨hj, hjA⟩` from `mem_iUnion.mp hj`. Use `hmin j hj (δ⁻¹ * γ) (Γ.mul_mem (Γ.inv_mem hδ) hγ) ?_` and prove the remaining obligations.

Simplify `hjA` using `[mul_assoc]`. Use `⟨⟨γ, hγ⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show ((⟨γ, hγ⟩ : Γ) • x ∈ firstHit Γ A)`. Rewrite using `[Subgroup.smul_def, smul_eq_mul]`. Conclude with `hγF`.

Establish `key : ∀ (α β : Γ), (α : G) * x ∈ firstHit Γ A → (β : G) * x ∈ firstHit Γ A → ∀ i i', (α : G) * x ∈ A i \ saturate Γ (⋃ j < i, A j) → (β : G) * x ∈ A i' \ saturate Γ (⋃ j < i', A j) → i ≤ i'`. Introduce `α β _ _ i i' hα hβ`. Assume the negation of the conclusion as `hlt'`. Establish `hlt` using `not_le.mp hlt'`. Apply `hα.2` to reduce the goal to its premises.

Use `⟨(α : G) * (β : G)⁻¹, Γ.mul_mem α.2 (Γ.inv_mem β.2), ?_⟩` and prove the remaining obligations. Use `mem_iUnion₂.mpr ⟨i', hlt, ?_⟩` and prove the remaining obligations. Simplify `hβ.1` using `[mul_assoc]`. Introduce `β hβ`. Rewrite `hβ` using `[Subgroup.smul_def, smul_eq_mul]`.

Take `⟨i, hi⟩` from `mem_iUnion.mp hβ`. Take `⟨i', hi'⟩` from `mem_iUnion.mp hγF`. Establish `h1` using `key β ⟨γ, hγ⟩ hβ hγF i i' hi hi'`. Establish `h2` using `key ⟨γ, hγ⟩ β hγF hβ i' i hi' hi`. Establish `hii : i = i'` using `le_antisymm h1 h2`.

Substitute `hii` using the available equality. Establish `hmul` using `hinj i ((γ : G) * (β : G)⁻¹) (Γ.mul_mem hγ (Γ.inv_mem β.2)) _ hi.1 (by simpa [mul_assoc] using hi'.1)`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `: (γ : G) = β`. Use `congrArg (· * (β : G)) hmul` as an intermediate fact.

Simplify using `using this`. Conclude with `this.symm`.
-/
theorem existsUnique_mem_firstHit (Γ : Subgroup G) (A : ℕ → Set G)
    (hinj : ∀ i, ∀ γ ∈ Γ, ∀ x ∈ A i, γ * x ∈ A i → γ = 1)
    (hcov : ∀ x : G, ∃ i, ∃ γ ∈ Γ, γ * x ∈ A i) (x : G) :
    ∃! γ : Γ, γ • x ∈ firstHit Γ A := by
  classical
  have hex : ∃ i, ∃ γ ∈ Γ, γ * x ∈ A i := hcov x
  let i₀ := Nat.find hex
  obtain ⟨γ, hγ, hγx⟩ := Nat.find_spec hex
  have hmin : ∀ j < i₀, ∀ δ ∈ Γ, δ * x ∉ A j := fun j hj δ hδ hδx =>
    Nat.find_min hex hj ⟨δ, hδ, hδx⟩
  have hγF : (γ : G) * x ∈ firstHit Γ A := by
    refine mem_iUnion.mpr ⟨i₀, hγx, ?_⟩
    rintro ⟨δ, hδ, hδy⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hδy
    obtain ⟨hj, hjA⟩ := mem_iUnion.mp hj
    refine hmin j hj (δ⁻¹ * γ) (Γ.mul_mem (Γ.inv_mem hδ) hγ) ?_
    simpa [mul_assoc] using hjA
  refine ⟨⟨γ, hγ⟩, ?_, ?_⟩
  · show ((⟨γ, hγ⟩ : Γ) • x ∈ firstHit Γ A)
    rw [Subgroup.smul_def, smul_eq_mul]
    exact hγF
  ·
    have key : ∀ (α β : Γ), (α : G) * x ∈ firstHit Γ A → (β : G) * x ∈ firstHit Γ A →
        ∀ i i', (α : G) * x ∈ A i \ saturate Γ (⋃ j < i, A j) →
          (β : G) * x ∈ A i' \ saturate Γ (⋃ j < i', A j) → i ≤ i' := by
      intro α β _ _ i i' hα hβ
      by_contra hlt'
      have hlt := not_le.mp hlt'
      apply hα.2
      refine ⟨(α : G) * (β : G)⁻¹, Γ.mul_mem α.2 (Γ.inv_mem β.2), ?_⟩
      refine mem_iUnion₂.mpr ⟨i', hlt, ?_⟩
      simpa [mul_assoc] using hβ.1
    intro β hβ
    rw [Subgroup.smul_def, smul_eq_mul] at hβ
    obtain ⟨i, hi⟩ := mem_iUnion.mp hβ
    obtain ⟨i', hi'⟩ := mem_iUnion.mp hγF
    have h1 := key β ⟨γ, hγ⟩ hβ hγF i i' hi hi'
    have h2 := key ⟨γ, hγ⟩ β hγF hβ i' i hi' hi
    have hii : i = i' := le_antisymm h1 h2
    subst hii
    have hmul := hinj i ((γ : G) * (β : G)⁻¹) (Γ.mul_mem hγ (Γ.inv_mem β.2)) _ hi.1
      (by simpa [mul_assoc] using hi'.1)
    apply Subtype.ext
    have : (γ : G) = β := by
      have := congrArg (· * (β : G)) hmul
      simpa using this
    exact this.symm

/- English proof (translation)
Use `choose V hVo hcV hVL hVinj using exists_isOpen_small Γ`. Take `⟨t, ht⟩` from `hC.elim_finite_subcover V hVo (fun c _ => mem_iUnion.mpr ⟨c, hcV c⟩)`. Set `l` to `t.toList`. Set `A : ℕ → Set G` to `fun i => if h : i < l.length then V (l.get ⟨i, h⟩) else ∅`. Establish `hAo : ∀ i, IsOpen (A i)` using `fun i => by`.

Simplify using `only [A]`. Use `split_ifs`. Conclude with `hVo _`. Conclude with `isOpen_empty`. Establish `hinj : ∀ i, ∀ γ ∈ Γ, ∀ x ∈ A i, γ * x ∈ A i → γ = 1`.

Introduce `i γ hγ x hx hγx`. Simplify using `only [A] at hx hγx`. Use `split_ifs at hx hγx with h`. Conclude with `hVinj _ γ hγ x hx hγx`. Conclude with `hx.elim`.

Establish `hcovA : ∀ x : G, ∃ i, ∃ γ ∈ Γ, γ * x ∈ A i`. Introduce `x`. Take `⟨γ, hγ, hγC⟩` from `hcov x`. Take `⟨c, hc⟩` from `mem_iUnion.mp (ht hγC)`. Take `⟨hct, hcV'⟩` from `mem_iUnion.mp hc`.

Take `⟨n, hn, hnc⟩` from `List.getElem_of_mem (Finset.mem_toList.mpr hct)`. Use `⟨n, γ, hγ, ?_⟩` and prove the remaining obligations. Use `show γ * x ∈ (if h : n < l.length then V (l.get ⟨n, h⟩) else ∅)`. Rewrite using `[dif_pos hn]`. Establish `hget : l.get ⟨n, hn⟩ = c` using `hnc`.

Rewrite using `[hget]`. Conclude with `hcV'`. Use `choose L hL hVL' using hVL`. Use `⟨firstHit Γ A, ⋃ c ∈ t, L c, measurableSet_firstHit Γ hAo, t.isCompact_biUnion fun c _ => hL c, ?_, existsUnique_mem_firstHit Γ A hinj hcovA⟩` and prove the remaining obligations. Introduce `y hy`.

Take `⟨i, hi, -⟩` from `mem_iUnion.mp hy`. Simplify using `only [A] at hi`. Use `split_ifs at hi with h`. Conclude with `mem_iUnion₂.mpr ⟨l.get ⟨i, h⟩, Finset.mem_toList.mp (List.get_mem l _), hVL' _ hi⟩`. Conclude with `hi.elim`.
-/
theorem exists_isFundamentalDomain_of_isCompact [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] {C : Set G} (hC : IsCompact C)
    (hcov : ∀ x : G, ∃ γ ∈ Γ, γ * x ∈ C) :
    ∃ 𝓕 L : Set G, MeasurableSet 𝓕 ∧ IsCompact L ∧ 𝓕 ⊆ L ∧ ∀ x, ∃! γ : Γ, γ • x ∈ 𝓕 := by
  classical
  choose V hVo hcV hVL hVinj using exists_isOpen_small Γ
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover V hVo (fun c _ => mem_iUnion.mpr ⟨c, hcV c⟩)
  let l := t.toList
  let A : ℕ → Set G := fun i => if h : i < l.length then V (l.get ⟨i, h⟩) else ∅
  have hAo : ∀ i, IsOpen (A i) := fun i => by
    simp only [A]; split_ifs
    · exact hVo _
    · exact isOpen_empty
  have hinj : ∀ i, ∀ γ ∈ Γ, ∀ x ∈ A i, γ * x ∈ A i → γ = 1 := by
    intro i γ hγ x hx hγx
    simp only [A] at hx hγx
    split_ifs at hx hγx with h
    · exact hVinj _ γ hγ x hx hγx
    · exact hx.elim
  have hcovA : ∀ x : G, ∃ i, ∃ γ ∈ Γ, γ * x ∈ A i := by
    intro x
    obtain ⟨γ, hγ, hγC⟩ := hcov x
    obtain ⟨c, hc⟩ := mem_iUnion.mp (ht hγC)
    obtain ⟨hct, hcV'⟩ := mem_iUnion.mp hc
    obtain ⟨n, hn, hnc⟩ := List.getElem_of_mem (Finset.mem_toList.mpr hct)
    refine ⟨n, γ, hγ, ?_⟩
    show γ * x ∈ (if h : n < l.length then V (l.get ⟨n, h⟩) else ∅)
    rw [dif_pos hn]
    have hget : l.get ⟨n, hn⟩ = c := hnc
    rw [hget]
    exact hcV'
  choose L hL hVL' using hVL
  refine ⟨firstHit Γ A, ⋃ c ∈ t, L c, measurableSet_firstHit Γ hAo,
    t.isCompact_biUnion fun c _ => hL c, ?_, existsUnique_mem_firstHit Γ A hinj hcovA⟩
  intro y hy
  obtain ⟨i, hi, -⟩ := mem_iUnion.mp hy
  simp only [A] at hi
  split_ifs at hi with h
  · exact mem_iUnion₂.mpr ⟨l.get ⟨i, h⟩, Finset.mem_toList.mp (List.get_mem l _), hVL' _ hi⟩
  · exact hi.elim

end GroundTheory.Heights₂.Theta
