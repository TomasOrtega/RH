import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def LCompInt : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p →
  ConnectedSpace X → IsIntegral X

/- English proof (translation)
Take `⟨S, hSf, hSc, hSi, hSu⟩` from `TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_univ (X := α))`. Establish `hin : ∀ x : α, ∃ t ∈ S, x ∈ t` using `fun x => by`. Establish `: x ∈ ⋃₀ S` using `hSu ▸ Set.mem_univ x`. Simplify using `using this`. Establish `hsub : ∀ t ∈ S, ∀ z ∈ t, t ⊆ connectedComponent z` using `fun t ht z hz => (IsIrreducible.isConnected (hSi t ht)).isPreconnected.subset_connectedComponent hz`.

Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Establish `: Finite S` using `hSf.to_subtype`. Use `Finite.of_surjective (fun t : S => (((IsIrreducible.nonempty (hSi t.1 t.2)).some : α) : _root_.ConnectedComponents α)) ?_` and prove the remaining obligations. Introduce `c`. Take `⟨x, rfl⟩` from `ConnectedComponents.surjective_coe c`.

Take `⟨t, ht, hxt⟩` from `hin x`. Use `⟨⟨t, ht⟩, ConnectedComponents.coe_eq_coe.mpr ?_⟩` and prove the remaining obligations. Conclude with `connectedComponent_eq (hsub t ht _ (IsIrreducible.nonempty (hSi t ht)).some_mem hxt)`. Establish `hc : (connectedComponent x)ᶜ = ⋃₀ {t ∈ S | Disjoint t (connectedComponent x)}`. Use extensionality with `z`.

Simplify using `only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Take `⟨t, ht, hzt⟩` from `hin z`. Use `⟨t, ⟨ht, Set.disjoint_left.mpr fun w hwt hwx => hz ?_⟩, hzt⟩` and prove the remaining obligations.

Rewrite using `[connectedComponent_eq hwx]`. Conclude with `hsub t ht w hwt hzt`. Introduce and unpack `⟨t, ⟨_, hd⟩, hzt⟩ hzx`. Conclude with `Set.disjoint_left.mp hd hzt hzx`. Rewrite using `[← isClosed_compl_iff, hc]`.

Establish `hfin : ({t ∈ S | Disjoint t (connectedComponent x)}).Finite` using `hSf.subset (Set.sep_subset _ _)`. Rewrite using `[Set.sUnion_eq_biUnion]`. Conclude with `hfin.isClosed_biUnion fun t ht => hSc t ht.1`.
-/
theorem noeth_components {α : Type*} [TopologicalSpace α] [TopologicalSpace.NoetherianSpace α] :
    Finite (_root_.ConnectedComponents α) ∧ ∀ x : α, IsOpen (connectedComponent x) := by
  classical
  obtain ⟨S, hSf, hSc, hSi, hSu⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_univ (X := α))
  have hin : ∀ x : α, ∃ t ∈ S, x ∈ t := fun x => by
    have : x ∈ ⋃₀ S := hSu ▸ Set.mem_univ x
    simpa using this
  have hsub : ∀ t ∈ S, ∀ z ∈ t, t ⊆ connectedComponent z := fun t ht z hz =>
    (IsIrreducible.isConnected (hSi t ht)).isPreconnected.subset_connectedComponent hz
  refine ⟨?_, fun x => ?_⟩
  · have : Finite S := hSf.to_subtype
    refine Finite.of_surjective (fun t : S => (((IsIrreducible.nonempty (hSi t.1 t.2)).some : α) : _root_.ConnectedComponents α)) ?_
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨t, ht, hxt⟩ := hin x
    refine ⟨⟨t, ht⟩, ConnectedComponents.coe_eq_coe.mpr ?_⟩
    exact connectedComponent_eq (hsub t ht _ (IsIrreducible.nonempty (hSi t ht)).some_mem hxt)
  · have hc : (connectedComponent x)ᶜ = ⋃₀ {t ∈ S | Disjoint t (connectedComponent x)} := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_setOf_eq]
      constructor
      · intro hz
        obtain ⟨t, ht, hzt⟩ := hin z
        refine ⟨t, ⟨ht, Set.disjoint_left.mpr fun w hwt hwx => hz ?_⟩, hzt⟩
        rw [connectedComponent_eq hwx]; exact hsub t ht w hwt hzt
      · rintro ⟨t, ⟨_, hd⟩, hzt⟩ hzx
        exact Set.disjoint_left.mp hd hzt hzx
    rw [← isClosed_compl_iff, hc]
    have hfin : ({t ∈ S | Disjoint t (connectedComponent x)}).Finite := hSf.subset (Set.sep_subset _ _)
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun t ht => hSc t ht.1

/- English proof (translation)
Use `hp.1` as an intermediate fact. Use `hp.2` as an intermediate fact. Establish `: Smooth p` using `SmoothOfRelativeDimension.smooth d p`. Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace p`. Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian p`.

Establish `: IsNoetherian X` using `{}`. Conclude with `noeth_components`.
-/
theorem comp_fin {k : Type} [Field k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) :
    Finite (_root_.ConnectedComponents X) ∧ ∀ x : X, IsOpen (connectedComponent x) := by
  have := hp.1; have := hp.2
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian X := {}
  exact noeth_components

/- English proof (translation)
Establish `: IsClosedImmersion U.ι` using `.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU)`. Use `hp.1` as an intermediate fact. Use `hp.2` as an intermediate fact. Establish `hs` using `smoothOfRelativeDimension_comp (n := 0) (m := d) U.ι p`. Rewrite `hs` using `[Nat.zero_add]`.

Use `⟨⟨inferInstance, hs⟩, ?_⟩` and prove the remaining obligations. Take `⟨N, ι, hι, hιp⟩` from `hX`. Conclude with `⟨N, U.ι ≫ ι, inferInstance, by rw [Category.assoc, hιp]⟩`.
-/
theorem clopen_smoothProper_projective {k : Type} [Field k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (hX : IsProj p)
    (U : X.Opens) (hU : IsClosed (U : Set X)) : SP d (U.ι ≫ p) ∧ IsProj (U.ι ≫ p) := by
  have : IsClosedImmersion U.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU)
  have := hp.1
  have := hp.2
  have hs := smoothOfRelativeDimension_comp (n := 0) (m := d) U.ι p
  rw [Nat.zero_add] at hs
  refine ⟨⟨inferInstance, hs⟩, ?_⟩
  obtain ⟨N, ι, hι, hιp⟩ := hX
  exact ⟨N, U.ι ≫ ι, inferInstance, by rw [Category.assoc, hιp]⟩

end LateralTheory.EtaleTrace
