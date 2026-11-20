import Mathlib
import GroundTheory.AutomorphicForms.LocallyProfinite

noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Filter Function Set Topology

open scoped RestrictedProduct

variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  {K : ∀ v, Subgroup (G v)}

instance totallyDisconnectedSpace_restrictedProduct [∀ v, TotallyDisconnectedSpace (G v)] :
    TotallyDisconnectedSpace (Πʳ v, [G v, K v]) :=
  ⟨fun s _ hs => Set.subsingleton_of_image
    (f := ((↑) : (Πʳ v, [G v, K v]) → ∀ v, G v)) (fun x y h => Subtype.ext h)
    s (isTotallyDisconnected_of_totallyDisconnectedSpace _ _ (Set.subset_univ _)
      (hs.image _ RestrictedProduct.continuous_coe.continuousOn))⟩

variable (K) in

def boxSubgroup (K' : ∀ v, Subgroup (G v)) : Subgroup (Πʳ v, [G v, K v]) where
  carrier := {g | ∀ v, g v ∈ K' v}
  mul_mem' {a b} ha hb v := by
    rw [RestrictedProduct.mul_apply]
    exact (K' v).mul_mem (ha v) (hb v)
  one_mem' v := by
    rw [RestrictedProduct.one_apply]
    exact (K' v).one_mem
  inv_mem' {a} ha v := by
    rw [RestrictedProduct.inv_apply]
    exact (K' v).inv_mem (ha v)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_boxSubgroup {K' : ∀ v, Subgroup (G v)} {g : Πʳ v, [G v, K v]} :
    g ∈ boxSubgroup K K' ↔ ∀ v, g v ∈ K' v :=
  Iff.rfl

/- English proof (translation)
Use `set F := (Filter.eventually_cofinite.1 hK').toFinset`. Establish `heq : (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) = {g : Πʳ v, [G v, K v] | ∀ v, v ∉ F → g.1 v ∈ (K v : Set (G v))} ∩ ⋂ v ∈ F, (fun g : Πʳ v, [G v, K v] => g v) ⁻¹' (K' v : Set (G v))`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, mem_boxSubgroup, mem_inter_iff, mem_setOf_eq, mem_iInter, mem_preimage]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨fun v hv => ?_, fun v _ => h v⟩` and prove the remaining obligations. Establish `: K' v = K v` using `by simpa [F] using hv`. Rewrite using `[← this]`. Conclude with `h v`.

Introduce and unpack `⟨h1, h2⟩ v`. Distinguish the cases in `hv : v ∈ F`. Conclude with `h2 v hv`. Establish `: K' v = K v` using `by simpa [F] using hv`. Rewrite using `[this]`.

Conclude with `h1 v hv`. Rewrite using `[heq]`. Use `(RestrictedProduct.isOpen_forall_imp_mem hKo.out).inter ?_` and prove the remaining obligations. Conclude with `isOpen_biInter_finset fun v _ => (hK'o v).preimage (RestrictedProduct.continuous_eval v)`.
-/
theorem isOpen_boxSubgroup [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
    {K' : ∀ v, Subgroup (G v)} (hK'o : ∀ v, IsOpen (K' v : Set (G v)))
    (hK' : ∀ᶠ v in cofinite, K' v = K v) :
    IsOpen (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) := by
  classical
  set F := (Filter.eventually_cofinite.1 hK').toFinset
  have heq : (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) =
      {g : Πʳ v, [G v, K v] | ∀ v, v ∉ F → g.1 v ∈ (K v : Set (G v))} ∩
        ⋂ v ∈ F, (fun g : Πʳ v, [G v, K v] => g v) ⁻¹' (K' v : Set (G v)) := by
    ext g
    simp only [SetLike.mem_coe, mem_boxSubgroup, mem_inter_iff, mem_setOf_eq, mem_iInter,
      mem_preimage]
    constructor
    · intro h
      refine ⟨fun v hv => ?_, fun v _ => h v⟩
      have : K' v = K v := by simpa [F] using hv
      rw [← this]
      exact h v
    · rintro ⟨h1, h2⟩ v
      by_cases hv : v ∈ F
      · exact h2 v hv
      · have : K' v = K v := by simpa [F] using hv
        rw [this]
        exact h1 v hv
  rw [heq]
  refine (RestrictedProduct.isOpen_forall_imp_mem hKo.out).inter ?_
  exact isOpen_biInter_finset fun v _ => (hK'o v).preimage (RestrictedProduct.continuous_eval v)

/- English proof (translation)
Use `set S : Set ι := {v | K' v ≤ K v}`. Establish `hS : cofinite ≤ 𝓟 S` using `le_principal_iff.2 hK'`. Use `set C : Set (Πʳ v, [G v, K v]_[𝓟 S]) := ((↑) : (Πʳ v, [G v, K v]_[𝓟 S]) → ∀ v, G v) ⁻¹' (Set.pi univ fun v => (K' v : Set (G v)))`. Establish `hC : IsCompact C`. Use `(RestrictedProduct.isEmbedding_coe_of_principal.isInducing.isCompact_preimage_iff ?_).2 (isCompact_univ_pi hK'c)` and prove the remaining obligations.

Rewrite using `[RestrictedProduct.range_coe_principal]`. Introduce `f hf v hv`. Conclude with `hv (hf v (mem_univ v))`. Establish `heq : (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) = RestrictedProduct.inclusion G (fun v => (K v : Set (G v))) hS '' C`. Use extensionality with `g`.

Prove the components needed by the constructor for the conclusion. Introduce `hg`. Use `⟨⟨g.1, Filter.eventually_principal.2 fun v hv => hv (hg v)⟩, fun v _ => hg v, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression. Introduce and unpack `⟨h, hh, rfl⟩ v`.

Conclude with `hh v (mem_univ v)`. Rewrite using `[heq]`. Conclude with `hC.image (RestrictedProduct.continuous_inclusion hS)`.
-/
theorem isCompact_boxSubgroup {K' : ∀ v, Subgroup (G v)}
    (hK'c : ∀ v, IsCompact (K' v : Set (G v))) (hK' : ∀ᶠ v in cofinite, K' v ≤ K v) :
    IsCompact (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) := by
  set S : Set ι := {v | K' v ≤ K v}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 hK'
  set C : Set (Πʳ v, [G v, K v]_[𝓟 S]) :=
    ((↑) : (Πʳ v, [G v, K v]_[𝓟 S]) → ∀ v, G v) ⁻¹' (Set.pi univ fun v => (K' v : Set (G v)))
  have hC : IsCompact C := by
    refine (RestrictedProduct.isEmbedding_coe_of_principal.isInducing.isCompact_preimage_iff
      ?_).2 (isCompact_univ_pi hK'c)
    rw [RestrictedProduct.range_coe_principal]
    intro f hf v hv
    exact hv (hf v (mem_univ v))
  have heq : (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) =
      RestrictedProduct.inclusion G (fun v => (K v : Set (G v))) hS '' C := by
    ext g
    constructor
    · intro hg
      refine ⟨⟨g.1, Filter.eventually_principal.2 fun v hv => hv (hg v)⟩, fun v _ => hg v, ?_⟩
      rfl
    · rintro ⟨h, hh, rfl⟩ v
      exact hh v (mem_univ v)
  rw [heq]
  exact hC.image (RestrictedProduct.continuous_inclusion hS)

/- English proof (translation)
Use `set x₁ : ∀ v, ((K v : Set (G v)) : Type _) := fun v => ⟨1, (K v).one_mem⟩`. Establish `h1 : RestrictedProduct.structureMap G (fun v => (K v : Set (G v))) cofinite x₁ = 1` using `Subtype.ext rfl`. Rewrite `hU` using `[← h1, RestrictedProduct.nhds_eq_map_structureMap hKo.out, Filter.mem_map, nhds_pi, Filter.mem_pi]`. Take `⟨I, hI, t, ht, hIt⟩` from `hU`. Establish `hloc : ∀ v, ∃ L : Subgroup (G v), IsCompact (L : Set (G v)) ∧ IsOpen (L : Set (G v)) ∧ L ≤ K v ∧ (v ∈ I → ∀ g ∈ L, ∀ hg : g ∈ K v, (⟨g, hg⟩ : (K v : Set (G v))) ∈ t v)`.

Introduce `v`. Distinguish the cases in `hv : v ∈ I`. Establish `hnhds : ((↑) : ((K v : Set (G v)) : Type _) → G v) '' t v ∈ 𝓝 (1 : G v)` using `(hKo.out v).isOpenEmbedding_subtypeVal.image_mem_nhds.2 (ht v)`. Take `⟨L, hLc, hLU⟩` from `exists_openSubgroup_isCompact_subset hnhds`. Use `⟨L, hLc, L.isOpen, fun g hg => ?_, fun _ g hg hgK => ?_⟩` and prove the remaining obligations.

Take `⟨y, _, rfl⟩` from `hLU hg`. Conclude with `y.2`. Take `⟨y, hy, hyg⟩` from `hLU hg`. Establish `: y = ⟨g, hgK⟩` using `Subtype.ext hyg`. Rewrite using `[← this]`.

Conclude with `hy`. Conclude with `⟨K v, hKc v, hKo.out v, le_rfl, fun h => absurd h hv⟩`. Use `choose L hLc hLo hLK hLt using hloc`. Use `set K' : ∀ v, Subgroup (G v) := fun v => if v ∈ I then L v else K v`. Use `⟨K', fun v => ?_, fun v => ?_, fun v => ?_, ?_, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `by_cases hv : v ∈ I <;> simp [K', hv, hLc v, hKc v]`. Apply the tactic sequence `by_cases hv : v ∈ I <;> simp [K', hv, hLo v, hKo.out v]`. Apply the tactic sequence `by_cases hv : v ∈ I <;> simp [K', hv, hLK v]`. Conclude with `Filter.eventually_cofinite.2 (hI.subset fun v hv => by`. Assume the negation of the conclusion as `hvI`.

Conclude with `hv (by simp [K', hvI]))`. Introduce `g hg`. Establish `hgK : ∀ v, g v ∈ K v` using `fun v => by`. Distinguish the cases in `hv : v ∈ I`. Use `hg v` as an intermediate fact.

Simplify using `only [K', hv, if_true] at this`. Conclude with `hLK v this`. Use `hg v` as an intermediate fact. Simplify `this` using `[K', hv]`. Establish `hx : RestrictedProduct.structureMap G (fun v => (K v : Set (G v))) cofinite (fun v => ⟨g v, hgK v⟩) = g` using `Subtype.ext rfl`.

Rewrite using `[← hx]`. Use `hIt fun v hv => ?_` and prove the remaining obligations. Use `hg v` as an intermediate fact. Simplify using `only [K', hv, if_true] at this`. Conclude with `hLt v hv (g v) this (hgK v)`.
-/
theorem exists_boxSubgroup_subset [∀ v, IsTopologicalGroup (G v)]
    [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)] [∀ v, TotallyDisconnectedSpace (G v)]
    [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))] (hKc : ∀ v, IsCompact (K v : Set (G v)))
    {U : Set (Πʳ v, [G v, K v])} (hU : U ∈ 𝓝 1) :
    ∃ K' : ∀ v, Subgroup (G v), (∀ v, IsCompact (K' v : Set (G v))) ∧
      (∀ v, IsOpen (K' v : Set (G v))) ∧ (∀ v, K' v ≤ K v) ∧ (∀ᶠ v in cofinite, K' v = K v) ∧
        (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) ⊆ U := by
  classical
  set x₁ : ∀ v, ((K v : Set (G v)) : Type _) := fun v => ⟨1, (K v).one_mem⟩
  have h1 : RestrictedProduct.structureMap G (fun v => (K v : Set (G v))) cofinite x₁ = 1 :=
    Subtype.ext rfl
  rw [← h1, RestrictedProduct.nhds_eq_map_structureMap hKo.out, Filter.mem_map, nhds_pi,
    Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hIt⟩ := hU
  have hloc : ∀ v, ∃ L : Subgroup (G v), IsCompact (L : Set (G v)) ∧ IsOpen (L : Set (G v)) ∧
      L ≤ K v ∧ (v ∈ I → ∀ g ∈ L, ∀ hg : g ∈ K v, (⟨g, hg⟩ : (K v : Set (G v))) ∈ t v) := by
    intro v
    by_cases hv : v ∈ I
    · have hnhds : ((↑) : ((K v : Set (G v)) : Type _) → G v) '' t v ∈ 𝓝 (1 : G v) :=
        (hKo.out v).isOpenEmbedding_subtypeVal.image_mem_nhds.2 (ht v)
      obtain ⟨L, hLc, hLU⟩ := exists_openSubgroup_isCompact_subset hnhds
      refine ⟨L, hLc, L.isOpen, fun g hg => ?_, fun _ g hg hgK => ?_⟩
      · obtain ⟨y, _, rfl⟩ := hLU hg
        exact y.2
      · obtain ⟨y, hy, hyg⟩ := hLU hg
        have : y = ⟨g, hgK⟩ := Subtype.ext hyg
        rw [← this]
        exact hy
    · exact ⟨K v, hKc v, hKo.out v, le_rfl, fun h => absurd h hv⟩
  choose L hLc hLo hLK hLt using hloc
  set K' : ∀ v, Subgroup (G v) := fun v => if v ∈ I then L v else K v
  refine ⟨K', fun v => ?_, fun v => ?_, fun v => ?_, ?_, ?_⟩
  · by_cases hv : v ∈ I <;> simp [K', hv, hLc v, hKc v]
  · by_cases hv : v ∈ I <;> simp [K', hv, hLo v, hKo.out v]
  · by_cases hv : v ∈ I <;> simp [K', hv, hLK v]
  · exact Filter.eventually_cofinite.2 (hI.subset fun v hv => by
      by_contra hvI
      exact hv (by simp [K', hvI]))
  · intro g hg
    have hgK : ∀ v, g v ∈ K v := fun v => by
      by_cases hv : v ∈ I
      · have := hg v
        simp only [K', hv, if_true] at this
        exact hLK v this
      · have := hg v
        simpa [K', hv] using this
    have hx : RestrictedProduct.structureMap G (fun v => (K v : Set (G v))) cofinite
        (fun v => ⟨g v, hgK v⟩) = g := Subtype.ext rfl
    rw [← hx]
    refine hIt fun v hv => ?_
    have := hg v
    simp only [K', hv, if_true] at this
    exact hLt v hv (g v) this (hgK v)

end RestrictedTensor

end GroundTheory.Automorphic
