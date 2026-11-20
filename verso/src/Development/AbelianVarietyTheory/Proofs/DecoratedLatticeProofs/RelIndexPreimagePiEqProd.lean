import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMemProjEqOnFinset

namespace GlobalTheory

/- English proof (translation)
Introduce `G _ r H _ φ U U' K J _ hUK hsurj hU'`. Set `f : U →* (∀ i, K i)` to `{ toFun := fun g i => ⟨φ g i, hUK g g.2 i⟩ map_one' := by`. Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Use the proof step `map_mul' := by`. Introduce `a b`. Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `}`.

Establish `hf : Function.Surjective f`. Introduce `x`. Take `⟨g, hg, hx⟩` from `hsurj (fun i => (x i : H i)) (fun i => (x i).2)`. Use `⟨⟨g, hg⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `φ g i = _`. Rewrite using `[hx]`. Establish `hc : U'.subgroupOf U = (Subgroup.pi Set.univ fun i => (J i).subgroupOf (K i)).comap f`. Use extensionality with `g`.

Rewrite using `[Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hU']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩ i -`. Conclude with `Subgroup.mem_subgroupOf.2 (h i)`. Introduce `h`.

Conclude with `⟨g.2, fun i => Subgroup.mem_subgroupOf.1 (h i (Set.mem_univ _))⟩`. Rewrite using `[Subgroup.relIndex, hc, Subgroup.index_comap_of_surjective _ hf, index_pi_univ_dep]`. Both sides reduce to the same expression.
-/
theorem relIndex_preimage_pi_eq_prod :
    ∀ {G : Type} [Group G] {r : ℕ} {H : Fin r → Type} [∀ i, Group (H i)]
      (φ : G →* ((i : Fin r) → H i)) (U U' : Subgroup G) (K J : (i : Fin r) → Subgroup (H i)),
      (∀ i, J i ≤ K i) → (∀ g ∈ U, ∀ i, φ g i ∈ K i) →
      (∀ x : (i : Fin r) → H i, (∀ i, x i ∈ K i) → ∃ g ∈ U, φ g = x) →
      (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i, φ g i ∈ J i) →
      U'.relIndex U = ∏ i, (J i).relIndex (K i) := by
  intro G _ r H _ φ U U' K J _ hUK hsurj hU'
  let f : U →* (∀ i, K i) :=
    { toFun := fun g i => ⟨φ g i, hUK g g.2 i⟩
      map_one' := by
        funext i
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        funext i
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, hg, hx⟩ := hsurj (fun i => (x i : H i)) (fun i => (x i).2)
    refine ⟨⟨g, hg⟩, ?_⟩
    funext i
    apply Subtype.ext
    change φ g i = _
    rw [hx]
  have hc : U'.subgroupOf U =
      (Subgroup.pi Set.univ fun i => (J i).subgroupOf (K i)).comap f := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hU']
    constructor
    · rintro ⟨-, h⟩ i -
      exact Subgroup.mem_subgroupOf.2 (h i)
    · intro h
      exact ⟨g.2, fun i => Subgroup.mem_subgroupOf.1 (h i (Set.mem_univ _))⟩
  rw [Subgroup.relIndex, hc, Subgroup.index_comap_of_surjective _ hf, index_pi_univ_dep]
  rfl

end GlobalTheory
