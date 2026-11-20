import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOfStableUnderGeneralizationOfConstructible

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Introduce `X Z hZ hpc`. Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `x hx`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Establish `hU : IsAffineOpen U` using `hU`.

Establish `key : ∀ (p : PrimeSpectrum Γ(X, U)) (a : Γ(X, U)), hU.fromSpec p ∈ X.basicOpen a ↔ a ∉ p.asIdeal`. Introduce `p a`. Establish `h` using `hU.fromSpec_preimage_basicOpen a`. Establish `h2 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a ↔ p ∈ PrimeSpectrum.basicOpen a`. Rewrite using `[h]`.

Both sides reduce to the same expression. Conclude with `h2`. Establish `hopen : IsOpen (X` using `PrimeSpectrum Γ(X, U)) (hU.fromSpec ⁻¹' Z) := by`. Use `GlobalTheory.isOpen_of_stableUnderGeneralization_of_constructible_pieces Γ(X, U) _ ?_ ?_` and prove the remaining obligations. Introduce `p q hpq hp`.

Conclude with `hZ (hpq.map hU.fromSpec.continuous) hp`. Introduce `p hp`. Take `⟨W, W', J, hWW', hpW, hpJ, hsub⟩` from `hpc _ hp`. Establish `hpU : hU.fromSpec p ∈ U` using `hU.range_fromSpec.le ⟨p, rfl⟩`. Take `⟨a, haW, hpa⟩` from `hU.exists_basicOpen_le (V := W) ⟨_, hpW⟩ hpU`.

Establish `hc : ∀ c : Γ(X, W'), ∃ c' : Γ(X, U), X.basicOpen c' = X.basicOpen a ⊓ X.basicOpen c`. Introduce `c`. Take `⟨c', hc'⟩` from `hU.basicOpen_basicOpen_is_basicOpen a (X.presheaf.map (homOfLE (haW.trans hWW')).op c)`. Conclude with `⟨c', by rw [hc', Scheme.basicOpen_res]⟩`. Use `choose g hg using hc`.

Use `⟨a, J.image g, (key p a).1 hpa, ?_, ?_⟩` and prove the remaining obligations. Introduce `c' hc'`. Take `⟨c, hcJ, rfl⟩` from `Finset.mem_image.1 hc'`. Assume the negation of the conclusion as `hn`. Use `(key p _).2 hn` as an intermediate fact.

Rewrite `this` using `[hg]`. Conclude with `hpJ c hcJ this.2`. Introduce `t hta htI`. Establish `hta'` using `(key t a).2 hta`. Use `hsub _ (haW hta') fun c hcJ htc => ?_` and prove the remaining obligations.

Use `(key t (g c)).1 ?_ (htI _ (Finset.mem_image_of_mem g hcJ))` and prove the remaining obligations. Rewrite using `[hg]`. Conclude with `⟨hta', htc⟩`. Use `⟨hU.fromSpec '' (hU.fromSpec ⁻¹' Z), Set.image_preimage_subset _ _, hU.fromSpec.isOpenEmbedding.isOpenMap _ hopen, ?_⟩` and prove the remaining obligations. Take `⟨p, rfl⟩` from `hU.range_fromSpec.ge hxU`.

Conclude with `⟨p, hx, rfl⟩`.
-/
theorem isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces :
    ∀ (X : Scheme.{0}) (Z : Set X), StableUnderGeneralization Z → (∀ x ∈ Z, ∃ (W W' : X.Opens) (J : Finset Γ(X, W')), W ≤ W' ∧ x ∈ W ∧ (∀ c ∈ J, x ∉ X.basicOpen c) ∧ ∀ y ∈ W, (∀ c ∈ J, y ∉ X.basicOpen c) → y ∈ Z) → IsOpen Z := by
  classical
  intro X Z hZ hpc
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  have key : ∀ (p : PrimeSpectrum Γ(X, U)) (a : Γ(X, U)),
      hU.fromSpec p ∈ X.basicOpen a ↔ a ∉ p.asIdeal := by
    intro p a
    have h := hU.fromSpec_preimage_basicOpen a
    have h2 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a ↔ p ∈ PrimeSpectrum.basicOpen a := by
      rw [h]; rfl
    exact h2
  have hopen : IsOpen (X := PrimeSpectrum Γ(X, U)) (hU.fromSpec ⁻¹' Z) := by
    refine GlobalTheory.isOpen_of_stableUnderGeneralization_of_constructible_pieces Γ(X, U) _ ?_ ?_
    · intro p q hpq hp
      exact hZ (hpq.map hU.fromSpec.continuous) hp
    · intro p hp
      obtain ⟨W, W', J, hWW', hpW, hpJ, hsub⟩ := hpc _ hp
      have hpU : hU.fromSpec p ∈ U := hU.range_fromSpec.le ⟨p, rfl⟩
      obtain ⟨a, haW, hpa⟩ := hU.exists_basicOpen_le (V := W) ⟨_, hpW⟩ hpU
      have hc : ∀ c : Γ(X, W'), ∃ c' : Γ(X, U),
          X.basicOpen c' = X.basicOpen a ⊓ X.basicOpen c := by
        intro c
        obtain ⟨c', hc'⟩ := hU.basicOpen_basicOpen_is_basicOpen a
          (X.presheaf.map (homOfLE (haW.trans hWW')).op c)
        exact ⟨c', by rw [hc', Scheme.basicOpen_res]⟩
      choose g hg using hc
      refine ⟨a, J.image g, (key p a).1 hpa, ?_, ?_⟩
      · intro c' hc'
        obtain ⟨c, hcJ, rfl⟩ := Finset.mem_image.1 hc'
        by_contra hn
        have := (key p _).2 hn
        rw [hg] at this
        exact hpJ c hcJ this.2
      · intro t hta htI
        have hta' := (key t a).2 hta
        refine hsub _ (haW hta') fun c hcJ htc => ?_
        refine (key t (g c)).1 ?_ (htI _ (Finset.mem_image_of_mem g hcJ))
        rw [hg]
        exact ⟨hta', htc⟩
  refine ⟨hU.fromSpec '' (hU.fromSpec ⁻¹' Z), Set.image_preimage_subset _ _,
    hU.fromSpec.isOpenEmbedding.isOpenMap _ hopen, ?_⟩
  obtain ⟨p, rfl⟩ := hU.range_fromSpec.ge hxU
  exact ⟨p, hx, rfl⟩

end GlobalTheory
