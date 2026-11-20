import Development.EtaleCohomology.CohomologicalPurity.LeafExcSheafCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def pcok (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A) (b : B' ⟶ B)
    (w : i' ≫ b = a ≫ i) : cokernel ((freeP R).map i') ⟶ cokernel ((freeP R).map i) :=
  cokernel.map _ _ ((freeP R).map a) ((freeP R).map b) (by rw [← Functor.map_comp, ← Functor.map_comp, w])

/- English proof (translation)
Rewrite `hW` using `[GrothendieckTopology.W_iff]`. Set `G` to `presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))`. Establish `w' : (freeP R).map i' ≫ (freeP R).map b = (freeP R).map a ≫ (freeP R).map i`. Rewrite using `[← Functor.map_comp, ← Functor.map_comp, w]`. Establish `key` using `cokernel_map_comp_cokernelComparison ((freeP R).map i') G ((freeP R).map i) ((freeP R).map a) ((freeP R).map b) w'`.

Establish `h2 : IsIso (cokernelComparison ((freeP R).map i') G ≫ G.map (pcok R i' i a b w))`. Establish `: IsIso (G.map (pcok R i' i a b w))` using `hW`. Use `infer_instance`. Establish `h3 : IsIso (cokernel.map (G.map ((freeP R).map i')) (G.map ((freeP R).map i)) (G.map ((freeP R).map a)) (G.map ((freeP R).map b)) (by rw [← G.map_comp, w', G.map_comp]))`. Establish `h4 : IsIso (cokernel.map (G.map ((freeP R).map i')) (G.map ((freeP R).map i)) (G.map ((freeP R).map a)) (G.map ((freeP R).map b)) (by rw [← G.map_comp, w', G.map_comp]) ≫ cokernelComparison _ G)`.

Rewrite using `[key]`. Conclude with `h2`. Conclude with `IsIso.of_isIso_comp_right _ (cokernelComparison ((freeP R).map i) G)`. Conclude with `h3`.
-/
theorem isIso_cokernel_map_of_etale_local_iso (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i) (hW : Scheme.etaleTopology.W (pcok R i' i a b w)) :
    IsIso (cokernel.map ((free R).map i') ((free R).map i) ((free R).map a) ((free R).map b)
      (by rw [← Functor.map_comp, ← Functor.map_comp, w])) := by
  rw [GrothendieckTopology.W_iff] at hW
  let G := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  have w' : (freeP R).map i' ≫ (freeP R).map b = (freeP R).map a ≫ (freeP R).map i := by
    rw [← Functor.map_comp, ← Functor.map_comp, w]
  have key := cokernel_map_comp_cokernelComparison ((freeP R).map i') G ((freeP R).map i) ((freeP R).map a)
    ((freeP R).map b) w'
  have h2 : IsIso (cokernelComparison ((freeP R).map i') G ≫ G.map (pcok R i' i a b w)) := by
    have : IsIso (G.map (pcok R i' i a b w)) := hW
    infer_instance
  have h3 : IsIso (cokernel.map (G.map ((freeP R).map i')) (G.map ((freeP R).map i)) (G.map ((freeP R).map a))
      (G.map ((freeP R).map b)) (by rw [← G.map_comp, w', G.map_comp])) := by
    have h4 : IsIso (cokernel.map (G.map ((freeP R).map i')) (G.map ((freeP R).map i)) (G.map ((freeP R).map a))
      (G.map ((freeP R).map b)) (by rw [← G.map_comp, w', G.map_comp]) ≫ cokernelComparison _ G) := by
      rw [key]; exact h2
    exact IsIso.of_isIso_comp_right _ (cokernelComparison ((freeP R).map i) G)
  exact h3

def LeafFreeCokSurj : Prop := ∀ (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
  (b : B' ⟶ B) (w : i' ≫ b = a ≫ i),
  (∀ (T : Scheme.{0}) (y : B.obj (op T)), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
    (∃ x : A.obj (op V), i.app (op V) x = B.map g.op y) ∨ ∃ y' : B'.obj (op V), b.app (op V) y' = B.map g.op y) →
  Presheaf.IsLocallySurjective Scheme.etaleTopology (pcok R i' i a b w)

def LeafFreeCokInj : Prop := ∀ (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
  (b : B' ⟶ B) (w : i' ≫ b = a ≫ i),
  (∀ (T : Scheme.{0}) (y : B'.obj (op T)) (x : A.obj (op T)), i.app (op T) x = b.app (op T) y →
    ∃ x' : A'.obj (op T), i'.app (op T) x' = y) →
  (∀ (T : Scheme.{0}) (y₁ y₂ : B'.obj (op T)), b.app (op T) y₁ = b.app (op T) y₂ →
    ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      B'.map g.op y₁ = B'.map g.op y₂ ∨ ∃ x : A.obj (op V), i.app (op V) x = b.app (op V) (B'.map g.op y₁)) →
  Presheaf.IsLocallyInjective Scheme.etaleTopology (pcok R i' i a b w)

/- English proof (translation)
Introduce `R _ A' B' A B i' i a b w h1 h2 h3`. Apply `isIso_cokernel_map_of_etale_local_iso` to reduce the goal to its premises. Use `hS R i' i a b w h2` as an intermediate fact. Use `hI R i' i a b w h1 h3` as an intermediate fact. Conclude with `GrothendieckTopology.W_of_isLocallyBijective _ _`.
-/
theorem LeafFreeCok_of (hS : LeafFreeCokSurj) (hI : LeafFreeCokInj) : LeafFreeCok := by
  intro R _ A' B' A B i' i a b w h1 h2 h3
  apply isIso_cokernel_map_of_etale_local_iso
  have := hS R i' i a b w h2
  have := hI R i' i a b w h1 h3
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

end LateralTheory.CohomologicalPurity
