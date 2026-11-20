import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd

/- English proof (translation)
Establish `: ∀ U, Mono (((freeP R).map g).app U)`. Introduce `U`. Establish `hg : Function.Injective (g.app U)` using `(mono_iff_injective _).1 inferInstance`. Rewrite using `[ModuleCat.mono_iff_injective]`. Simplify using `[freeP]`.

Conclude with `Finsupp.mapDomain_injective (fun a b h => ULift.ext _ _ (hg (congrArg ULift.down h)))`. Conclude with `NatTrans.mono_of_mono_app _`.
-/
theorem mono_freeP (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q) [Mono g] : Mono ((freeP R).map g) := by
  have : ∀ U, Mono (((freeP R).map g).app U) := by
    intro U
    have hg : Function.Injective (g.app U) := (mono_iff_injective _).1 inferInstance
    rw [ModuleCat.mono_iff_injective]
    dsimp [freeP]
    exact Finsupp.mapDomain_injective (fun a b h => ULift.ext _ _ (hg (congrArg ULift.down h)))
  exact NatTrans.mono_of_mono_app _

/- English proof (translation)
Use `mono_freeP R g` as an intermediate fact. Simplify using `[free]`. Use `infer_instance`.
-/
theorem mono_free (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q) [Mono g] : Mono ((free R).map g) := by
  have := mono_freeP R g
  dsimp [free]
  infer_instance

/- English proof (translation)
Introduce `R _ U E f hf p`. Establish `hk : ∀ k : ℕ, Mono (((chainsN R).map f).f k)`. Introduce `k`. Establish `: Mono (f.app (op (SimplexCategory.mk k)))` using `inferInstance`. Use `mono_free R (f.app (op (SimplexCategory.mk k)))` as an intermediate fact.

Simplify using `only [chainsN, Functor.comp_map, AlgebraicTopology.alternatingFaceMapComplex_map_f]`. Conclude with `this`. Distinguish the cases in `h : ∃ k : ℕ, -(k : ℤ) = p`. Take `⟨k, rfl⟩` from `h`. Establish `e` using `HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := k) (i' := -(k:ℤ)) rfl`.

Express the relevant statement in the definitionally equal form `Mono (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat |>.f _)`. Rewrite using `[e]`. Use `hk k` as an intermediate fact. Use `infer_instance`. Establish `hz : IsZero (((chains R).obj U).X p)`.

Apply `HomologicalComplex.isZero_extend_X` to reduce the goal to its premises. Introduce `k hk`. Conclude with `h ⟨k, hk⟩`. Conclude with `hz.mono _`.
-/
theorem LeafMono_of : LeafMono := by
  intro R _ U E f hf p
  have hk : ∀ k : ℕ, Mono (((chainsN R).map f).f k) := by
    intro k
    have : Mono (f.app (op (SimplexCategory.mk k))) := inferInstance
    have := mono_free R (f.app (op (SimplexCategory.mk k)))
    simp only [chainsN, Functor.comp_map, AlgebraicTopology.alternatingFaceMapComplex_map_f]
    exact this
  by_cases h : ∃ k : ℕ, -(k : ℤ) = p
  · obtain ⟨k, rfl⟩ := h
    have e := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := k) (i' := -(k:ℤ)) rfl
    change Mono (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat |>.f _)
    rw [e]
    have := hk k
    infer_instance
  · have hz : IsZero (((chains R).obj U).X p) := by
      apply HomologicalComplex.isZero_extend_X
      intro k hk; exact h ⟨k, hk⟩
    exact hz.mono _
