import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Substitute `h` using the available equality. Use `IsPullback.of_bot ?_ (bcMap_fst g f rfl).symm (IsPullback.of_hasPullback p g)` and prove the remaining obligations. Rewrite using `[bcMap_snd]`. Conclude with `IsPullback.of_hasPullback (f ≫ p) g`.
-/
private theorem bcMap_isPullback {B B' X Y : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} (f : Y ⟶ X)
    (h : f ≫ p = q) : IsPullback (pullback.fst q g) (bcMap g f h) f (pullback.fst p g) := by
  subst h
  refine IsPullback.of_bot ?_ (bcMap_fst g f rfl).symm (IsPullback.of_hasPullback p g)
  rw [bcMap_snd]
  exact IsPullback.of_hasPullback (f ≫ p) g

/- English proof (translation)
Introduce `hB B B' Z W g p r c hc G _ _ a ha hG`. Take `⟨hfin, het, hsur, h1, hmul, hsp⟩` from `hG`. Take `⟨f1, f2, f3⟩` from `@hB B B' Z W W g p r r c hc c hc G _ a ha hfin het`. Use `⟨f1, f2, ?_, ?_, ?_, f3 hsp⟩` and prove the remaining obligations. Conclude with `MorphismProperty.of_isPullback (P := @Surjective) (bcMap_isPullback g c hc) hsur`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[bcMap_fst, h1, Category.comp_id, Category.id_comp]`. Rewrite using `[bcMap_snd, Category.id_comp]`. Introduce `x y`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, Category.assoc, hmul]`. Rewrite using `[bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]`.
-/
theorem UpperTheory.Gal.G3.pBcGal :
    BcSplits → BcGal := by
  intro hB B B' Z W g p r c hc G _ _ a ha hG
  obtain ⟨hfin, het, hsur, h1, hmul, hsp⟩ := hG
  obtain ⟨f1, f2, f3⟩ := @hB B B' Z W W g p r r c hc c hc G _ a ha hfin het
  refine ⟨f1, f2, ?_, ?_, ?_, f3 hsp⟩
  · exact MorphismProperty.of_isPullback (P := @Surjective) (bcMap_isPullback g c hc) hsur
  · apply pullback.hom_ext
    · rw [bcMap_fst, h1, Category.comp_id, Category.id_comp]
    · rw [bcMap_snd, Category.id_comp]
  · intro x y
    apply pullback.hom_ext
    · rw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, Category.assoc, hmul]
    · rw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]
