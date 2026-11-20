import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

/- English proof (translation)
Use `IsPullback.of_bot (v₂₁ := pullback.snd p c) (v₂₂ := p) (h₃₁ := c) ?_ ?_ (IsPullback.of_hasPullback p c)` and prove the remaining obligations. Rewrite using `[pullback.lift_snd]`. Conclude with `IsPullback.of_hasPullback (s ≫ p) c`. Rewrite using `[pullback.lift_fst]`.
-/
private theorem sq_bc {T Y S B : Scheme.{0}} (s : T ⟶ Y) (p : Y ⟶ S) (c : B ⟶ S) :
    IsPullback (pullback.fst (s ≫ p) c)
      (pullback.lift (pullback.fst (s ≫ p) c ≫ s) (pullback.snd (s ≫ p) c)
        (by rw [Category.assoc, pullback.condition]) : pullback (s ≫ p) c ⟶ pullback p c)
      s (pullback.fst p c) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd p c) (v₂₂ := p) (h₃₁ := c) ?_ ?_
    (IsPullback.of_hasPullback p c)
  · rw [pullback.lift_snd]
    exact IsPullback.of_hasPullback (s ≫ p) c
  · rw [pullback.lift_fst]

/- English proof (translation)
Introduce `hb k L _ _ H θ O _ _ C D`. Use `haveI : Smooth C.p := C.smooth`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Smooth (pullback.snd C.p (UpperTheory.Gal.Int.Geo.gen O k)) infer_instance`. Conclude with `GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap O k) C.proj`.

Introduce `g`. Conclude with `⟨D.d g, hb.1 _ _ _ _ _ (sq_bc (D.s g) C.p (UpperTheory.Gal.Int.Geo.gen O k)) (D.fet g)⟩`.
-/
theorem UpperTheory.Gal.G3.jLowNice :
    FEtBasic → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowNice := by
  intro hb k L _ _ H θ O _ _ C D
  haveI : Smooth C.p := C.smooth
  refine ⟨?_, ?_, ?_⟩
  · show Smooth (pullback.snd C.p (UpperTheory.Gal.Int.Geo.gen O k))
    infer_instance
  · exact GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap O k) C.proj
  · intro g
    exact ⟨D.d g, hb.1 _ _ _ _ _ (sq_bc (D.s g) C.p (UpperTheory.Gal.Int.Geo.gen O k)) (D.fet g)⟩
