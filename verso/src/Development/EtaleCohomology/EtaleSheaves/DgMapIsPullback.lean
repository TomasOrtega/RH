import Development.EtaleCohomology.EtaleSheaves.LeafMapFPPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafPairFPPf LateralTheory.E.LeafMapFPPf

namespace LateralTheory.E.LeafMapFPPf2

/- English proof (translation)
Establish `t : IsPullback (dgMap q1 hS hT h ≫ pullback.fst _ _) (pullback.snd q1 (incl hT)) q1 (incl h ≫ incl hS)`. Rewrite using `[dgMap_fst, incl_comp]`. Conclude with `IsPullback.of_hasPullback _ _`. Conclude with `IsPullback.of_right t (dgMap_snd q1 hS hT h) (IsPullback.of_hasPullback _ _)`.
-/
theorem dgMap_isPullback {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R : Subalgebra k Ω} {D1 : Scheme.{0}}
    (q1 : D1 ⟶ Sp R) {S T : Subalgebra k Ω} (hS : R ≤ S) (hT : R ≤ T) (h : S ≤ T) :
    IsPullback (dgMap q1 hS hT h) (pullback.snd q1 (incl hT)) (pullback.snd q1 (incl hS)) (incl h) := by
  have t : IsPullback (dgMap q1 hS hT h ≫ pullback.fst _ _) (pullback.snd q1 (incl hT)) q1 (incl h ≫ incl hS) := by
    rw [dgMap_fst, incl_comp]; exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right t (dgMap_snd q1 hS hT h) (IsPullback.of_hasPullback _ _)

/- English proof (translation)
Introduce `k _ Ω _ _ R D1 q1 hq1`. Take `⟨_, h2, h3⟩` from `hq1`. Use `⟨fun S => ⟨?_, ?_⟩, fun S T h => ?_⟩` and prove the remaining obligations. Establish `: QuasiCompact (pullback.snd q1 (incl S.unop.2.2))` using `by first`. Consider the case `exact MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback q1 (incl S.unop.2.2)) h2`.

Conclude with `@QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.snd q1 (incl S.unop.2.2)) this _`. Establish `: QuasiSeparated (pullback.snd q1 (incl S.unop.2.2))` using `by first`. Consider the case `exact MorphismProperty.of_isPullback (P := @QuasiSeparated) (IsPullback.of_hasPullback q1 (incl S.unop.2.2)) h3`. Conclude with `@quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.snd q1 (incl S.unop.2.2)) _ this`. Use `first`.

Consider the case `exact MorphismProperty.of_isPullback (P := @IsAffineHom) (dgMap_isPullback q1 S.2.2 T.2.2 h) inferInstance`. Consider the case `exact MorphismProperty.of_isPullback (P := @IsAffineHom) (dgMap_isPullback q1 S.2.2 T.2.2 h).flip inferInstance`.
-/
theorem stages : LeafStagesFP := by
  intro k _ Ω _ _ R D1 q1 hq1
  obtain ⟨_, h2, h3⟩ := hq1
  refine ⟨fun S => ⟨?_, ?_⟩, fun S T h => ?_⟩
  · have : QuasiCompact (pullback.snd q1 (incl S.unop.2.2)) :=
      by
      first
        | exact MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback q1 (incl S.unop.2.2)) h2
    exact @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.snd q1 (incl S.unop.2.2)) this _
  · have : QuasiSeparated (pullback.snd q1 (incl S.unop.2.2)) :=
      by
      first
        | exact MorphismProperty.of_isPullback (P := @QuasiSeparated) (IsPullback.of_hasPullback q1 (incl S.unop.2.2)) h3
    exact @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.snd q1 (incl S.unop.2.2)) _ this
  · first
      | exact MorphismProperty.of_isPullback (P := @IsAffineHom) (dgMap_isPullback q1 S.2.2 T.2.2 h) inferInstance
      | exact MorphismProperty.of_isPullback (P := @IsAffineHom) (dgMap_isPullback q1 S.2.2 T.2.2 h).flip inferInstance

/- English proof (translation)
The claim follows from `LateralTheory.E.LeafMapFPPf.morphismDescent_of_isLimit hL stages`.
-/
theorem morphismDescent_of_isLimit (hL : LeafLimFP) : LeafMapFP := LateralTheory.E.LeafMapFPPf.morphismDescent_of_isLimit hL stages

end LateralTheory.E.LeafMapFPPf2

end
