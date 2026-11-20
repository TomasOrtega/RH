import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Introduce `W Z B _ p _ f g hfg hpt`. Set `X' : Over B` to `Over.mk (f ≫ p)`. Set `Y' : Over B` to `Over.mk p`. Set `f' : X' ⟶ Y'` to `Over.homMk f`. Set `g' : X' ⟶ Y'` to `Over.homMk g hfg.symm`.

Establish `: IsSeparated Y'.hom` using `‹_›`. Establish `hsurj : Surjective (equalizer.ι f' g').left`. Prove the components needed by the constructor for the conclusion. Introduce `x`. Set `K` to `W.residueField x`.

Set `Ω` to `AlgebraicClosure K`. Set `y : Spec (CommRingCat.of Ω) ⟶ W` to `Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ W.fromSpecResidueField x`. Establish `hy : y ≫ f = y ≫ g` using `hpt Ω y`. Set `U' : Over B` to `Over.mk (y ≫ f ≫ p)`. Set `y' : U' ⟶ X'` to `Over.homMk y`.

Establish `hy' : y' ≫ f' = y' ≫ g'` using `by ext1`. Conclude with `hy`. Set `pt : Spec (CommRingCat.of Ω)` to `IsLocalRing.closedPoint Ω`. Use `⟨(equalizer.lift y' hy').left pt, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]`.

Use `show (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ W.fromSpecResidueField x) pt = x`. Rewrite using `[Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]`. Use `isIso_of_isClosedImmersion_of_surjective (Y := W) (equalizer.ι f' g').left` as an intermediate fact. Rewrite using `[← cancel_epi (equalizer.ι f' g').left]`. Conclude with `congr($(equalizer.condition f' g').left)`.
-/
theorem UpperTheory.Gal.G3.pExtPts :
    ExtPts := by
  intro W Z B _ p _ f g hfg hpt
  let X' : Over B := Over.mk (f ≫ p)
  let Y' : Over B := Over.mk p
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g hfg.symm
  have : IsSeparated Y'.hom := ‹_›
  have hsurj : Surjective (equalizer.ι f' g').left := by
    constructor
    intro x
    let K := W.residueField x
    let Ω := AlgebraicClosure K
    let y : Spec (CommRingCat.of Ω) ⟶ W :=
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ W.fromSpecResidueField x
    have hy : y ≫ f = y ≫ g := hpt Ω y
    let U' : Over B := Over.mk (y ≫ f ≫ p)
    let y' : U' ⟶ X' := Over.homMk y
    have hy' : y' ≫ f' = y' ≫ g' := by
      ext1
      exact hy
    let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
    refine ⟨(equalizer.lift y' hy').left pt, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
    show (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ W.fromSpecResidueField x) pt = x
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have := isIso_of_isClosedImmersion_of_surjective (Y := W) (equalizer.ι f' g').left
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)
