import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperAndGeometricallyConnectedOfIsNilpotent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

/- English proof (translation)
Use `⟨fun x ↦ ⟨t, ?_⟩⟩` and prove the remaining obligations. Establish `: Subsingleton (PrimeSpectrum K)` using `inferInstance`. Conclude with `Subsingleton.elim (α := PrimeSpectrum K) _ _`.
-/
theorem surjective_to_spec_field {T : Scheme.{0}} (K : Type) [Field K] (h : T ⟶ Spec (CommRingCat.of K))
    (t : T) : Surjective h := by
  refine ⟨fun x ↦ ⟨t, ?_⟩⟩
  have : Subsingleton (PrimeSpectrum K) := inferInstance
  exact Subsingleton.elim (α := PrimeSpectrum K) _ _

/- English proof (translation)
Use `⟨fun K _ y Z fst snd hz ↦ ?_⟩` and prove the remaining obligations. Establish `hb : Surjective (pullback.snd q y)` using `MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback q y) inferInstance`. Establish `k : Spec (CommRingCat.of K)` using `IsLocalRing.closedPoint K`. Take `⟨z, -⟩` from `(pullback.snd q y).surjective k`. Set `t` to `(pullback q y).fromSpecResidueField z`.

Set `L` to `(pullback q y).residueField z`. Set `W` to `pullback f' (t ≫ pullback.fst q y)`. Establish `hW : ConnectedSpace W` using `GeometricallyConnected.geometrically_connectedSpace (f := f') (t ≫ pullback.fst q y) (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)`. Establish `hbig : IsPullback (pullback.fst f' (t ≫ pullback.fst q y) ≫ p) (pullback.snd _ _) f ((t ≫ pullback.fst q y) ≫ q)` using `(IsPullback.of_hasPullback _ _).paste_horiz hsq`. Establish `hbig' : IsPullback (pullback.fst f' (t ≫ pullback.fst q y) ≫ p) (pullback.snd _ _) f ((t ≫ pullback.snd q y) ≫ y)`.

Use `hbig using 1` and compare the differences between its conclusion and the goal. Simplify using `[pullback.condition]`. Set `w : W ⟶ Z` to `hz.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _ ≫ t ≫ pullback.snd q y) (by`. Simplify using `using hbig'.w)`. Establish `hw : IsPullback w (pullback.snd f' (t ≫ pullback.fst q y)) snd (t ≫ pullback.snd q y)`.

Use `IsPullback.of_right (h₁₂ := fst) (v₁₃ := f) (h₂₂ := y) ?_ (by simp [w]) hz` and prove the remaining obligations. Use `hbig' using 1` and compare the differences between its conclusion and the goal. Simplify using `[w]`. Establish `hs : Surjective (t ≫ pullback.snd q y)` using `surjective_to_spec_field K _ (IsLocalRing.closedPoint L)`. Establish `: Surjective w` using `MorphismProperty.of_isPullback (P := @Surjective) hw.flip hs`.

Conclude with `w.surjective.connectedSpace w.continuous`.
-/
theorem geometricallyConnected_of_isPullback {X X' Y Y' : Scheme.{0}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X}
    {q : Y' ⟶ Y} (hsq : IsPullback p f' f q) [Surjective q] [GeometricallyConnected f'] :
    GeometricallyConnected f := by
  refine ⟨fun K _ y Z fst snd hz ↦ ?_⟩
  have hb : Surjective (pullback.snd q y) :=
    MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback q y) inferInstance
  have k : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  obtain ⟨z, -⟩ := (pullback.snd q y).surjective k
  let t := (pullback q y).fromSpecResidueField z
  let L := (pullback q y).residueField z
  let W := pullback f' (t ≫ pullback.fst q y)
  have hW : ConnectedSpace W :=
    GeometricallyConnected.geometrically_connectedSpace (f := f') (t ≫ pullback.fst q y)
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hbig : IsPullback (pullback.fst f' (t ≫ pullback.fst q y) ≫ p) (pullback.snd _ _) f
      ((t ≫ pullback.fst q y) ≫ q) := (IsPullback.of_hasPullback _ _).paste_horiz hsq
  have hbig' : IsPullback (pullback.fst f' (t ≫ pullback.fst q y) ≫ p) (pullback.snd _ _) f
      ((t ≫ pullback.snd q y) ≫ y) := by
    convert hbig using 1
    simp [pullback.condition]
  let w : W ⟶ Z := hz.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _ ≫ t ≫ pullback.snd q y) (by
    simpa using hbig'.w)
  have hw : IsPullback w (pullback.snd f' (t ≫ pullback.fst q y)) snd (t ≫ pullback.snd q y) := by
    refine IsPullback.of_right (h₁₂ := fst) (v₁₃ := f) (h₂₂ := y) ?_ (by simp [w]) hz
    convert hbig' using 1
    simp [w]
  have hs : Surjective (t ≫ pullback.snd q y) := surjective_to_spec_field K _ (IsLocalRing.closedPoint L)
  have : Surjective w := MorphismProperty.of_isPullback (P := @Surjective) hw.flip hs
  exact w.surjective.connectedSpace w.continuous

/- English proof (translation)
Introduce `X X' Y Y' f f' p q g hsq hq hqs hf hf'`. Use `hf'.proper` as an intermediate fact. Use `hf'.conn` as an intermediate fact. Establish `: Surjective p` using `MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hqs`. Establish `: IsFinite p` using `MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip hq`.

Establish `: IsProper (p ≫ f)` using `by rw [hsq.w]; infer_instance`. Establish `: UniversallyClosed f` using `UniversallyClosed.of_comp_surjective p f`. Establish `: IsSeparated f` using `GlobalTheory.NilProper.isSeparated_of_comp_surjective p f`. Establish `: Smooth f` using `hf.smooth`. Establish `: LocallyOfFiniteType f` using `inferInstance`.

Conclude with `⟨{}, hf, geometricallyConnected_of_isPullback hsq⟩`.
-/
theorem good_of_isPullback_finite_surjective : ∀ (X X' Y Y' : Scheme.{0}) (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X)
    (q : Y' ⟶ Y) (g : ℕ), IsPullback p f' f q → IsFinite q → Surjective q → SmoothOfRelativeDimension g f →
    GlobalTheory.DualCon.Good g f' → GlobalTheory.DualCon.Good g f := by
  intro X X' Y Y' f f' p q g hsq hq hqs hf hf'
  have := hf'.proper
  have := hf'.conn
  have : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hqs
  have : IsFinite p := MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip hq
  have : IsProper (p ≫ f) := by rw [hsq.w]; infer_instance
  have : UniversallyClosed f := UniversallyClosed.of_comp_surjective p f
  have : IsSeparated f := GlobalTheory.NilProper.isSeparated_of_comp_surjective p f
  have : Smooth f := hf.smooth
  have : LocallyOfFiniteType f := inferInstance
  exact ⟨{}, hf, geometricallyConnected_of_isPullback hsq⟩

end GlobalTheory.DualCon
