import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicPointLiftsFiniteType
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Introduce `K _ A B p`. Establish `hAs : Smooth A.X.hom` using `A.ab.smooth`. Establish `hBs : Smooth B.X.hom` using `B.ab.smooth`. Establish `hBp : IsProper B.X.hom` using `B.ab.proper`. Establish `hw : p.hom.left ≫ B.X.hom = A.X.hom` using `Over.w p.hom`.

Establish `hlft : LocallyOfFiniteType p.hom.left`. Establish `: LocallyOfFiniteType (p.hom.left ≫ B.X.hom)` using `by rw [hw]; infer_instance`. Conclude with `locallyOfFiniteType_of_comp p.hom.left B.X.hom`. Prove the components needed by the constructor for the conclusion. Introduce `hs y`.

Take `⟨u, hu⟩` from `hs.surj (y.left (IsLocalRing.closedPoint (AlgebraicClosure K)))`. Take `⟨w, hw'⟩` from `GlobalTheory.CovLift.exists_lift_of_locallyOfFiniteType _ _ p.hom.left hlft (AlgebraicClosure K) y.left u hu`. Use `⟨Over.homMk w ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `w ≫ A.X.hom = spMap (algebraMap K (AlgebraicClosure K))`. Rewrite using `[← hw, ← Category.assoc, hw']`.

Conclude with `Over.w y`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `using hw'`. Introduce `hs`. Establish `: IsProper (p.hom.left ≫ B.X.hom)` using `by rw [hw]; exact A.ab.proper`.

Establish `hp : IsProper p.hom.left` using `IsProper.of_comp p.hom.left B.X.hom`. Establish `hcl : IsClosed (Set.range p.hom.left)` using `p.hom.left.isClosedMap.isClosed_range`. Establish `hJ : JacobsonSpace B.X.left` using `LocallyOfFiniteType.jacobsonSpace B.X.hom`. Establish `hsub : closedPoints B.X.left ⊆ Set.range p.hom.left`. Introduce `b hb`.

Set `t : Sp (AlgebraicClosure K) ⟶ Sp K` to `spMap (algebraMap K (AlgebraicClosure K))`. Use `haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))`. Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := B.X.hom) (g := t) b (IsLocalRing.closedPoint (AlgebraicClosure K)) (Subsingleton.elim _ _)`. Establish `: JacobsonSpace ↥(pullback B.X.hom t : Scheme.{0})` using `LocallyOfFiniteType.jacobsonSpace (pullback.snd B.X.hom t)`. Establish `hF : IsClosed ((pullback.fst B.X.hom t) ⁻¹' {b})` using `(show IsClosed {b} from hb).preimage (pullback.fst B.X.hom t).continuous`.

Take `⟨c, hcF, hc'⟩` from `nonempty_inter_closedPoints (X := ↥(pullback B.X.hom t : Scheme.{0})) (Z := (pullback.fst B.X.hom t) ⁻¹' {b}) ⟨z, hz⟩ hF.isLocallyClosed`. Establish `hc : IsClosed {c}` using `hc'`. Set `x0 : Sp (AlgebraicClosure K) ⟶ B.X.left` to `pointOfClosedPoint (pullback.snd B.X.hom t) c hc ≫ pullback.fst B.X.hom t`. Establish `hx0 : x0 ≫ B.X.hom = t`. Simplify using `only [x0, Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]`.

Take `⟨x, hx⟩` from `hs (Over.homMk x0 hx0 : ptOver K (AlgebraicClosure K) ⟶ B.X)`. Use `⟨x.left (IsLocalRing.closedPoint (AlgebraicClosure K)), ?_⟩` and prove the remaining obligations. Establish `e : x.left ≫ p.hom.left = x0` using `congrArg CommaMorphism.left hx`. Establish `e3 : p.hom.left (x.left (IsLocalRing.closedPoint (AlgebraicClosure K))) = x0 (IsLocalRing.closedPoint (AlgebraicClosure K))`. Rewrite using `[← e]`.

Both sides reduce to the same expression. Establish `e4 : x0 (IsLocalRing.closedPoint (AlgebraicClosure K)) = pullback.fst B.X.hom t c`. Express the relevant statement in the definitionally equal form `pullback.fst B.X.hom t (pointOfClosedPoint (pullback.snd B.X.hom t) c hc (IsLocalRing.closedPoint (AlgebraicClosure K))) = _`. Conclude with `congrArg (pullback.fst B.X.hom t) (pointOfClosedPoint_apply (pullback.snd B.X.hom t) c hc _)`. Rewrite using `[e3, e4]`.

Conclude with `hcF`. Establish `huniv : Set.univ ⊆ Set.range p.hom.left`. Rewrite using `[← closure_closedPoints]`. Conclude with `closure_minimal hsub hcl`. Conclude with `⟨fun b => huniv (Set.mem_univ b)⟩`.
-/
theorem surjective_iff_ptMap_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B),
    Surjective p.hom.left ↔ Function.Surjective (ptMap p) := by
  intro K _ A B p
  have hAs : Smooth A.X.hom := A.ab.smooth
  have hBs : Smooth B.X.hom := B.ab.smooth
  have hBp : IsProper B.X.hom := B.ab.proper
  have hw : p.hom.left ≫ B.X.hom = A.X.hom := Over.w p.hom
  have hlft : LocallyOfFiniteType p.hom.left := by
    have : LocallyOfFiniteType (p.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
    exact locallyOfFiniteType_of_comp p.hom.left B.X.hom
  constructor
  · intro hs y
    obtain ⟨u, hu⟩ := hs.surj (y.left (IsLocalRing.closedPoint (AlgebraicClosure K)))
    obtain ⟨w, hw'⟩ := GlobalTheory.CovLift.exists_lift_of_locallyOfFiniteType _ _ p.hom.left hlft
      (AlgebraicClosure K) y.left u hu
    refine ⟨Over.homMk w ?_, ?_⟩
    · change w ≫ A.X.hom = spMap (algebraMap K (AlgebraicClosure K))
      rw [← hw, ← Category.assoc, hw']
      exact Over.w y
    · apply Over.OverMorphism.ext
      simpa using hw'
  · intro hs
    have : IsProper (p.hom.left ≫ B.X.hom) := by rw [hw]; exact A.ab.proper
    have hp : IsProper p.hom.left := IsProper.of_comp p.hom.left B.X.hom
    have hcl : IsClosed (Set.range p.hom.left) := p.hom.left.isClosedMap.isClosed_range
    have hJ : JacobsonSpace B.X.left := LocallyOfFiniteType.jacobsonSpace B.X.hom
    have hsub : closedPoints B.X.left ⊆ Set.range p.hom.left := by
      intro b hb
      let t : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K (AlgebraicClosure K))
      haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := B.X.hom) (g := t) b
        (IsLocalRing.closedPoint (AlgebraicClosure K)) (Subsingleton.elim _ _)
      have : JacobsonSpace ↥(pullback B.X.hom t : Scheme.{0}) :=
        LocallyOfFiniteType.jacobsonSpace (pullback.snd B.X.hom t)
      have hF : IsClosed ((pullback.fst B.X.hom t) ⁻¹' {b}) :=
        (show IsClosed {b} from hb).preimage (pullback.fst B.X.hom t).continuous
      obtain ⟨c, hcF, hc'⟩ := nonempty_inter_closedPoints (X := ↥(pullback B.X.hom t : Scheme.{0}))
        (Z := (pullback.fst B.X.hom t) ⁻¹' {b}) ⟨z, hz⟩ hF.isLocallyClosed
      have hc : IsClosed {c} := hc'
      let x0 : Sp (AlgebraicClosure K) ⟶ B.X.left :=
        pointOfClosedPoint (pullback.snd B.X.hom t) c hc ≫ pullback.fst B.X.hom t
      have hx0 : x0 ≫ B.X.hom = t := by
        simp only [x0, Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
      obtain ⟨x, hx⟩ := hs (Over.homMk x0 hx0 : ptOver K (AlgebraicClosure K) ⟶ B.X)
      refine ⟨x.left (IsLocalRing.closedPoint (AlgebraicClosure K)), ?_⟩
      have e : x.left ≫ p.hom.left = x0 := congrArg CommaMorphism.left hx
      have e3 : p.hom.left (x.left (IsLocalRing.closedPoint (AlgebraicClosure K))) =
          x0 (IsLocalRing.closedPoint (AlgebraicClosure K)) := by
        rw [← e]; rfl
      have e4 : x0 (IsLocalRing.closedPoint (AlgebraicClosure K)) = pullback.fst B.X.hom t c := by
        change pullback.fst B.X.hom t (pointOfClosedPoint (pullback.snd B.X.hom t) c hc
          (IsLocalRing.closedPoint (AlgebraicClosure K))) = _
        exact congrArg (pullback.fst B.X.hom t) (pointOfClosedPoint_apply (pullback.snd B.X.hom t) c hc _)
      rw [e3, e4]
      exact hcF
    have huniv : Set.univ ⊆ Set.range p.hom.left := by
      rw [← closure_closedPoints]
      exact closure_minimal hsub hcl
    exact ⟨fun b => huniv (Set.mem_univ b)⟩

end GlobalTheory.AV.AbVar
