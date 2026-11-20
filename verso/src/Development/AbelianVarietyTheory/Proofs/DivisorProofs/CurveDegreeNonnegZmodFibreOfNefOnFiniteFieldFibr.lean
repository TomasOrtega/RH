import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.NefFibPrime

/- English proof (translation)
The claim follows from `IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p)))`.
-/
theorem isClosedImmersion_spMap_zmod (p : ℕ) : IsClosedImmersion (spMap (Int.castRingHom (ZMod p))) :=
  IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p)))

/- English proof (translation)
Use `isClosedImmersion_spMap_zmod p` as an intermediate fact. Establish `: IsClosedImmersion (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))` using `IsClosedImmersion.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip this`. Use `set f := pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))) with hf`. Establish `h1` using `h Z (i ≫ f) (ZMod p) hd`. Establish `e : topSelfIntersection (ZMod p) ((L.B.pull f).pull i) 1 = topSelfIntersection (ZMod p) (L.B.pull (i ≫ f)) 1`.

Rewrite using `[topSelf_def, topSelf_def]`. Use `interNum_congr_cls (ZMod p) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB f) i) (fun _ => LB.isLB_pull L.isLB (i ≫ f)) fun _ => ?_` and prove the remaining obligations. Use `show pull i (pull f (cls L.B L.isLB)) = pull (i ≫ f) (cls L.B L.isLB)`. Rewrite using `[← pull_comp]`. Rewrite using `[e]`.

Conclude with `h1`.
-/
theorem topSelf_nonneg_of_nefFib (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (L : HermLB q) (p : ℕ)
    [Fact p.Prime] (h : ArInt.NefFib L) (Z : Scheme.{0})
    (i : Z ⟶ pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))
    [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    0 ≤ topSelfIntersection (ZMod p) ((L.B.pull (pullback.fst (q ≫ spMap (Int.castRingHom k))
      (spMap (Int.castRingHom (ZMod p))))).pull i) 1 := by
  have := isClosedImmersion_spMap_zmod p
  have : IsClosedImmersion (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip this
  set f := pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))) with hf
  have h1 := h Z (i ≫ f) (ZMod p) hd
  have e : topSelfIntersection (ZMod p) ((L.B.pull f).pull i) 1 = topSelfIntersection (ZMod p) (L.B.pull (i ≫ f)) 1 := by
    rw [topSelf_def, topSelf_def]
    refine interNum_congr_cls (ZMod p) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB f) i)
      (fun _ => LB.isLB_pull L.isLB (i ≫ f)) fun _ => ?_
    show pull i (pull f (cls L.B L.isLB)) = pull (i ≫ f) (cls L.B L.isLB)
    rw [← pull_comp]
  rw [e]
  exact h1

end GlobalTheory.NefFibPrime
