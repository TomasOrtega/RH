import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.HtTensCurve

/- English proof (translation)
Establish `HD` using `diffVanish_chiPic_of_isProjOver (f := strHom κ Z) (algebraMap_eq_strHom κ Z) (structureModule Z) hp (d := 1) (by rw [QCoh.suppDim_structureModule, hd]; rfl)`. Establish `e` using `HD.interNum_update_tens (ι := Fin 1) (L := fun _ => A) (by simp) (fun _ => hA) 0 hA hB`. Establish `hu (N : LB Z) : Function.update (fun _ : Fin 1 => A) 0 N = fun _ => N`. Use function extensionality and compare the values at `fun j => by fin_cases j; simp`. Simplify `e` using `only [topSelf_def, hu]`.
-/
theorem topSelf_one_tens {κ : Type} [Field κ] {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)]
    (hp : IsProjOver (strHom κ Z)) (hd : topologicalKrullDim Z = 1) {A B : LB Z} (hA : A.IsLB)
    (hB : B.IsLB) : topSelfIntersection κ (CechPic.tens A B) 1 = topSelfIntersection κ A 1 + topSelfIntersection κ B 1 := by
  have HD := diffVanish_chiPic_of_isProjOver (f := strHom κ Z) (algebraMap_eq_strHom κ Z)
    (structureModule Z) hp (d := 1) (by rw [QCoh.suppDim_structureModule, hd]; rfl)
  have e := HD.interNum_update_tens (ι := Fin 1) (L := fun _ => A) (by simp) (fun _ => hA) 0 hA hB
  have hu (N : LB Z) : Function.update (fun _ : Fin 1 => A) 0 N = fun _ => N :=
    funext fun j => by fin_cases j; simp
  simpa only [topSelf_def, hu] using e

/- English proof (translation)
Establish `hA'` using `LB.isLB_pull hA i`. Establish `hB'` using `LB.isLB_pull hB i`. Rewrite using `[← topSelf_one_tens hp hd hA' hB', topSelf_def, topSelf_def]`. Use `interNum_congr_cls κ _ (fun _ => LB.isLB_pull (isLB_tens hA hB) i) (fun _ => isLB_tens hA' hB') fun _ => ?_` and prove the remaining obligations. Rewrite using `[cls_pull (isLB_tens hA hB) i, cls_tens hA hB, cls_tens hA' hB', cls_pull hA i, cls_pull hB i, map_add]`.
-/
theorem topSelf_one_pull_tens {κ : Type} [Field κ] {X Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)]
    (hp : IsProjOver (strHom κ Z)) (hd : topologicalKrullDim Z = 1) (i : Z ⟶ X) {A B : LB X}
    (hA : A.IsLB) (hB : B.IsLB) :
    topSelfIntersection κ ((CechPic.tens A B).pull i) 1 = topSelfIntersection κ (A.pull i) 1 + topSelfIntersection κ (B.pull i) 1 := by
  have hA' := LB.isLB_pull hA i
  have hB' := LB.isLB_pull hB i
  rw [← topSelf_one_tens hp hd hA' hB', topSelf_def, topSelf_def]
  refine interNum_congr_cls κ _ (fun _ => LB.isLB_pull (isLB_tens hA hB) i)
    (fun _ => isLB_tens hA' hB') fun _ => ?_
  rw [cls_pull (isLB_tens hA hB) i, cls_tens hA hB, cls_tens hA' hB', cls_pull hA i, cls_pull hB i,
    map_add]

end GlobalTheory.HtTensCurve

namespace GlobalTheory.HtTensCurve

/- English proof (translation)
Introduce `k _ X _ p D hX L M h h' h'' H H' H'' Z i _ _ hd`. Use `hX.isNoetherian_sub i` as an intermediate fact. Break down `hX.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, -⟩` into its components or cases. Establish `: Module.Finite ℤ k` using `hX.finite`. Establish `: IsProper p` using `(isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1`.

Establish `hproj : IsProjOver (strHom (ZMod ℓ) Z)`. Establish `: IsFinite (spMap (Int.castRingHom k))`. Rewrite using `[spMap, IsFinite.SpecMap_iff]`. Conclude with `(RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance`. Establish `e : strHom (ZMod ℓ) Z ≫ spMap (Int.castRingHom (ZMod ℓ)) = i ≫ p ≫ spMap (Int.castRingHom k)` using `specZIsTerminal.hom_ext _ _`.

Establish `: IsProper (strHom (ZMod ℓ) Z ≫ spMap (Int.castRingHom (ZMod ℓ)))`. Rewrite using `[e]`. Use `infer_instance`. Establish `: IsProper (strHom (ZMod ℓ) Z)` using `IsProper.of_comp _ (spMap (Int.castRingHom (ZMod ℓ)))`. Conclude with `ProperCurve.isProjOver_of_isProper _ hd`.

Rewrite using `[H''.vertical Z i (ZMod ℓ) 1 hd, H.vertical Z i (ZMod ℓ) 1 hd, H'.vertical Z i (ZMod ℓ) 1 hd, ← add_mul]`. Use `congr 1`. Conclude with `topSelf_one_pull_tens hproj hd i L.isLB M.isLB` after adjusting the coercions. Conclude with `PtHtComb.height_tens hX H H' H'' (HtSelfInter.isAlgPt_genericPoint i hc hd)`.
-/
theorem height_tens_curve : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ}, GlobalTheory.IsArithVar p D → ∀ (L M : GlobalTheory.HermLB p) (h h' h'' : X → ℝ), L.IsArithHeight h →
    M.IsArithHeight h' → (L.tens M).IsArithHeight h'' → ∀ (Z : Scheme.{0}) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z], topologicalKrullDim Z = 1 →
    h'' (i (genericPoint Z)) = h (i (genericPoint Z)) + h' (i (genericPoint Z)) := by
  intro k _ X _ p D hX L M h h' h'' H H' H'' Z i _ _ hd
  have := hX.isNoetherian_sub i
  rcases hX.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, -⟩
  · have : Module.Finite ℤ k := hX.finite
    have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
    have hproj : IsProjOver (strHom (ZMod ℓ) Z) := by
      have : IsFinite (spMap (Int.castRingHom k)) := by
        rw [spMap, IsFinite.SpecMap_iff]
        exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
      have e : strHom (ZMod ℓ) Z ≫ spMap (Int.castRingHom (ZMod ℓ)) =
          i ≫ p ≫ spMap (Int.castRingHom k) := specZIsTerminal.hom_ext _ _
      have : IsProper (strHom (ZMod ℓ) Z ≫ spMap (Int.castRingHom (ZMod ℓ))) := by
        rw [e]; infer_instance
      have : IsProper (strHom (ZMod ℓ) Z) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod ℓ)))
      exact ProperCurve.isProjOver_of_isProper _ hd
    rw [H''.vertical Z i (ZMod ℓ) 1 hd, H.vertical Z i (ZMod ℓ) 1 hd, H'.vertical Z i (ZMod ℓ) 1 hd,
      ← add_mul]
    congr 1
    exact_mod_cast topSelf_one_pull_tens hproj hd i L.isLB M.isLB
  · exact PtHtComb.height_tens hX H H' H'' (HtSelfInter.isAlgPt_genericPoint i hc hd)

end GlobalTheory.HtTensCurve
