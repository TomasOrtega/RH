import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

open Limits in

/- English proof (translation)
Introduce `S _ ι s hs Y e he`. Set `𝒰` to `(Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) s hs).openCover`. Establish `hf : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ e i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ e j`. Introduce `i j`. Use `Scheme.Cover.hom_ext (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.openCover _ _ fun k => ?_` and prove the remaining obligations.

Set `a : Spec ((pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.X k) ⟶ pullback (𝒰.f i) (𝒰.f j)` to `(pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.f k`. Set `T` to `(pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.X k`. Set `A : CommRingCat.of (Localization.Away (s i)) ⟶ T` to `Spec.preimage (a ≫ pullback.fst (𝒰.f i) (𝒰.f j))`. Set `B : CommRingCat.of (Localization.Away (s j)) ⟶ T` to `Spec.preimage (a ≫ pullback.snd (𝒰.f i) (𝒰.f j))`. Establish `ea : Spec.map A = a ≫ pullback.fst (𝒰.f i) (𝒰.f j)` using `Spec.map_preimage _`.

Establish `eb : Spec.map B = a ≫ pullback.snd (𝒰.f i) (𝒰.f j)` using `Spec.map_preimage _`. Establish `e1 : Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s i))) ≫ A) = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s j))) ≫ B)`. Rewrite using `[Spec.map_comp, Spec.map_comp, ea, eb]`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (a ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)`. Establish `key : A.hom.comp (algebraMap S (Localization.Away (s i))) = B.hom.comp (algebraMap S (Localization.Away (s j)))` using `congrArg CommRingCat.Hom.hom (Spec.map_injective e1)`.

Establish `hu : IsUnit ((A.hom.comp (algebraMap S (Localization.Away (s i)))) (s i * s j))`. Rewrite using `[map_mul]`. Use `IsUnit.mul ?_ ?_` and prove the remaining obligations. Conclude with `(IsLocalization.Away.algebraMap_isUnit (s i)).map A.hom`. Rewrite using `[key]`.

Conclude with `(IsLocalization.Away.algebraMap_isUnit (s j)).map B.hom`. Set `L : Localization.Away (s i * s j) →+* T` to `IsLocalization.Away.lift (s i * s j) hu`. Establish `hL : L.comp (algebraMap S (Localization.Away (s i * s j))) = A.hom.comp (algebraMap S (Localization.Away (s i)))` using `IsLocalization.Away.lift_comp _ _`. Establish `hLA : L.comp (IsLocalization.Away.awayToAwayRight (P` using `Localization.Away (s i * s j)) (s i) (s j)) = A.hom := by`. Use `IsLocalization.ringHom_ext (Submonoid.powers (s i)) (RingHom.ext fun x => ?_)` and prove the remaining obligations.

Use `congrArg (fun f => f x) hL` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this ⊢`. Rewrite using `[IsLocalization.Away.awayToAwayRight_eq, this]`. Establish `hLB : L.comp (IsLocalization.Away.awayToAwayLeft (P` using `Localization.Away (s i * s j)) (s j) (s i)) = B.hom := by`. Use `IsLocalization.ringHom_ext (Submonoid.powers (s j)) (RingHom.ext fun x => ?_)` and prove the remaining obligations.

Use `congrArg (fun f => f x) (hL.trans key)` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this ⊢`. Rewrite using `[IsLocalization.Away.awayToAwayLeft_eq, this]`. Establish `hA : Spec.map A = Spec.map (CommRingCat.ofHom L) ≫ spMap (IsLocalization.Away.awayToAwayRight (P` using `Localization.Away (s i * s j)) (s i) (s j)) := by`. Rewrite using `[spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hLA]`.

Both sides reduce to the same expression. Establish `hB : Spec.map B = Spec.map (CommRingCat.ofHom L) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P` using `Localization.Away (s i * s j)) (s j) (s i)) := by`. Rewrite using `[spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hLB]`. Both sides reduce to the same expression. Establish `h2 : Spec.map A ≫ e i = Spec.map B ≫ e j`.

Rewrite using `[hA, hB, Category.assoc, Category.assoc, he i j]`. Rewrite `h2` using `[ea, eb]`. Conclude with `(Category.assoc _ _ _).symm.trans (h2.trans (Category.assoc _ _ _))`. Conclude with `⟨𝒰.glueMorphisms e hf, fun i => Scheme.Cover.ι_glueMorphisms 𝒰 e hf i⟩`.
-/
theorem glue_away : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (e : ∀ i, Sp (Localization.Away (s i)) ⟶ Y),
    (∀ i j, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) ≫ e i =
      spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) ≫ e j) →
    ∃ a : Sp S ⟶ Y, ∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = e i := by
  intro S _ ι s hs Y e he
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) s hs).openCover
  have hf : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ e i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ e j := by
    intro i j
    refine Scheme.Cover.hom_ext (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.openCover _ _ fun k => ?_
    let a : Spec ((pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.X k) ⟶ pullback (𝒰.f i) (𝒰.f j) :=
      (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.f k
    let T := (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.X k
    let A : CommRingCat.of (Localization.Away (s i)) ⟶ T := Spec.preimage (a ≫ pullback.fst (𝒰.f i) (𝒰.f j))
    let B : CommRingCat.of (Localization.Away (s j)) ⟶ T := Spec.preimage (a ≫ pullback.snd (𝒰.f i) (𝒰.f j))
    have ea : Spec.map A = a ≫ pullback.fst (𝒰.f i) (𝒰.f j) := Spec.map_preimage _
    have eb : Spec.map B = a ≫ pullback.snd (𝒰.f i) (𝒰.f j) := Spec.map_preimage _
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s i))) ≫ A) =
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s j))) ≫ B) := by
      rw [Spec.map_comp, Spec.map_comp, ea, eb]
      exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    have key : A.hom.comp (algebraMap S (Localization.Away (s i))) =
        B.hom.comp (algebraMap S (Localization.Away (s j))) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    have hu : IsUnit ((A.hom.comp (algebraMap S (Localization.Away (s i)))) (s i * s j)) := by
      rw [map_mul]
      refine IsUnit.mul ?_ ?_
      · exact (IsLocalization.Away.algebraMap_isUnit (s i)).map A.hom
      · rw [key]; exact (IsLocalization.Away.algebraMap_isUnit (s j)).map B.hom
    let L : Localization.Away (s i * s j) →+* T := IsLocalization.Away.lift (s i * s j) hu
    have hL : L.comp (algebraMap S (Localization.Away (s i * s j))) =
        A.hom.comp (algebraMap S (Localization.Away (s i))) := IsLocalization.Away.lift_comp _ _
    have hLA : L.comp (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) = A.hom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (s i)) (RingHom.ext fun x => ?_)
      have := congrArg (fun f => f x) hL
      simp only [RingHom.comp_apply] at this ⊢
      rw [IsLocalization.Away.awayToAwayRight_eq, this]
    have hLB : L.comp (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) = B.hom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (s j)) (RingHom.ext fun x => ?_)
      have := congrArg (fun f => f x) (hL.trans key)
      simp only [RingHom.comp_apply] at this ⊢
      rw [IsLocalization.Away.awayToAwayLeft_eq, this]
    have hA : Spec.map A = Spec.map (CommRingCat.ofHom L) ≫
        spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hLA]; rfl
    have hB : Spec.map B = Spec.map (CommRingCat.ofHom L) ≫
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hLB]; rfl
    have h2 : Spec.map A ≫ e i = Spec.map B ≫ e j := by
      rw [hA, hB, Category.assoc, Category.assoc, he i j]
    rw [ea, eb] at h2
    exact (Category.assoc _ _ _).symm.trans (h2.trans (Category.assoc _ _ _))
  exact ⟨𝒰.glueMorphisms e hf, fun i => Scheme.Cover.ι_glueMorphisms 𝒰 e hf i⟩

end GlobalTheory.SecGlue
