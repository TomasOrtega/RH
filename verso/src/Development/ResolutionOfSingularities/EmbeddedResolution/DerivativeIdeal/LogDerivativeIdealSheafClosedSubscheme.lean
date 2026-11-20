import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealQuotient
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Establish `h : (u ≫ q).app U = q.app U ≫ u.app (q ⁻¹ᵁ U)` using `Scheme.Hom.comp_app u q U`. Conclude with `DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) a`.
-/
private theorem comp_app_apply {X Y Z : Scheme.{u}} (u : X ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens)
    (a : Γ(Z, U)) : ((u ≫ q).app U).hom a = (u.app (q ⁻¹ᵁ U)).hom ((q.app U).hom a) := by
  have h : (u ≫ q).app U = q.app U ≫ u.app (q ⁻¹ᵁ U) := Scheme.Hom.comp_app u q U
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) a

/- English proof (translation)
Establish `key : ∀ (U : X.affineOpens), L.ideal U ≤ RingHom.ker ((D.subschemeι ≫ ι).app (U : X.Opens)).hom`. Introduce `U a ha`. Establish `h1` using `h U (Ideal.mem_map_of_mem _ ha)`. Establish `h2 : (Scheme.Hom.ker D.subschemeι).ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ = RingHom.ker (D.subschemeι.app (ι ⁻¹ᵁ (U : X.Opens))).hom`. Rewrite using `[Scheme.Hom.ker_apply]`.

Rewrite `h2` using `[Scheme.IdealSheafData.ker_subschemeι]`. Rewrite `h1` using `[h2]`. Use `RingHom.mem_ker.mpr ?_` and prove the remaining obligations. Rewrite using `[comp_app_apply]`. Conclude with `RingHom.mem_ker.mp h1`.

Establish `hle : L ≤ Scheme.Hom.ker (D.subschemeι ≫ ι)`. Unfold `Scheme.Hom.ker`. Conclude with `Scheme.IdealSheafData.le_ofIdeals_iff.mpr key`. Rewrite using `[← Scheme.IdealSheafData.le_map_iff_comap_le]`. Conclude with `hle`.
-/
private theorem comap_le_of_map_ideal_le {S X : Scheme.{u}} (ι : S ⟶ X) [IsAffineHom ι]
    (L : X.IdealSheafData) (D : S.IdealSheafData)
    (h : ∀ U : X.affineOpens, Ideal.map (ι.app (U : X.Opens)).hom (L.ideal U)
        ≤ D.ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩) :
    L.comap ι ≤ D := by
  have key : ∀ (U : X.affineOpens), L.ideal U
      ≤ RingHom.ker ((D.subschemeι ≫ ι).app (U : X.Opens)).hom := by
    intro U a ha
    have h1 := h U (Ideal.mem_map_of_mem _ ha)
    have h2 : (Scheme.Hom.ker D.subschemeι).ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩
        = RingHom.ker (D.subschemeι.app (ι ⁻¹ᵁ (U : X.Opens))).hom := by
      rw [Scheme.Hom.ker_apply]
    rw [Scheme.IdealSheafData.ker_subschemeι] at h2
    rw [h2] at h1
    refine RingHom.mem_ker.mpr ?_
    rw [comp_app_apply]
    exact RingHom.mem_ker.mp h1
  have hle : L ≤ Scheme.Hom.ker (D.subschemeι ≫ ι) := by
    unfold Scheme.Hom.ker
    exact Scheme.IdealSheafData.le_ofIdeals_iff.mpr key
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
  exact hle

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => exact h`. Consider the case `succ r ih`. Rewrite using `[derivIdealIterate_succ, derivIdealIterate_succ]`. Conclude with `derivIdeal_mono k ih`.
-/
private theorem derivIdealIterate_mono_of_le (k : Type u) [CommRing k] {T : Type u} [CommRing T]
    [Algebra k T] (r : ℕ) {I J : Ideal T} (h : I ≤ J) :
    derivIdealIterate k r I ≤ derivIdealIterate k r J := by
  induction r with
  | zero => exact h
  | succ r ih =>
      rw [derivIdealIterate_succ, derivIdealIterate_succ]
      exact derivIdeal_mono k ih

/- English proof (translation)
Establish `happ : ι.appLE U (ι ⁻¹ᵁ U) le_rfl = ι.app U` using `Scheme.Hom.appLE_eq_app ι`. Establish `hc : p.appLE ⊤ U (le_preimage_top k p U) ≫ ι.appLE U (ι ⁻¹ᵁ U) le_rfl = (ι ≫ p).appLE ⊤ (ι ⁻¹ᵁ U) (le_preimage_top k (ι ≫ p) (ι ⁻¹ᵁ U))` using `Scheme.Hom.appLE_comp_appLE ι p ⊤ U (ι ⁻¹ᵁ U) (le_preimage_top k p U) le_rfl`. Establish `hmor : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U)) ≫ ι.app U = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (ι ≫ p).appLE ⊤ (ι ⁻¹ᵁ U) (le_preimage_top k (ι ≫ p) (ι ⁻¹ᵁ U))`. Rewrite using `[Category.assoc, ← happ, hc]`. Rewrite using `[sectionsAlgebraMap_eq k p U, sectionsAlgebraMap_eq k (ι ≫ p) (ι ⁻¹ᵁ U)]`.

Conclude with `congrArg CommRingCat.Hom.hom hmor`.
-/
private theorem app_comp_sectionsAlgebraMap (k : Type u) [CommRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (ι : S ⟶ X) (U : X.Opens) :
    (ι.app U).hom.comp (sectionsAlgebraMap k p U) = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ U) := by
  have happ : ι.appLE U (ι ⁻¹ᵁ U) le_rfl = ι.app U := Scheme.Hom.appLE_eq_app ι
  have hc : p.appLE ⊤ U (le_preimage_top k p U) ≫ ι.appLE U (ι ⁻¹ᵁ U) le_rfl
      = (ι ≫ p).appLE ⊤ (ι ⁻¹ᵁ U) (le_preimage_top k (ι ≫ p) (ι ⁻¹ᵁ U)) :=
    Scheme.Hom.appLE_comp_appLE ι p ⊤ U (ι ⁻¹ᵁ U) (le_preimage_top k p U) le_rfl
  have hmor : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U))
        ≫ ι.app U
      = (Scheme.ΓSpecIso (CommRingCat.of k)).inv
        ≫ (ι ≫ p).appLE ⊤ (ι ⁻¹ᵁ U) (le_preimage_top k (ι ≫ p) (ι ⁻¹ᵁ U)) := by
    rw [Category.assoc, ← happ, hc]
  rw [sectionsAlgebraMap_eq k p U, sectionsAlgebraMap_eq k (ι ≫ p) (ι ⁻¹ᵁ U)]
  exact congrArg CommRingCat.Hom.hom hmor

/- English proof (translation)
The claim follows from `DFunLike.congr_fun (app_comp_sectionsAlgebraMap k p ι U) a`.
-/
private theorem app_sectionsAlgebraMap (k : Type u) [CommRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (ι : S ⟶ X) (U : X.Opens) (a : k) :
    (ι.app U).hom (sectionsAlgebraMap k p U a) = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ U) a :=
  DFunLike.congr_fun (app_comp_sectionsAlgebraMap k p ι U) a

/- English proof (translation)
Establish `hcomm : ∀ a : k, (ι.app (U : X.Opens)).hom (@algebraMap k _ _ _ (sectionsAlgebra k p (U : X.Opens)) a) = @algebraMap k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) a`. Introduce `a`. Establish `e1 : @algebraMap k _ _ _ (sectionsAlgebra k p (U : X.Opens)) = sectionsAlgebraMap k p (U : X.Opens)` using `algebraMap_sectionsAlgebra k p (U : X.Opens)`. Establish `e2 : @algebraMap k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))` using `algebraMap_sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))`. Rewrite using `[e1, e2]`.

Conclude with `app_sectionsAlgebraMap k p ι (U : X.Opens) a`. Establish `hmapLE : ∀ (V : S.affineOpens) (e : (V : S.Opens) ≤ ι ⁻¹ᵁ (U : X.Opens)), Ideal.map (ι.appLE (U : X.Opens) (V : S.Opens) e).hom (A.ideal U) ≤ (A.comap ι).ideal V`. Introduce `V e`. Apply `Scheme.IdealSheafData.map_appLE_le_comap_ideal` to reduce the goal to its premises. Establish `hmap : Ideal.map (ι.app (U : X.Opens)).hom (A.ideal U) ≤ (A.comap ι).ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩`.

Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `hmapLE ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ le_rfl`. Establish `halg` using `@map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker k _ _ _ _ _ (sectionsAlgebra k p (U : X.Opens)) (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) (@AlgHom.mk k _ _ _ _ _ (sectionsAlgebra k p (U : X.Opens)) (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) (ι.app (U : …`. Rewrite using `[logDerivIdealSheafIterate_ideal, Scheme.Hom.ker_apply, derivIdealSheafIterate_ideal]`. Use `le_trans halg ?_` and prove the remaining obligations.

Conclude with `@derivIdealIterate_mono_of_le k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) r _ _ hmap`.
-/
private theorem map_logDerivIdealSheafIterate_ideal_le
    (k : Type u) [CommRing k] [IsNoetherianRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)]
    (A : X.IdealSheafData) (r : ℕ) (U : X.affineOpens) :
    Ideal.map (ι.app (U : X.Opens)).hom ((logDerivIdealSheafIterate k p ι.ker r A).ideal U)
      ≤ (derivIdealSheafIterate k (ι ≫ p) r (A.comap ι)).ideal
          ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ := by
  have hcomm : ∀ a : k,
      (ι.app (U : X.Opens)).hom
          (@algebraMap k _ _ _ (sectionsAlgebra k p (U : X.Opens)) a)
        = @algebraMap k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) a := by
    intro a
    have e1 : @algebraMap k _ _ _ (sectionsAlgebra k p (U : X.Opens))
        = sectionsAlgebraMap k p (U : X.Opens) :=
      algebraMap_sectionsAlgebra k p (U : X.Opens)
    have e2 : @algebraMap k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)))
        = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)) :=
      algebraMap_sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))
    rw [e1, e2]
    exact app_sectionsAlgebraMap k p ι (U : X.Opens) a
  have hmapLE : ∀ (V : S.affineOpens) (e : (V : S.Opens) ≤ ι ⁻¹ᵁ (U : X.Opens)),
      Ideal.map (ι.appLE (U : X.Opens) (V : S.Opens) e).hom (A.ideal U)
        ≤ (A.comap ι).ideal V := by
    intro V e
    apply Scheme.IdealSheafData.map_appLE_le_comap_ideal
  have hmap : Ideal.map (ι.app (U : X.Opens)).hom (A.ideal U)
      ≤ (A.comap ι).ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ := by
    rw [Scheme.Hom.app_eq_appLE]
    exact hmapLE ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ le_rfl
  have halg := @map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker k _ _ _ _ _
      (sectionsAlgebra k p (U : X.Opens))
      (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)))
      (@AlgHom.mk k _ _ _ _ _ (sectionsAlgebra k p (U : X.Opens))
        (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) (ι.app (U : X.Opens)).hom hcomm)
      (Scheme.Hom.app_surjective ι (U : X.Opens) U.2) _ rfl r (A.ideal U)
  rw [logDerivIdealSheafIterate_ideal, Scheme.Hom.ker_apply, derivIdealSheafIterate_ideal]
  refine le_trans halg ?_
  exact @derivIdealIterate_mono_of_le k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) r _ _
    hmap

/- English proof (translation)
The claim follows from `comap_le_of_map_ideal_le ι (logDerivIdealSheafIterate k p ι.ker r A) (derivIdealSheafIterate k (ι ≫ p) r (A.comap ι)) (map_logDerivIdealSheafIterate_ideal_le k p ι A r)`.
-/
private theorem logDerivIdealSheafIterate_comap_le_derivIdealSheafIterate
    (k : Type u) [CommRing k] [IsNoetherianRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)]
    (A : X.IdealSheafData) (r : ℕ) :
    (logDerivIdealSheafIterate k p ι.ker r A).comap ι
      ≤ derivIdealSheafIterate k (ι ≫ p) r (A.comap ι) :=
  comap_le_of_map_ideal_le ι (logDerivIdealSheafIterate k p ι.ker r A)
    (derivIdealSheafIterate k (ι ≫ p) r (A.comap ι))
    (map_logDerivIdealSheafIterate_ideal_le k p ι A r)

/- English proof (translation)
The claim follows from `logDerivIdealSheafIterate_comap_le_derivIdealSheafIterate k p ι A r`.
-/
theorem comap_logDerivIdealSheafIterate_ker_le_derivIdealSheafIterate
    (k : Type u) [CommRing k] [IsNoetherianRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)]
    (A : X.IdealSheafData) (r : ℕ) :
    (logDerivIdealSheafIterate k p ι.ker r A).comap ι
      ≤ derivIdealSheafIterate k (ι ≫ p) r (A.comap ι) :=
  logDerivIdealSheafIterate_comap_le_derivIdealSheafIterate k p ι A r

end FunctorialResolution.EmbeddedResolution
