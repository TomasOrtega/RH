import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

/- English proof (translation)
Establish `e : (epsScaleR c).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S)`. Apply the tactic sequence `ext s <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]`. Use `conv_rhs => rw [← e]`. Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
theorem spMap_epsScaleR_comp {S : Type} [CommRing S] (c : S) :
    spMap (epsScaleR c) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by
  have e : (epsScaleR c).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
    ext s <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  conv_rhs => rw [← e]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo S _ x G' _ φ hp`. Set `up : ∀ w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left, w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x → (epsR S ⟶ G')` to `fun w h => Over.homMk (hp.1.lift w _ h) (hp.1.lift_snd _ _ _)`. Establish `hup : ∀ w h, (up w h).left ≫ φ = w` using `fun w h => hp.1.lift_fst _ _ _`. Establish `inj : ∀ {T : Over (Sp S)} {u v : T ⟶ G'}, u.left ≫ φ = v.left ≫ φ → u = v` using `fun h => Over.OverMorphism.ext (hp.1.hom_ext h ((Over.w _).trans (Over.w _).symm))`. Establish `one : ∀ T : Over (Sp S), (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ x) ⟶ Xo.univ.t.G).left` using `fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))`.

Establish `e : η[G'].left ≫ φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left`. Establish `e₁ : (1 : 𝟙_ (Over (Sp S)) ⟶ G') = η[G']` using `by rw [Hom.one_def]; simp`. Rewrite using `[← e₁, one]`. Conclude with `congrArg (· ≫ (η[Xo.univ.t.G]).left) (Category.id_comp x)`. Establish `zs : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _`.

Establish `e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S`. Use extensionality with `s`. Simplify using the standard rewrite rules. Simplify using `only [spMap]`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, e]`.

Simplify using the standard rewrite rules. Establish `tan : ∀ w : epsR S ⟶ G', IsTangent w ↔ IsTanAt x (w.left ≫ φ)` using `fun w => by`. Use `⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => hp.1.hom_ext ?_ ?_⟩` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ φ) h).trans e)`. Conclude with `(Category.assoc _ _ _).trans (h.2.trans e.symm)`.

Use `(Category.assoc _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Over.w w, Over.w η[G']]`. Conclude with `zs`. Establish `pr : ∀ {n} (u : Fin n → (epsR S ⟶ G')), (List.ofFn u).prod.left ≫ φ = (List.ofFn fun i => (pushPt hp.1.w (u i) : tEps x ⟶ Xo.univ.t.G)).prod.left` using `fun u => congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))`. Establish `comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) w, IsLieComb c v w ↔ IsCombAt x (fun i => (v i).left ≫ φ) c (w.left ≫ φ)` using `fun c v w => by`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩`. Introduce and unpack `⟨u, hu, hw⟩`. Use `⟨fun i => up (u i).left (Over.w _), fun i => hp.1.hom_ext ?_ ?_, inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩` and prove the remaining obligations.

Conclude with `(hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)`. Use `(Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm` and prove the remaining obligations. Conclude with `(spMap_epsScaleR_comp (c i)).symm`. Establish `: u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEps x ⟶ Xo.univ.t.G)`.

Use function extensionality and compare the values at `fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm`. Conclude with `congrArg (fun q : _ → (tEps x ⟶ Xo.univ.t.G) => (List.ofFn q).prod.left) this`. Use `⟨fun w hw => ⟨up w hw.1, hup _ _⟩, fun n v => ⟨fun hB => ⟨fun i => (tan _).1 (hB.1 i), fun w hw => ?_⟩, fun hB => ⟨fun i => (tan _).2 (hB.1 i), fun w hw => ?_⟩⟩⟩` and prove the remaining obligations. Establish `h` using `hB.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))`. Simplify using `only [comb, hup] at h`.

Conclude with `h`. Establish `h` using `hB.2 _ ((tan _).1 hw)`. Simplify using `only [comb]`. Conclude with `h`.
-/
theorem lieBasis_iff_tanBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (G' : Over (Sp S)) [GrpObj G'] (φ : G'.left ⟶ Xo.univ.t.G.left), IsGrpPullback G' Xo.univ.t.G x φ → (∀ w : (Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsTanAt x w → ∃ v : epsR S ⟶ G', v.left ≫ φ = w) ∧ ∀ (n : ℕ) (v : Fin n → (epsR S ⟶ G')), IsLieBasis v ↔ TanBasis x (fun i => (v i).left ≫ φ) := by
  intro E _ _ _ H Dw l Xo S _ x G' _ φ hp
  let up : ∀ w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left,
      w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x → (epsR S ⟶ G') :=
    fun w h => Over.homMk (hp.1.lift w _ h) (hp.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => hp.1.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ G'}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (hp.1.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ x) ⟶ Xo.univ.t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have e : η[G'].left ≫ φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
    have e₁ : (1 : 𝟙_ (Over (Sp S)) ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [← e₁, one]
    exact congrArg (· ≫ (η[Xo.univ.t.G]).left) (Category.id_comp x)
  have zs : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have tan : ∀ w : epsR S ⟶ G', IsTangent w ↔ IsTanAt x (w.left ≫ φ) := fun w => by
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => hp.1.hom_ext ?_ ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
    · refine (Category.assoc _ _ _).trans ?_
      rw [Over.w w, Over.w η[G']]
      exact zs
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ G')), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEps x ⟶ Xo.univ.t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) w,
      IsLieComb c v w ↔ IsCombAt x (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => hp.1.hom_ext ?_ ?_,
        inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (spMap_epsScaleR_comp (c i)).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEps x ⟶ Xo.univ.t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEps x ⟶ Xo.univ.t.G) => (List.ofFn q).prod.left) this
  refine ⟨fun w hw => ⟨up w hw.1, hup _ _⟩, fun n v => ⟨fun hB => ⟨fun i => (tan _).1 (hB.1 i), fun w hw => ?_⟩,
    fun hB => ⟨fun i => (tan _).2 (hB.1 i), fun w hw => ?_⟩⟩⟩
  · have h := hB.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))
    simp only [comb, hup] at h
    exact h
  · have h := hB.2 _ ((tan _).1 hw)
    simp only [comb]
    exact h

end GlobalTheory.Frames
