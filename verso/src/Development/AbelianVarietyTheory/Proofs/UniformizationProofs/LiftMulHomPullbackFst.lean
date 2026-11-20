import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothLocusBaseChange

/- English proof (translation)
Establish `key : (lift a b).left = i ≫ (lift x y).left ≫ (Functor.LaxMonoidal.μ (Over.pullback φ) G G).left ≫ pullback.fst (G ⊗ G).hom φ`. Apply `pullback.hom_ext` to reduce the goal to its premises. Establish `h1 : (lift a b).left ≫ pullback.fst _ _ = a.left` using `congrArg (·.left) (lift_fst a b)`. Establish `h2 : (lift x y).left ≫ pullback.fst _ _ = x.left` using `congrArg (·.left) (lift_fst x y)`. Use `(h1.trans ha).trans ?_` and prove the remaining obligations.

Rewrite using `[← h2]`. Simplify using `only [Category.assoc]`. Use `erw [Over.μ_pullback_left_fst_fst]`. Establish `h1 : (lift a b).left ≫ pullback.snd _ _ = b.left` using `congrArg (·.left) (lift_snd a b)`. Establish `h2 : (lift x y).left ≫ pullback.snd _ _ = y.left` using `congrArg (·.left) (lift_snd x y)`.

Use `(h1.trans hb).trans ?_` and prove the remaining obligations. Rewrite using `[← h2]`. Simplify using `only [Category.assoc]`. Use `erw [Over.μ_pullback_left_fst_snd]`. Rewrite using `[Over.comp_left, key]`.

Simplify using `only [Functor.obj.μ_def, Over.comp_left, Category.assoc, Over.pullback_map_left]`. Use `erw [pullback.lift_fst]`.
-/
theorem lift_mul_pullback_fst {S S' : Scheme.{0}} (φ : S' ⟶ S) (G : Over S) [GrpObj G]
    {Z : Over S'} (x y : Z ⟶ (Over.pullback φ).obj G) {Z₀ : Over S} (i : Z₀.left ⟶ Z.left)
    (a b : Z₀ ⟶ G) (ha : a.left = i ≫ x.left ≫ pullback.fst _ _)
    (hb : b.left = i ≫ y.left ≫ pullback.fst _ _) :
    (lift a b ≫ μ[G]).left =
      i ≫ (lift x y ≫ μ[(Over.pullback φ).obj G]).left ≫ pullback.fst _ _ := by
  have key : (lift a b).left = i ≫ (lift x y).left ≫
      (Functor.LaxMonoidal.μ (Over.pullback φ) G G).left ≫ pullback.fst (G ⊗ G).hom φ := by
    apply pullback.hom_ext
    · have h1 : (lift a b).left ≫ pullback.fst _ _ = a.left := congrArg (·.left) (lift_fst a b)
      have h2 : (lift x y).left ≫ pullback.fst _ _ = x.left := congrArg (·.left) (lift_fst x y)
      refine (h1.trans ha).trans ?_
      rw [← h2]
      simp only [Category.assoc]
      erw [Over.μ_pullback_left_fst_fst]
    · have h1 : (lift a b).left ≫ pullback.snd _ _ = b.left := congrArg (·.left) (lift_snd a b)
      have h2 : (lift x y).left ≫ pullback.snd _ _ = y.left := congrArg (·.left) (lift_snd x y)
      refine (h1.trans hb).trans ?_
      rw [← h2]
      simp only [Category.assoc]
      erw [Over.μ_pullback_left_fst_snd]
  rw [Over.comp_left, key]
  simp only [Functor.obj.μ_def, Over.comp_left, Category.assoc, Over.pullback_map_left]
  erw [pullback.lift_fst]

/- English proof (translation)
Rewrite using `[lift_mul_pullback_fst φ G (x ≫ q) (y ≫ q) i a b (by simpa using ha) (by simpa using hb)]`. Establish `: lift (x ≫ q) (y ≫ q) ≫ μ[(Over.pullback φ).obj G] = (lift x y ≫ μ[E]) ≫ q`. Rewrite using `[Category.assoc, IsMonHom.mul_hom, lift_map_assoc]`. Rewrite using `[this, Over.comp_left, Category.assoc]`.
-/
theorem lift_mul_hom_pullback_fst {S S' : Scheme.{0}} (φ : S' ⟶ S) (G : Over S) [GrpObj G]
    {E : Over S'} [MonObj E] (q : E ⟶ (Over.pullback φ).obj G) [IsMonHom q]
    {Z : Over S'} (x y : Z ⟶ E) {Z₀ : Over S} (i : Z₀.left ⟶ Z.left)
    (a b : Z₀ ⟶ G) (ha : a.left = i ≫ x.left ≫ q.left ≫ pullback.fst _ _)
    (hb : b.left = i ≫ y.left ≫ q.left ≫ pullback.fst _ _) :
    (lift a b ≫ μ[G]).left =
      i ≫ (lift x y ≫ μ[E]).left ≫ q.left ≫ pullback.fst _ _ := by
  rw [lift_mul_pullback_fst φ G (x ≫ q) (y ≫ q) i a b (by simpa using ha) (by simpa using hb)]
  have : lift (x ≫ q) (y ≫ q) ≫ μ[(Over.pullback φ).obj G] = (lift x y ≫ μ[E]) ≫ q := by
    rw [Category.assoc, IsMonHom.mul_hom, lift_map_assoc]
  rw [this, Over.comp_left, Category.assoc]

open GlobalTheory.WeierstrassCurve in

/- English proof (translation)
Introduce `R R' _ _ _ _ f W U hU _ _ _ hmul`. Set `φ` to `Spec.map (CommRingCat.ofHom f)`. Set `U' : (scheme (W.map f)).Opens` to `mapHom W f rfl ⁻¹ᵁ U`. Establish `hpb : IsPullback (mapHom W f rfl ∣_ U) (U'.ι ≫ toSpec (W.map f)) (U.ι ≫ toSpec W) φ` using `(isPullback_morphismRestrict (mapHom W f rfl) U).paste_vert (isPullback_mapHom W f rfl)`. Set `e : Over.mk (U'.ι ≫ toSpec (W.map f)) ≅ (Over.pullback φ).obj (Over.mk (U.ι ≫ toSpec W))` to `Over.isoMk hpb.isoPullback hpb.isoPullback_hom_snd`.

Establish `he : e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ = mapHom W f rfl ∣_ U` using `hpb.isoPullback_hom_fst`. Establish `he' : e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ ≫ U.ι = U'.ι ≫ mapHom W f rfl`. Rewrite using `[← Category.assoc, he]`. Conclude with `morphismRestrict_ι _ _`. Set `: GrpObj (Over.mk (U'.ι ≫ toSpec (W.map f)))` to `GrpObj.ofIso e.symm`.

Establish `hinv : IsMonHom e.symm.hom` using `isMonHom_ofIso e.symm`. Establish `hhom : IsMonHom e.hom` using `inferInstanceAs (IsMonHom e.symm.inv)`. Use `⟨U', inferInstance, e, hhom, he', ?_, ?_⟩` and prove the remaining obligations. Introduce `k _ ρ P h`. Use `hU k (ρ.comp f) P (h.comp_of_map_eq rfl)` as an intermediate fact.

Rewrite `this` using `[← ptHom_mapHom W f rfl ρ P h, Scheme.Hom.comp_preimage]`. Conclude with `this`. Introduce `k _ ρ x y P Q hP hQ hx hy`. Establish `hw : ∀ z : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ Over.mk (U'.ι ≫ toSpec (W.map f)), (z.left ≫ e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ) ≫ U.ι ≫ toSpec W = Spec.map (CommRingCat.ofHom (ρ.comp f))`. Introduce `z`.

Establish `hz : z.left ≫ U'.ι ≫ toSpec (W.map f) = Spec.map (CommRingCat.ofHom ρ)` using `Over.w z`. Rewrite using `[he, Category.assoc, hpb.w, ← Category.assoc]`. Use `erw [hz]`. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp]`. Establish `hι : ∀ z : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ Over.mk (U'.ι ≫ toSpec (W.map f)), (z.left ≫ e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ) ≫ U.ι = (z.left ≫ U'.ι) ≫ mapHom W f rfl`.

Introduce `z`. Simplify using `only [Category.assoc]`. Use `erw [he']`. Set `a : Over.mk (Spec.map (CommRingCat.ofHom (ρ.comp f))) ⟶ Over.mk (U.ι ≫ toSpec W)` to `Over.homMk _ (hw x)`. Set `b : Over.mk (Spec.map (CommRingCat.ofHom (ρ.comp f))) ⟶ Over.mk (U.ι ≫ toSpec W)` to `Over.homMk _ (hw y)`.

Take `⟨h, hab⟩` from `hmul k (ρ.comp f) a b P Q (hP.comp_of_map_eq rfl) (hQ.comp_of_map_eq rfl) ((hι x).trans (by rw [hx]; exact ptHom_mapHom W f rfl ρ P hP)) ((hι y).trans (by rw [hy]; exact ptHom_mapHom W f rfl ρ Q hQ))`. Use `⟨h, ?_⟩` and prove the remaining obligations. Establish `hl` using `lift_mul_hom_pullback_fst φ (Over.mk (U.ι ≫ toSpec W)) e.hom x y (Z₀ := Over.mk (Spec.map (CommRingCat.ofHom (ρ.comp f)))) (𝟙 _) a b (Category.id_comp _).symm (Category.id_comp _).symm`. Apply `(isPullback_mapHom W f rfl).hom_ext` to reduce the goal to its premises. Use `(hι _).symm.trans ?_` and prove the remaining obligations.

Use `Eq.trans ?_ (hab.trans (ptHom_mapHom W f rfl ρ _ h).symm)` and prove the remaining obligations. Rewrite using `[hl]`. Use `erw [Category.id_comp]`. Both sides reduce to the same expression. Conclude with `(Category.assoc _ _ _).trans ((Over.w (lift x y ≫ μ[Over.mk (U'.ι ≫ toSpec (W.map f))])).trans (ptHom_toSpec (W.map f) ρ _ h).symm)`.
-/
theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] (f : R →+* R') (W : WeierstrassCurve R) (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∀ [GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))], (∀ (k : Type) [Field k] (ρ : R →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) → ∃ (U' : (GlobalTheory.WeierstrassCurve.scheme (W.map f)).Opens) (_ : GrpObj (Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f)))) (e : (Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f))) ≅ (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))), IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst _ _ ≫ U.ι = U'.ι ≫ GlobalTheory.WeierstrassCurve.mapHom W f rfl ∧ (∀ (k : Type) [Field k] (ρ : R' →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ P h ⁻¹ᵁ U' ↔ ((W.map f).map ρ).toProjective.Nonsingular P) ∧ (∀ (k : Type) [Field k] (ρ : R' →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f)))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) Q), x.left ≫ U'.ι = GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ P hP → y.left ≫ U'.ι = GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((W.map f).map ρ) (((W.map f).map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U'.ι ≫ GlobalTheory.WeierstrassCurve.toSpec (W.map f)))]).left ≫ U'.ι = GlobalTheory.WeierstrassCurve.ptHom (W.map f) ρ _ h) := by
  intro R R' _ _ _ _ f W U hU _ _ _ hmul
  let φ := Spec.map (CommRingCat.ofHom f)
  let U' : (scheme (W.map f)).Opens := mapHom W f rfl ⁻¹ᵁ U
  have hpb : IsPullback (mapHom W f rfl ∣_ U) (U'.ι ≫ toSpec (W.map f)) (U.ι ≫ toSpec W) φ :=
    (isPullback_morphismRestrict (mapHom W f rfl) U).paste_vert (isPullback_mapHom W f rfl)
  let e : Over.mk (U'.ι ≫ toSpec (W.map f)) ≅
      (Over.pullback φ).obj (Over.mk (U.ι ≫ toSpec W)) :=
    Over.isoMk hpb.isoPullback hpb.isoPullback_hom_snd
  have he : e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ = mapHom W f rfl ∣_ U :=
    hpb.isoPullback_hom_fst
  have he' : e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ ≫ U.ι = U'.ι ≫ mapHom W f rfl := by
    rw [← Category.assoc, he]
    exact morphismRestrict_ι _ _
  let : GrpObj (Over.mk (U'.ι ≫ toSpec (W.map f))) := GrpObj.ofIso e.symm
  have hinv : IsMonHom e.symm.hom := isMonHom_ofIso e.symm
  have hhom : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  refine ⟨U', inferInstance, e, hhom, he', ?_, ?_⟩
  · intro k _ ρ P h
    have := hU k (ρ.comp f) P (h.comp_of_map_eq rfl)
    rw [← ptHom_mapHom W f rfl ρ P h, Scheme.Hom.comp_preimage] at this
    exact this
  · intro k _ ρ x y P Q hP hQ hx hy
    have hw : ∀ z : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶
        Over.mk (U'.ι ≫ toSpec (W.map f)),
        (z.left ≫ e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ) ≫ U.ι ≫ toSpec W =
          Spec.map (CommRingCat.ofHom (ρ.comp f)) := by
      intro z
      have hz : z.left ≫ U'.ι ≫ toSpec (W.map f) = Spec.map (CommRingCat.ofHom ρ) := Over.w z
      rw [he, Category.assoc, hpb.w, ← Category.assoc]
      erw [hz]
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
    have hι : ∀ z : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶
        Over.mk (U'.ι ≫ toSpec (W.map f)),
        (z.left ≫ e.hom.left ≫ pullback.fst (U.ι ≫ toSpec W) φ) ≫ U.ι =
          (z.left ≫ U'.ι) ≫ mapHom W f rfl := by
      intro z
      simp only [Category.assoc]
      erw [he']
    let a : Over.mk (Spec.map (CommRingCat.ofHom (ρ.comp f))) ⟶ Over.mk (U.ι ≫ toSpec W) :=
      Over.homMk _ (hw x)
    let b : Over.mk (Spec.map (CommRingCat.ofHom (ρ.comp f))) ⟶ Over.mk (U.ι ≫ toSpec W) :=
      Over.homMk _ (hw y)
    obtain ⟨h, hab⟩ := hmul k (ρ.comp f) a b P Q (hP.comp_of_map_eq rfl) (hQ.comp_of_map_eq rfl)
      ((hι x).trans (by rw [hx]; exact ptHom_mapHom W f rfl ρ P hP))
      ((hι y).trans (by rw [hy]; exact ptHom_mapHom W f rfl ρ Q hQ))
    refine ⟨h, ?_⟩
    have hl := lift_mul_hom_pullback_fst φ (Over.mk (U.ι ≫ toSpec W)) e.hom x y
      (Z₀ := Over.mk (Spec.map (CommRingCat.ofHom (ρ.comp f)))) (𝟙 _) a b
      (Category.id_comp _).symm (Category.id_comp _).symm
    apply (isPullback_mapHom W f rfl).hom_ext
    · refine (hι _).symm.trans ?_
      refine Eq.trans ?_ (hab.trans (ptHom_mapHom W f rfl ρ _ h).symm)
      rw [hl]
      erw [Category.id_comp]
      rfl
    · exact (Category.assoc _ _ _).trans ((Over.w
        (lift x y ≫ μ[Over.mk (U'.ι ≫ toSpec (W.map f))])).trans
        (ptHom_toSpec (W.map f) ρ _ h).symm)

end GlobalTheory.SmoothLocusBaseChange
