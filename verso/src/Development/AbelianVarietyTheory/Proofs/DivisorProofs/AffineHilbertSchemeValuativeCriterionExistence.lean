import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapIdealTopOfIsAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSubschemeOfQuotientFlatAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatIdealValuationRingPullbackStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

/- English proof (translation)
Take `⟨J₀, hf, hJ⟩` from `GlobalTheory.T.exists_flat_ideal_valuationRing_pullback V K X X' p p' b h (I.ideal ⟨⊤, isAffineOpen_top X'⟩)`. Establish `e : (Scheme.IdealSheafData.ofIdealTop J₀).ideal ⟨⊤, isAffineOpen_top X⟩ = J₀` using `Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply J₀`. Use `⟨Scheme.IdealSheafData.ofIdealTop J₀, GlobalTheory.T.flat_subscheme_of_quotient_flat_affine V X p _ (by rw [e]; exact hf), ?_⟩` and prove the remaining obligations. Apply `Scheme.IdealSheafData.ext_of_isAffine` to reduce the goal to its premises. Rewrite using `[GlobalTheory.T.idealSheafData_comap_ideal_top_of_isAffine, e, hJ]`.
-/
theorem exists_flat_ideal_extension (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) [IsAffine X] [IsAffine X']
    (p : X ⟶ Spec (CommRingCat.of V)) (p' : X' ⟶ Spec (CommRingCat.of K)) (b : X' ⟶ X)
    (h : IsPullback b p' p (Spec.map (CommRingCat.ofHom (algebraMap V K))))
    (I : X'.IdealSheafData) : ∃ J : X.IdealSheafData, Flat (J.subschemeι ≫ p) ∧ J.comap b = I := by
  obtain ⟨J₀, hf, hJ⟩ := GlobalTheory.T.exists_flat_ideal_valuationRing_pullback V K X X' p p' b h (I.ideal ⟨⊤, isAffineOpen_top X'⟩)
  have e : (Scheme.IdealSheafData.ofIdealTop J₀).ideal ⟨⊤, isAffineOpen_top X⟩ = J₀ :=
    Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply J₀
  refine ⟨Scheme.IdealSheafData.ofIdealTop J₀, GlobalTheory.T.flat_subscheme_of_quotient_flat_affine V X p _ (by rw [e]; exact hf), ?_⟩
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [GlobalTheory.T.idealSheafData_comap_ideal_top_of_isAffine, e, hJ]

/- English proof (translation)
Establish `: IsAffine Z` using `isAffine_of_isAffineHom f`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (Z.isoSpec.inv ≫ f)`. Establish `ef : f = Z.isoSpec.hom ≫ Spec.map φ` using `by rw [hφ]; simp`. Establish `hf1 : IsFinite (Spec.map φ)` using `by rw [hφ]; infer_instance`. Establish `hf2 : Flat (Spec.map φ)` using `by rw [hφ]; infer_instance`.

Establish `hr1` using `hf1`. Establish `hr2` using `hf2`. Rewrite `hr1` using `[IsFinite.SpecMap_iff]`. Rewrite `hr2` using `[Flat.SpecMap_iff]`. Rewrite using `[ef, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hr1 hr2]`.

Use `algebraize [φ.hom]`. Establish `: Module.Free V Γ(Z, ⊤)` using `Module.free_of_flat_of_isLocalRing`. Rewrite using `[← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap]`. Simplify using `only [Module.rankAtStalk_eq_finrank_of_free]`. Both sides reduce to the same expression.
-/
theorem finrank_const_of_isLocalRing (V : Type) [CommRing V] [IsLocalRing V] (Z : Scheme.{0})
    (f : Z ⟶ Spec (CommRingCat.of V)) (h1 : IsFinite f) (h2 : Flat f) (x y : Spec (CommRingCat.of V)) :
    f.finrank x = f.finrank y := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ f)
  have ef : f = Z.isoSpec.hom ≫ Spec.map φ := by rw [hφ]; simp
  have hf1 : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hf2 : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have hr1 := hf1
  have hr2 := hf2
  rw [IsFinite.SpecMap_iff] at hr1
  rw [Flat.SpecMap_iff] at hr2
  rw [ef, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hr1 hr2]
  algebraize [φ.hom]
  have : Module.Free V Γ(Z, ⊤) := Module.free_of_flat_of_isLocalRing
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap]
  simp only [Module.rankAtStalk_eq_finrank_of_free]
  rfl

/- English proof (translation)
Take `⟨J, hJf, hJ⟩` from `exists_flat_ideal_extension V K _ _ (pullback.snd (str A B) g) (pullback.snd _ _) _ (isPullback_bc A B g _) I`. Establish `: IsFinite (str A B)`. Rewrite using `[IsFinite.SpecMap_iff]`. Conclude with `RingHom.finite_algebraMap.mpr inferInstance`. Establish `h1 : IsFinite (J.subschemeι ≫ pullback.snd (str A B) g)` using `inferInstance`.

Use `⟨J, ⟨h1, hJf, fun y => ?_⟩, hJ⟩` and prove the remaining obligations. Take `⟨_, _, h3⟩` from `hI`. Substitute `hJ` using the available equality. Use `set a := Spec.map (CommRingCat.ofHom (algebraMap V K))`. Take `⟨pt⟩ : Nonempty (Spec (CommRingCat.of K))` from `inferInstance`.

Rewrite using `[finrank_const_of_isLocalRing V _ _ h1 hJf y (a pt)]`. Establish `H : IsPullback (pullback.snd (bc A B g a) J.subschemeι) (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g)) (J.subschemeι ≫ pullback.snd _ g) a` using `(IsPullback.of_hasPullback (bc A B g a) J.subschemeι).flip.paste_vert (isPullback_bc A B g a)`. Establish `e : (J.comap (bc A B g a)).subschemeι ≫ pullback.snd _ (a ≫ g) = (J.comapIso (bc A B g a)).hom ≫ (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g))`. Rewrite using `[← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]`. Establish `f1 : IsFinite (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g))` using `MorphismProperty.of_isPullback (P := @IsFinite) H h1`.

Establish `f2 : Flat (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g))` using `MorphismProperty.of_isPullback (P := @Flat) H hJf`. Use `h3 pt` as an intermediate fact. Rewrite `this` using `[e, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_of_isPullback _ _ _ _ H pt]`. Conclude with `this`.
-/
theorem exists_good_extension (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (r : ℕ) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (g : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ g)).IdealSheafData)
    (hI : Good A B r _ I) :
    ∃ J, Good A B r g J ∧ J.comap (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K)))) = I := by
  obtain ⟨J, hJf, hJ⟩ := exists_flat_ideal_extension V K _ _ (pullback.snd (str A B) g) (pullback.snd _ _) _
    (isPullback_bc A B g _) I
  have : IsFinite (str A B) := by
    rw [IsFinite.SpecMap_iff]; exact RingHom.finite_algebraMap.mpr inferInstance
  have h1 : IsFinite (J.subschemeι ≫ pullback.snd (str A B) g) := inferInstance
  refine ⟨J, ⟨h1, hJf, fun y => ?_⟩, hJ⟩
  obtain ⟨_, _, h3⟩ := hI
  subst hJ
  set a := Spec.map (CommRingCat.ofHom (algebraMap V K))
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  rw [finrank_const_of_isLocalRing V _ _ h1 hJf y (a pt)]
  have H : IsPullback (pullback.snd (bc A B g a) J.subschemeι)
      (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g))
      (J.subschemeι ≫ pullback.snd _ g) a :=
    (IsPullback.of_hasPullback (bc A B g a) J.subschemeι).flip.paste_vert (isPullback_bc A B g a)
  have e : (J.comap (bc A B g a)).subschemeι ≫ pullback.snd _ (a ≫ g) =
      (J.comapIso (bc A B g a)).hom ≫ (pullback.fst (bc A B g a) J.subschemeι ≫
        pullback.snd _ (a ≫ g)) := by
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have f1 : IsFinite (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) H h1
  have f2 : Flat (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @Flat) H hJf
  have := h3 pt
  rw [e, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_of_isPullback _ _ _ _ H pt]
    at this
  exact this

/- English proof (translation)
Introduce `S`. Establish `key : ∀ {T : Scheme.{0}} (f : T ⟶ H), (R.homEquiv f).1 = f ≫ (R.homEquiv (𝟙 H)).1`. Introduce `T f`. Establish `h` using `R.homEquiv_comp f (𝟙 H)`. Rewrite `h` using `[Category.comp_id]`.

Rewrite using `[h]`. Both sides reduce to the same expression. Use `set ι := Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) with hι`. Establish `gen : ∀ x : (functor A B r).obj (op (Spec (CommRingCat.of S.K))), x.1 = ι ≫ S.i₂ → ∃ y : (functor A B r).obj (op (Spec (CommRingCat.of S.R))), y.1 = S.i₂ ∧ (functor A B r).map ι.op y = x`. Introduce and unpack `⟨g', I, hI⟩ hx`.

Simplify using `only at hx`. Substitute `hx` using the available equality. Take `⟨J, hJ, hJI⟩` from `exists_good_extension A B r S.R S.K S.i₂ I hI`. Substitute `hJI` using the available equality. Conclude with `⟨⟨S.i₂, J, hJ⟩, rfl, rfl⟩`.

Take `⟨y, hy1, hy2⟩` from `gen (R.homEquiv S.i₁) ((key S.i₁).trans S.commSq.w)`. Use `⟨⟨{ l := R.homEquiv.symm y, fac_left := ?_, fac_right := ?_ }⟩⟩` and prove the remaining obligations. Apply `R.homEquiv.injective` to reduce the goal to its premises. Rewrite using `[R.homEquiv_comp, Equiv.apply_symm_apply, hy2]`. Rewrite using `[← key, Equiv.apply_symm_apply, hy1]`.
-/
theorem valuativeExistence (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H) :
    ValuativeCriterion.Existence (R.homEquiv (𝟙 H)).1 := by
  intro S
  have key : ∀ {T : Scheme.{0}} (f : T ⟶ H), (R.homEquiv f).1 = f ≫ (R.homEquiv (𝟙 H)).1 := by
    intro T f
    have h := R.homEquiv_comp f (𝟙 H)
    rw [Category.comp_id] at h
    rw [h]; rfl
  set ι := Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) with hι
  have gen : ∀ x : (functor A B r).obj (op (Spec (CommRingCat.of S.K))), x.1 = ι ≫ S.i₂ →
      ∃ y : (functor A B r).obj (op (Spec (CommRingCat.of S.R))),
        y.1 = S.i₂ ∧ (functor A B r).map ι.op y = x := by
    rintro ⟨g', I, hI⟩ hx
    dsimp only at hx
    subst hx
    obtain ⟨J, hJ, hJI⟩ := exists_good_extension A B r S.R S.K S.i₂ I hI
    subst hJI
    exact ⟨⟨S.i₂, J, hJ⟩, rfl, rfl⟩
  obtain ⟨y, hy1, hy2⟩ := gen (R.homEquiv S.i₁) ((key S.i₁).trans S.commSq.w)
  refine ⟨⟨{ l := R.homEquiv.symm y, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply R.homEquiv.injective
    rw [R.homEquiv_comp, Equiv.apply_symm_apply, hy2]
  · rw [← key, Equiv.apply_symm_apply, hy1]

end GlobalTheory.HilbAff
