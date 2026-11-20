import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

/- English proof (translation)
Use `letI := f.hom.toAlgebra`. Use `letI := g.hom.toAlgebra`. Use `haveI : Module.Flat R S := hf`. Establish `ht` using `CommRingCat.isPushout_tensorProduct R R' S`. Set `e` to `IsPushout.isoIsPushout _ _ h.flip ht`.

Establish `he : inl ≫ e.hom = CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom` using `IsPushout.inr_isoIsPushout_hom _ _ h.flip ht`. Introduce `x y hxy`. Establish `hi : Function.Injective (Algebra.TensorProduct.includeRight (R` using `R) (A := R') (B := S)) := Algebra.TensorProduct.includeRight_injective hg`. Apply `hi` to reduce the goal to its premises. Establish `h1` using `congrArg (fun φ => φ.hom x) he`.

Establish `h2` using `congrArg (fun φ => φ.hom y) he`. Simplify using `only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h1 h2`. Express the relevant statement in the definitionally equal form `_ = Algebra.TensorProduct.includeRight.toRingHom x at h1`. Express the relevant statement in the definitionally equal form `_ = Algebra.TensorProduct.includeRight.toRingHom y at h2`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1 h2`.

Rewrite using `[← h1, ← h2, hxy]`.
-/
theorem pushout_inl_injective {R S R' P : CommRingCat.{0}} {f : R ⟶ S} {g : R ⟶ R'}
    {inl : S ⟶ P} {inr : R' ⟶ P} (h : IsPushout f g inl inr) (hf : f.hom.Flat)
    (hg : Function.Injective g.hom) : Function.Injective inl.hom := by
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  haveI : Module.Flat R S := hf
  have ht := CommRingCat.isPushout_tensorProduct R R' S
  let e := IsPushout.isoIsPushout _ _ h.flip ht
  have he : inl ≫ e.hom = CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom :=
    IsPushout.inr_isoIsPushout_hom _ _ h.flip ht
  intro x y hxy
  have hi : Function.Injective (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := S)) :=
    Algebra.TensorProduct.includeRight_injective hg
  apply hi
  have h1 := congrArg (fun φ => φ.hom x) he
  have h2 := congrArg (fun φ => φ.hom y) he
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h1 h2
  change _ = Algebra.TensorProduct.includeRight.toRingHom x at h1
  change _ = Algebra.TensorProduct.includeRight.toRingHom y at h2
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1 h2
  rw [← h1, ← h2, hxy]

/- English proof (translation)
Use `haveI : IsAffine ZK := .of_isPullback H`. Establish `hP` using `isPushout_appTop_of_isPullback H`. Establish `hf : π.appTop.hom.Flat` using `(HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp inferInstance`. Establish `hinj` using `pushout_inl_injective hP hf hj`. Rewrite using `[Scheme.ker_of_isAffine, (RingHom.injective_iff_ker_eq_bot _).mp hinj]`.

Apply the tactic sequence `first | exact map_bot (Scheme.IdealSheafData.equivOfIsAffine (X := Z)).symm | simp`.
-/
theorem ker_eq_bot_of_isPullback {Z ZK Y Y' : Scheme.{0}} [IsAffine Z] [IsAffine Y] [IsAffine Y']
    {p : ZK ⟶ Z} {q : ZK ⟶ Y'} {π : Z ⟶ Y} {j : Y' ⟶ Y} (H : IsPullback p q π j) [Flat π]
    (hj : Function.Injective j.appTop.hom) : p.ker = ⊥ := by
  haveI : IsAffine ZK := .of_isPullback H
  have hP := isPushout_appTop_of_isPullback H
  have hf : π.appTop.hom.Flat := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp inferInstance
  have hinj := pushout_inl_injective hP hf hj
  rw [Scheme.ker_of_isAffine, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
  first | exact map_bot (Scheme.IdealSheafData.equivOfIsAffine (X := Z)).symm | simp

/- English proof (translation)
Introduce `x y hxy`. Establish `e` using `Scheme.ΓSpecIso_naturality f`. Establish `h1` using `congrArg (fun φ => φ.hom x) e`. Establish `h2` using `congrArg (fun φ => φ.hom y) e`. Simplify using `only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1 h2`.

Rewrite `h1` using `[hxy]`. Use `hf (h1.symm.trans h2)` as an intermediate fact. Conclude with `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1 this`.
-/
theorem appTop_spec_injective {R S : CommRingCat.{0}} (f : R ⟶ S) (hf : Function.Injective f.hom) :
    Function.Injective (Spec.map f).appTop.hom := by
  intro x y hxy
  have e := Scheme.ΓSpecIso_naturality f
  have h1 := congrArg (fun φ => φ.hom x) e
  have h2 := congrArg (fun φ => φ.hom y) e
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1 h2
  rw [hxy] at h1
  have := hf (h1.symm.trans h2)
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1 this

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

/- English proof (translation)
Use `set a := Spec.map (CommRingCat.ofHom (algebraMap V K))`. Take `⟨-, h2, -⟩` from `hI`. Use `haveI : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι`. Establish `H : IsPullback (pullback.snd (bc A B g a) I.subschemeι) (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g)) (I.subschemeι ≫ pullback.snd _ g) a` using `(IsPullback.of_hasPullback (bc A B g a) I.subschemeι).flip.paste_vert (isPullback_bc A B g a)`. Establish `hk : (pullback.snd (bc A B g a) I.subschemeι).ker = ⊥` using `ker_eq_bot_of_isPullback H (appTop_spec_injective _ (IsFractionRing.injective V K))`.

Rewrite using `[Scheme.IdealSheafData.comap, Scheme.IdealSheafData.map_ker, pullback.condition, Scheme.Hom.ker_comp, hk, Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]`.
-/
theorem map_comap_bc_eq (r : ℕ) {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] (g : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (hI : Good A B r g I) :
    (I.comap (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K))))).map
      (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K)))) = I := by
  set a := Spec.map (CommRingCat.ofHom (algebraMap V K))
  obtain ⟨-, h2, -⟩ := hI
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have H : IsPullback (pullback.snd (bc A B g a) I.subschemeι)
      (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g))
      (I.subschemeι ≫ pullback.snd _ g) a :=
    (IsPullback.of_hasPullback (bc A B g a) I.subschemeι).flip.paste_vert (isPullback_bc A B g a)
  have hk : (pullback.snd (bc A B g a) I.subschemeι).ker = ⊥ :=
    ker_eq_bot_of_isPullback H (appTop_spec_injective _ (IsFractionRing.injective V K))
  rw [Scheme.IdealSheafData.comap, Scheme.IdealSheafData.map_ker, pullback.condition,
    Scheme.Hom.ker_comp, hk, Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]

/- English proof (translation)
Rewrite using `[← map_comap_bc_eq A B r (K := K) g I hI, ← map_comap_bc_eq A B r (K := K) g I' hI', h]`.
-/
theorem eq_of_comap_bc_eq (r : ℕ) {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] (g : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of A))
    (I I' : (pullback (str A B) g).IdealSheafData) (hI : Good A B r g I) (hI' : Good A B r g I')
    (h : I.comap (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K)))) =
      I'.comap (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K))))) : I = I' := by
  rw [← map_comap_bc_eq A B r (K := K) g I hI, ← map_comap_bc_eq A B r (K := K) g I' hI', h]

end GlobalTheory.HilbAff

namespace GlobalTheory.HilbAff

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

/- English proof (translation)
Rewrite `h2` using `[functor_map, functor_map]`. Establish `h3` using `(Sigma.ext_iff.mp h2).2`. Take `⟨g, I, hI⟩` from `x`. Take `⟨g', I', hI'⟩` from `x'`. Simplify using `only at h1 h3`.

Substitute `h1` using the available equality. Establish `h4` using `congrArg Subtype.val (eq_of_heq h3)`. Use `eq_of_comap_bc_eq A B r (K := K) g I I' hI hI' h4` as an intermediate fact. Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
theorem eq_of_map_eq (r : ℕ) {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] (x x' : (functor A B r).obj (op (Spec (CommRingCat.of V))))
    (h1 : x.1 = x'.1)
    (h2 : (functor A B r).map (Spec.map (CommRingCat.ofHom (algebraMap V K))).op x =
      (functor A B r).map (Spec.map (CommRingCat.ofHom (algebraMap V K))).op x') : x = x' := by
  rw [functor_map, functor_map] at h2
  have h3 := (Sigma.ext_iff.mp h2).2
  obtain ⟨g, I, hI⟩ := x
  obtain ⟨g', I', hI'⟩ := x'
  dsimp only at h1 h3
  subst h1
  have h4 := congrArg Subtype.val (eq_of_heq h3)
  have := eq_of_comap_bc_eq A B r (K := K) g I I' hI hI' h4
  subst this
  rfl

/- English proof (translation)
Introduce `A B _ _ _ _ _ r H Rep S`. Use `⟨fun l₁ l₂ => CommSq.LiftStruct.ext ?_⟩` and prove the remaining obligations. Apply `Rep.homEquiv.injective` to reduce the goal to its premises. Establish `e : ∀ l : Spec (CommRingCat.of S.R) ⟶ H, Rep.homEquiv l = (functor A B r).map l.op (Rep.homEquiv (𝟙 H))` using `fun l => by`. Rewrite using `[← Rep.homEquiv_comp, Category.comp_id]`.

Apply `eq_of_map_eq A B r (K := S.K)` to reduce the goal to its premises. Rewrite using `[e l₁.l, e l₂.l, functor_map, functor_map] dsimp only`. Rewrite using `[l₁.fac_right, l₂.fac_right]`. Rewrite using `[← Rep.homEquiv_comp, ← Rep.homEquiv_comp, l₁.fac_left, l₂.fac_left]`.
-/
theorem valuativeCriterion_uniqueness : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0})
    (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H),
    ValuativeCriterion.Uniqueness (R.homEquiv (𝟙 H)).1 := by
  intro A B _ _ _ _ _ r H Rep S
  refine ⟨fun l₁ l₂ => CommSq.LiftStruct.ext ?_⟩
  apply Rep.homEquiv.injective
  have e : ∀ l : Spec (CommRingCat.of S.R) ⟶ H,
      Rep.homEquiv l = (functor A B r).map l.op (Rep.homEquiv (𝟙 H)) := fun l => by
    rw [← Rep.homEquiv_comp, Category.comp_id]
  apply eq_of_map_eq A B r (K := S.K)
  · rw [e l₁.l, e l₂.l, functor_map, functor_map]
    dsimp only
    rw [l₁.fac_right, l₂.fac_right]
  · rw [← Rep.homEquiv_comp, ← Rep.homEquiv_comp, l₁.fac_left, l₂.fac_left]

end GlobalTheory.HilbAff
