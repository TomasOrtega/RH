import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharValMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.TorusUniformizationCompare

section Alg

variable {k : Type} [Field k] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

/- English proof (translation)
Take `⟨ρ, hρ⟩` from `hex (AddMonoidAlgebra k X) (algebraMap k _) (AddMonoidAlgebra.of k X)`. Establish `key : ∀ (A : Type) [CommRing A] [Algebra k A] (θ : Multiplicative X →* A), P A (algebraMap k A) θ ((((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) : AddMonoidAlgebra k X →+* A) : AddMonoidAlgebra k X →* A).comp ρ)`. Introduce `A _ _ θ`. Establish `h` using `hnat _ A _ ((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) : AddMonoidAlgebra k X →+* A) _ _ hρ`. Establish `e1 : (((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) : AddMonoidAlgebra k X →+* A)).comp (algebraMap k _) = algebraMap k A` using `AlgHom.comp_algebraMap _`.

Establish `e2 : (((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) : AddMonoidAlgebra k X →+* A) : AddMonoidAlgebra k X →* A).comp (AddMonoidAlgebra.of k X) = θ`. Use `MonoidHom.ext fun y => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite `h` using `[e1, e2]`. Then use the resulting hypothesis. Establish `h2` using `hun k _ _ _ _ h1 (key k 1)`.

Establish `h3 : ∀ y : Y, ∃ a : X, (ρ (Multiplicative.ofAdd y) : AddMonoidAlgebra k X) = AddMonoidAlgebra.single a 1`. Introduce `y`. Take `⟨a, c, -, e⟩` from `Rosenlicht.isUnit_eq_single ((Group.isUnit (Multiplicative.ofAdd y)).map ρ)`. Establish `h4` using `congrArg (fun f : Multiplicative Y →* k => f (Multiplicative.ofAdd y)) h2`. Simplify using `[e] at h4`.

Conclude with `⟨a, by rw [e, ← h4]⟩`. Use `choose φ hφ using h3`. Establish `hadd : ∀ a b, φ (a + b) = φ a + φ b`. Introduce `a b`. Establish `h5` using `hφ (a + b)`.

Rewrite `h5` using `[ofAdd_add, map_mul, hφ, hφ, AddMonoidAlgebra.single_mul_single, _root_.mul_one]`. Assume the negation of the conclusion as `hne`. Use `congrArg (fun f => AddMonoidAlgebra.coeff f (φ (a + b))) h5` as an intermediate fact. Simplify using `[AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hne] at this`. Use `⟨AddMonoidHom.mk' φ hadd, fun A _ g θ => ?_⟩` and prove the remaining obligations.

Use `letI : Algebra k A := g.toAlgebra`. Establish `h` using `key A θ`. Establish `e : (((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) : AddMonoidAlgebra k X →+* A) : AddMonoidAlgebra k X →* A).comp ρ = θ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.mk' φ hadd))`. Use `MonoidHom.ext fun y => ?_` and prove the remaining obligations. Use `hφ y.toAdd` as an intermediate fact.

Rewrite `this` using `[ofAdd_toAdd]`. Simplify using `[this]`. Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem half [Module.Free ℤ X] [Module.Finite ℤ X]
    (P : ∀ (A : Type) [CommRing A], (k →+* A) → (Multiplicative X →* A) → (Multiplicative Y →* A) → Prop)
    (hex : ∀ (A : Type) [CommRing A] (g : k →+* A) θ, ∃ θ', P A g θ θ')
    (hun : ∀ (A : Type) [CommRing A] (g : k →+* A) θ θ' θ'', P A g θ θ' → P A g θ θ'' → θ' = θ'')
    (hnat : ∀ (A B : Type) [CommRing A] [CommRing B] (g : k →+* A) (h : A →+* B) θ θ', P A g θ θ' →
      P B (h.comp g) ((h : A →* B).comp θ) ((h : A →* B).comp θ'))
    (h1 : P k (RingHom.id k) 1 1) :
    ∃ φ : Y →+ X, ∀ (A : Type) [CommRing A] (g : k →+* A) θ,
      P A g θ (θ.comp (AddMonoidHom.toMultiplicative φ)) := by
  classical
  obtain ⟨ρ, hρ⟩ := hex (AddMonoidAlgebra k X) (algebraMap k _) (AddMonoidAlgebra.of k X)
  have key : ∀ (A : Type) [CommRing A] [Algebra k A] (θ : Multiplicative X →* A),
      P A (algebraMap k A) θ ((((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) :
        AddMonoidAlgebra k X →+* A) : AddMonoidAlgebra k X →* A).comp ρ) := by
    intro A _ _ θ
    have h := hnat _ A _ ((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) :
        AddMonoidAlgebra k X →+* A) _ _ hρ
    have e1 : (((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) :
        AddMonoidAlgebra k X →+* A)).comp (algebraMap k _) = algebraMap k A := AlgHom.comp_algebraMap _
    have e2 : (((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) :
        AddMonoidAlgebra k X →+* A) : AddMonoidAlgebra k X →* A).comp (AddMonoidAlgebra.of k X) = θ := by
      refine MonoidHom.ext fun y => ?_
      simp
    rwa [e1, e2] at h
  have h2 := hun k _ _ _ _ h1 (key k 1)
  have h3 : ∀ y : Y, ∃ a : X, (ρ (Multiplicative.ofAdd y) : AddMonoidAlgebra k X) = AddMonoidAlgebra.single a 1 := by
    intro y
    obtain ⟨a, c, -, e⟩ := Rosenlicht.isUnit_eq_single ((Group.isUnit (Multiplicative.ofAdd y)).map ρ)
    have h4 := congrArg (fun f : Multiplicative Y →* k => f (Multiplicative.ofAdd y)) h2
    simp [e] at h4
    exact ⟨a, by rw [e, ← h4]⟩
  choose φ hφ using h3
  have hadd : ∀ a b, φ (a + b) = φ a + φ b := by
    intro a b
    have h5 := hφ (a + b)
    rw [ofAdd_add, map_mul, hφ, hφ, AddMonoidAlgebra.single_mul_single, _root_.mul_one] at h5
    by_contra hne
    have := congrArg (fun f => AddMonoidAlgebra.coeff f (φ (a + b))) h5
    simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hne] at this
  refine ⟨AddMonoidHom.mk' φ hadd, fun A _ g θ => ?_⟩
  letI : Algebra k A := g.toAlgebra
  have h := key A θ
  have e : (((AddMonoidAlgebra.lift k A X θ : AddMonoidAlgebra k X →ₐ[k] A) :
        AddMonoidAlgebra k X →+* A) : AddMonoidAlgebra k X →* A).comp ρ =
      θ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.mk' φ hadd)) := by
    refine MonoidHom.ext fun y => ?_
    have := hφ y.toAdd
    rw [ofAdd_toAdd] at this
    simp [this]
  rw [e] at h
  exact h

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `congrArg (fun f => AddMonoidAlgebra.coeff f a) h` as an intermediate fact. Simplify using `[AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hne] at this`.
-/
theorem of_inj {a b : X} (h : AddMonoidAlgebra.of k X (Multiplicative.ofAdd a) =
    AddMonoidAlgebra.of k X (Multiplicative.ofAdd b)) : a = b := by
  classical
  by_contra hne
  have := congrArg (fun f => AddMonoidAlgebra.coeff f a) h
  simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hne] at this

/- English proof (translation)
Take `⟨φ, hφ⟩` from `half P hex hun hnat h1`. Take `⟨φ', hφ'⟩` from `half (fun A _ g θ' θ => P A g θ θ') hex' hun' (fun A B _ _ g h θ θ' H => hnat A B g h θ' θ H) h1`. Establish `a1 : ∀ a, φ (φ' a) = a`. Introduce `a`. Establish `h` using `hun' _ (algebraMap k _) _ _ _ (hφ' _ _ _) (hφ _ _ (AddMonoidAlgebra.of k X))`.

Conclude with `of_inj (k := k) (congrArg (fun f : Multiplicative X →* AddMonoidAlgebra k X => f (Multiplicative.ofAdd a)) h)`. Establish `a2 : ∀ a, φ' (φ a) = a`. Introduce `a`. Establish `h` using `hun _ (algebraMap k _) _ _ _ (hφ _ _ _) (hφ' _ _ (AddMonoidAlgebra.of k Y))`. Conclude with `of_inj (k := k) (congrArg (fun f : Multiplicative Y →* AddMonoidAlgebra k Y => f (Multiplicative.ofAdd a)) h)`.

Conclude with `⟨{ toFun := φ, invFun := φ', left_inv := a2, right_inv := a1, map_add' := φ.map_add }, hφ⟩`.
-/
theorem full [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : ∀ (A : Type) [CommRing A], (k →+* A) → (Multiplicative X →* A) → (Multiplicative Y →* A) → Prop)
    (hex : ∀ (A : Type) [CommRing A] (g : k →+* A) θ, ∃ θ', P A g θ θ')
    (hun : ∀ (A : Type) [CommRing A] (g : k →+* A) θ θ' θ'', P A g θ θ' → P A g θ θ'' → θ' = θ'')
    (hex' : ∀ (A : Type) [CommRing A] (g : k →+* A) θ', ∃ θ, P A g θ θ')
    (hun' : ∀ (A : Type) [CommRing A] (g : k →+* A) θ θ' θ'', P A g θ' θ → P A g θ'' θ → θ' = θ'')
    (hnat : ∀ (A B : Type) [CommRing A] [CommRing B] (g : k →+* A) (h : A →+* B) θ θ', P A g θ θ' →
      P B (h.comp g) ((h : A →* B).comp θ) ((h : A →* B).comp θ'))
    (h1 : P k (RingHom.id k) 1 1) :
    ∃ e : Y ≃+ X, ∀ (A : Type) [CommRing A] (g : k →+* A) θ,
      P A g θ (θ.comp (AddMonoidHom.toMultiplicative e.toAddMonoidHom)) := by
  obtain ⟨φ, hφ⟩ := half P hex hun hnat h1
  obtain ⟨φ', hφ'⟩ := half (fun A _ g θ' θ => P A g θ θ') hex' hun'
    (fun A B _ _ g h θ θ' H => hnat A B g h θ' θ H) h1
  have a1 : ∀ a, φ (φ' a) = a := by
    intro a
    have h := hun' _ (algebraMap k _) _ _ _ (hφ' _ _ _) (hφ _ _ (AddMonoidAlgebra.of k X))
    exact of_inj (k := k) (congrArg (fun f : Multiplicative X →* AddMonoidAlgebra k X =>
      f (Multiplicative.ofAdd a)) h)
  have a2 : ∀ a, φ' (φ a) = a := by
    intro a
    have h := hun _ (algebraMap k _) _ _ _ (hφ _ _ _) (hφ' _ _ (AddMonoidAlgebra.of k Y))
    exact of_inj (k := k) (congrArg (fun f : Multiplicative Y →* AddMonoidAlgebra k Y =>
      f (Multiplicative.ofAdd a)) h)
  exact ⟨{ toFun := φ, invFun := φ', left_inv := a2, right_inv := a1, map_add' := φ.map_add }, hφ⟩

end Alg

section Pts

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {A : Type} [CommRing A]

noncomputable def cv {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) : Multiplicative X →* A where
  toFun χ := charVal t χ.toAdd
  map_one' := ((GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.1 t).1
  map_mul' χ χ' := ((GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.1 t).2 _ _

/- English proof (translation)
The claim follows from `(GlobalTheory.T.charVal_multiplicative S X A a).1 t t' fun χ => congrArg (fun f : Multiplicative X →* A => f (Multiplicative.ofAdd χ)) h`.
-/
theorem cv_inj {a : Sp A ⟶ S} {t t' : Over.mk a ⟶ splitTorus S X} (h : cv t = cv t') : t = t' :=
  (GlobalTheory.T.charVal_multiplicative S X A a).1 t t' fun χ =>
    congrArg (fun f : Multiplicative X →* A => f (Multiplicative.ofAdd χ)) h

/- English proof (translation)
Take `⟨t, ht⟩` from `(GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.1 θ`. Conclude with `⟨t, MonoidHom.ext fun χ => ht χ.toAdd⟩`.
-/
theorem cv_surj (a : Sp A ⟶ S) (θ : Multiplicative X →* A) : ∃ t : Over.mk a ⟶ splitTorus S X, cv t = θ := by
  obtain ⟨t, ht⟩ := (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.1 θ
  exact ⟨t, MonoidHom.ext fun χ => ht χ.toAdd⟩

/- English proof (translation)
The claim follows from `MonoidHom.ext fun χ => (GlobalTheory.T.charVal_multiplicative S X A a).2.2.1 χ.toAdd`.
-/
theorem cv_one (a : Sp A ⟶ S) : cv (1 : Over.mk a ⟶ splitTorus S X) = 1 :=
  MonoidHom.ext fun χ => (GlobalTheory.T.charVal_multiplicative S X A a).2.2.1 χ.toAdd

/- English proof (translation)
Substitute `hb` using the available equality. Set `t' : Over.mk (spMap h ≫ a) ⟶ splitTorus S X` to `Over.homMk (spMap h ≫ t.left) (by rw [Category.assoc, Over.w t]; rfl)`. Conclude with `⟨t', rfl, MonoidHom.ext fun χ => (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.2 B h t t' rfl χ.toAdd⟩`.
-/
theorem cv_nat {a : Sp A ⟶ S} {B : Type} [CommRing B] (h : A →+* B) {b : Sp B ⟶ S} (hb : spMap h ≫ a = b)
    (t : Over.mk a ⟶ splitTorus S X) :
    ∃ t' : Over.mk b ⟶ splitTorus S X, t'.left = spMap h ≫ t.left ∧ cv t' = (h : A →* B).comp (cv t) := by
  subst hb
  let t' : Over.mk (spMap h ≫ a) ⟶ splitTorus S X :=
    Over.homMk (spMap h ≫ t.left) (by rw [Category.assoc, Over.w t]; rfl)
  exact ⟨t', rfl, MonoidHom.ext fun χ => (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.2 B h t t' rfl χ.toAdd⟩

end Pts

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (h : B →+* C) :
    spMap (h.comp g) = spMap h ≫ spMap g := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/- English proof (translation)
Use `letI := T.grpB`. Use `letI := T.addCommGroup`. Use `haveI := T.q_hom`. Use `haveI := T.i_hom`. Take `⟨e, he, -⟩` from `GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X`.

Establish `hq` using `GlobalTheory.SS.isPullback_overPullback_map_left f T.q`. Use `⟨{ X := T.X addCommGroup := T.addCommGroup free := T.free finite := T.finite B := (Over.pullback f).obj T.B grpB := inferInstance isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian q := (Over.pullback f).map T.q q_hom := inferInstance q_flat := MorphismPrope …` and prove the remaining obligations. Establish `hk` using `T.isKernel.map (Over.pullback f)`. Use `IsPullback.of_iso hk e.symm (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Conclude with `toUnit_unique _ _`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce `W p p₀ hp`. Establish `hB` using `isGrpPullback_pullback T.B f`.

Establish `e1 : LiePull.pts hB (T` using `W) rfl (p ≫ (Over.pullback f).map T.q) = p₀ ≫ T.q := by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(p.left ≫ ((Over.pullback f).map T.q).left) ≫ pullback.fst T.B.hom f = p₀.left ≫ T.q.left`. Rewrite using `[hp, Category.assoc, Category.assoc, hq.w]`. Express the relevant statement in the definitionally equal form `p ≫ (Over.pullback f).map T.q = 1 ↔ p₀ ≫ T.q = 1`.

Rewrite using `[← e1]`. Conclude with `(MulEquiv.map_eq_one_iff _).symm`.
-/
theorem exists_pullback_ext {k Ω : Type} [Field k] [Field Ω] (f : Sp Ω ⟶ Sp k)
    (G : Over (Sp k)) [GrpObj G] (T : TorusExtension G) :
    ∃ T' : TorusExtension ((Over.pullback f).obj G), ∀ (W : Over (Sp Ω)) (p : W ⟶ (Over.pullback f).obj G)
      (p₀ : Over.mk (W.hom ≫ f) ⟶ G), p₀.left = p.left ≫ pullback.fst G.hom f →
      ((letI := T'.grpB; p ≫ T'.q = 1) ↔ (letI := T.grpB; p₀ ≫ T.q = 1)) := by
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  obtain ⟨e, he, -⟩ := GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X
  have hq := GlobalTheory.SS.isPullback_overPullback_map_left f T.q
  refine ⟨{ X := T.X
            addCommGroup := T.addCommGroup
            free := T.free
            finite := T.finite
            B := (Over.pullback f).obj T.B
            grpB := inferInstance
            isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
            q := (Over.pullback f).map T.q
            q_hom := inferInstance
            q_flat := MorphismProperty.of_isPullback (P := @Flat) hq T.q_flat
            q_surjective := MorphismProperty.of_isPullback (P := @Surjective) hq T.q_surjective
            q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) hq T.q_quasiCompact
            i := e.hom ≫ (Over.pullback f).map T.i
            i_hom := inferInstance
            isKernel := ?_ }, ?_⟩
  · have hk := T.isKernel.map (Over.pullback f)
    refine IsPullback.of_iso hk e.symm (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp
    · exact toUnit_unique _ _
    · simp
    · simp
  · intro W p p₀ hp
    have hB := isGrpPullback_pullback T.B f
    have e1 : LiePull.pts hB (T := W) rfl (p ≫ (Over.pullback f).map T.q) = p₀ ≫ T.q := by
      apply Over.OverMorphism.ext
      change (p.left ≫ ((Over.pullback f).map T.q).left) ≫ pullback.fst T.B.hom f = p₀.left ≫ T.q.left
      rw [hp, Category.assoc, Category.assoc, hq.w]
    change p ≫ (Over.pullback f).map T.q = 1 ↔ p₀ ≫ T.q = 1
    rw [← e1]
    exact (MulEquiv.map_eq_one_iff _).symm

/- English proof (translation)
Use `letI := T.grpB`. Use `letI := T.addCommGroup`. Prove the components needed by the constructor for the conclusion. Introduce `hp`. Conclude with `⟨T.isKernel.lift p (toUnit _) hp, T.isKernel.lift_fst _ _ _⟩`.

Introduce and unpack `⟨t, rfl⟩`. Rewrite using `[Category.assoc, T.isKernel.w, ← Category.assoc, Hom.one_def]`. Use `congr 1`. Conclude with `toUnit_unique _ _`.
-/
theorem ker_iff {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] (T : TorusExtension G) {W : Over (Sp k)}
    (p : W ⟶ G) : (letI := T.grpB; p ≫ T.q = 1) ↔
      (letI := T.addCommGroup; ∃ t : W ⟶ splitTorus (Sp k) T.X, t ≫ T.i = p) := by
  letI := T.grpB
  letI := T.addCommGroup
  constructor
  · intro hp
    exact ⟨T.isKernel.lift p (toUnit _) hp, T.isKernel.lift_fst _ _ _⟩
  · rintro ⟨t, rfl⟩
    rw [Category.assoc, T.isKernel.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `h.hom_ext e ((Over.w p).trans (Over.w q).symm)`.
-/
theorem left_cancel {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsPullback φ G'.hom G.hom f) {W : Over S'} {p q : W ⟶ G'} (e : p.left ≫ φ = q.left ≫ φ) : p = q := by
  apply Over.OverMorphism.ext
  exact h.hom_ext e ((Over.w p).trans (Over.w q).symm)

end PositivityTheory.Xgn.TorusUniformizationCompare

open PositivityTheory.Xgn.TorusUniformizationCompare in
/- English proof (translation)
Introduce `X Z' G _ G' _ ρ Φ hΦ Xc _ _ _ u _ L k _ _ _ x zL hx GK _ φ hφ τ hinj hker`. Use `letI := τ.addCommGroup`. Use `letI := τ.grpB`. Use `haveI := τ.free`. Use `haveI := τ.finite`.

Use `haveI := τ.i_hom`. Establish `hm : Mono τ.i` using `⟨fun a b hab => τ.isKernel.hom_ext hab (toUnit_unique _ _)⟩`. Set `s : Sp k ⟶ Sp L` to `spMap (algebraMap L k)`. Establish `hπ` using `isGrpPullback_pullback GK s`. Set `ψ : ((Over.pullback s).obj GK).left ⟶ G'.left` to `hΦ.1.lift (pullback.fst GK.hom s ≫ φ) (((Over.pullback s).obj GK).hom ≫ x) (by`.

Rewrite using `[Category.assoc, hφ.1.w, ← Category.assoc, hπ.1.w, Category.assoc, Category.assoc, hx])`. Establish `hψ1 : ψ ≫ Φ = pullback.fst GK.hom s ≫ φ` using `hΦ.1.lift_fst _ _ _`. Establish `hψ2 : ψ ≫ G'.hom = ((Over.pullback s).obj GK).hom ≫ x` using `hΦ.1.lift_snd _ _ _`. Establish `hψ : IsGrpPullback ((Over.pullback s).obj GK) G' x ψ` using `hΦ.cancel ((hπ.comp hφ).congr hx.symm hψ1.symm) hψ2`. Take `⟨τ', hτ'⟩` from `exists_pullback_ext s GK τ`.

Establish `hk` using `hker _ ψ hψ τ'`. Set `P : ∀ (A : Type) [CommRing A], (k →+* A) → (Multiplicative Xc →* A) → (Multiplicative τ.X →* A) → Prop` to `fun A _ g θ θ' => ∃ (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc) (t' : Over.mk (spMap g ≫ s) ⟶ splitTorus (Sp L) τ.X), cv t = θ ∧ cv t' = θ' ∧ (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ`. Take `⟨e, he⟩` from `full (k := k) P (by`. Introduce `A _ g θ`. Take `⟨t, rfl⟩` from `cv_surj (spMap g ≫ x) θ`.

Set `p : Over.mk (spMap g) ⟶ (Over.pullback s).obj GK` to `LiePull.pull hψ (T := Over.mk (spMap g)) (g := spMap g ≫ x) rfl (t ≫ u)`. Establish `hp : p.left ≫ ψ = (t ≫ u).left` using `hψ.1.lift_fst _ _ _`. Establish `h1` using `(hk A g p).2 ⟨t, hp.symm⟩`. Set `p₀ : Over.mk (spMap g ≫ s) ⟶ GK` to `LiePull.push hπ (T := Over.mk (spMap g)) rfl p`. Establish `hp₀ : p₀.left = p.left ≫ pullback.fst GK.hom s` using `rfl`.

Take `⟨t', ht'⟩` from `(ker_iff τ p₀).1 ((hτ' _ p p₀ hp₀).1 h1)`. Use `⟨cv t', t, t', rfl, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[ht', hp₀, ← hp, Category.assoc, Category.assoc, hψ1])`. Use the proof step `(by`. Introduce and unpack `A _ g θ θ' θ'' ⟨t₁, t₁', h₁, rfl, e₁⟩ ⟨t₂, t₂', h₂, rfl, e₂⟩`.

Take `rfl : t₁ = t₂` from `cv_inj (h₁.trans h₂.symm)`. Use `left_cancel hφ.1 (e₁.symm.trans e₂)` as an intermediate fact. Rewrite using `[(cancel_mono τ.i).1 this])`. Use the proof step `(by`. Introduce `A _ g θ'`.

Take `⟨t', rfl⟩` from `cv_surj (spMap g ≫ s) θ'`. Set `p : Over.mk (spMap g) ⟶ (Over.pullback s).obj GK` to `LiePull.pull hπ (T := Over.mk (spMap g)) (g := spMap g ≫ s) rfl (t' ≫ τ.i)`. Establish `hp : p.left ≫ pullback.fst GK.hom s = (t' ≫ τ.i).left` using `hπ.1.lift_fst _ _ _`. Establish `h1` using `(hτ' _ p (t' ≫ τ.i) hp.symm).2 ((ker_iff τ _).2 ⟨t', rfl⟩)`. Take `⟨t, ht⟩` from `(hk A g p).1 h1`.

Use `⟨cv t, t, t', rfl, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[ht, ← hp, Category.assoc, Category.assoc, hψ1])`. Use the proof step `(by`. Introduce and unpack `A _ g θ θ' θ'' ⟨t₁, t₁', rfl, h₁, e₁⟩ ⟨t₂, t₂', rfl, h₂, e₂⟩`. Take `rfl : t₁' = t₂'` from `cv_inj (h₁.trans h₂.symm)`.

Establish `h3 : t₁ ≫ u = t₂ ≫ u` using `left_cancel hΦ.1 (e₁.trans e₂.symm)`. Establish `h4 : t₁ = t₂` using `(injective_iff_map_eq_one (IsMonHom.monoidHom u _)).2 (hinj A g) h3`. Rewrite using `[h4])`. Use the proof step `(by`. Introduce and unpack `A B _ _ g h θ θ' ⟨t, t', rfl, rfl, e⟩`.

Take `⟨r, hr, hr1⟩` from `cv_nat h (b := spMap (h.comp g) ≫ x) (by rw [spMap_comp', Category.assoc]) t`. Take `⟨r', hr', hr1'⟩` from `cv_nat h (b := spMap (h.comp g) ≫ s) (by rw [spMap_comp', Category.assoc]) t'`. Use `⟨r, r', hr1, hr1', ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(r.left ≫ u.left) ≫ Φ = (r'.left ≫ τ.i.left) ≫ φ`. Express the relevant statement in the definitionally equal form `(t.left ≫ u.left) ≫ Φ = (t'.left ≫ τ.i.left) ≫ φ at e`.

Rewrite using `[hr, hr']`. Simplify using `only [Category.assoc] at e ⊢`. Rewrite using `[e])`. Use the proof step `(by`. Use `⟨1, 1, cv_one _, cv_one _, ?_⟩` and prove the remaining obligations.

Rewrite using `[MonObj.one_comp, MonObj.one_comp, LiePull.one_left hΦ, LiePull.one_left hφ]`. Establish `: ∀ a b : Sp k ⟶ X, a = b → (1 : Over.mk a ⟶ G).left = (1 : Over.mk b ⟶ G).left`. Introduce and unpack `a b rfl`. Both sides reduce to the same expression. Conclude with `this _ _ (by rw [Category.assoc, Category.assoc, hx]))`.

Use `⟨e, ?_⟩` and prove the remaining obligations. Introduce `A _ g b hb b' hb' t t' h`. Rewrite `hb'` using `[spMap_comp']`. Substitute `hb hb'` using the available equality. Take `⟨r, r', hr, hr', H⟩` from `he A g (cv t)`.

Take `rfl : r = t` from `cv_inj hr`. Take `rfl : r' = t'` from `cv_inj (hr'.trans (MonoidHom.ext fun χ => (h χ.toAdd).symm))`. Conclude with `H`.
-/
theorem PositivityTheory.Xgn.torus_uniformization_compare : ∀ (X Z' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over Z') [GrpObj G'] (ρ : Z' ⟶ X)
    (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ → ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc]
    (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (L k : Type) [Field L] [Field k] [Algebra L k] (x : Sp k ⟶ Z') (zL : Sp L ⟶ X),
    x ≫ ρ = spMap (algebraMap L k) ≫ zL → ∀ (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left),
    IsGrpPullback GK G zL φ → ∀ τ : TorusExtension GK,
    (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc), t ≫ u = 1 → t = 1) →
    (∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ' : TorusExtension Gk,
      letI := τ'.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk),
        p ≫ τ'.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc, (t ≫ u).left = p.left ≫ ψ) →
    letI := τ.addCommGroup
    ∃ e : τ.X ≃+ Xc, ∀ (A : Type) [CommRing A] (g : k →+* A) (b : Sp A ⟶ Z') (_ : spMap g ≫ x = b) (b' : Sp A ⟶ Sp L)
      (_ : spMap (g.comp (algebraMap L k)) = b') (t : Over.mk b ⟶ splitTorus Z' Xc) (t' : Over.mk b' ⟶ splitTorus (Sp L) τ.X),
      (∀ χ, charVal t' χ = charVal t (e χ)) → (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ := by
  intro X Z' G _ G' _ ρ Φ hΦ Xc _ _ _ u _ L k _ _ _ x zL hx GK _ φ hφ τ hinj hker
  letI := τ.addCommGroup
  letI := τ.grpB
  haveI := τ.free
  haveI := τ.finite
  haveI := τ.i_hom
  have hm : Mono τ.i := ⟨fun a b hab => τ.isKernel.hom_ext hab (toUnit_unique _ _)⟩
  let s : Sp k ⟶ Sp L := spMap (algebraMap L k)
  have hπ := isGrpPullback_pullback GK s
  let ψ : ((Over.pullback s).obj GK).left ⟶ G'.left :=
    hΦ.1.lift (pullback.fst GK.hom s ≫ φ) (((Over.pullback s).obj GK).hom ≫ x) (by
      rw [Category.assoc, hφ.1.w, ← Category.assoc, hπ.1.w, Category.assoc, Category.assoc, hx])
  have hψ1 : ψ ≫ Φ = pullback.fst GK.hom s ≫ φ := hΦ.1.lift_fst _ _ _
  have hψ2 : ψ ≫ G'.hom = ((Over.pullback s).obj GK).hom ≫ x := hΦ.1.lift_snd _ _ _
  have hψ : IsGrpPullback ((Over.pullback s).obj GK) G' x ψ :=
    hΦ.cancel ((hπ.comp hφ).congr hx.symm hψ1.symm) hψ2
  obtain ⟨τ', hτ'⟩ := exists_pullback_ext s GK τ
  have hk := hker _ ψ hψ τ'
  let P : ∀ (A : Type) [CommRing A], (k →+* A) → (Multiplicative Xc →* A) → (Multiplicative τ.X →* A) → Prop :=
    fun A _ g θ θ' => ∃ (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc)
      (t' : Over.mk (spMap g ≫ s) ⟶ splitTorus (Sp L) τ.X), cv t = θ ∧ cv t' = θ' ∧
        (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ
  obtain ⟨e, he⟩ := full (k := k) P
    (by
      intro A _ g θ
      obtain ⟨t, rfl⟩ := cv_surj (spMap g ≫ x) θ
      let p : Over.mk (spMap g) ⟶ (Over.pullback s).obj GK :=
        LiePull.pull hψ (T := Over.mk (spMap g)) (g := spMap g ≫ x) rfl (t ≫ u)
      have hp : p.left ≫ ψ = (t ≫ u).left := hψ.1.lift_fst _ _ _
      have h1 := (hk A g p).2 ⟨t, hp.symm⟩
      let p₀ : Over.mk (spMap g ≫ s) ⟶ GK := LiePull.push hπ (T := Over.mk (spMap g)) rfl p
      have hp₀ : p₀.left = p.left ≫ pullback.fst GK.hom s := rfl
      obtain ⟨t', ht'⟩ := (ker_iff τ p₀).1 ((hτ' _ p p₀ hp₀).1 h1)
      refine ⟨cv t', t, t', rfl, rfl, ?_⟩
      rw [ht', hp₀, ← hp, Category.assoc, Category.assoc, hψ1])
    (by
      rintro A _ g θ θ' θ'' ⟨t₁, t₁', h₁, rfl, e₁⟩ ⟨t₂, t₂', h₂, rfl, e₂⟩
      obtain rfl : t₁ = t₂ := cv_inj (h₁.trans h₂.symm)
      have := left_cancel hφ.1 (e₁.symm.trans e₂)
      rw [(cancel_mono τ.i).1 this])
    (by
      intro A _ g θ'
      obtain ⟨t', rfl⟩ := cv_surj (spMap g ≫ s) θ'
      let p : Over.mk (spMap g) ⟶ (Over.pullback s).obj GK :=
        LiePull.pull hπ (T := Over.mk (spMap g)) (g := spMap g ≫ s) rfl (t' ≫ τ.i)
      have hp : p.left ≫ pullback.fst GK.hom s = (t' ≫ τ.i).left := hπ.1.lift_fst _ _ _
      have h1 := (hτ' _ p (t' ≫ τ.i) hp.symm).2 ((ker_iff τ _).2 ⟨t', rfl⟩)
      obtain ⟨t, ht⟩ := (hk A g p).1 h1
      refine ⟨cv t, t, t', rfl, rfl, ?_⟩
      rw [ht, ← hp, Category.assoc, Category.assoc, hψ1])
    (by
      rintro A _ g θ θ' θ'' ⟨t₁, t₁', rfl, h₁, e₁⟩ ⟨t₂, t₂', rfl, h₂, e₂⟩
      obtain rfl : t₁' = t₂' := cv_inj (h₁.trans h₂.symm)
      have h3 : t₁ ≫ u = t₂ ≫ u := left_cancel hΦ.1 (e₁.trans e₂.symm)
      have h4 : t₁ = t₂ := (injective_iff_map_eq_one (IsMonHom.monoidHom u _)).2 (hinj A g) h3
      rw [h4])
    (by
      rintro A B _ _ g h θ θ' ⟨t, t', rfl, rfl, e⟩
      obtain ⟨r, hr, hr1⟩ := cv_nat h (b := spMap (h.comp g) ≫ x) (by rw [spMap_comp', Category.assoc]) t
      obtain ⟨r', hr', hr1'⟩ := cv_nat h (b := spMap (h.comp g) ≫ s) (by rw [spMap_comp', Category.assoc]) t'
      refine ⟨r, r', hr1, hr1', ?_⟩
      change (r.left ≫ u.left) ≫ Φ = (r'.left ≫ τ.i.left) ≫ φ
      change (t.left ≫ u.left) ≫ Φ = (t'.left ≫ τ.i.left) ≫ φ at e
      rw [hr, hr']
      simp only [Category.assoc] at e ⊢
      rw [e])
    (by
      refine ⟨1, 1, cv_one _, cv_one _, ?_⟩
      rw [MonObj.one_comp, MonObj.one_comp, LiePull.one_left hΦ, LiePull.one_left hφ]
      have : ∀ a b : Sp k ⟶ X, a = b → (1 : Over.mk a ⟶ G).left = (1 : Over.mk b ⟶ G).left := by
        rintro a b rfl; rfl
      exact this _ _ (by rw [Category.assoc, Category.assoc, hx]))
  refine ⟨e, ?_⟩
  intro A _ g b hb b' hb' t t' h
  rw [spMap_comp'] at hb'
  subst hb hb'
  obtain ⟨r, r', hr, hr', H⟩ := he A g (cv t)
  obtain rfl : r = t := cv_inj hr
  obtain rfl : r' = t' := cv_inj (hr'.trans (MonoidHom.ext fun χ => (h χ.toAdd).symm))
  exact H
