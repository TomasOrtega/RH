import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasChartsOfForallIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open GlobalTheory.CompanionTheory.Ar.GR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.KerFF

variable {R : Type} [CommRing R]

/- English proof (translation)
Use `haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)`. Establish `f₁ : IsFinite (Spec.map φ)` using `by rw [hφ]; infer_instance`. Establish `f₂ : Flat (Spec.map φ)` using `by rw [hφ]; infer_instance`. Establish `f₃ : LocallyOfFinitePresentation (Spec.map φ)` using `by rw [hφ]; infer_instance`.

Rewrite `f₁` using `[IsFinite.SpecMap_iff]`. Rewrite `f₂` using `[Flat.SpecMap_iff]`. Rewrite `f₃` using `[LocallyOfFinitePresentation.SpecMap_iff]`. Use `letI : Algebra R Γ(X.left, ⊤) := φ.hom.toAlgebra`. Use `haveI : Module.Finite R Γ(X.left, ⊤) := RingHom.finite_algebraMap.1 f₁`.

Use `haveI : Module.Flat R Γ(X.left, ⊤) := RingHom.flat_algebraMap_iff.1 f₂`. Use `haveI : Algebra.FinitePresentation R Γ(X.left, ⊤) := RingHom.finitePresentation_algebraMap.1 f₃`. Use `haveI : Module.FinitePresentation R Γ(X.left, ⊤) := Module.FinitePresentation.of_finite_of_finitePresentation _ _`. Use `⟨Γ(X.left, ⊤), inferInstance, inferInstance, ⟨Over.isoMk X.left.isoSpec.symm ?_⟩, inferInstance, Module.Flat.projective_of_finitePresentation⟩` and prove the remaining obligations. Conclude with `hφ.symm`.
-/
theorem exists_sp_iso (X : Over (Sp R)) [IsFinite X.hom] [Flat X.hom] [LocallyOfFinitePresentation X.hom] :
    ∃ (F : Type) (_ : CommRing F) (_ : Algebra R F) (_ : Nonempty (sp (R₀ := R) F ≅ X)),
      Module.Finite R F ∧ Module.Projective R F := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  have f₁ : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have f₂ : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have f₃ : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at f₁
  rw [Flat.SpecMap_iff] at f₂
  rw [LocallyOfFinitePresentation.SpecMap_iff] at f₃
  letI : Algebra R Γ(X.left, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite R Γ(X.left, ⊤) := RingHom.finite_algebraMap.1 f₁
  haveI : Module.Flat R Γ(X.left, ⊤) := RingHom.flat_algebraMap_iff.1 f₂
  haveI : Algebra.FinitePresentation R Γ(X.left, ⊤) := RingHom.finitePresentation_algebraMap.1 f₃
  haveI : Module.FinitePresentation R Γ(X.left, ⊤) := Module.FinitePresentation.of_finite_of_finitePresentation _ _
  refine ⟨Γ(X.left, ⊤), inferInstance, inferInstance,
    ⟨Over.isoMk X.left.isoSpec.symm ?_⟩, inferInstance, Module.Flat.projective_of_finitePresentation⟩
  exact hφ.symm

/- English proof (translation)
Rewrite using `[Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]`.
-/
theorem mul_comp_hom {A B T : Over (Sp R)} [GrpObj A] [GrpObj B] (u v : T ⟶ A) (l : A ⟶ B) [IsMonHom l] :
    (u * v) ≫ l = (u ≫ l) * (v ≫ l) := by
  rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

/- English proof (translation)
Rewrite using `[Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]`.
-/
theorem one_comp_hom {A B T : Over (Sp R)} [GrpObj A] [GrpObj B] (l : A ⟶ B) [IsMonHom l] :
    (1 : T ⟶ A) ≫ l = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

/- English proof (translation)
Introduce `R _ A B _ _ l hA hB hl hfin hflat`. Use `haveI := hA.smooth`. Use `haveI := hB.smooth`. Use `haveI : IsFinite l.left := hfin`. Use `haveI : Flat l.left := hflat`.

Use `haveI : IsMonHom l := hl`. Establish `hw : l.left ≫ B.hom = A.hom` using `Over.w l`. Use `haveI : LocallyOfFinitePresentation (l.left ≫ B.hom) := by rw [hw]; infer_instance`. Use `haveI : LocallyOfFinitePresentation l.left := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp l.left B.hom`. Set `e : Sp R ⟶ B.left` to `(η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left`.

Establish `he : e ≫ B.hom = 𝟙 _` using `Over.w (η[B] : 𝟙_ (Over (Sp R)) ⟶ B)`. Use `haveI : Mono e := mono_of_mono_fac he`. Set `X : Over (Sp R)` to `Over.mk (pullback.snd l.left e)`. Use `haveI : IsFinite X.hom := inferInstanceAs (IsFinite (pullback.snd l.left e))`. Use `haveI : Flat X.hom := inferInstanceAs (Flat (pullback.snd l.left e))`.

Use `haveI : LocallyOfFinitePresentation X.hom := inferInstanceAs (LocallyOfFinitePresentation (pullback.snd l.left e))`. Establish `hf : pullback.fst l.left e ≫ A.hom = X.hom`. Rewrite using `[← hw, pullback.condition_assoc, he, Category.comp_id]`. Both sides reduce to the same expression. Set `f : X ⟶ A` to `Over.homMk (pullback.fst l.left e) hf`.

Establish `key : ∀ (T : Over (Sp R)) (z : T ⟶ A), z ≫ l = 1 ↔ ∃ t : T ⟶ X, t ≫ f = z`. Introduce `T z`. Establish `one_left : (1 : T ⟶ B).left = T.hom ≫ e`. Rewrite using `[Hom.one_def, Over.comp_left, Over.toUnit_left]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h' : z.left ≫ l.left = T.hom ≫ e`. Rewrite using `[← one_left, ← h, Over.comp_left]`. Use `⟨Over.homMk (pullback.lift z.left T.hom h') (pullback.lift_snd _ _ _), ?_⟩` and prove the remaining obligations. Conclude with `Over.OverMorphism.ext (pullback.lift_fst _ _ _)`.

Introduce and unpack `⟨t, rfl⟩`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[one_left, ← Over.w t]`. Express the relevant statement in the definitionally equal form `(t.left ≫ pullback.fst l.left e) ≫ l.left = (t.left ≫ pullback.snd l.left e) ≫ e`. Rewrite using `[Category.assoc, Category.assoc, pullback.condition]`.

Establish `fmono : ∀ {T : Over (Sp R)} (t t' : T ⟶ X), t ≫ f = t' ≫ f → t = t'`. Introduce `T t t' h`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← cancel_mono (pullback.fst l.left e)]`. Conclude with `congrArg (fun u => u.left) h`.

Take `⟨F, iF, aF, ⟨ee⟩, hfinF, hproj⟩` from `exists_sp_iso X`. Establish `ker : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀` using `R) S ⟶ A), z ≫ l = 1 ↔ ∃ φ : F →ₐ[R] S, spMap φ ≫ (ee.hom ≫ f) = z := by`. Introduce `S _ _ z`. Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨t, rfl⟩`. Take `⟨φ, hφ⟩` from `GlobalTheory.NatFun.spMap_surjective (k := R) (A := F) (B := S) (t ≫ ee.inv)`. Conclude with `⟨φ, by rw [hφ]; simp⟩`. Introduce and unpack `⟨φ, rfl⟩`. Conclude with `⟨spMap φ ≫ ee.hom, by simp⟩`.

Use `⟨F, iF, aF, ee.hom ≫ f, ⟨hproj, hfinF, ?_, ?_, ?_, ?_⟩, ker⟩` and prove the remaining obligations. Introduce `S _ _ φ φ' h`. Apply `GlobalTheory.NatFun.spMap_injective (k := R) (A := F) (B := S)` to reduce the goal to its premises. Establish `h₁ : (spMap φ ≫ ee.hom) ≫ f = (spMap φ' ≫ ee.hom) ≫ f` using `by simpa using h`. Conclude with `(cancel_mono ee.hom).1 (fmono _ _ h₁)`.

Introduce `S _ _`. Conclude with `(ker S 1).1 (one_comp_hom l)`. Introduce `S _ _ φ φ'`. Conclude with `(ker S _).1 (by`. Rewrite using `[mul_comp_hom, (ker S _).2 ⟨φ, rfl⟩, (ker S _).2 ⟨φ', rfl⟩, _root_.mul_one])`.

Introduce `S _ _ φ`. Establish `hz` using `(ker S _).2 ⟨φ, rfl⟩`. Establish `h₂ : (spMap φ ≫ ee.hom ≫ f)⁻¹ ≫ l = 1`. Establish `h₃` using `mul_comp_hom (spMap φ ≫ ee.hom ≫ f)⁻¹ (spMap φ ≫ ee.hom ≫ f) l`. Rewrite `h₃` using `[inv_mul_cancel, one_comp_hom, hz, _root_.mul_one]`.

Conclude with `h₃.symm`. Take `⟨χ, hχ⟩` from `(ker S _).1 h₂`. Conclude with `⟨χ, by rw [hχ, inv_mul_cancel]⟩`.
-/
theorem kernelFinFlat : PositivityTheory.Tls2.Zar3.Ch1.KernelFinFlat := by
  intro R _ A B _ _ l hA hB hl hfin hflat
  haveI := hA.smooth
  haveI := hB.smooth
  haveI : IsFinite l.left := hfin
  haveI : Flat l.left := hflat
  haveI : IsMonHom l := hl
  have hw : l.left ≫ B.hom = A.hom := Over.w l
  haveI : LocallyOfFinitePresentation (l.left ≫ B.hom) := by rw [hw]; infer_instance
  haveI : LocallyOfFinitePresentation l.left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp l.left B.hom
  let e : Sp R ⟶ B.left := (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left
  have he : e ≫ B.hom = 𝟙 _ := Over.w (η[B] : 𝟙_ (Over (Sp R)) ⟶ B)
  haveI : Mono e := mono_of_mono_fac he
  let X : Over (Sp R) := Over.mk (pullback.snd l.left e)
  haveI : IsFinite X.hom := inferInstanceAs (IsFinite (pullback.snd l.left e))
  haveI : Flat X.hom := inferInstanceAs (Flat (pullback.snd l.left e))
  haveI : LocallyOfFinitePresentation X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd l.left e))
  have hf : pullback.fst l.left e ≫ A.hom = X.hom := by
    rw [← hw, pullback.condition_assoc, he, Category.comp_id]
    rfl
  let f : X ⟶ A := Over.homMk (pullback.fst l.left e) hf
  have key : ∀ (T : Over (Sp R)) (z : T ⟶ A), z ≫ l = 1 ↔ ∃ t : T ⟶ X, t ≫ f = z := by
    intro T z
    have one_left : (1 : T ⟶ B).left = T.hom ≫ e := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    constructor
    · intro h
      have h' : z.left ≫ l.left = T.hom ≫ e := by
        rw [← one_left, ← h, Over.comp_left]
      refine ⟨Over.homMk (pullback.lift z.left T.hom h') (pullback.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    · rintro ⟨t, rfl⟩
      apply Over.OverMorphism.ext
      rw [one_left, ← Over.w t]
      change (t.left ≫ pullback.fst l.left e) ≫ l.left = (t.left ≫ pullback.snd l.left e) ≫ e
      rw [Category.assoc, Category.assoc, pullback.condition]
  have fmono : ∀ {T : Over (Sp R)} (t t' : T ⟶ X), t ≫ f = t' ≫ f → t = t' := by
    intro T t t' h
    apply Over.OverMorphism.ext
    rw [← cancel_mono (pullback.fst l.left e)]
    exact congrArg (fun u => u.left) h
  obtain ⟨F, iF, aF, ⟨ee⟩, hfinF, hproj⟩ := exists_sp_iso X
  have ker : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A),
      z ≫ l = 1 ↔ ∃ φ : F →ₐ[R] S, spMap φ ≫ (ee.hom ≫ f) = z := by
    intro S _ _ z
    rw [key]
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨φ, hφ⟩ := GlobalTheory.NatFun.spMap_surjective (k := R) (A := F) (B := S) (t ≫ ee.inv)
      exact ⟨φ, by rw [hφ]; simp⟩
    · rintro ⟨φ, rfl⟩
      exact ⟨spMap φ ≫ ee.hom, by simp⟩
  refine ⟨F, iF, aF, ee.hom ≫ f, ⟨hproj, hfinF, ?_, ?_, ?_, ?_⟩, ker⟩
  · intro S _ _ φ φ' h
    apply GlobalTheory.NatFun.spMap_injective (k := R) (A := F) (B := S)
    have h₁ : (spMap φ ≫ ee.hom) ≫ f = (spMap φ' ≫ ee.hom) ≫ f := by simpa using h
    exact (cancel_mono ee.hom).1 (fmono _ _ h₁)
  · intro S _ _
    exact (ker S 1).1 (one_comp_hom l)
  · intro S _ _ φ φ'
    exact (ker S _).1 (by
      rw [mul_comp_hom, (ker S _).2 ⟨φ, rfl⟩, (ker S _).2 ⟨φ', rfl⟩, _root_.mul_one])
  · intro S _ _ φ
    have hz := (ker S _).2 ⟨φ, rfl⟩
    have h₂ : (spMap φ ≫ ee.hom ≫ f)⁻¹ ≫ l = 1 := by
      have h₃ := mul_comp_hom (spMap φ ≫ ee.hom ≫ f)⁻¹ (spMap φ ≫ ee.hom ≫ f) l
      rw [inv_mul_cancel, one_comp_hom, hz, _root_.mul_one] at h₃
      exact h₃.symm
    obtain ⟨χ, hχ⟩ := (ker S _).1 h₂
    exact ⟨χ, by rw [hχ, inv_mul_cancel]⟩

end GlobalTheory.CompanionTheory.Ar.KerFF
