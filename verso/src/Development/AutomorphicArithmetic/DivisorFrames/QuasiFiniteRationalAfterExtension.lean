import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

/- English proof (translation)
Use `letI : ∀ m, Algebra K (A m) := fun m => (f m).toAlgebra`. Use `haveI hfin : ∀ m, Module.Finite K (A m) := hf`. Use `choose s hs using fun m => (hfin m).fg_top`. Set `p : Polynomial K` to `∏ m, ∏ a ∈ s m, minpoly K a`. Establish `hp : p ≠ 0` using `Finset.prod_ne_zero_iff.2 fun m _ => Finset.prod_ne_zero_iff.2 fun a _ => minpoly.ne_zero (Algebra.IsIntegral.isIntegral a)`.

Use `⟨p.SplittingField, inferInstance, inferInstance, inferInstance, fun m Ω _ β φ h => ?_⟩` and prove the remaining obligations. Establish `hgen : ∀ a ∈ s m, φ a ∈ β.range`. Introduce `a ha`. Establish `hdvd : minpoly K a ∣ p` using `(Finset.dvd_prod_of_mem _ ha).trans (Finset.dvd_prod_of_mem (fun m => ∏ a ∈ s m, minpoly K a) (Finset.mem_univ m))`. Establish `hsp : ((minpoly K a).map (algebraMap K p.SplittingField)).Splits` using `(Polynomial.SplittingField.splits p).of_dvd (Polynomial.map_ne_zero hp) (Polynomial.map_dvd _ hdvd)`.

Establish `hne : minpoly K a ≠ 0` using `minpoly.ne_zero (Algebra.IsIntegral.isIntegral a)`. Use `hsp.mem_range_of_isRoot (by simpa using hne) ?_` and prove the remaining obligations. Rewrite using `[Polynomial.IsRoot, Polynomial.map_map, ← h, Polynomial.eval_map, ← Polynomial.hom_eval₂]`. Use `minpoly.aeval K a` as an intermediate fact. Rewrite `this` using `[Polynomial.aeval_def]`.

Conclude with `(congrArg φ this).trans (map_zero φ)`. Establish `hall : ∀ a, φ a ∈ β.range`. Introduce `a`. Establish `ha : a ∈ Submodule.span K (s m : Set (A m))` using `(hs m).symm ▸ Submodule.mem_top`. Proceed by induction on `ha using Submodule.span_induction with`.

Consider the case `mem a ha => exact hgen a ha`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha`.

Rewrite using `[Algebra.smul_def, map_mul]`. Conclude with `mul_mem ⟨algebraMap K _ c, (RingHom.congr_fun h c).symm⟩ ha`. Set `e` to `RingEquiv.ofBijective β.rangeRestrict ⟨fun a b hab => β.injective (congrArg Subtype.val hab), β.rangeRestrict_surjective⟩`. Establish `he : β.comp (e.symm.toRingHom.comp (φ.codRestrict β.range hall)) = φ` using `RingHom.ext fun a => congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict β.range hall a))`. Use `⟨_, RingHom.ext fun c => β.injective ?_, he⟩` and prove the remaining obligations.

Conclude with `(RingHom.congr_fun he (f m c)).trans (RingHom.congr_fun h c)`.
-/
private theorem alg_rat (K : Type) [Field K] (n : ℕ) (A : Fin n → Type) [∀ m, CommRing (A m)]
    (f : ∀ m, K →+* A m) (hf : ∀ m, (f m).Finite) :
    ∃ (K₁ : Type) (_ : Field K₁) (_ : Algebra K K₁), FiniteDimensional K K₁ ∧
      ∀ m (Ω : Type) [Field Ω] (β : K₁ →+* Ω) (φ : A m →+* Ω), φ.comp (f m) = β.comp (algebraMap K K₁) →
        ∃ ψ : A m →+* K₁, ψ.comp (f m) = algebraMap K K₁ ∧ β.comp ψ = φ := by
  classical
  letI : ∀ m, Algebra K (A m) := fun m => (f m).toAlgebra
  haveI hfin : ∀ m, Module.Finite K (A m) := hf
  choose s hs using fun m => (hfin m).fg_top
  let p : Polynomial K := ∏ m, ∏ a ∈ s m, minpoly K a
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun m _ => Finset.prod_ne_zero_iff.2 fun a _ =>
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral a)
  refine ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, fun m Ω _ β φ h => ?_⟩
  have hgen : ∀ a ∈ s m, φ a ∈ β.range := by
    intro a ha
    have hdvd : minpoly K a ∣ p :=
      (Finset.dvd_prod_of_mem _ ha).trans
        (Finset.dvd_prod_of_mem (fun m => ∏ a ∈ s m, minpoly K a) (Finset.mem_univ m))
    have hsp : ((minpoly K a).map (algebraMap K p.SplittingField)).Splits :=
      (Polynomial.SplittingField.splits p).of_dvd (Polynomial.map_ne_zero hp) (Polynomial.map_dvd _ hdvd)
    have hne : minpoly K a ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral a)
    refine hsp.mem_range_of_isRoot (by simpa using hne) ?_
    rw [Polynomial.IsRoot, Polynomial.map_map, ← h, Polynomial.eval_map, ← Polynomial.hom_eval₂]
    have := minpoly.aeval K a
    rw [Polynomial.aeval_def] at this
    exact (congrArg φ this).trans (map_zero φ)
  have hall : ∀ a, φ a ∈ β.range := by
    intro a
    have ha : a ∈ Submodule.span K (s m : Set (A m)) := (hs m).symm ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem a ha => exact hgen a ha
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [Algebra.smul_def, map_mul]
      exact mul_mem ⟨algebraMap K _ c, (RingHom.congr_fun h c).symm⟩ ha
  let e := RingEquiv.ofBijective β.rangeRestrict
    ⟨fun a b hab => β.injective (congrArg Subtype.val hab), β.rangeRestrict_surjective⟩
  have he : β.comp (e.symm.toRingHom.comp (φ.codRestrict β.range hall)) = φ :=
    RingHom.ext fun a => congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict β.range hall a))
  refine ⟨_, RingHom.ext fun c => β.injective ?_, he⟩
  exact (RingHom.congr_fun he (f m c)).trans (RingHom.congr_fun h c)

/- English proof (translation)
Take `⟨_, _, _, _⟩` from `hZ`. Establish `: IsFinite (pullback.snd Z.hom x)` using `IsFinite.of_locallyQuasiFinite _`. Establish `: IsAffine (pullback Z.hom x)` using `isAffine_of_isAffineHom (pullback.snd Z.hom x)`. Take `⟨f, hf⟩` from `Spec.map_surjective ((pullback Z.hom x).isoSpec.inv ≫ pullback.snd Z.hom x)`. Use `⟨_, f, (pullback Z.hom x).isoSpec.inv ≫ pullback.fst Z.hom x, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← IsFinite.SpecMap_iff, hf]`. Use `infer_instance`. Rewrite using `[hf]`. Conclude with `(IsPullback.of_hasPullback Z.hom x).of_iso (pullback Z.hom x).isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)`.
-/
private theorem fibre_spec {S : Scheme.{0}} (Z : Over S) (hZ : QFin Z) {K : Type} [Field K] (x : Sp K ⟶ S) :
    ∃ (A : CommRingCat.{0}) (f : CommRingCat.of K ⟶ A) (g : Spec A ⟶ Z.left),
      f.hom.Finite ∧ IsPullback g (Spec.map f) Z.hom x := by
  obtain ⟨_, _, _, _⟩ := hZ
  have : IsFinite (pullback.snd Z.hom x) := IsFinite.of_locallyQuasiFinite _
  have : IsAffine (pullback Z.hom x) := isAffine_of_isAffineHom (pullback.snd Z.hom x)
  obtain ⟨f, hf⟩ := Spec.map_surjective ((pullback Z.hom x).isoSpec.inv ≫ pullback.snd Z.hom x)
  refine ⟨_, f, (pullback Z.hom x).isoSpec.inv ≫ pullback.fst Z.hom x, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff, hf]; infer_instance
  · rw [hf]
    exact (IsPullback.of_hasPullback Z.hom x).of_iso (pullback Z.hom x).isoSpec (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

/- English proof (translation)
Introduce `S n Z hZ K _ x`. Use `choose A f g hf hP using fun m => fibre_spec (Z m) (hZ m) x`. Take `⟨K₁, _, _, hfd, H⟩` from `alg_rat K n (fun m => A m) (fun m => (f m).hom) hf`. Use `⟨K₁, _, _, hfd, fun m Ω _ β y hy => ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ⟩` from `Spec.map_surjective ((hP m).lift y (spMap β ≫ spMap (algebraMap K K₁)) (hy.trans (Category.assoc _ _ _).symm))`.

Establish `h₁ : Spec.map φ ≫ g m = y` using `by rw [hφ]; exact (hP m).lift_fst _ _ _`. Establish `h₂ : Spec.map φ ≫ Spec.map (f m) = spMap β ≫ spMap (algebraMap K K₁)`. Rewrite using `[hφ]`. Conclude with `(hP m).lift_snd _ _ _`. Establish `h₃ : f m ≫ φ = CommRingCat.ofHom (algebraMap K K₁) ≫ CommRingCat.ofHom β` using `Spec.map_injective (by rw [Spec.map_comp, Spec.map_comp]; exact h₂)`.

Take `⟨ψ, hψ₁, hψ₂⟩` from `H m Ω β φ.hom (congrArg CommRingCat.Hom.hom h₃)`. Use `⟨Spec.map (CommRingCat.ofHom ψ) ≫ g m, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, (hP m).w, ← Category.assoc, ← Spec.map_comp]`. Establish `: f m ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (algebraMap K K₁)` using `CommRingCat.hom_ext hψ₁`. Conclude with `congrArg (fun t => Spec.map t ≫ x) this`.

Rewrite using `[← h₁, ← Category.assoc]`. Establish `: CommRingCat.ofHom ψ ≫ CommRingCat.ofHom β = φ` using `CommRingCat.hom_ext hψ₂`. Rewrite using `[← this, Spec.map_comp]`.
-/
theorem UpperTheory.quasi_finite_rational_after_extension :
    ∀ (S : Scheme.{0}) (n : ℕ) (Z : Fin n → Over S), (∀ m, QFin (Z m)) → ∀ (K : Type) [Field K] (x : Sp K ⟶ S),
        ∃ (K₁ : Type) (_ : Field K₁) (_ : Algebra K K₁), FiniteDimensional K K₁ ∧
          ∀ m, RatOver (Z m) (spMap (algebraMap K K₁) ≫ x) := by
  intro S n Z hZ K _ x
  choose A f g hf hP using fun m => fibre_spec (Z m) (hZ m) x
  obtain ⟨K₁, _, _, hfd, H⟩ := alg_rat K n (fun m => A m) (fun m => (f m).hom) hf
  refine ⟨K₁, _, _, hfd, fun m Ω _ β y hy => ?_⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective
    ((hP m).lift y (spMap β ≫ spMap (algebraMap K K₁)) (hy.trans (Category.assoc _ _ _).symm))
  have h₁ : Spec.map φ ≫ g m = y := by rw [hφ]; exact (hP m).lift_fst _ _ _
  have h₂ : Spec.map φ ≫ Spec.map (f m) = spMap β ≫ spMap (algebraMap K K₁) := by
    rw [hφ]; exact (hP m).lift_snd _ _ _
  have h₃ : f m ≫ φ = CommRingCat.ofHom (algebraMap K K₁) ≫ CommRingCat.ofHom β :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_comp]; exact h₂)
  obtain ⟨ψ, hψ₁, hψ₂⟩ := H m Ω β φ.hom (congrArg CommRingCat.Hom.hom h₃)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ g m, ?_, ?_⟩
  · rw [Category.assoc, (hP m).w, ← Category.assoc, ← Spec.map_comp]
    have : f m ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (algebraMap K K₁) := CommRingCat.hom_ext hψ₁
    exact congrArg (fun t => Spec.map t ≫ x) this
  · rw [← h₁, ← Category.assoc]
    have : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom β = φ := CommRingCat.hom_ext hψ₂
    rw [← this, Spec.map_comp]
