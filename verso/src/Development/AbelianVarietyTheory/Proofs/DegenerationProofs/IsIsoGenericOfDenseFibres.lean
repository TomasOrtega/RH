import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowSmulKerEqZeroOfDense
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

open TensorProduct

namespace GlobalTheory

namespace GenericIso

/- English proof (translation)
Rewrite using `[← H.isoPullback_hom_snd, isIso_comp_left_iff]`.
-/
theorem isIso_iff_of_isPullback {P X' Y X : Scheme.{0}} {a : P ⟶ X'} {b : P ⟶ Y} {h : X' ⟶ X}
    {g : Y ⟶ X} (H : IsPullback a b h g) : IsIso b ↔ IsIso (pullback.snd h g) := by
  rw [← H.isoPullback_hom_snd, isIso_comp_left_iff]

/- English proof (translation)
Use `(IsPullback.of_hasPullback (pullback.snd h g) k).paste_horiz (IsPullback.of_hasPullback h g)` as an intermediate fact. Conclude with `(isIso_iff_of_isPullback this).1 inferInstance`.
-/
theorem isIso_snd_comp {X' Y X Z : Scheme.{0}} (h : X' ⟶ X) (g : Y ⟶ X) (k : Z ⟶ Y)
    (H : IsIso (pullback.snd h g)) : IsIso (pullback.snd h (k ≫ g)) := by
  have := (IsPullback.of_hasPullback (pullback.snd h g) k).paste_horiz
    (IsPullback.of_hasPullback h g)
  exact (isIso_iff_of_isPullback this).1 inferInstance

/- English proof (translation)
Use `IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback X.hom t)` and prove the remaining obligations. Establish `e : ((Over.pullback t).map h).left ≫ pullback.snd X.hom t = pullback.snd X'.hom t` using `pullback.lift_snd _ _ _`. Rewrite using `[e, Over.w h]`. Conclude with `IsPullback.of_hasPullback X'.hom t`. Conclude with `(pullback.lift_fst _ _ _).symm`.
-/
theorem isPullback_over {S T : Scheme.{0}} (t : T ⟶ S) {X' X : Over S} (h : X' ⟶ X) :
    IsPullback (pullback.fst X'.hom t) ((Over.pullback t).map h).left h.left
      (pullback.fst X.hom t) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback X.hom t)
  · have e : ((Over.pullback t).map h).left ≫ pullback.snd X.hom t = pullback.snd X'.hom t :=
      pullback.lift_snd _ _ _
    rw [e, Over.w h]
    exact IsPullback.of_hasPullback X'.hom t
  · exact (pullback.lift_fst _ _ _).symm

/- English proof (translation)
Rewrite using `[← isIso_iff_of_isPullback (isPullback_over t h)]`. Conclude with `(isIso_iff_of_reflects_iso _ (Over.forget T)).symm`.
-/
theorem isIso_over_iff {S T : Scheme.{0}} (t : T ⟶ S) {X' X : Over S} (h : X' ⟶ X) :
    IsIso ((Over.pullback t).map h) ↔ IsIso (pullback.snd h.left (pullback.fst X.hom t)) := by
  rw [← isIso_iff_of_isPullback (isPullback_over t h)]
  exact (isIso_iff_of_reflects_iso _ (Over.forget T)).symm

section Affine

variable {R A₀ A : Type} [CommRing R] [CommRing A₀] [CommRing A] [Algebra R A₀] [Algebra R A]
  (f : A₀ →ₐ[R] A) (B : Type) [CommRing B] [Algebra R B]

/- English proof (translation)
The claim follows from `(isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R B A)).flip`.
-/
theorem isPullback_tensor (A : Type) [CommRing A] [Algebra R A] :
    IsPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R B A)).flip

/- English proof (translation)
Use `IsPullback.of_bot ?_ ?_ (isPullback_tensor B A₀)` and prove the remaining obligations. Use `isPullback_tensor (R := R) B A using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Use extensionality with `b`.

Simplify using the standard rewrite rules. Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Use extensionality with `b`. Simplify using the standard rewrite rules.

Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`.
-/
theorem isPullback_tensor_map :
    IsPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R B) f).toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A₀)).toRingHom)) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_tensor B A₀)
  · convert isPullback_tensor (R := R) B A using 1
    · rw [← Spec.map_comp]
      congr 1
      ext b
      simp
    · rw [← Spec.map_comp]
      congr 1
      ext b
      simp
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1

/- English proof (translation)
Rewrite using `[isIso_SpecMap_iff]`. Both sides reduce to the same expression.
-/
theorem isIso_spec_iff {C D : Type} [CommRing C] [CommRing D] (φ : C →+* D) :
    IsIso (Spec.map (CommRingCat.ofHom φ)) ↔ Function.Bijective φ := by
  rw [isIso_SpecMap_iff]
  rfl

/- English proof (translation)
Establish `e : LinearMap.lTensor C (f.toLinearMap.baseChange B) = ((AlgebraTensorModule.cancelBaseChange R B B C A).symm.toLinearMap ∘ₗ AlgebraTensorModule.lTensor B C f.toLinearMap) ∘ₗ (AlgebraTensorModule.cancelBaseChange R B B C A₀).toLinearMap`. Use `ext`. Simplify using the standard rewrite rules. Establish `h1 : Function.Bijective (LinearMap.lTensor C (f.toLinearMap.baseChange B))`. Rewrite using `[e]`.

Conclude with `((AlgebraTensorModule.cancelBaseChange R B B C A).symm.bijective.comp H).comp (AlgebraTensorModule.cancelBaseChange R B B C A₀).bijective`. Conclude with `(Module.FaithfullyFlat.lTensor_bijective_iff_bijective B C _).1 h1`.
-/
theorem bijective_of_faithfullyFlat (C : Type) [CommRing C] [Algebra R C] [Algebra B C]
    [IsScalarTower R B C] [Module.FaithfullyFlat B C]
    (H : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R C) f)) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R B) f) := by
  have e : LinearMap.lTensor C (f.toLinearMap.baseChange B) =
      ((AlgebraTensorModule.cancelBaseChange R B B C A).symm.toLinearMap ∘ₗ
        AlgebraTensorModule.lTensor B C f.toLinearMap) ∘ₗ
        (AlgebraTensorModule.cancelBaseChange R B B C A₀).toLinearMap := by
    ext
    simp
  have h1 : Function.Bijective (LinearMap.lTensor C (f.toLinearMap.baseChange B)) := by
    rw [e]
    exact ((AlgebraTensorModule.cancelBaseChange R B B C A).symm.bijective.comp H).comp
      (AlgebraTensorModule.cancelBaseChange R B B C A₀).bijective
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective B C _).1 h1

/- English proof (translation)
Establish `h1 : x.asIdeal ≤ RingHom.ker (algebraMap R K)` using `hx.le`. Establish `h2 : x.asIdeal.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap R K)` using `fun r hr => by`. Express the relevant statement in the definitionally equal form `IsUnit (algebraMap R K r)`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`.

Conclude with `hr (hx.ge h0)`. Set `: Algebra x.asIdeal.ResidueField K` to `(Ideal.ResidueField.lift x.asIdeal (algebraMap R K) h1 h2).toAlgebra`. Establish `: IsScalarTower R x.asIdeal.ResidueField K` using `.of_algebraMap_eq fun r => (Ideal.ResidueField.lift_algebraMap _ _ h1 h2 r).symm`. Conclude with `bijective_of_faithfullyFlat f _ K H`.
-/
theorem bijective_residueField (K : Type) [Field K] [Algebra R K] (x : PrimeSpectrum R)
    (hx : x.asIdeal = RingHom.ker (algebraMap R K))
    (H : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R K) f)) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R x.asIdeal.ResidueField) f) := by
  have h1 : x.asIdeal ≤ RingHom.ker (algebraMap R K) := hx.le
  have h2 : x.asIdeal.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap R K) := fun r hr => by
    change IsUnit (algebraMap R K r)
    rw [isUnit_iff_ne_zero]
    intro h0
    exact hr (hx.ge h0)
  let : Algebra x.asIdeal.ResidueField K :=
    (Ideal.ResidueField.lift x.asIdeal (algebraMap R K) h1 h2).toAlgebra
  have : IsScalarTower R x.asIdeal.ResidueField K :=
    .of_algebraMap_eq fun r => (Ideal.ResidueField.lift_algebraMap _ _ h1 h2 r).symm
  exact bijective_of_faithfullyFlat f _ K H

end Affine

end GenericIso

open GenericIso

/- English proof (translation)
Introduce `R _ _ _ X' X _ _ _ h _ Sg hD H`. Rewrite using `[isIso_over_iff]`. Use `IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms _) (X.left.affineCover.pullback₁ (pullback.fst X.hom (Out.jK R))) fun (i : X.left.affineCover.I₀) => ?_` and prove the remaining obligations. Take `⟨A₀, u, hu₀, ⟨e, he⟩⟩ : ∃ (A₀ : CommRingCat.{0}) (u : Spec A₀ ⟶ X.left) (_ : IsOpenImmersion u), ∃ e : X.left.affineCover.X i ⟶ Spec A₀, e ≫ u = X.left.affineCover.f i` from `⟨_, (X.left.affineCover.X i).isoSpec.inv ≫ X.left.affineCover.f i, inferInstance, (X.left.affineCover.X i).isoSpec.hom, by simp⟩`. Establish `: IsAffine (pullback h.left u)` using `isAffine_of_isAffineHom (pullback.snd h.left u)`.

Choose the witnesses or unpack the hypotheses as in `⟨A, j, hj, f, sq⟩ : ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ X'.left) (_ : IsOpenImmersion j) (f : A₀ ⟶ A), IsPullback j (Spec.map f) h.left u := by`. Take `⟨f, hf⟩` from `Spec.map_surjective ((pullback h.left u).isoSpec.inv ≫ pullback.snd h.left u)`. Use `⟨_, (pullback h.left u).isoSpec.inv ≫ pullback.fst h.left u, inferInstance, f, ?_⟩` and prove the remaining obligations. Rewrite using `[hf]`. Conclude with `IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ (pullback h.left u).isoSpec.symm rfl rfl`.

Take `⟨φ, hφ⟩` from `Spec.map_surjective (u ≫ X.hom)`. Set `: Algebra R A₀` to `φ.hom.toAlgebra`. Set `: Algebra R A` to `(φ ≫ f).hom.toAlgebra`. Set `F : A₀ →ₐ[R] A` to `⟨f.hom, fun _ => rfl⟩`. Establish `: Algebra.FiniteType R A₀`.

Establish `: LocallyOfFiniteType (Spec.map φ)` using `by rw [hφ]; infer_instance`. Conclude with `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this`. Establish `: Algebra.FiniteType R A`. Establish `: LocallyOfFiniteType (Spec.map (φ ≫ f))`. Rewrite using `[Spec.map_comp, hφ, ← Category.assoc, ← sq.w, Category.assoc, Over.w h]`.

Use `infer_instance`. Conclude with `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this`. Establish `hφ' : Spec.map (CommRingCat.ofHom (algebraMap R A₀)) = u ≫ X.hom` using `hφ`. Establish `key : ∀ (B : Type) [CommRing B] [Algebra R B], Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R B) F) ↔ IsIso (pullback.snd h.left (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R` using `R) (A := B) (B := A₀)).toRingHom) ≫ u)) := by`. Introduce `B _ _`.

Rewrite using `[← isIso_iff_of_isPullback ((isPullback_tensor_map F B).paste_horiz sq), isIso_spec_iff]`. Both sides reduce to the same expression. Establish `hfib : ∀ x : PrimeSpectrum R, x ∈ (Sg : Set (PrimeSpectrum R)) → Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R x.asIdeal.ResidueField) F)`. Introduce `x hx`. Take `⟨K, _, t, ht, hiso⟩` from `H x hx`.

Take `⟨ψ, rfl⟩` from `Spec.map_surjective t`. Set `: Algebra R K` to `ψ.hom.toAlgebra`. Use `bijective_residueField F K x ?_ ((key K).2 ?_)` and prove the remaining obligations. Establish `: Spec.map ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = x` using `ht.le (Set.mem_range_self _)`. Rewrite using `[← this]`.

Both sides reduce to the same expression. Establish `w` using `(isPullback_tensor (R := R) K A₀).w`. Rewrite `w` using `[hφ', ← Category.assoc]`. Use `isIso_snd_comp _ _ (pullback.lift _ _ w) ((isIso_over_iff _ h).1 hiso)` as an intermediate fact. Rewrite `this` using `[pullback.lift_fst]`. Then use the resulting hypothesis.

Take `⟨a, ha0, ha⟩` from `exists_baseChange_injective_of_dense.{0} F hD fun x hx => (hfib x hx).1`. Take `⟨b, hb0, hb⟩` from `exists_baseChange_surjective_of_dense.{0} F hD fun x hx => (hfib x hx).2`. Establish `hu : ∀ c : R, c ≠ 0 → IsUnit (algebraMap R (FractionRing R) c)` using `fun c hc => IsLocalization.map_units (M := nonZeroDivisors R) _ ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩`. Establish `hK` using `(key (FractionRing R)).1 ⟨ha _ (hu a ha0), hb _ (hu b hb0)⟩`. Set `q` to `pullback.fst X.hom (Out.jK R)`.

Establish `w : (pullback.snd q (X.left.affineCover.f i) ≫ e) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A₀)) = (pullback.fst q (X.left.affineCover.f i) ≫ pullback.snd X.hom (Out.jK R)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))`. Rewrite using `[hφ', Category.assoc, reassoc_of% he, ← pullback.condition_assoc, Category.assoc, pullback.condition]`. Establish `h3` using `isIso_snd_comp _ _ ((isPullback_tensor (R := R) (FractionRing R) A₀).lift _ _ w) hK`. Rewrite `h3` using `[IsPullback.lift_fst_assoc, Category.assoc, he, ← pullback.condition]`. Establish `sq2` using `(IsPullback.of_hasPullback (pullback.snd h.left q) (pullback.fst q (X.left.affineCover.f i))).paste_horiz (IsPullback.of_hasPullback h.left q)`.

Conclude with `(isIso_iff_of_isPullback sq2).2 h3`.
-/
theorem isIso_generic_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X' X : Over (Sp R))
      [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      (h : X' ⟶ X) [IsAffineHom h.left] (Sg : Set (Sp R)), Dense Sg →
      (∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
        IsIso ((Over.pullback t).map h)) → IsIso ((Over.pullback (Out.jK R)).map h) := by
  intro R _ _ _ X' X _ _ _ h _ Sg hD H
  rw [isIso_over_iff]
  refine IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms _)
    (X.left.affineCover.pullback₁ (pullback.fst X.hom (Out.jK R))) fun (i : X.left.affineCover.I₀) => ?_

  obtain ⟨A₀, u, hu₀, ⟨e, he⟩⟩ : ∃ (A₀ : CommRingCat.{0}) (u : Spec A₀ ⟶ X.left)
      (_ : IsOpenImmersion u), ∃ e : X.left.affineCover.X i ⟶ Spec A₀,
      e ≫ u = X.left.affineCover.f i :=
    ⟨_, (X.left.affineCover.X i).isoSpec.inv ≫ X.left.affineCover.f i, inferInstance,
      (X.left.affineCover.X i).isoSpec.hom, by simp⟩
  have : IsAffine (pullback h.left u) := isAffine_of_isAffineHom (pullback.snd h.left u)
  obtain ⟨A, j, hj, f, sq⟩ : ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ X'.left)
      (_ : IsOpenImmersion j) (f : A₀ ⟶ A), IsPullback j (Spec.map f) h.left u := by
    obtain ⟨f, hf⟩ := Spec.map_surjective
      ((pullback h.left u).isoSpec.inv ≫ pullback.snd h.left u)
    refine ⟨_, (pullback h.left u).isoSpec.inv ≫ pullback.fst h.left u, inferInstance, f, ?_⟩
    rw [hf]
    exact IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩
      (pullback h.left u).isoSpec.symm rfl rfl
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (u ≫ X.hom)
  let : Algebra R A₀ := φ.hom.toAlgebra
  let : Algebra R A := (φ ≫ f).hom.toAlgebra
  let F : A₀ →ₐ[R] A := ⟨f.hom, fun _ => rfl⟩
  have : Algebra.FiniteType R A₀ := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have : Algebra.FiniteType R A := by
    have : LocallyOfFiniteType (Spec.map (φ ≫ f)) := by
      rw [Spec.map_comp, hφ, ← Category.assoc, ← sq.w, Category.assoc, Over.w h]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap R A₀)) = u ≫ X.hom := hφ
  have key : ∀ (B : Type) [CommRing B] [Algebra R B],
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R B) F) ↔
      IsIso (pullback.snd h.left (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A₀)).toRingHom) ≫ u)) := by
    intro B _ _
    rw [← isIso_iff_of_isPullback ((isPullback_tensor_map F B).paste_horiz sq), isIso_spec_iff]
    rfl
  have hfib : ∀ x : PrimeSpectrum R, x ∈ (Sg : Set (PrimeSpectrum R)) → Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id R x.asIdeal.ResidueField) F) := by
    intro x hx
    obtain ⟨K, _, t, ht, hiso⟩ := H x hx
    obtain ⟨ψ, rfl⟩ := Spec.map_surjective t
    let : Algebra R K := ψ.hom.toAlgebra
    refine bijective_residueField F K x ?_ ((key K).2 ?_)
    · have : Spec.map ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = x :=
        ht.le (Set.mem_range_self _)
      rw [← this]
      rfl
    · have w := (isPullback_tensor (R := R) K A₀).w
      rw [hφ', ← Category.assoc] at w
      have := isIso_snd_comp _ _ (pullback.lift _ _ w) ((isIso_over_iff _ h).1 hiso)
      rwa [pullback.lift_fst] at this
  obtain ⟨a, ha0, ha⟩ := exists_baseChange_injective_of_dense.{0} F hD fun x hx => (hfib x hx).1
  obtain ⟨b, hb0, hb⟩ := exists_baseChange_surjective_of_dense.{0} F hD fun x hx => (hfib x hx).2
  have hu : ∀ c : R, c ≠ 0 → IsUnit (algebraMap R (FractionRing R) c) := fun c hc =>
    IsLocalization.map_units (M := nonZeroDivisors R) _ ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩
  have hK := (key (FractionRing R)).1 ⟨ha _ (hu a ha0), hb _ (hu b hb0)⟩
  let q := pullback.fst X.hom (Out.jK R)
  have w : (pullback.snd q (X.left.affineCover.f i) ≫ e) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A₀)) =
      (pullback.fst q (X.left.affineCover.f i) ≫ pullback.snd X.hom (Out.jK R)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
    rw [hφ', Category.assoc, reassoc_of% he, ← pullback.condition_assoc, Category.assoc,
      pullback.condition]
  have h3 := isIso_snd_comp _ _ ((isPullback_tensor (R := R) (FractionRing R) A₀).lift _ _ w) hK
  rw [IsPullback.lift_fst_assoc, Category.assoc, he, ← pullback.condition] at h3
  have sq2 := (IsPullback.of_hasPullback (pullback.snd h.left q)
    (pullback.fst q (X.left.affineCover.f i))).paste_horiz (IsPullback.of_hasPullback h.left q)
  exact (isIso_iff_of_isPullback sq2).2 h3

end GlobalTheory
