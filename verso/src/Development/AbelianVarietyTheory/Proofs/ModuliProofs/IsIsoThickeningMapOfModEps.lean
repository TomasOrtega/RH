import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.ThickeningIso

/- English proof (translation)
Establish `hk : RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom = Ideal.span {DualNumber.eps}`. Use extensionality with `x`. Rewrite using `[Ideal.mem_span_singleton', RingHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Establish `hx' : x.fst = 0` using `hx`. Apply the tactic sequence `exact ⟨TrivSqZeroExt.inl x.snd, by ext <;> simp [hx']⟩`. Introduce and unpack `⟨y, rfl⟩`. Express the relevant statement in the definitionally equal form `(y * DualNumber.eps).fst = 0`. Simplify using the standard rewrite rules.

Establish `hB' : ∀ b, p (φ b) = 0 → ∃ b', b = b' * a DualNumber.eps` using `fun b hb => by`. Establish `: b ∈ RingHom.ker (p.comp φ)` using `hb`. Rewrite `this` using `[hB, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']`. Take `⟨b', h⟩` from `this`. Conclude with `⟨b', h.symm⟩`.

Establish `hC' : ∀ c, p c = 0 → ∃ c', c = c' * φ (a DualNumber.eps)` using `fun c hc => by`. Establish `: c ∈ RingHom.ker p` using `hc`. Rewrite `this` using `[hC, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']`. Take `⟨b', h⟩` from `this`. Conclude with `⟨b', h.symm⟩`.

Establish `he : a DualNumber.eps * a DualNumber.eps = 0`. Rewrite using `[← map_mul, DualNumber.eps_mul_eps, map_zero]`. Establish `hfl : ∀ c, c * φ (a DualNumber.eps) = 0 → p c = 0` using `fun c hc => by`. Set `_ : Algebra (DualNumber K) C` to `(φ.comp a).toAlgebra`. Establish `: Module.Flat (DualNumber K) C` using `hf`.

Take `⟨k, m, y, h1, h2⟩` from `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := DualNumber K) (M := C) (f := fun _ : Unit => DualNumber.eps) (x := fun _ => c) (by`. Rewrite using `[Fintype.sum_unique, Algebra.smul_def, _root_.mul_comm]`. Conclude with `hc)`. Rewrite using `[← RingHom.mem_ker, show c = _ from h1 (), hC]`. Use `Ideal.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def]`. Use `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)` and prove the remaining obligations. Establish `h3` using `congrArg TrivSqZeroExt.snd (h2 j)`. Express the relevant statement in the definitionally equal form `(m () j).fst = 0`. Simplify using `using h3`.

Establish `h1 : ∀ c, ∃ b c', c = φ b + c' * φ (a DualNumber.eps)` using `fun c => by`. Take `⟨b, hb⟩` from `hs (p c)`. Take `⟨c', h⟩` from `hC' (c - φ b) (by rw [map_sub, ← hb]; exact sub_self _)`. Conclude with `⟨b, c', by rw [← h]; ring⟩`. Use `⟨(injective_iff_map_eq_zero φ).2 fun b hb => ?_, fun c => ?_⟩` and prove the remaining obligations.

Take `⟨b', rfl⟩` from `hB' b (by rw [hb, map_zero])`. Take `⟨b'', rfl⟩` from `hB' b' (hfl _ (by rw [← map_mul, hb]))`. Rewrite using `[_root_.mul_assoc, he, mul_zero]`. Take `⟨b, c', rfl⟩` from `h1 c`. Take `⟨b', c'', rfl⟩` from `h1 c'`.

Use `⟨b + b' * a DualNumber.eps, ?_⟩` and prove the remaining obligations. Rewrite using `[add_mul, _root_.mul_assoc, ← map_mul φ (a _), he]`. Simplify using the standard rewrite rules.
-/
theorem bijective_of_mod_eps {K B C D : Type} [Field K] [CommRing B] [CommRing C] [CommRing D]
    (a : DualNumber K →+* B) (φ : B →+* C) (p : C →+* D) (hf : (φ.comp a).Flat)
    (hs : Function.Surjective (p.comp φ))
    (hB : RingHom.ker (p.comp φ) = (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).map a)
    (hC : RingHom.ker p = (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).map (φ.comp a)) :
    Function.Bijective φ := by
  have hk : RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom = Ideal.span {DualNumber.eps} := by
    ext x
    rw [Ideal.mem_span_singleton', RingHom.mem_ker]
    constructor
    · intro hx
      have hx' : x.fst = 0 := hx
      exact ⟨TrivSqZeroExt.inl x.snd, by ext <;> simp [hx']⟩
    · rintro ⟨y, rfl⟩
      change (y * DualNumber.eps).fst = 0
      simp
  have hB' : ∀ b, p (φ b) = 0 → ∃ b', b = b' * a DualNumber.eps := fun b hb => by
    have : b ∈ RingHom.ker (p.comp φ) := hb
    rw [hB, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at this
    obtain ⟨b', h⟩ := this
    exact ⟨b', h.symm⟩
  have hC' : ∀ c, p c = 0 → ∃ c', c = c' * φ (a DualNumber.eps) := fun c hc => by
    have : c ∈ RingHom.ker p := hc
    rw [hC, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at this
    obtain ⟨b', h⟩ := this
    exact ⟨b', h.symm⟩
  have he : a DualNumber.eps * a DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hfl : ∀ c, c * φ (a DualNumber.eps) = 0 → p c = 0 := fun c hc => by
    let _ : Algebra (DualNumber K) C := (φ.comp a).toAlgebra
    have : Module.Flat (DualNumber K) C := hf
    obtain ⟨k, m, y, h1, h2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (R := DualNumber K) (M := C) (f := fun _ : Unit => DualNumber.eps) (x := fun _ => c) (by
        rw [Fintype.sum_unique, Algebra.smul_def, _root_.mul_comm]; exact hc)
    rw [← RingHom.mem_ker, show c = _ from h1 (), hC]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have h3 := congrArg TrivSqZeroExt.snd (h2 j)
    change (m () j).fst = 0
    simpa using h3
  have h1 : ∀ c, ∃ b c', c = φ b + c' * φ (a DualNumber.eps) := fun c => by
    obtain ⟨b, hb⟩ := hs (p c)
    obtain ⟨c', h⟩ := hC' (c - φ b) (by rw [map_sub, ← hb]; exact sub_self _)
    exact ⟨b, c', by rw [← h]; ring⟩
  refine ⟨(injective_iff_map_eq_zero φ).2 fun b hb => ?_, fun c => ?_⟩
  · obtain ⟨b', rfl⟩ := hB' b (by rw [hb, map_zero])
    obtain ⟨b'', rfl⟩ := hB' b' (hfl _ (by rw [← map_mul, hb]))
    rw [_root_.mul_assoc, he, mul_zero]
  · obtain ⟨b, c', rfl⟩ := h1 c
    obtain ⟨b', c'', rfl⟩ := h1 c'
    refine ⟨b + b' * a DualNumber.eps, ?_⟩
    rw [add_mul, _root_.mul_assoc, ← map_mul φ (a _), he]
    simp

/- English proof (translation)
Establish `hpo` using `(isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) le_top le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) (isAffineOpen_top _))`. Establish `hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appTop) β i.appTop ((Scheme.ΓSpecIso C).inv ≫ f'.appTop)`. Use `hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Rewrite using `[← Scheme.ΓSpecIso_naturality]`.

Use `congr 1`. Simplify using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Simplify using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Conclude with `PrimeSection.ker_eq_map_of_isPushout hpo' hβ`.
-/
theorem ker_appTop {A C : CommRingCat.{0}} {β : A ⟶ C} (hβ : Function.Surjective β) {Y Z : Scheme.{0}}
    {f : Y ⟶ Spec A} {i : Z ⟶ Y} {f' : Z ⟶ Spec C} (h : IsPullback i f' f (Spec.map β)) [IsAffine Y] :
    RingHom.ker i.appTop.hom =
      (RingHom.ker β.hom).map ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) (isAffineOpen_top _))
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appTop) β i.appTop
      ((Scheme.ΓSpecIso C).inv ≫ f'.appTop) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    · rw [← Scheme.ΓSpecIso_naturality]
      congr 1
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact PrimeSection.ker_eq_map_of_isPushout hpo' hβ

/- English proof (translation)
Introduce `x` and use `⟨TrivSqZeroExt.inl x, rfl⟩`.
-/
theorem surjective_fst (K : Type) [Field K] :
    Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩

/- English proof (translation)
The claim follows from `(MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr (inferInstanceAs (IsIso (Spec.map f.appTop)))`.
-/
theorem isIso_of_isAffine_of_isIso_appTop {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [IsIso f.appTop] : IsIso f :=
  (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map f.appTop)))

/- English proof (translation)
Establish `hs` using `surjective_fst K`. Establish `h1 : IsClosedImmersion (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)` using `IsClosedImmersion.spec_of_surjective _ hs`. Establish `h2 : IsClosedImmersion (j ≫ e)` using `MorphismProperty.of_isPullback h'.flip h1`. Establish `hY : IsAffine Y` using `isAffine_of_isAffineHom (j ≫ e)`. Establish `hY' : IsAffine Y'`.

Use `AffineThickening.isAffine_of_isPullback_of_sq_eq_bot (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs ?_ h` and prove the remaining obligations. Rewrite using `[pow_two, eq_bot_iff, Ideal.mul_le]`. Introduce `x hx y hy`. Establish `hx' : x.fst = 0` using `hx`. Establish `hy' : y.fst = 0` using `hy`.

Apply the tactic sequence `have : (x * y : DualNumber K) = 0 := by ext <;> simp [hx', hy']`. Conclude with `this`. It suffices to establish `hh : IsIso e.appTop from isIso_of_isAffine_of_isIso_appTop e`. Rewrite using `[ConcreteCategory.isIso_iff_bijective]`. Establish `k` using `ker_appTop (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs h`.

Establish `k'` using `ker_appTop (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs h'`. Establish `hfl : ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ (e ≫ π').appTop).hom.Flat`. Rewrite using `[CommRingCat.hom_comp]`. Conclude with `RingHom.Flat.comp (.of_bijective (ConcreteCategory.bijective_of_isIso _)) ((HasRingHomProperty.iff_of_isAffine (P := @Flat)).1 hf)`. Establish `hsur : Function.Surjective (j ≫ e).appTop.hom` using `(IsClosedImmersion.isAffine_surjective_of_isAffine (j ≫ e)).2`.

Rewrite `k`, `k'`, `hfl`, `hsur` using `[Scheme.Hom.comp_appTop]`. Conclude with `bijective_of_mod_eps ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ π'.appTop).hom e.appTop.hom j.appTop.hom hfl hsur k' k`.
-/
theorem isIso_of_isAffine {K : Type} [Field K] {Y Y' Z' : Scheme.{0}} [IsAffine Z'] {q : Y ⟶ Sp K}
    {π' : Z' ⟶ Sp (DualNumber K)} {j : Y ⟶ Y'} {e : Y' ⟶ Z'}
    (h : IsPullback j q (e ≫ π') (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (h' : IsPullback (j ≫ e) q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (hf : Flat (e ≫ π')) : IsIso e := by
  have hs := surjective_fst K
  have h1 : IsClosedImmersion (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    IsClosedImmersion.spec_of_surjective _ hs
  have h2 : IsClosedImmersion (j ≫ e) := MorphismProperty.of_isPullback h'.flip h1
  have hY : IsAffine Y := isAffine_of_isAffineHom (j ≫ e)
  have hY' : IsAffine Y' := by
    refine AffineThickening.isAffine_of_isPullback_of_sq_eq_bot
      (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs ?_ h
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    have : (x * y : DualNumber K) = 0 := by ext <;> simp [hx', hy']
    exact this
  suffices hh : IsIso e.appTop from isIso_of_isAffine_of_isIso_appTop e
  rw [ConcreteCategory.isIso_iff_bijective]
  have k := ker_appTop (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs h
  have k' := ker_appTop (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs h'
  have hfl : ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ (e ≫ π').appTop).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (.of_bijective (ConcreteCategory.bijective_of_isIso _))
      ((HasRingHomProperty.iff_of_isAffine (P := @Flat)).1 hf)
  have hsur : Function.Surjective (j ≫ e).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (j ≫ e)).2
  rw [Scheme.Hom.comp_appTop] at k k' hfl hsur
  exact bijective_of_mod_eps
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ π'.appTop).hom e.appTop.hom j.appTop.hom
    hfl hsur k' k

/- English proof (translation)
Introduce and unpack `Y Y' Z' q _ π' j _ e h h' hf rfl rfl`. Use `(IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _ (iSup_affineOpens_eq_top Z')).mpr fun U => ?_` and prove the remaining obligations. Establish `: IsAffine U.1` using `U.2`. Establish `p1` using `(isPullback_morphismRestrict j (e ⁻¹ᵁ U.1))`. Establish `p2` using `(isPullback_morphismRestrict e U.1)`.

Establish `hw : e ∣_ U.1 ≫ U.1.ι ≫ π' = (e ⁻¹ᵁ U.1).ι ≫ e ≫ π'`. Rewrite using `[← Category.assoc, morphismRestrict_ι, Category.assoc]`. Use `isIso_of_isAffine (K := ℂ) (π' := U.1.ι ≫ π') (j := j ∣_ (e ⁻¹ᵁ U.1)) (q := (j ⁻¹ᵁ (e ⁻¹ᵁ U.1)).ι ≫ q) ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hw]`. Conclude with `p1.paste_vert h`.

Conclude with `(p1.paste_horiz p2).paste_vert h'`. Rewrite using `[hw]`. Use `infer_instance`.
-/
theorem isIso_of_mod_eps : ∀ (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (π' : Z' ⟶ Sp (DualNumber ℂ)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  rintro Y Y' Z' q _ π' j _ e h h' hf rfl rfl
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _
    (iSup_affineOpens_eq_top Z')).mpr fun U => ?_
  have : IsAffine U.1 := U.2
  have p1 := (isPullback_morphismRestrict j (e ⁻¹ᵁ U.1))
  have p2 := (isPullback_morphismRestrict e U.1)
  have hw : e ∣_ U.1 ≫ U.1.ι ≫ π' = (e ⁻¹ᵁ U.1).ι ≫ e ≫ π' := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  refine isIso_of_isAffine (K := ℂ) (π' := U.1.ι ≫ π') (j := j ∣_ (e ⁻¹ᵁ U.1))
    (q := (j ⁻¹ᵁ (e ⁻¹ᵁ U.1)).ι ≫ q) ?_ ?_ ?_
  · rw [hw]
    exact p1.paste_vert h
  · exact (p1.paste_horiz p2).paste_vert h'
  · rw [hw]; infer_instance

end GlobalTheory.ThickeningIso
