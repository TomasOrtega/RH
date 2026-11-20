import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RingHomFlatCodescendsAlongFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFlatFibresDvr

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FiniteFibreFlat

open TensorProduct IsLocalRing

section Algebra

/- English proof (translation)
Set `I` to `p.map (algebraMap R A)`. Set `c : p →ₗ[R] I` to `{ toFun := fun r => ⟨algebraMap R A r, Ideal.mem_map_of_mem _ r.2⟩ map_add' := fun r s => Subtype.ext (by simp) map_smul' := fun r s => Subtype.ext (by simp [Algebra.smul_def]) }`. Set `φ : M ⊗[R] p →ₗ[R] M ⊗[A] I` to `TensorProduct.mapOfCompatibleSMul A R R M I ∘ₗ c.lTensor M`. Establish `hφ : ∀ m r, φ (m ⊗ₜ r) = m ⊗ₜ[A] c r` using `fun _ _ => rfl`. Establish `hsurj : ∀ x, x ∈ LinearMap.range φ`.

Introduce `x`. Proceed by induction on `x with`. Consider the case `zero => exact zero_mem _`. Consider the case `add a b ha hb => exact add_mem ha hb`. Consider the case `tmul m i`.

Take `⟨i, hi⟩` from `i`. Proceed by induction on `hi using Submodule.span_induction generalizing m with`. Consider the case `mem x hx`. Take `⟨r, hr, rfl⟩` from `hx`. Conclude with `⟨m ⊗ₜ ⟨r, hr⟩, rfl⟩`.

Consider the case `zero`. Express the relevant statement in the definitionally equal form `m ⊗ₜ[A] (0 : I) ∈ _`. Rewrite using `[tmul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y hx hy ihx ihy`.

Express the relevant statement in the definitionally equal form `m ⊗ₜ[A] ((⟨x, hx⟩ : I) + ⟨y, hy⟩) ∈ _`. Rewrite using `[tmul_add]`. Conclude with `add_mem (ihx m) (ihy m)`. Consider the case `smul a x hx ih`. Express the relevant statement in the definitionally equal form `m ⊗ₜ[A] (a • (⟨x, hx⟩ : I)) ∈ _`.

Rewrite using `[← smul_tmul]`. Conclude with `ih _`. Establish `hcomp : ∀ y, TensorProduct.rid A M (I.subtype.lTensor M (φ y)) = TensorProduct.rid R M (p.subtype.lTensor M y)`. Introduce `y`. Proceed by induction on `y with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul m r => simp [hφ, c]`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Take `⟨y, rfl⟩` from `hsurj x`. Establish `h0` using `hcomp y`. Rewrite `h0` using `[hx, map_zero, eq_comm, map_eq_zero_iff _ (TensorProduct.rid R M).injective, map_eq_zero_iff _ (Module.Flat.lTensor_preserves_injective_linearMap p.subtype p.injective_subtype)]`. Rewrite using `[h0, map_zero]`.
-/
theorem lTensor_map_injective {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    (p : Ideal R) :
    Function.Injective ((p.map (algebraMap R A)).subtype.lTensor M) := by
  let I := p.map (algebraMap R A)
  let c : p →ₗ[R] I :=
    { toFun := fun r => ⟨algebraMap R A r, Ideal.mem_map_of_mem _ r.2⟩
      map_add' := fun r s => Subtype.ext (by simp)
      map_smul' := fun r s => Subtype.ext (by simp [Algebra.smul_def]) }
  let φ : M ⊗[R] p →ₗ[R] M ⊗[A] I :=
    TensorProduct.mapOfCompatibleSMul A R R M I ∘ₗ c.lTensor M
  have hφ : ∀ m r, φ (m ⊗ₜ r) = m ⊗ₜ[A] c r := fun _ _ => rfl
  have hsurj : ∀ x, x ∈ LinearMap.range φ := by
    intro x
    induction x with
    | zero => exact zero_mem _
    | add a b ha hb => exact add_mem ha hb
    | tmul m i =>
      obtain ⟨i, hi⟩ := i
      induction hi using Submodule.span_induction generalizing m with
      | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := hx
        exact ⟨m ⊗ₜ ⟨r, hr⟩, rfl⟩
      | zero =>
        change m ⊗ₜ[A] (0 : I) ∈ _
        rw [tmul_zero]
        exact zero_mem _
      | add x y hx hy ihx ihy =>
        change m ⊗ₜ[A] ((⟨x, hx⟩ : I) + ⟨y, hy⟩) ∈ _
        rw [tmul_add]
        exact add_mem (ihx m) (ihy m)
      | smul a x hx ih =>
        change m ⊗ₜ[A] (a • (⟨x, hx⟩ : I)) ∈ _
        rw [← smul_tmul]
        exact ih _
  have hcomp : ∀ y, TensorProduct.rid A M (I.subtype.lTensor M (φ y)) =
      TensorProduct.rid R M (p.subtype.lTensor M y) := by
    intro y
    induction y with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul m r => simp [hφ, c]
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  have h0 := hcomp y
  rw [hx, map_zero, eq_comm, map_eq_zero_iff _ (TensorProduct.rid R M).injective,
    map_eq_zero_iff _ (Module.Flat.lTensor_preserves_injective_linearMap p.subtype
      p.injective_subtype)] at h0
  rw [h0, map_zero]

/- English proof (translation)
Use `set I := p.map (algebraMap R A) with hI`. Use `Module.finitePresentation_of_finite A M` as an intermediate fact. Establish `hrel : LocalFlat.RelationsLift I M` using `LocalFlat.relationsLift_of_flat (C := A ⧸ I) Ideal.Quotient.mk_surjective Ideal.mk_ker (TensorProduct.mk A (A ⧸ I) M 1) (TensorProduct.mk_surjective A M (A ⧸ I) Ideal.Quotient.mk_surjective) (LinearMap.ker_tensorProductMk M)`. Apply `Module.free_of_maximalIdeal_rTensor_injective` to reduce the goal to its premises. Rewrite using `[← LinearMap.lTensor_inj_iff_rTensor_inj, injective_iff_map_eq_zero]`.

Introduce `x hx`. Take `⟨y, rfl⟩` from `hrel (maximalIdeal A) (maximalIdeal A).subtype x (by rw [hx]; simp)`. Set `e` to `Submodule.comapSubtypeEquivOfLe hp`. Establish `hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0`. Rewrite using `[← hx, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]`.

Both sides reduce to the same expression. Rewrite `hy` using `[map_eq_zero_iff _ (lTensor_map_injective p)]`. Establish `: y = 0` using `(LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)`. Rewrite using `[this, map_zero]`.
-/
theorem free_of_flat_reduction {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    [Module.Finite A M] (p : Ideal R) (hp : p.map (algebraMap R A) ≤ maximalIdeal A)
    [Module.Flat (A ⧸ p.map (algebraMap R A)) ((A ⧸ p.map (algebraMap R A)) ⊗[A] M)] :
    Module.Free A M := by
  set I := p.map (algebraMap R A) with hI
  have := Module.finitePresentation_of_finite A M
  have hrel : LocalFlat.RelationsLift I M :=
    LocalFlat.relationsLift_of_flat (C := A ⧸ I) Ideal.Quotient.mk_surjective Ideal.mk_ker
      (TensorProduct.mk A (A ⧸ I) M 1) (TensorProduct.mk_surjective A M (A ⧸ I)
        Ideal.Quotient.mk_surjective) (LinearMap.ker_tensorProductMk M)
  apply Module.free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj, injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hrel (maximalIdeal A) (maximalIdeal A).subtype x (by rw [hx]; simp)
  let e := Submodule.comapSubtypeEquivOfLe hp
  have hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0 := by
    rw [← hx, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl
  rw [map_eq_zero_iff _ (lTensor_map_injective p)] at hy
  have : y = 0 := (LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)
  rw [this, map_zero]

/- English proof (translation)
Use `Module.flat_of_isLocalized_maximal A B (fun P _ => Localization.AtPrime P ⊗[A] B) (fun P _ => TensorProduct.mk A (Localization.AtPrime P) B 1) fun P _ => ?_` and prove the remaining obligations. Set `A'` to `Localization.AtPrime P`. Set `p : Ideal R` to `(maximalIdeal A').comap (algebraMap R A')`. Set `I` to `p.map (algebraMap R A')`. Establish `h1 : Module.Flat R (B ⊗[A] A')` using `Module.Flat.trans R B (B ⊗[A] A')`.

Establish `h2 : Module.Flat R (A' ⊗[A] B)` using `Module.Flat.of_linearEquiv ((Algebra.TensorProduct.comm A A' B).restrictScalars R).toLinearEquiv`. Establish `h3 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A] B)`. Set `ψ : R →+* A' ⧸ I` to `(Ideal.Quotient.mk I).comp (algebraMap R A')`. Establish `hψ₁ : p ≤ RingHom.ker ψ` using `fun r hr => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)`. Establish `hψ₂ : p.primeCompl ≤ (IsUnit.submonoid (A' ⧸ I)).comap ψ`.

Introduce `r hr`. Establish `: IsUnit (algebraMap R A' r)`. Assume the negation of the conclusion as `h`. Conclude with `hr h`. Conclude with `this.map (Ideal.Quotient.mk I)`.

Use `H p.ResidueField (A' ⧸ I) (algebraMap R _) (Ideal.ResidueField.lift p ψ hψ₁ hψ₂) ?_` and prove the remaining obligations. Use extensionality with `r`. Conclude with `(Ideal.ResidueField.lift_algebraMap p ψ hψ₁ hψ₂ r).symm`. Establish `h4 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A'] (A' ⊗[A] B))` using `Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange A A' (A' ⧸ I) (A' ⧸ I) B)`. Establish `h5 : Module.Free A' (A' ⊗[A] B)` using `free_of_flat_reduction p Ideal.map_comap_le`.

Establish `h6 : Module.Flat A' (A' ⊗[A] B)` using `Module.Flat.of_free`. Conclude with `Module.Flat.trans A A' (A' ⊗[A] B)`.
-/
theorem flat_of_flat_fibres {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsNoetherianRing A] [Module.Finite A B]
    [Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) :
    Module.Flat A B := by
  refine Module.flat_of_isLocalized_maximal A B (fun P _ => Localization.AtPrime P ⊗[A] B)
    (fun P _ => TensorProduct.mk A (Localization.AtPrime P) B 1) fun P _ => ?_
  let A' := Localization.AtPrime P
  let p : Ideal R := (maximalIdeal A').comap (algebraMap R A')
  let I := p.map (algebraMap R A')
  have h1 : Module.Flat R (B ⊗[A] A') := Module.Flat.trans R B (B ⊗[A] A')
  have h2 : Module.Flat R (A' ⊗[A] B) :=
    Module.Flat.of_linearEquiv
      ((Algebra.TensorProduct.comm A A' B).restrictScalars R).toLinearEquiv
  have h3 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A] B) := by
    let ψ : R →+* A' ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R A')
    have hψ₁ : p ≤ RingHom.ker ψ := fun r hr =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
    have hψ₂ : p.primeCompl ≤ (IsUnit.submonoid (A' ⧸ I)).comap ψ := by
      intro r hr
      have : IsUnit (algebraMap R A' r) := by
        by_contra h
        exact hr h
      exact this.map (Ideal.Quotient.mk I)
    refine H p.ResidueField (A' ⧸ I) (algebraMap R _) (Ideal.ResidueField.lift p ψ hψ₁ hψ₂) ?_
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p ψ hψ₁ hψ₂ r).symm
  have h4 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A'] (A' ⊗[A] B)) :=
    Module.Flat.of_linearEquiv
      (AlgebraTensorModule.cancelBaseChange A A' (A' ⧸ I) (A' ⧸ I) B)
  have h5 : Module.Free A' (A' ⊗[A] B) :=
    free_of_flat_reduction p Ideal.map_comap_le
  have h6 : Module.Flat A' (A' ⊗[A] B) := Module.Flat.of_free
  exact Module.Flat.trans A A' (A' ⊗[A] B)

end Algebra

open FibreFlat

variable {X Y S S' : Scheme.{0}} {f : X ⟶ Y}

/- English proof (translation)
Introduce `_ _ a b j h sq e` and use `H a b j h sq (by rw [← Category.assoc, e, Category.assoc])`.
-/
theorem flatOver_of_comp_base {S₀ : Scheme.{0}} {g : Y ⟶ S₀} {u : S₀ ⟶ S} {t : S' ⟶ S₀}
    (H : FlatOver f (g ≫ u) (t ≫ u)) : FlatOver f g t :=
  fun _ _ a b j h sq e => H a b j h sq (by rw [← Category.assoc, e, Category.assoc])

/- English proof (translation)
Introduce `W Z a b j h sq e`. Use `haveI := flat_descendsAlong_fpqc`. Establish `sq1` using `IsPullback.of_hasPullback b (pullback.fst h σ)`. Establish `h1 : Flat (pullback.snd b (pullback.fst h σ))` using `H _ _ _ (pullback.snd h σ) (sq1.paste_horiz sq) (by rw [Category.assoc, e, ← Category.assoc, pullback.condition, Category.assoc])`. Conclude with `MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq1.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h1`.
-/
theorem flatOver_descend {S'' : Scheme.{0}} {g : Y ⟶ S} {t : S' ⟶ S} (σ : S'' ⟶ S')
    [Surjective σ] [Flat σ] [QuasiCompact σ] (H : FlatOver f g (σ ≫ t)) : FlatOver f g t := by
  intro W Z a b j h sq e
  haveI := flat_descendsAlong_fpqc
  have sq1 := IsPullback.of_hasPullback b (pullback.fst h σ)
  have h1 : Flat (pullback.snd b (pullback.fst h σ)) :=
    H _ _ _ (pullback.snd h σ) (sq1.paste_horiz sq)
      (by rw [Category.assoc, e, ← Category.assoc, pullback.condition, Category.assoc])
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq1.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h1

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Use `wlog hS : ∃ R, S = Spec R generalizing X Y S`. Use `IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_` and prove the remaining obligations. Set `u` to `S.affineCover.f i`. Establish `sq` using `IsPullback.of_hasPullback f (pullback.fst g u)`. Establish `sq'` using `IsPullback.of_hasPullback g u`.

Use `this (pullback.snd f (pullback.fst g u)) (pullback.snd g u) (LocallyOfFiniteType.isLocallyNoetherian (pullback.fst g u)) (MorphismProperty.of_isPullback (sq.paste_vert sq') h1) inferInstance (fun k _ t => flatOver_of_comp_base (u := u) ?_) ⟨_, rfl⟩` and prove the remaining obligations. Rewrite using `[← pullback.condition]`. Conclude with `(H k _).target sq`. Take `⟨R, rfl⟩` from `hS`. Use `wlog hA : ∃ A, Y = Spec A generalizing X Y`.

Use `IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_` and prove the remaining obligations. Establish `sq` using `IsPullback.of_hasPullback f (Y.affineCover.f i)`. Establish `e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g = pullback.fst f (Y.affineCover.f i) ≫ f ≫ g`. Rewrite using `[← Category.assoc, ← sq.w, Category.assoc]`. Conclude with `this (pullback.snd f (Y.affineCover.f i)) (LocallyOfFiniteType.isLocallyNoetherian (Y.affineCover.f i)) inferInstance (Y.affineCover.f i ≫ g) (by rw [e]; infer_instance) (fun k _ t => (H k t).target sq) ⟨_, rfl⟩`.

Take `⟨A, rfl⟩` from `hA`. Use `wlog hX : ∃ B, X = Spec B generalizing X`. Use `haveI hX' : IsAffine X := isAffine_of_isAffineHom f`. Rewrite using `[← MorphismProperty.cancel_left_of_respectsIso @Flat X.isoSpec.inv]`. Conclude with `this (X.isoSpec.inv ≫ f) inferInstance (by rw [Category.assoc]; infer_instance) (fun k _ t => (H k t).source _) ⟨_, rfl⟩`.

Take `⟨B, rfl⟩` from `hX`. Take `⟨f, rfl⟩` from `Spec.map_surjective f`. Take `⟨g, rfl⟩` from `Spec.map_surjective g`. Rewrite `h1` using `[← Spec.map_comp]`. Rewrite `h1`, the goal using `[Flat.SpecMap_iff]`.

Rewrite `h2` using `[IsFinite.SpecMap_iff]`. Rewrite `hY` using `[isLocallyNoetherian_Spec]`. Use `letI : Algebra R A := g.hom.toAlgebra`. Use `letI : Algebra A B := f.hom.toAlgebra`. Use `letI : Algebra R B := (g ≫ f).hom.toAlgebra`.

Use `haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : Module.Flat R B := h1`. Use `haveI : Module.Finite A B := h2`. Use `flat_of_flat_fibres (R := R) (A := A) (B := B) fun k C _ _ _ t h e => ?_` and prove the remaining obligations. Establish `sq` using `isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)`.

Use `H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip (by` as an intermediate fact. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Use `ext1`. Conclude with `e)`.

Rewrite `this` using `[Flat.SpecMap_iff]`. Conclude with `RingHom.flat_algebraMap_iff.mp this`.
-/
theorem flat_of_flatOver_fields (f : X ⟶ Y) (g : Y ⟶ S) (hY : IsLocallyNoetherian Y)
    (h1 : Flat (f ≫ g)) (h2 : IsFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    have sq := IsPullback.of_hasPullback f (pullback.fst g u)
    have sq' := IsPullback.of_hasPullback g u
    refine this (pullback.snd f (pullback.fst g u)) (pullback.snd g u)
      (LocallyOfFiniteType.isLocallyNoetherian (pullback.fst g u))
      (MorphismProperty.of_isPullback (sq.paste_vert sq') h1) inferInstance
      (fun k _ t => flatOver_of_comp_base (u := u) ?_) ⟨_, rfl⟩
    rw [← pullback.condition]
    exact (H k _).target sq
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i))
      (LocallyOfFiniteType.isLocallyNoetherian (Y.affineCover.f i)) inferInstance
      (Y.affineCover.f i ≫ g) (by rw [e]; infer_instance) (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X
  · haveI hX' : IsAffine X := isAffine_of_isAffineHom f
    rw [← MorphismProperty.cancel_left_of_respectsIso @Flat X.isoSpec.inv]
    exact this (X.isoSpec.inv ≫ f) inferInstance (by rw [Category.assoc]; infer_instance)
      (fun k _ t => (H k t).source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [IsFinite.SpecMap_iff] at h2
  rw [isLocallyNoetherian_Spec] at hY
  letI : Algebra R A := g.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra R B := (g ≫ f).hom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat R B := h1
  haveI : Module.Finite A B := h2
  refine flat_of_flat_fibres (R := R) (A := A) (B := B) fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at this
  exact RingHom.flat_algebraMap_iff.mp this

end FiniteFibreFlat

/- English proof (translation)
Introduce `S _ X Y f h1 h2 h3 H`. Use `FiniteFibreFlat.flat_of_flatOver_fields f.left Y.hom (LocallyOfFiniteType.isLocallyNoetherian Y.hom) (by rwa [Over.w]) h3 fun k _ t => ?_` and prove the remaining obligations. Conclude with `FiniteFibreFlat.flatOver_descend (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) (FibreFlat.flatOver_of_pullback f _ (H _ _))`.
-/
theorem flat_of_isFinite_of_flat_geometric_fibres :
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFiniteType Y.hom → IsFinite f.left → (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S), Flat ((Over.pullback t).map f).left) → Flat f.left := by
  intro S _ X Y f h1 h2 h3 H
  refine FiniteFibreFlat.flat_of_flatOver_fields f.left Y.hom
    (LocallyOfFiniteType.isLocallyNoetherian Y.hom) (by rwa [Over.w]) h3 fun k _ t => ?_
  exact FiniteFibreFlat.flatOver_descend
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
    (FibreFlat.flatOver_of_pullback f _ (H _ _))

end GlobalTheory
