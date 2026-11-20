import Mathlib
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBaseChangeQuotientOfMapMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

noncomputable section

namespace GlobalTheory.LatLenExt

open Formalism.L2.Col TensorProduct

section Int

variable {K : Type} [Field K] [NumberField K] {O : Type} [CommRing O] [IsDomain O]
  (e : K →+* FractionRing O) (he : ∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range)

def intMap : 𝓞 K →+* O :=
  (RingEquiv.ofBijective (algebraMap O (FractionRing O)).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective O (FractionRing O) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).symm.toRingHom.comp
    ((e.comp (algebraMap (𝓞 K) K)).codRestrict _ he)

/- English proof (translation)
Establish `h` using `(RingEquiv.ofBijective (algebraMap O (FractionRing O)).rangeRestrict ⟨fun _ _ h => IsFractionRing.injective O (FractionRing O) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).apply_symm_apply ((e.comp (algebraMap (𝓞 K) K)).codRestrict _ he a)`. Conclude with `congrArg Subtype.val h`.
-/
theorem algebraMap_intMap (a : 𝓞 K) :
    algebraMap O (FractionRing O) (intMap e he a) = e (a : K) := by
  have h := (RingEquiv.ofBijective (algebraMap O (FractionRing O)).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective O (FractionRing O) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).apply_symm_apply
      ((e.comp (algebraMap (𝓞 K) K)).codRestrict _ he a)
  exact congrArg Subtype.val h

variable [IsDiscreteValuationRing O] (w : HeightOneSpectrum (𝓞 K))
  (hw : ∀ a : 𝓞 K, ∀ z : O, algebraMap O (FractionRing O) z = e (a : K) →
    (a ∈ w.asIdeal ↔ ¬ IsUnit z))

include hw in
/- English proof (translation)
Assume the negation of the conclusion as `h`. Conclude with `ha ((hw a _ (algebraMap_intMap e he a)).2 h)`.
-/
theorem isUnit_intMap {a : 𝓞 K} (ha : a ∉ w.asIdeal) : IsUnit (intMap e he a) := by
  by_contra h
  exact ha ((hw a _ (algebraMap_intMap e he a)).2 h)

def owHom : Ow w →+* O :=
  IsLocalization.lift (M := w.asIdeal.primeCompl) (g := intMap e he)
    (fun s => isUnit_intMap e he w hw s.2)

/- English proof (translation)
The claim follows from `IsLocalization.lift_eq _ _`.
-/
theorem owHom_algebraMap (a : 𝓞 K) :
    owHom e he w hw (algebraMap (𝓞 K) (Ow w) a) = intMap e he a :=
  IsLocalization.lift_eq _ _

/- English proof (translation)
Establish `: (algebraMap O (FractionRing O)).comp (owHom e he w hw) = e.comp (algebraMap (Ow w) K)` using `IsLocalization.ringHom_ext w.asIdeal.primeCompl (RingHom.ext fun a => by`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, owHom_algebraMap, algebraMap_intMap, ← IsScalarTower.algebraMap_apply])`. Conclude with `RingHom.congr_fun this x`.
-/
theorem algebraMap_owHom (x : Ow w) :
    algebraMap O (FractionRing O) (owHom e he w hw x) = e (algebraMap (Ow w) K x) := by
  have : (algebraMap O (FractionRing O)).comp (owHom e he w hw) = e.comp (algebraMap (Ow w) K) :=
    IsLocalization.ringHom_ext w.asIdeal.primeCompl (RingHom.ext fun a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
        owHom_algebraMap, algebraMap_intMap, ← IsScalarTower.algebraMap_apply])
  exact RingHom.congr_fun this x

/- English proof (translation)
Introduce `x y h`. Use `congrArg (algebraMap O (FractionRing O)) h` as an intermediate fact. Rewrite `this` using `[algebraMap_owHom, algebraMap_owHom]`. Conclude with `algebraMap_ow_injective w (e.injective this)`.
-/
theorem owHom_injective : Function.Injective (owHom e he w hw) := by
  intro x y h
  have := congrArg (algebraMap O (FractionRing O)) h
  rw [algebraMap_owHom, algebraMap_owHom] at this
  exact algebraMap_ow_injective w (e.injective this)

/- English proof (translation)
Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective w.asIdeal.primeCompl x`. Rewrite `hx` using `[owHom, IsLocalization.lift_mk']`. Establish `ha : IsUnit (intMap e he a)` using `(IsUnit.mul_iff.1 hx).1`. Establish `: a ∉ w.asIdeal` using `fun h => ((hw a _ (algebraMap_intMap e he a)).1 h) ha`.

Conclude with `(IsLocalization.AtPrime.isUnit_mk'_iff (Ow w) w.asIdeal a s).2 this`.
-/
theorem owHom_isLocalHom : IsLocalHom (owHom e he w hw) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl x
  rw [owHom, IsLocalization.lift_mk'] at hx
  have ha : IsUnit (intMap e he a) := (IsUnit.mul_iff.1 hx).1
  have : a ∉ w.asIdeal := fun h => ((hw a _ (algebraMap_intMap e he a)).1 h) ha
  exact (IsLocalization.AtPrime.isUnit_mk'_iff (Ow w) w.asIdeal a s).2 this

end Int

/- English proof (translation)
Substitute `hP hQ` using the available equality. Use `⟨Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf P) ?_⟩` and prove the remaining obligations. Use extensionality with `⟨y, hy⟩`. Simplify using `only [Submodule.mem_map, Submodule.mem_comap, Submodule.submoduleOf, Submodule.subtype_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, hxy⟩`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hxy` as an intermediate fact. Simplify using `using this`. Introduce and unpack `⟨q, hq, rfl⟩`.

Take `⟨p, hp, hpq⟩` from `hy`. Take `rfl` from `hf hpq`. Conclude with `⟨⟨p, hp⟩, hq, rfl⟩`.
-/
theorem nonempty_quot_map_equiv {S M N : Type*} [Ring S] [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] (f : M →ₗ[S] N) (hf : Function.Injective f)
    (P Q : Submodule S M) (P' Q' : Submodule S N) (hP : P.map f = P') (hQ : Q.map f = Q') :
    Nonempty ((P ⧸ Q.submoduleOf P) ≃ₗ[S] (P' ⧸ Q'.comap P'.subtype)) := by
  subst hP hQ
  refine ⟨Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf P) ?_⟩
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.submoduleOf, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    have := congrArg Subtype.val hxy
    simpa using this
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hpq⟩ := hy
    obtain rfl := hf hpq
    exact ⟨⟨p, hp⟩, hq, rfl⟩

end GlobalTheory.LatLenExt

namespace GlobalTheory.LatLenExt

open Formalism.L2.Col TensorProduct

/- English proof (translation)
Introduce `K _ _ O _ _ _ e V V' _ _ _ _ _ _ _ _ _ iV ι b hli he w l hl hlw hw A B _ _`. Use `letI : Algebra (Ow w) O := (owHom e he w hw).toAlgebra`. Use `letI : Algebra K (FractionRing O) := e.toAlgebra`. Use `haveI : IsScalarTower (Ow w) K (FractionRing O) := IsScalarTower.of_algebraMap_eq fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply (Ow w) O (FractionRing O)]`.

Conclude with `algebraMap_owHom e he w hw x`. Use `haveI : FaithfulSMul (Ow w) O := (faithfulSMul_iff_algebraMap_injective _ _).2 (owHom_injective e he w hw)`. Use `haveI : IsLocalHom (algebraMap (Ow w) O) := owHom_isLocalHom e he w hw`. Use `letI : Module K V' := Module.compHom V' e`. Use `haveI : IsScalarTower K (FractionRing O) V' := ⟨fun c x y => by show (c • x) • y = e c • (x • y)`.

Rewrite using `[Algebra.smul_def, mul_smul]`. Use the proof step `rfl⟩`. Set `iVK : V →ₗ[K] V'` to `{ toFun := iV, map_add' := iV.map_add, map_smul' := fun c x => iV.map_smulₛₗ c x }`. Set `Φ : FractionRing O ⊗[K] V →ₗ[FractionRing O] V'` to `iVK.liftBaseChange (FractionRing O)`. Establish `hΦ : ∀ v, Φ ((1 : FractionRing O) ⊗ₜ[K] v) = iV v` using `fun v => by`.

Simplify using `[Φ, iVK]`. Establish `hinj : Function.Injective Φ`. Use `LinearMap.injective_of_linearIndependent (Algebra.TensorProduct.basis (FractionRing O) b).span_eq ?_` and prove the remaining obligations. Establish `hc : (Φ ∘ ⇑(Algebra.TensorProduct.basis (FractionRing O) b)) = fun a => iV (b a)`. Use function extensionality and compare the values at `fun i => by simp [hΦ]`.

Rewrite using `[hc]`. Conclude with `hli`. Set `Φs` to `Φ.restrictScalars O`. Establish `key : ∀ A' : Submodule (𝓞 K) V, (GlobalTheory.spanBaseChange K O (FractionRing O) (atW w A')).map Φs = Submodule.span O (iV '' (A' : Set V))`. Introduce `A'`.

Rewrite using `[GlobalTheory.spanBaseChange, Submodule.map_span, Set.image_image]`. Establish `h1 : (fun m => Φs ((1 : FractionRing O) ⊗ₜ[K] m)) = iV` using `funext fun m => hΦ m`. Rewrite using `[h1]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨s, hs, hsx⟩` from `mem_atW_iff.1 hx`. Take `⟨u, hu⟩` from `isUnit_intMap e he w hw hs`. Establish `h2 : iV (s • x) = intMap e he s • iV x`. Rewrite using `[← algebraMap_smul K s x, iV.map_smulₛₗ, ← algebraMap_smul (FractionRing O) (intMap e he s), algebraMap_intMap]`.

Establish `h3 : iV x = ((u⁻¹ : Oˣ) : O) • iV (s • x)`. Rewrite using `[h2, ← hu, smul_smul, Units.inv_mul, one_smul]`. Rewrite using `[SetLike.mem_coe, h3]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsx, rfl⟩)`. Conclude with `Submodule.span_mono (Set.image_mono fun x hx => Submodule.subset_span hx)`.

Take `⟨E2⟩` from `nonempty_quot_map_equiv Φs hinj _ _ _ _ (key A) (key B)`. Set `E` to `GlobalTheory.spanBaseChangeSubquotEquiv K O (FractionRing O) (atW w A) (atW w B) ≪≫ₗ E2`. Establish `hlen : Module.length O (↥(Submodule.span O (iV '' (A : Set V))) ⧸ (Submodule.span O (iV '' (B : Set V))).comap (Submodule.span O (iV '' (A : Set V))).subtype) = lenW w A B * ((IsLocalRing.maximalIdeal O).ramificationIdx (Ow w) : ℕ)`. Rewrite using `[← E.length_eq, GlobalTheory.length_baseChange_dvr]`. Both sides reduce to the same expression.

Establish `hden : Module.length O (O ⧸ Ideal.span {(l : O)}) = (eW w : ℕ∞) * ((IsLocalRing.maximalIdeal O).ramificationIdx (Ow w) : ℕ)`. Take `rfl` from `eq_prW_of_mem w hl hlw`. Rewrite using `[GlobalTheory.length_quotient_span_singleton_eq_addVal, ← map_natCast (algebraMap (Ow w) O), GlobalTheory.addVal_algebraMap, ← GlobalTheory.length_quotient_span_singleton_eq_addVal, length_ow_quot_prW]`. Establish `hpos` using `GlobalTheory.ramificationIdx_maximalIdeal_pos (Ow w) O`. Unfold `lenUnit lenUW`.

Rewrite using `[hlen, hden]`. Simplify using `only [ENat.toNat_mul, ENat.toNat_coe]`. Use `push_cast`. Conclude with `mul_div_mul_right _ _ (by exact_mod_cast hpos.ne')`.
-/
theorem lenUnit_span_eq_lenUW : ∀ (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V), LinearIndependent (FractionRing O) (fun a => iV (b a)) → (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) → ∀ (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → (l : 𝓞 K) ∈ w.asIdeal → (∀ a : 𝓞 K, ∀ z : O, algebraMap O (FractionRing O) z = e (a : K) → (a ∈ w.asIdeal ↔ ¬ IsUnit z)) → ∀ (A B : Submodule (𝓞 K) V), A.FG → B ≤ A → lenUnit (O := O) l (↥(Submodule.span O (iV '' (A : Set V))) ⧸ (Submodule.span O (iV '' (B : Set V))).comap (Submodule.span O (iV '' (A : Set V))).subtype) = Formalism.L2.Col.lenUW w A B := by
  intro K _ _ O _ _ _ e V V' _ _ _ _ _ _ _ _ _ iV ι b hli he w l hl hlw hw A B _ _
  letI : Algebra (Ow w) O := (owHom e he w hw).toAlgebra
  letI : Algebra K (FractionRing O) := e.toAlgebra
  haveI : IsScalarTower (Ow w) K (FractionRing O) := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (Ow w) O (FractionRing O)]
    exact algebraMap_owHom e he w hw x
  haveI : FaithfulSMul (Ow w) O :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (owHom_injective e he w hw)
  haveI : IsLocalHom (algebraMap (Ow w) O) := owHom_isLocalHom e he w hw
  letI : Module K V' := Module.compHom V' e
  haveI : IsScalarTower K (FractionRing O) V' := ⟨fun c x y => by
    show (c • x) • y = e c • (x • y)
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let iVK : V →ₗ[K] V' :=
    { toFun := iV, map_add' := iV.map_add, map_smul' := fun c x => iV.map_smulₛₗ c x }
  let Φ : FractionRing O ⊗[K] V →ₗ[FractionRing O] V' := iVK.liftBaseChange (FractionRing O)
  have hΦ : ∀ v, Φ ((1 : FractionRing O) ⊗ₜ[K] v) = iV v := fun v => by
    simp [Φ, iVK]
  have hinj : Function.Injective Φ := by
    refine LinearMap.injective_of_linearIndependent (Algebra.TensorProduct.basis (FractionRing O) b).span_eq ?_
    have hc : (Φ ∘ ⇑(Algebra.TensorProduct.basis (FractionRing O) b)) = fun a => iV (b a) :=
      funext fun i => by simp [hΦ]
    rw [hc]
    exact hli
  let Φs := Φ.restrictScalars O
  have key : ∀ A' : Submodule (𝓞 K) V,
      (GlobalTheory.spanBaseChange K O (FractionRing O) (atW w A')).map Φs =
        Submodule.span O (iV '' (A' : Set V)) := by
    intro A'
    rw [GlobalTheory.spanBaseChange, Submodule.map_span, Set.image_image]
    have h1 : (fun m => Φs ((1 : FractionRing O) ⊗ₜ[K] m)) = iV := funext fun m => hΦ m
    rw [h1]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨s, hs, hsx⟩ := mem_atW_iff.1 hx
      obtain ⟨u, hu⟩ := isUnit_intMap e he w hw hs
      have h2 : iV (s • x) = intMap e he s • iV x := by
        rw [← algebraMap_smul K s x, iV.map_smulₛₗ, ← algebraMap_smul (FractionRing O) (intMap e he s),
          algebraMap_intMap]
      have h3 : iV x = ((u⁻¹ : Oˣ) : O) • iV (s • x) := by
        rw [h2, ← hu, smul_smul, Units.inv_mul, one_smul]
      rw [SetLike.mem_coe, h3]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsx, rfl⟩)
    · exact Submodule.span_mono (Set.image_mono fun x hx => Submodule.subset_span hx)
  obtain ⟨E2⟩ := nonempty_quot_map_equiv Φs hinj _ _ _ _ (key A) (key B)
  let E := GlobalTheory.spanBaseChangeSubquotEquiv K O (FractionRing O) (atW w A) (atW w B) ≪≫ₗ E2
  have hlen : Module.length O (↥(Submodule.span O (iV '' (A : Set V))) ⧸
      (Submodule.span O (iV '' (B : Set V))).comap (Submodule.span O (iV '' (A : Set V))).subtype) =
      lenW w A B * ((IsLocalRing.maximalIdeal O).ramificationIdx (Ow w) : ℕ) := by
    rw [← E.length_eq, GlobalTheory.length_baseChange_dvr]
    rfl
  have hden : Module.length O (O ⧸ Ideal.span {(l : O)}) =
      (eW w : ℕ∞) * ((IsLocalRing.maximalIdeal O).ramificationIdx (Ow w) : ℕ) := by
    obtain rfl := eq_prW_of_mem w hl hlw
    rw [GlobalTheory.length_quotient_span_singleton_eq_addVal, ← map_natCast (algebraMap (Ow w) O),
      GlobalTheory.addVal_algebraMap, ← GlobalTheory.length_quotient_span_singleton_eq_addVal, length_ow_quot_prW]
  have hpos := GlobalTheory.ramificationIdx_maximalIdeal_pos (Ow w) O
  unfold lenUnit lenUW
  rw [hlen, hden]
  simp only [ENat.toNat_mul, ENat.toNat_coe]
  push_cast
  exact mul_div_mul_right _ _ (by exact_mod_cast hpos.ne')

end GlobalTheory.LatLenExt
