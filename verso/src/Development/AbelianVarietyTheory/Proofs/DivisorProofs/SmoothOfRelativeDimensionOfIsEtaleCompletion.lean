import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.RegSmooth

/- English proof (translation)
Rewrite using `[← TensorProduct.spanFinrank_top_eq_of_residueField (⊤ : Submodule R M) Module.Finite.fg_top, ← Module.finrank_eq_spanFinrank_of_free]`. Conclude with `(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (ResidueField R) (ResidueField R)) (Submodule.topEquiv (R := R) (M := M))).finrank_eq`.
-/
theorem spanFinrank_top_eq_finrank_residueField (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (⊤ : Submodule R M).spanFinrank = Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) := by
  rw [← TensorProduct.spanFinrank_top_eq_of_residueField (⊤ : Submodule R M) Module.Finite.fg_top,
    ← Module.finrank_eq_spanFinrank_of_free]
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (ResidueField R) (ResidueField R))
    (Submodule.topEquiv (R := R) (M := M))).finrank_eq

/- English proof (translation)
Rewrite using `[spanFinrank_top_eq_finrank_residueField, spanFinrank_top_eq_finrank_residueField]`. Set `e₁` to `TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B) (ResidueField B) N`. Set `e₂` to `TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A) (ResidueField B) (ResidueField B) N`. Rewrite using `[e₁.finrank_eq, ← e₂.finrank_eq, Module.finrank_baseChange]`.
-/
theorem spanFinrank_top_tensor_eq {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] {N : Type*} [AddCommGroup N]
    [Module A N] [Module.Finite A N] :
    (⊤ : Submodule B (B ⊗[A] N)).spanFinrank = (⊤ : Submodule A N).spanFinrank := by
  rw [spanFinrank_top_eq_finrank_residueField, spanFinrank_top_eq_finrank_residueField]
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B)
    (ResidueField B) N
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A) (ResidueField B)
    (ResidueField B) N
  rw [e₁.finrank_eq, ← e₂.finrank_eq, Module.finrank_baseChange]

/- English proof (translation)
Set `g : B ⊗[A] I →ₗ[B] B` to `(TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap ∘ₗ TensorProduct.AlgebraTensorModule.lTensor B B I.subtype`. Establish `hg : Function.Injective g`. Establish `h1 : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor B B I.subtype)` using `Module.Flat.lTensor_preserves_injective_linearMap (M := B) I.subtype Subtype.val_injective`. Conclude with `(TensorProduct.AlgebraTensorModule.rid A B B).injective.comp h1`. Establish `hr : Submodule.map g ⊤ = I.map (algebraMap A B)`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, -, rfl⟩`. Proceed by induction on `x with`. Consider the case `zero => simp`. Consider the case `tmul b i`.

Establish `: g (b ⊗ₜ i) = b * algebraMap A B i`. Simplify using `[g, Algebra.smul_def, mul_comm]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ i.2)`. Consider the case `add x y hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Rewrite using `[Ideal.map, Ideal.span_le]`. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Use `⟨(1 : B) ⊗ₜ ⟨i, hi⟩, trivial, ?_⟩` and prove the remaining obligations. Simplify using `[g, Algebra.smul_def]`.

Rewrite using `[← hr, Submodule.spanFinrank_map_eq_of_injective g hg]`.
-/
theorem spanFinrank_map_eq_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (I : Ideal A) :
    (I.map (algebraMap A B)).spanFinrank = (⊤ : Submodule B (B ⊗[A] I)).spanFinrank := by
  let g : B ⊗[A] I →ₗ[B] B :=
    (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap ∘ₗ
      TensorProduct.AlgebraTensorModule.lTensor B B I.subtype
  have hg : Function.Injective g := by
    have h1 : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor B B I.subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := B) I.subtype Subtype.val_injective
    exact (TensorProduct.AlgebraTensorModule.rid A B B).injective.comp h1
  have hr : Submodule.map g ⊤ = I.map (algebraMap A B) := by
    apply le_antisymm
    · rintro _ ⟨x, -, rfl⟩
      induction x with
      | zero => simp
      | tmul b i =>
        have : g (b ⊗ₜ i) = b * algebraMap A B i := by
          simp [g, Algebra.smul_def, mul_comm]
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ i.2)
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · rw [Ideal.map, Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      refine ⟨(1 : B) ⊗ₜ ⟨i, hi⟩, trivial, ?_⟩
      simp [g, Algebra.smul_def]
  rw [← hr, Submodule.spanFinrank_map_eq_of_injective g hg]

/- English proof (translation)
Establish `: (maximalIdeal B).LiesOver (maximalIdeal A)` using `⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩`. Establish `: Algebra.HasGoingDown A B` using `Algebra.HasGoingDown.of_flat`. Establish `e` using `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)`. Rewrite `e` using `[h, Ideal.map_quotient_self, Ideal.height_bot, add_zero]`. Rewrite using `[← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, e]`.
-/
theorem ringKrullDim_eq_of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim A = ringKrullDim B := by
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have e := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
  rw [h, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at e
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, e]

/- English proof (translation)
Establish `hd` using `ringKrullDim_eq_of_flat_of_map_maximalIdeal h`. Use `⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le A ?_, hd⟩` and prove the remaining obligations. Establish `e : (maximalIdeal A).spanFinrank = (maximalIdeal B).spanFinrank`. Rewrite using `[← h, spanFinrank_map_eq_of_flat, spanFinrank_top_tensor_eq, Submodule.spanFinrank_top]`. Rewrite using `[e, hd]`.

Conclude with `((isRegularLocalRing_iff B).mp inferInstance).le`.
-/
theorem isRegularLocalRing_of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B := by
  have hd := ringKrullDim_eq_of_flat_of_map_maximalIdeal h
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le A ?_, hd⟩
  have e : (maximalIdeal A).spanFinrank = (maximalIdeal B).spanFinrank := by
    rw [← h, spanFinrank_map_eq_of_flat, spanFinrank_top_tensor_eq, Submodule.spanFinrank_top]
  rw [e, hd]
  exact ((isRegularLocalRing_iff B).mp inferInstance).le

/- English proof (translation)
Use `algebraize [φ]`. Establish `: IsLocalHom (algebraMap A B)`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hna`. Establish `hm : a ∈ maximalIdeal A` using `(mem_maximalIdeal a).2 hna`.

Establish `: algebraMap A B a ∈ maximalIdeal B` using `h ▸ Ideal.mem_map_of_mem _ hm`. Conclude with `(mem_maximalIdeal _).1 this ha`. Conclude with `isRegularLocalRing_of_flat_of_map_maximalIdeal h`.
-/
theorem isRegularLocalRing_of_flat_of_map_maximalIdeal' {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] (φ : A →+* B) (hf : φ.Flat)
    (h : (maximalIdeal A).map φ = maximalIdeal B) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B := by
  algebraize [φ]
  have : IsLocalHom (algebraMap A B) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 hna
    have : algebraMap A B a ∈ maximalIdeal B := h ▸ Ideal.mem_map_of_mem _ hm
    exact (mem_maximalIdeal _).1 this ha
  exact isRegularLocalRing_of_flat_of_map_maximalIdeal h

/- English proof (translation)
The claim follows from `isRegularLocalRing_of_flat_of_map_maximalIdeal' φ h.1 h.2.1`.
-/
theorem isRegularLocalRing_of_isEtaleCompletion {A B : Type} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] (φ : A →+* B)
    (h : GlobalTheory.Toroidal.IsEtaleCompletion φ) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B :=
  isRegularLocalRing_of_flat_of_map_maximalIdeal' φ h.1 h.2.1

/- English proof (translation)
Establish `: JacobsonSpace X` using `LocallyOfFiniteType.jacobsonSpace f`. Establish `hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n)` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension n) X.affineOpenCover.openCover fun i => ?_` and prove the remaining obligations. Set `R : CommRingCat.{0}` to `X.affineOpenCover.X i`. Set `x : Spec R ⟶ X` to `X.affineOpenCover.f i`.

Establish `hx : IsOpenImmersion x` using `X.affineOpenCover.map_prop i`. Set `φ : CommRingCat.of F ⟶ R` to `Spec.preimage (x ≫ f)`. Use `letI : Algebra F R := φ.hom.toAlgebra`. Establish `hφ : x ≫ f = spMap (algebraMap F R)` using `(Spec.map_preimage (x ≫ f)).symm`. Express the relevant statement in the definitionally equal form `SmoothOfRelativeDimension n (x ≫ f)`.

Rewrite using `[hφ]`. Establish `hft : LocallyOfFiniteType (spMap (algebraMap F R))` using `by rw [← hφ]; infer_instance`. Rewrite `hft` using `[HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]`. Establish `: Algebra.FiniteType F R` using `RingHom.finiteType_algebraMap.mp hft`. Use `GlobalTheory.RegGenSmooth.smooth_of_regular F R n fun m hm => ?_` and prove the remaining obligations.

Set `y : Spec R` to `(⟨m, hm.isPrime⟩ : PrimeSpectrum R)`. Establish `hcl : IsClosed ({x y} : Set X)`. Establish `h1 : IsClosed ({y} : Set (Spec R))` using `(PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm`. Establish `he` using `x.isOpenEmbedding`. Establish `hlc` using `IsLocallyClosed.image h1.isLocallyClosed he.isInducing he.isOpen_range.isLocallyClosed`.

Rewrite `hlc` using `[Set.image_singleton]`. Conclude with `isClosed_singleton_of_isLocallyClosed_singleton hlc`. Take `⟨h1, h2⟩` from `h (x y) hcl`. Set `e` to `(asIso (x.stalkMap y) ≪≫ Spec.stalkIso R y).commRingCatIsoToRingEquiv`. Conclude with `⟨IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h2⟩`.
-/
theorem smoothOfRelativeDimension_of_isRegularLocalRing {F : Type} [Field F] [PerfectField F]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] (n : ℕ)
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      IsRegularLocalRing (X.presheaf.stalk x) ∧ ringKrullDim (X.presheaf.stalk x) = n) :
    SmoothOfRelativeDimension n f := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension n)
    X.affineOpenCover.openCover fun i => ?_
  let R : CommRingCat.{0} := X.affineOpenCover.X i
  let x : Spec R ⟶ X := X.affineOpenCover.f i
  have hx : IsOpenImmersion x := X.affineOpenCover.map_prop i
  let φ : CommRingCat.of F ⟶ R := Spec.preimage (x ≫ f)
  letI : Algebra F R := φ.hom.toAlgebra
  have hφ : x ≫ f = spMap (algebraMap F R) := (Spec.map_preimage (x ≫ f)).symm
  change SmoothOfRelativeDimension n (x ≫ f)
  rw [hφ]
  have hft : LocallyOfFiniteType (spMap (algebraMap F R)) := by rw [← hφ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType F R := RingHom.finiteType_algebraMap.mp hft
  refine GlobalTheory.RegGenSmooth.smooth_of_regular F R n fun m hm => ?_
  let y : Spec R := (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
  have hcl : IsClosed ({x y} : Set X) := by
    have h1 : IsClosed ({y} : Set (Spec R)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm
    have he := x.isOpenEmbedding
    have hlc := IsLocallyClosed.image h1.isLocallyClosed he.isInducing
      he.isOpen_range.isLocallyClosed
    rw [Set.image_singleton] at hlc
    exact isClosed_singleton_of_isLocallyClosed_singleton hlc
  obtain ⟨h1, h2⟩ := h (x y) hcl
  let e := (asIso (x.stalkMap y) ≪≫ Spec.stalkIso R y).commRingCatIsoToRingEquiv
  exact ⟨IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h2⟩

end GlobalTheory.RegSmooth
