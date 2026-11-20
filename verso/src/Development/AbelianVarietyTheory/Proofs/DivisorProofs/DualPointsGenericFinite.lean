import Mathlib
set_option autoImplicit false
open scoped TensorProduct

namespace GlobalTheory

def dualOfDerivation {K A k : Type} [Field K] [CommRing A] [Algebra K A] [Field k] [Algebra K k]
    [Algebra A k] [IsScalarTower K A k] (D : Derivation K A k) : A →ₐ[K] DualNumber k where
  toFun a := TrivSqZeroExt.inl (algebraMap A k a) + TrivSqZeroExt.inr (D a)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Derivation.leibniz, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl]; ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' t := by
    ext
    · simp [IsScalarTower.algebraMap_apply K A k, TrivSqZeroExt.algebraMap_eq_inl']
    · simp [TrivSqZeroExt.algebraMap_eq_inl']

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ r hr C _ _ _ _ _ _ h`. Establish `hu : IsUnit (algebraMap R K r)` using `isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr)`. Use `letI : Algebra (Localization.Away r) K := (IsLocalization.Away.lift (S := Localization.Away r) r hu).toAlgebra`. Use `haveI : IsScalarTower R (Localization.Away r) K := IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq (M := Submonoid.powers r) (S := Localization.Away r) _ x).symm)`. Use `haveI : IsFractionRing (Localization.Away r) K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers r) _ K`.

Establish `hinj : Function.Injective (Algebra.TensorProduct.includeRight : C →ₐ[Localization.Away r] K ⊗[Localization.Away r] C)`. Establish `h1` using `Module.Flat.rTensor_preserves_injective_linearMap (M := C) (Algebra.linearMap (Localization.Away r) K) (IsFractionRing.injective (Localization.Away r) K)`. Introduce `x y hxy`. Apply `(TensorProduct.lid (Localization.Away r) C).symm.injective` to reduce the goal to its premises. Apply `h1` to reduce the goal to its premises.

Simplify `hxy` using `[TensorProduct.lid_symm_apply]`. It suffices to establish `hA : IsReduced (K ⊗[Localization.Away r] C) from isReduced_of_injective (Algebra.TensorProduct.includeRight : C →ₐ[Localization.Away r] K ⊗[Localization.Away r] C).toRingHom hinj`. Assume the negation of the conclusion as `hA`. Establish `hΩ : Nontrivial Ω[(K ⊗[Localization.Away r] C)⁄K]`. Assume the negation of the conclusion as `h'`.

Rewrite `h'` using `[not_nontrivial_iff_subsingleton]`. Use `haveI : Algebra.FormallyUnramified K (K ⊗[Localization.Away r] C) := ⟨h'⟩`. Conclude with `hA (Algebra.FormallyUnramified.isReduced_of_field K _)`. Take `⟨N, hN⟩` from `IsCoatomic.exists_coatom (Submodule (K ⊗[Localization.Away r] C) Ω[(K ⊗[Localization.Away r] C)⁄K])`. Use `haveI := isSimpleModule_iff_isCoatom.mpr hN`.

Take `⟨m, hm, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.mp this`. Use `haveI : m.IsMaximal := hm`. Use `letI : Field ((K ⊗[Localization.Away r] C) ⧸ m) := Ideal.Quotient.field m`. Set `f` to `e.toLinearMap ∘ₗ N.mkQ`. Establish `hf : f ≠ 0`.

Introduce `h0`. Establish `hs : Function.Surjective f` using `e.surjective.comp N.mkQ_surjective`. Take `⟨x, hx⟩` from `hs 1`. Rewrite `hx` using `[h0]`. Conclude with `one_ne_zero hx.symm`.

Set `D : Derivation K (K ⊗[Localization.Away r] C) ((K ⊗[Localization.Away r] C) ⧸ m)` to `KaehlerDifferential.linearMapEquivDerivation K _ f`. Establish `hD : D ≠ 0`. Introduce `h0`. Apply `hf` to reduce the goal to its premises. Conclude with `(KaehlerDifferential.linearMapEquivDerivation K _).injective (h0.trans (map_zero _).symm)`.

Set `φ` to `GlobalTheory.dualOfDerivation D`. Set `ψ : C →ₐ[R] DualNumber ((K ⊗[Localization.Away r] C) ⧸ m)` to `{ toRingHom := φ.toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[Localization.Away r] K ⊗[Localization.Away r] C).toRingHom commutes' := fun t => by`. Express the relevant statement in the definitionally equal form `φ (Algebra.TensorProduct.includeRight (algebraMap R C t)) = _`. Rewrite using `[IsScalarTower.algebraMap_apply R (Localization.Away r) C, AlgHom.commutes, IsScalarTower.algebraMap_apply (Localization.Away r) K (K ⊗[Localization.Away r] C), AlgHom.commutes, ← IsScalarTower.algebraMap_apply R (Localization.Away r) K, ← IsScalarTower.algebraMap_apply R K (Dual …`. Establish `hψ` using `h _ ψ`.

Establish `h1 : ∀ c : C, D ((1 : K) ⊗ₜ c) = 0`. Introduce `c`. Use `congrArg (fun g => TrivSqZeroExt.snd (g c)) hψ` as an intermediate fact. Simplify `this` using `[ψ, φ, GlobalTheory.dualOfDerivation]`. Apply `hD` to reduce the goal to its premises.

Use extensionality with `a`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x c`. Establish `: x ⊗ₜ[Localization.Away r] c = x • ((1 : K) ⊗ₜ c)`.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[this, D.map_smul, h1, smul_zero]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [map_add, hx, hy]`. Simplify using the standard rewrite rules.
-/
theorem isReduced_of_dualNumber_points_trivial : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (r : R), r ≠ 0 →
    ∀ (C : Type) [CommRing C] [Algebra R C] [Algebra (Localization.Away r) C] [IsScalarTower R (Localization.Away r) C]
      [Module.Finite (Localization.Away r) C] [Module.Free (Localization.Away r) C],
      (∀ (k : Type) [Field k] [Algebra R k] [Algebra K k] [IsScalarTower R K k] (ψ : C →ₐ[R] DualNumber k),
        ψ = ((TrivSqZeroExt.inlAlgHom R k k).comp (TrivSqZeroExt.fstHom R k k)).comp ψ) → IsReduced C := by
  intro R K _ _ _ _ _ _ r hr C _ _ _ _ _ _ h
  have hu : IsUnit (algebraMap R K r) :=
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr)
  letI : Algebra (Localization.Away r) K :=
    (IsLocalization.Away.lift (S := Localization.Away r) r hu).toAlgebra
  haveI : IsScalarTower R (Localization.Away r) K := IsScalarTower.of_algebraMap_eq (fun x =>
    (IsLocalization.lift_eq (M := Submonoid.powers r) (S := Localization.Away r) _ x).symm)
  haveI : IsFractionRing (Localization.Away r) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers r) _ K
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : C →ₐ[Localization.Away r] K ⊗[Localization.Away r] C) := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := C)
      (Algebra.linearMap (Localization.Away r) K) (IsFractionRing.injective (Localization.Away r) K)
    intro x y hxy
    apply (TensorProduct.lid (Localization.Away r) C).symm.injective
    apply h1
    simpa [TensorProduct.lid_symm_apply] using hxy
  suffices hA : IsReduced (K ⊗[Localization.Away r] C) from
    isReduced_of_injective (Algebra.TensorProduct.includeRight :
      C →ₐ[Localization.Away r] K ⊗[Localization.Away r] C).toRingHom hinj
  by_contra hA
  have hΩ : Nontrivial Ω[(K ⊗[Localization.Away r] C)⁄K] := by
    by_contra h'
    rw [not_nontrivial_iff_subsingleton] at h'
    haveI : Algebra.FormallyUnramified K (K ⊗[Localization.Away r] C) := ⟨h'⟩
    exact hA (Algebra.FormallyUnramified.isReduced_of_field K _)
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (Submodule (K ⊗[Localization.Away r] C) Ω[(K ⊗[Localization.Away r] C)⁄K])
  haveI := isSimpleModule_iff_isCoatom.mpr hN
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp this
  haveI : m.IsMaximal := hm
  letI : Field ((K ⊗[Localization.Away r] C) ⧸ m) := Ideal.Quotient.field m
  let f := e.toLinearMap ∘ₗ N.mkQ
  have hf : f ≠ 0 := by
    intro h0
    have hs : Function.Surjective f := e.surjective.comp N.mkQ_surjective
    obtain ⟨x, hx⟩ := hs 1
    rw [h0] at hx
    exact one_ne_zero hx.symm
  let D : Derivation K (K ⊗[Localization.Away r] C) ((K ⊗[Localization.Away r] C) ⧸ m) :=
    KaehlerDifferential.linearMapEquivDerivation K _ f
  have hD : D ≠ 0 := by
    intro h0
    apply hf
    exact (KaehlerDifferential.linearMapEquivDerivation K _).injective (h0.trans (map_zero _).symm)
  let φ := GlobalTheory.dualOfDerivation D
  let ψ : C →ₐ[R] DualNumber ((K ⊗[Localization.Away r] C) ⧸ m) :=
    { toRingHom := φ.toRingHom.comp (Algebra.TensorProduct.includeRight :
        C →ₐ[Localization.Away r] K ⊗[Localization.Away r] C).toRingHom
      commutes' := fun t => by
        change φ (Algebra.TensorProduct.includeRight (algebraMap R C t)) = _
        rw [IsScalarTower.algebraMap_apply R (Localization.Away r) C, AlgHom.commutes,
          IsScalarTower.algebraMap_apply (Localization.Away r) K (K ⊗[Localization.Away r] C), AlgHom.commutes,
          ← IsScalarTower.algebraMap_apply R (Localization.Away r) K,
          ← IsScalarTower.algebraMap_apply R K (DualNumber ((K ⊗[Localization.Away r] C) ⧸ m))] }
  have hψ := h _ ψ
  have h1 : ∀ c : C, D ((1 : K) ⊗ₜ c) = 0 := by
    intro c
    have := congrArg (fun g => TrivSqZeroExt.snd (g c)) hψ
    simpa [ψ, φ, GlobalTheory.dualOfDerivation] using this
  apply hD
  ext a
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x c =>
    have : x ⊗ₜ[Localization.Away r] c = x • ((1 : K) ⊗ₜ c) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, D.map_smul, h1, smul_zero]; rfl
  | add x y hx hy => rw [map_add, hx, hy]; simp

end GlobalTheory
