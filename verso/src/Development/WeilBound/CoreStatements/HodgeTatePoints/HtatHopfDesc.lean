import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatDesc
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace PositivityTheory.HtPt.Htat.HopfOrderFlatLocal

/- English proof (translation)
Set `Rp` to `Localization.AtPrime P`. Establish `hu : ∀ y : P.primeCompl, IsUnit (algebraMap R R' y)`. Introduce `y`. Assume the negation of the conclusion as `h`. Establish `h1 : (y : R) ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R')` using `(IsLocalRing.mem_maximalIdeal _).2 h`.

Conclude with `y.2 (hP.le h1)`. Set `ψ : Rp →+* R'` to `IsLocalization.lift hu`. Use `letI : Algebra Rp R' := ψ.toAlgebra`. Establish `hψ : ∀ r : R, algebraMap Rp R' (algebraMap R Rp r) = algebraMap R R' r` using `fun r => IsLocalization.lift_eq hu r`. Use `haveI : IsScalarTower R Rp R' := .of_algebraMap_eq (fun r => (hψ r).symm)`.

Use `haveI : Module.Flat Rp R' := (Module.flat_iff_of_isLocalization Rp P.primeCompl R').2 inferInstance`. Use `haveI : IsLocalHom (algebraMap Rp R') := ⟨fun x hx => by`. Take `⟨r, s, rfl⟩` from `IsLocalization.exists_mk'_eq P.primeCompl x`. Establish `e : algebraMap R R' r = algebraMap Rp R' (IsLocalization.mk' Rp r s) * algebraMap R R' s`. Rewrite using `[← hψ s, ← map_mul, IsLocalization.mk'_spec, hψ]`.

Establish `hr : IsUnit (algebraMap R R' r)`. Rewrite using `[e]`. Conclude with `hx.mul (hu s)`. Establish `hrP : r ∈ P.primeCompl`. Introduce `hmem`.

Rewrite `hmem` using `[← hP]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 hmem hr`. Establish `h3 : IsUnit (algebraMap R Rp r)` using `IsLocalization.map_units Rp (⟨r, hrP⟩ : P.primeCompl)`. Rewrite `h3` using `[← IsLocalization.mk'_spec Rp r s]`. Conclude with `isUnit_of_mul_isUnit_left h3⟩`.

Use `haveI : Module.FaithfullyFlat Rp R' := Module.FaithfullyFlat.of_flat_of_isLocalHom`. Use `haveI : Module.Flat R' (R' ⊗[Rp] (Rp ⊗[R] M)) := Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange R Rp R' R' M)`. Use `haveI : Module.Flat Rp (Rp ⊗[R] M) := Module.Flat.of_flat_tensorProduct Rp (Rp ⊗[R] M) R'`. Use `haveI : Module.Flat R (Rp ⊗[R] M) := (Module.flat_iff_of_isLocalization Rp P.primeCompl (Rp ⊗[R] M)).1 inferInstance`. Conclude with `Module.Flat.of_linearEquiv (IsLocalizedModule.linearEquiv P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl M) (TensorProduct.mk R Rp M 1))`.
-/
theorem flat_localized_of_flat_baseChange {R : Type} [CommRing R] (M : Type) [AddCommGroup M]
    [Module R M] (P : Ideal R) [P.IsMaximal] (R' : Type) [CommRing R'] [IsLocalRing R']
    [Algebra R R'] [Module.Flat R R']
    (hP : (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P)
    [Module.Flat R' (R' ⊗[R] M)] : Module.Flat R (LocalizedModule P.primeCompl M) := by
  let Rp := Localization.AtPrime P
  have hu : ∀ y : P.primeCompl, IsUnit (algebraMap R R' y) := by
    intro y
    by_contra h
    have h1 : (y : R) ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') :=
      (IsLocalRing.mem_maximalIdeal _).2 h
    exact y.2 (hP.le h1)
  let ψ : Rp →+* R' := IsLocalization.lift hu
  letI : Algebra Rp R' := ψ.toAlgebra
  have hψ : ∀ r : R, algebraMap Rp R' (algebraMap R Rp r) = algebraMap R R' r :=
    fun r => IsLocalization.lift_eq hu r
  haveI : IsScalarTower R Rp R' := .of_algebraMap_eq (fun r => (hψ r).symm)
  haveI : Module.Flat Rp R' := (Module.flat_iff_of_isLocalization Rp P.primeCompl R').2 inferInstance
  haveI : IsLocalHom (algebraMap Rp R') := ⟨fun x hx => by
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
    have e : algebraMap R R' r =
        algebraMap Rp R' (IsLocalization.mk' Rp r s) * algebraMap R R' s := by
      rw [← hψ s, ← map_mul, IsLocalization.mk'_spec, hψ]
    have hr : IsUnit (algebraMap R R' r) := by
      rw [e]; exact hx.mul (hu s)
    have hrP : r ∈ P.primeCompl := by
      intro hmem
      rw [← hP] at hmem
      exact (IsLocalRing.mem_maximalIdeal _).1 hmem hr
    have h3 : IsUnit (algebraMap R Rp r) :=
      IsLocalization.map_units Rp (⟨r, hrP⟩ : P.primeCompl)
    rw [← IsLocalization.mk'_spec Rp r s] at h3
    exact isUnit_of_mul_isUnit_left h3⟩
  haveI : Module.FaithfullyFlat Rp R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI : Module.Flat R' (R' ⊗[Rp] (Rp ⊗[R] M)) :=
    Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange R Rp R' R' M)
  haveI : Module.Flat Rp (Rp ⊗[R] M) := Module.Flat.of_flat_tensorProduct Rp (Rp ⊗[R] M) R'
  haveI : Module.Flat R (Rp ⊗[R] M) :=
    (Module.flat_iff_of_isLocalization Rp P.primeCompl (Rp ⊗[R] M)).1 inferInstance
  exact Module.Flat.of_linearEquiv
    (IsLocalizedModule.linearEquiv P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl M)
      (TensorProduct.mk R Rp M 1))

/- English proof (translation)
Consider the cases of `nonempty_fintype T`. Set `L : R' ⊗[R] A →ₗ[R'] (T → R')` to `(TensorProduct.piScalarRight R R' R' T).toLinearMap ∘ₗ LinearMap.baseChange R' A.val.toLinearMap`. Establish `hL : ∀ (r : R') (a : A), L (r ⊗ₜ a) = fun t => r * algebraMap R R' ((a : T → R) t)`. Introduce `r a`. Use extensionality with `t`.

Simplify using `[L, Algebra.smul_def, mul_comm]`. Establish `hinj : Function.Injective L`. Establish `h1 : Function.Injective (LinearMap.baseChange R' A.val.toLinearMap)`. Rewrite using `[LinearMap.baseChange_eq_ltensor]`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective`.

Conclude with `(TensorProduct.piScalarRight R R' R' T).injective.comp h1`. Establish `hrange : LinearMap.range L = Subalgebra.toSubmodule (extOrder (algebraMap R R') A)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, rfl⟩`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul r a`. Rewrite using `[hL]`. Establish `: (fun t => algebraMap R R' ((a : T → R) t)) ∈ extOrder (algebraMap R R') A` using `Algebra.subset_adjoin ⟨a, a.2, rfl⟩`. Conclude with `(extOrder (algebraMap R R') A).smul_mem this r`.

Consider the case `add x y hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Introduce `g hg`. Establish `h` using `(PositivityTheory.HtPt.Htat.ext_span R T R' (algebraMap R R') A g).1 hg`. Use `Submodule.span_le.2 ?_ h` and prove the remaining obligations.

Introduce and unpack `_ ⟨f, hf, rfl⟩`. Conclude with `⟨(1 : R') ⊗ₜ ⟨f, hf⟩, by rw [hL]; simp⟩`. Use `haveI : Module.Flat R' (Subalgebra.toSubmodule (extOrder (algebraMap R R') A)) := inferInstanceAs (Module.Flat R' (extOrder (algebraMap R R') A))`. Conclude with `Module.Flat.of_linearEquiv (LinearEquiv.ofInjective L hinj ≪≫ₗ LinearEquiv.ofEq _ _ hrange)`.
-/
theorem flat_baseChange_of_flat_extOrder {R : Type} [CommRing R] {T : Type} [CommGroup T] [Finite T]
    (A : Subalgebra R (T → R)) (R' : Type) [CommRing R'] [Algebra R R'] [Module.Flat R R']
    [Module.Flat R' (extOrder (algebraMap R R') A)] : Module.Flat R' (R' ⊗[R] A) := by
  classical
  cases nonempty_fintype T
  let L : R' ⊗[R] A →ₗ[R'] (T → R') :=
    (TensorProduct.piScalarRight R R' R' T).toLinearMap ∘ₗ LinearMap.baseChange R' A.val.toLinearMap
  have hL : ∀ (r : R') (a : A), L (r ⊗ₜ a) = fun t => r * algebraMap R R' ((a : T → R) t) := by
    intro r a
    ext t
    simp [L, Algebra.smul_def, mul_comm]
  have hinj : Function.Injective L := by
    have h1 : Function.Injective (LinearMap.baseChange R' A.val.toLinearMap) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    exact (TensorProduct.piScalarRight R R' R' T).injective.comp h1
  have hrange : LinearMap.range L = Subalgebra.toSubmodule (extOrder (algebraMap R R') A) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r a =>
        rw [hL]
        have : (fun t => algebraMap R R' ((a : T → R) t)) ∈ extOrder (algebraMap R R') A :=
          Algebra.subset_adjoin ⟨a, a.2, rfl⟩
        exact (extOrder (algebraMap R R') A).smul_mem this r
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · intro g hg
      have h := (PositivityTheory.HtPt.Htat.ext_span R T R' (algebraMap R R') A g).1 hg
      refine Submodule.span_le.2 ?_ h
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨(1 : R') ⊗ₜ ⟨f, hf⟩, by rw [hL]; simp⟩
  haveI : Module.Flat R' (Subalgebra.toSubmodule (extOrder (algebraMap R R') A)) :=
    inferInstanceAs (Module.Flat R' (extOrder (algebraMap R R') A))
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofInjective L hinj ≪≫ₗ LinearEquiv.ofEq _ _ hrange)

/- English proof (translation)
Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem a h`. Take `⟨a₀, ha₀, rfl⟩` from `h`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem b h`.

Take `⟨b₀, hb₀, rfl⟩` from `h`. Conclude with `Submodule.subset_span ⟨fun z => a₀ z.1 * b₀ z.2, Submodule.subset_span ⟨a₀, ha₀, b₀, hb₀, rfl⟩, by ext z; simp⟩`. Consider the case `zero`. Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`.

Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`. Use `add_mem hx hy using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Simplify using `[mul_add]`.

Consider the case `smul c x _ hx`. Use `Submodule.smul_mem _ c hx using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Consider the case `zero`. Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`.

Use `add_mem hx hy using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Simplify using `[add_mul]`. Consider the case `smul c x _ hx`. Use `Submodule.smul_mem _ c hx using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `z`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_mem_span_prodSpan_of_mem_span {R : Type} [CommRing R] {T : Type} [CommGroup T] {R' : Type} [CommRing R']
    (φ : R →+* R') (A : Subalgebra R (T → R)) {a b : T → R'}
    (ha : a ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)})
    (hb : b ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)}) :
    (fun z : T × T => a z.1 * b z.2) ∈
      Submodule.span R' {g : T × T → R' | ∃ n ∈ prodSpan A, g = fun i => φ (n i)} := by
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨a₀, ha₀, rfl⟩ := h
    induction hb using Submodule.span_induction with
    | mem b h =>
      obtain ⟨b₀, hb₀, rfl⟩ := h
      exact Submodule.subset_span ⟨fun z => a₀ z.1 * b₀ z.2,
        Submodule.subset_span ⟨a₀, ha₀, b₀, hb₀, rfl⟩, by ext z; simp⟩
    | zero =>
      convert Submodule.zero_mem _ using 1
      ext z; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      ext z; simp [mul_add]
    | smul c x _ hx =>
      convert Submodule.smul_mem _ c hx using 1
      ext z; simp; ring
  | zero =>
      convert Submodule.zero_mem _ using 1
      ext z; simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    ext z; simp [add_mul]
  | smul c x _ hx =>
    convert Submodule.smul_mem _ c hx using 1
    ext z; simp; ring

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, b, hb, rfl⟩`. Conclude with `mul_mem_span_prodSpan_of_mem_span φ A ((PositivityTheory.HtPt.Htat.ext_span R T R' φ A a).1 ha) ((PositivityTheory.HtPt.Htat.ext_span R T R' φ A b).1 hb)`.
-/
theorem prodSpan_extOrder_le {R : Type} [CommRing R] {T : Type} [CommGroup T] {R' : Type}
    [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) :
    prodSpan (extOrder φ A) ≤
      Submodule.span R' {g : T × T → R' | ∃ n ∈ prodSpan A, g = fun i => φ (n i)} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact mul_mem_span_prodSpan_of_mem_span φ A ((PositivityTheory.HtPt.Htat.ext_span R T R' φ A a).1 ha) ((PositivityTheory.HtPt.Htat.ext_span R T R' φ A b).1 hb)

/- English proof (translation)
Introduce `R _ _ T _ _ _ A hfull H`. Use `haveI hfin : Module.Finite R A := Module.Finite.of_injective A.val.toLinearMap Subtype.val_injective`. Use `haveI : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A`. Use `haveI hflat : Module.Flat R A := Module.flat_of_localized_maximal A fun P hP => by`. Take `⟨R', _, _, _, _, hf, hP', hH⟩` from `H P hP`.

Use `haveI := hH.projective`. Use `haveI : Module.Flat R' (R' ⊗[R] A) := flat_baseChange_of_flat_extOrder A R'`. Conclude with `flat_localized_of_flat_baseChange A P R' hP'`. Use `⟨hfin, Module.Flat.projective_of_finitePresentation, hfull, ?_, ?_⟩` and prove the remaining obligations. Introduce `f hf`.

Use `PositivityTheory.HtPt.Htat.mem_descent R (T × T) (prodSpan A) _ fun P hP => ?_` and prove the remaining obligations. Take `⟨R', i1, i2, i3, i4, hf', hP', hH⟩` from `H P hP`. Use `⟨R', i1, i3, i4, hf', hP', ?_⟩` and prove the remaining obligations. Establish `h1 : (fun t => algebraMap R R' (f t)) ∈ extOrder (algebraMap R R') A` using `Algebra.subset_adjoin ⟨f, hf, rfl⟩`. Conclude with `prodSpan_extOrder_le _ A (hH.comul _ h1)`.

Introduce `f hf`. Use `PositivityTheory.HtPt.Htat.mem_descent R T (Subalgebra.toSubmodule A) _ fun P hP => ?_` and prove the remaining obligations. Take `⟨R', i1, i2, i3, i4, hf', hP', hH⟩` from `H P hP`. Use `⟨R', i1, i3, i4, hf', hP', ?_⟩` and prove the remaining obligations. Establish `h1 : (fun t => algebraMap R R' (f t)) ∈ extOrder (algebraMap R R') A` using `Algebra.subset_adjoin ⟨f, hf, rfl⟩`.

Conclude with `(PositivityTheory.HtPt.Htat.ext_span R T R' (algebraMap R R') A _).1 (hH.inv _ h1)`.
-/
theorem isHopfOrder_of_flat_local :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] [IsNoetherianRing R]
      (A : Subalgebra R (T → R)), (∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) →
      (∀ P : Ideal R, P.IsMaximal → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R')
        (_ : IsLocalRing R') (_ : Algebra R R'), Module.Flat R R' ∧
        (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧
        IsHopfOrder (extOrder (algebraMap R R') A)) → IsHopfOrder A := by
  intro R _ _ T _ _ _ A hfull H
  haveI hfin : Module.Finite R A :=
    Module.Finite.of_injective A.val.toLinearMap Subtype.val_injective
  haveI : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A
  haveI hflat : Module.Flat R A := Module.flat_of_localized_maximal A fun P hP => by
    obtain ⟨R', _, _, _, _, hf, hP', hH⟩ := H P hP
    haveI := hH.projective
    haveI : Module.Flat R' (R' ⊗[R] A) := flat_baseChange_of_flat_extOrder A R'
    exact flat_localized_of_flat_baseChange A P R' hP'
  refine ⟨hfin, Module.Flat.projective_of_finitePresentation, hfull, ?_, ?_⟩
  · intro f hf
    refine PositivityTheory.HtPt.Htat.mem_descent R (T × T) (prodSpan A) _ fun P hP => ?_
    obtain ⟨R', i1, i2, i3, i4, hf', hP', hH⟩ := H P hP
    refine ⟨R', i1, i3, i4, hf', hP', ?_⟩
    have h1 : (fun t => algebraMap R R' (f t)) ∈ extOrder (algebraMap R R') A :=
      Algebra.subset_adjoin ⟨f, hf, rfl⟩
    exact prodSpan_extOrder_le _ A (hH.comul _ h1)
  · intro f hf
    refine PositivityTheory.HtPt.Htat.mem_descent R T (Subalgebra.toSubmodule A) _ fun P hP => ?_
    obtain ⟨R', i1, i2, i3, i4, hf', hP', hH⟩ := H P hP
    refine ⟨R', i1, i3, i4, hf', hP', ?_⟩
    have h1 : (fun t => algebraMap R R' (f t)) ∈ extOrder (algebraMap R R') A :=
      Algebra.subset_adjoin ⟨f, hf, rfl⟩
    exact (PositivityTheory.HtPt.Htat.ext_span R T R' (algebraMap R R') A _).1 (hH.inv _ h1)

end PositivityTheory.HtPt.Htat.HopfOrderFlatLocal

/- English proof (translation)
The claim follows from `@PositivityTheory.HtPt.Htat.HopfOrderFlatLocal.isHopfOrder_of_flat_local`.
-/
theorem PositivityTheory.HtPt.Htat.bt_hopf_descent : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] [IsNoetherianRing R] (A : Subalgebra R (T → R)), (∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) → (∀ P : Ideal R, P.IsMaximal → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : Algebra R R'), Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧ IsHopfOrder (extOrder (algebraMap R R') A)) → IsHopfOrder A :=
  @PositivityTheory.HtPt.Htat.HopfOrderFlatLocal.isHopfOrder_of_flat_local
