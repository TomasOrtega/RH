import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange

open Module
open TensorProduct

namespace GlobalTheory

namespace GenericFreeness

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/- English proof (translation)
Set `f` to `TensorProduct.mk R (Localization.Away a) M 1`. Use `⟨Module.Basis.mk (v := f ∘ fun x : s => (x : M)) (LinearIndependent.of_isLocalizedModule (Localization.Away a) (.powers a) f h.linearIndepOn) ?_, fun x => Module.Basis.mk_apply _ _ x⟩` and prove the remaining obligations. Introduce `y _`. Proceed by induction on `y with`. Consider the case `zero => exact Submodule.zero_mem _`.

Consider the case `add y z hy hz => exact Submodule.add_mem _ (hy trivial) (hz trivial)`. Consider the case `tmul c m`. Take `⟨n, hn⟩` from `h.2.2 m trivial`. Rewrite `hn` using `[bot_sup_eq]`. Establish `h1` using `Submodule.mem_map_of_mem (f := f) hn`.

Rewrite `h1` using `[Submodule.map_span]`. Establish `h2` using `Submodule.span_subset_span R (Localization.Away a) _ h1`. Take `⟨u, hu⟩` from `((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).pow n).exists_left_inv`. Establish `e : c ⊗ₜ[R] m = (c * u) • f (a ^ n • m)`. Simplify using `only [f, TensorProduct.mk_apply, ← smul_tmul, smul_tmul', smul_eq_mul, Algebra.smul_def, map_pow, mul_one, mul_assoc, hu]`.

Rewrite using `[e, Set.range_comp, Subtype.range_coe]`. Conclude with `Submodule.smul_mem _ _ h2`.
-/
theorem IsBasisAway.exists_basis_apply_eq {a : R} {s : Set M}
    (h : IsBasisAway a (⊥ : Submodule R M) ⊤ s) :
    ∃ b : Module.Basis s (Localization.Away a) (Localization.Away a ⊗[R] M),
      ∀ x : s, b x = 1 ⊗ₜ (x : M) := by
  let f := TensorProduct.mk R (Localization.Away a) M 1
  refine ⟨Module.Basis.mk (v := f ∘ fun x : s => (x : M))
    (LinearIndependent.of_isLocalizedModule (Localization.Away a) (.powers a) f h.linearIndepOn)
    ?_, fun x => Module.Basis.mk_apply _ _ x⟩
  intro y _
  induction y with
  | zero => exact Submodule.zero_mem _
  | add y z hy hz => exact Submodule.add_mem _ (hy trivial) (hz trivial)
  | tmul c m =>
    obtain ⟨n, hn⟩ := h.2.2 m trivial
    rw [bot_sup_eq] at hn
    have h1 := Submodule.mem_map_of_mem (f := f) hn
    rw [Submodule.map_span] at h1
    have h2 := Submodule.span_subset_span R (Localization.Away a) _ h1
    obtain ⟨u, hu⟩ :=
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).pow n).exists_left_inv
    have e : c ⊗ₜ[R] m = (c * u) • f (a ^ n • m) := by
      simp only [f, TensorProduct.mk_apply, ← smul_tmul, smul_tmul', smul_eq_mul,
        Algebra.smul_def, map_pow, mul_one, mul_assoc, hu]
    rw [e, Set.range_comp, Subtype.range_coe]
    exact Submodule.smul_mem _ _ h2

/- English proof (translation)
Take `⟨b, hb⟩` from `h.exists_basis_apply_eq`. Use `letI : Algebra (Localization.Away a) K := (IsLocalization.Away.lift a ha).toAlgebra`. Use `haveI : IsScalarTower R (Localization.Away a) K := .of_algebraMap_eq fun r => (IsLocalization.Away.lift_eq a ha r).symm`. Use `((b.baseChange K).map (AlgebraTensorModule.cancelBaseChange R _ K K M)).ne_zero ⟨x, hx⟩` as an intermediate fact. Simplify `this` using `[hb]`.
-/
theorem IsBasisAway.one_tmul_ne_zero {a : R} {s : Set M}
    (h : IsBasisAway a (⊥ : Submodule R M) ⊤ s) (K : Type*) [CommRing K] [Nontrivial K]
    [Algebra R K] (ha : IsUnit (algebraMap R K a)) {x : M} (hx : x ∈ s) :
    (1 : K) ⊗ₜ[R] x ≠ 0 := by
  obtain ⟨b, hb⟩ := h.exists_basis_apply_eq
  letI : Algebra (Localization.Away a) K := (IsLocalization.Away.lift a ha).toAlgebra
  haveI : IsScalarTower R (Localization.Away a) K :=
    .of_algebraMap_eq fun r => (IsLocalization.Away.lift_eq a ha r).symm
  have := ((b.baseChange K).map (AlgebraTensorModule.cancelBaseChange R _ K K M)).ne_zero ⟨x, hx⟩
  simpa [hb] using this

end GenericFreeness

open GenericFreeness

section

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  {A₀ : Type*} [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
  {A : Type*} [CommRing A] [Algebra R A] (φ : A₀ →ₐ[R] A)

/- English proof (translation)
Use `haveI : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing R A₀`. Set `J : Ideal A₀` to `RingHom.ker φ`. Take `⟨a, ha0, ha⟩` from `exists_hasBasisAway_of_finiteType (R := R) (A := A₀) J`. Take `⟨b, hb0, hb⟩` from `exists_hasBasisAway_quotient R A₀ A₀ J (IsNoetherian.noetherian J)`. Establish `ha1` using `HasBasisAway.map (a := a) (J.subtype.restrictScalars R) ⊥ (by`.

Establish `: Submodule.comap (J.subtype.restrictScalars R) ⊥ = ⊥` using `LinearMap.ker_eq_bot.2 Subtype.val_injective`. Rewrite using `[this])` and apply the resulting hypothesis. Establish `e : (⊥ : Submodule R A₀) ⊔ LinearMap.range (J.subtype.restrictScalars R) = J.restrictScalars R`. Rewrite using `[bot_sup_eq]`. Use extensionality with `x`.

Conclude with `⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩`. Rewrite `ha1` using `[e]`. Take `⟨s, hs⟩` from `ha1.of_dvd (dvd_mul_right a b)`. Take `⟨t, ht⟩` from `hb.of_dvd (dvd_mul_left b a)`. Establish `hst` using `hs.union bot_le le_top ht`.

Establish `hab` using `mul_ne_zero ha0 hb0`. Take `⟨x, hxD, hxa⟩` from `hD.exists_mem_open (PrimeSpectrum.basicOpen (a * b)).isOpen ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hab⟩`. Establish `hu : IsUnit (algebraMap R x.asIdeal.ResidueField (a * b))`. Rewrite using `[isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]`. Conclude with `hxa`.

Take `rfl : s = ∅` from `Set.eq_empty_of_forall_notMem fun y hy => by`. Use `hst.one_tmul_ne_zero _ hu (Or.inl hy) (h x hxD ?_)` and prove the remaining obligations. Establish `: φ y = 0` using `hs.1 hy`. Rewrite using `[Algebra.TensorProduct.map_tmul, this, tmul_zero, map_zero]`. Use `⟨a * b, hab, fun y hy => ?_⟩` and prove the remaining obligations.

Simplify using `using hs.2.2 y hy`.
-/
theorem exists_pow_smul_ker_eq_zero_of_dense {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (h : ∀ x ∈ D, Function.Injective (Algebra.TensorProduct.map
      (AlgHom.id R x.asIdeal.ResidueField) φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ y : A₀, φ y = 0 → ∃ n : ℕ, a ^ n • y = 0 := by
  haveI : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing R A₀
  let J : Ideal A₀ := RingHom.ker φ
  obtain ⟨a, ha0, ha⟩ := exists_hasBasisAway_of_finiteType (R := R) (A := A₀) J
  obtain ⟨b, hb0, hb⟩ := exists_hasBasisAway_quotient R A₀ A₀ J (IsNoetherian.noetherian J)
  have ha1 := HasBasisAway.map (a := a) (J.subtype.restrictScalars R) ⊥ (by
    have : Submodule.comap (J.subtype.restrictScalars R) ⊥ = ⊥ :=
      LinearMap.ker_eq_bot.2 Subtype.val_injective
    rwa [this])
  have e : (⊥ : Submodule R A₀) ⊔ LinearMap.range (J.subtype.restrictScalars R) =
      J.restrictScalars R := by
    rw [bot_sup_eq]
    ext x
    exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [e] at ha1
  obtain ⟨s, hs⟩ := ha1.of_dvd (dvd_mul_right a b)
  obtain ⟨t, ht⟩ := hb.of_dvd (dvd_mul_left b a)
  have hst := hs.union bot_le le_top ht
  have hab := mul_ne_zero ha0 hb0
  obtain ⟨x, hxD, hxa⟩ := hD.exists_mem_open (PrimeSpectrum.basicOpen (a * b)).isOpen
    ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hab⟩
  have hu : IsUnit (algebraMap R x.asIdeal.ResidueField (a * b)) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]
    exact hxa
  obtain rfl : s = ∅ := Set.eq_empty_of_forall_notMem fun y hy => by
    refine hst.one_tmul_ne_zero _ hu (Or.inl hy) (h x hxD ?_)
    have : φ y = 0 := hs.1 hy
    rw [Algebra.TensorProduct.map_tmul, this, tmul_zero, map_zero]
  refine ⟨a * b, hab, fun y hy => ?_⟩
  simpa using hs.2.2 y hy

/- English proof (translation)
Take `⟨a, ha0, ha⟩` from `exists_pow_smul_ker_eq_zero_of_dense φ hD h`. Use `⟨a, ha0, fun R' _ _ _ hu => (injective_iff_map_eq_zero _).2 fun z hz => ?_⟩` and prove the remaining obligations. Establish `hex` using `Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map φ.toLinearMap)`. Take `⟨w, rfl⟩` from `(hex z).1 hz`. Use `clear hz`.

Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `add y z hy hz => rw [map_add, hy, hz, add_zero]`. Consider the case `tmul c y`. Take `⟨n, hn⟩` from `ha y y.2`.

Take `⟨u, hu⟩` from `(hu.pow n).exists_left_inv`. Establish `e : c = a ^ n • (c * u)`. Rewrite using `[Algebra.smul_def, map_pow, mul_comm, mul_assoc, hu, mul_one]`. Rewrite using `[LinearMap.lTensor_tmul, e, smul_tmul, Submodule.subtype_apply, hn, tmul_zero]`.
-/
theorem exists_baseChange_injective_of_dense.{w} {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (h : ∀ x ∈ D, Function.Injective (Algebra.TensorProduct.map
      (AlgHom.id R x.asIdeal.ResidueField) φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type w) [CommRing R'] [Algebra R R'] [Module.Flat R R'],
      IsUnit (algebraMap R R' a) →
        Function.Injective (Algebra.TensorProduct.map (AlgHom.id R R') φ) := by
  obtain ⟨a, ha0, ha⟩ := exists_pow_smul_ker_eq_zero_of_dense φ hD h
  refine ⟨a, ha0, fun R' _ _ _ hu => (injective_iff_map_eq_zero _).2 fun z hz => ?_⟩
  have hex := Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map φ.toLinearMap)
  obtain ⟨w, rfl⟩ := (hex z).1 hz
  clear hz
  induction w with
  | zero => simp
  | add y z hy hz => rw [map_add, hy, hz, add_zero]
  | tmul c y =>
    obtain ⟨n, hn⟩ := ha y y.2
    obtain ⟨u, hu⟩ := (hu.pow n).exists_left_inv
    have e : c = a ^ n • (c * u) := by
      rw [Algebra.smul_def, map_pow, mul_comm, mul_assoc, hu, mul_one]
    rw [LinearMap.lTensor_tmul, e, smul_tmul, Submodule.subtype_apply, hn, tmul_zero]

end

end GlobalTheory
