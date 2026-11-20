import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Introduce `Ω _ _ _ A L _ _ _ hL`. Take `⟨N, hN, j, ζ, hm, hζ, hj⟩` from `hL`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`.

Use `haveI : Normal ℚ (CyclotomicField N ℚ) := by haveI : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.2 (NeZero.ne N)⟩`. Establish `h` using `CyclotomicField.isCyclotomicExtension (n := N) (K := ℚ)`. Establish `h2` using `(@IsCyclotomicExtension.isGalois _ _ _ _ _ _ h).to_normal`. Use `h2` and compare the differences between its conclusion and the goal. Conclude with `Subsingleton.elim _ _`.

Set `k : CyclotomicField N ℚ →ₐ[ℚ] Ω` to `IsAlgClosed.lift`. Use `letI : Algebra (CyclotomicField N ℚ) Ω := k.toRingHom.toAlgebra`. Use `haveI : IsScalarTower ℚ (CyclotomicField N ℚ) Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)`. Use `haveI : IsScalarTower ℚ L Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)`. Establish `key : ∀ σ : G ℚ Ω, (∀ x : L, σ (k (j x)) = k (j x)) ↔ galChar Ω A.m σ ∈ A.H`.

Introduce `σ`. Set `τ` to `σ.restrictNormal (CyclotomicField N ℚ)`. Establish `hτ : ∀ y, k (τ y) = σ (k y)` using `fun y => σ.restrictNormal_commutes (CyclotomicField N ℚ) y`. Establish `hkζ : IsPrimitiveRoot (k ζ) N` using `hζ.map_of_injective k.injective`. Establish `hσζ : σ (k ζ) = k ζ ^ (galChar Ω N σ : ZMod N).val` using `galChar_spec N σ (k ζ) hkζ.pow_eq_one`.

Establish `hτζ : τ ζ = ζ ^ (galChar Ω N σ : ZMod N).val`. Apply `k.injective` to reduce the goal to its premises. Use `show k (τ ζ) = k (ζ ^ _)`. Rewrite using `[hτ, hσζ, map_pow]`. Establish `h1` using `hj τ _ hτζ`.

Establish `hfix : (∀ x : L, τ (j x) = j x) ↔ (∀ x : L, σ (k (j x)) = k (j x))` using `forall_congr' fun x => by rw [← hτ]; exact k.injective.eq_iff.symm`. Rewrite using `[← hfix, h1]`. Take `⟨d, hd⟩` from `hm`. Establish `hprim : IsPrimitiveRoot (k ζ ^ d) A.m` using `hkζ.pow (Nat.pos_of_ne_zero (NeZero.ne N)) (hd.trans (mul_comm _ _))`. Establish `e1` using `galChar_spec A.m σ (k ζ ^ d) hprim.pow_eq_one`.

Rewrite `e1` using `[map_pow, hσζ, ← pow_mul, mul_comm _ d, pow_mul]`. Establish `hfin : IsOfFinOrder (k ζ ^ d)` using `isOfFinOrder_iff_pow_eq_one.2 ⟨A.m, A.pos, hprim.pow_eq_one⟩`. Establish `hmod : (galChar Ω N σ : ZMod N).val ≡ (galChar Ω A.m σ : ZMod A.m).val [MOD A.m]`. Establish `h2` using `hfin.pow_eq_pow_iff_modEq.1 e1`. Rewrite `h2` using `[← hprim.eq_orderOf]`. Then use the resulting hypothesis.

Establish `hcast : (((galChar Ω N σ : ZMod N).val : ℕ) : ZMod A.m) = (galChar Ω A.m σ : ZMod A.m)`. Rewrite using `[(ZMod.natCast_eq_natCast_iff _ _ _).2 hmod, ZMod.natCast_zmod_val]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, hua⟩`. Establish `hu' : u = galChar Ω A.m σ` using `Units.ext (hua.trans hcast)`.

Conclude with `hu' ▸ hu`. Introduce `h`. Conclude with `⟨_, h, hcast.symm⟩`. Set `σ₀ : Ω →ₐ[ℚ] Ω` to `j.liftNormal Ω`. Establish `hσ₀ : ∀ x : L, σ₀ (algebraMap L Ω x) = k (j x)` using `fun x => j.liftNormal_commutes Ω x`.

Set `e : Ω ≃ₐ[ℚ] Ω` to `AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)`. Establish `he : ∀ x : L, e (algebraMap L Ω x) = k (j x)` using `hσ₀`. Establish `hconj : ∀ σ : G ℚ Ω, galChar Ω A.m (e * σ * e⁻¹) = galChar Ω A.m σ`. Introduce `σ`. Rewrite using `[map_mul, map_mul, map_inv, mul_comm (galChar Ω A.m e), mul_assoc, mul_inv_cancel, mul_one]`.

Use extensionality with `σ`. Express the relevant statement in the definitionally equal form `(∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x) ↔ galChar Ω A.m σ ∈ A.H`. Rewrite using `[← hconj σ, ← key]`. Use `forall_congr' fun x => ?_` and prove the remaining obligations. Rewrite using `[← he, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply, e.injective.eq_iff]`.
-/
theorem UpperTheory.V.Two.abField :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : AbF) (L : Type) [Field L] [NumberField L] [Algebra L Ω], IsAbField A L → galOf ℚ L Ω = abU Ω A := by
  intro Ω _ _ _ A L _ _ _ hL
  obtain ⟨N, hN, j, ζ, hm, hζ, hj⟩ := hL
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Normal ℚ (CyclotomicField N ℚ) := by
    haveI : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.2 (NeZero.ne N)⟩
    have h := CyclotomicField.isCyclotomicExtension (n := N) (K := ℚ)
    have h2 := (@IsCyclotomicExtension.isGalois _ _ _ _ _ _ h).to_normal
    convert h2
    exact Subsingleton.elim _ _
  let k : CyclotomicField N ℚ →ₐ[ℚ] Ω := IsAlgClosed.lift
  letI : Algebra (CyclotomicField N ℚ) Ω := k.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (CyclotomicField N ℚ) Ω :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsScalarTower ℚ L Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have key : ∀ σ : G ℚ Ω, (∀ x : L, σ (k (j x)) = k (j x)) ↔ galChar Ω A.m σ ∈ A.H := by
    intro σ
    let τ := σ.restrictNormal (CyclotomicField N ℚ)
    have hτ : ∀ y, k (τ y) = σ (k y) := fun y => σ.restrictNormal_commutes (CyclotomicField N ℚ) y
    have hkζ : IsPrimitiveRoot (k ζ) N := hζ.map_of_injective k.injective
    have hσζ : σ (k ζ) = k ζ ^ (galChar Ω N σ : ZMod N).val :=
      galChar_spec N σ (k ζ) hkζ.pow_eq_one
    have hτζ : τ ζ = ζ ^ (galChar Ω N σ : ZMod N).val := by
      apply k.injective
      show k (τ ζ) = k (ζ ^ _)
      rw [hτ, hσζ, map_pow]
    have h1 := hj τ _ hτζ
    have hfix : (∀ x : L, τ (j x) = j x) ↔ (∀ x : L, σ (k (j x)) = k (j x)) :=
      forall_congr' fun x => by rw [← hτ]; exact k.injective.eq_iff.symm
    rw [← hfix, h1]
    obtain ⟨d, hd⟩ := hm
    have hprim : IsPrimitiveRoot (k ζ ^ d) A.m :=
      hkζ.pow (Nat.pos_of_ne_zero (NeZero.ne N)) (hd.trans (mul_comm _ _))
    have e1 := galChar_spec A.m σ (k ζ ^ d) hprim.pow_eq_one
    rw [map_pow, hσζ, ← pow_mul, mul_comm _ d, pow_mul] at e1
    have hfin : IsOfFinOrder (k ζ ^ d) := isOfFinOrder_iff_pow_eq_one.2 ⟨A.m, A.pos, hprim.pow_eq_one⟩
    have hmod : (galChar Ω N σ : ZMod N).val ≡ (galChar Ω A.m σ : ZMod A.m).val [MOD A.m] := by
      have h2 := hfin.pow_eq_pow_iff_modEq.1 e1
      rwa [← hprim.eq_orderOf] at h2
    have hcast : (((galChar Ω N σ : ZMod N).val : ℕ) : ZMod A.m) = (galChar Ω A.m σ : ZMod A.m) := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hmod, ZMod.natCast_zmod_val]
    constructor
    · rintro ⟨u, hu, hua⟩
      have hu' : u = galChar Ω A.m σ := Units.ext (hua.trans hcast)
      exact hu' ▸ hu
    · intro h
      exact ⟨_, h, hcast.symm⟩
  let σ₀ : Ω →ₐ[ℚ] Ω := j.liftNormal Ω
  have hσ₀ : ∀ x : L, σ₀ (algebraMap L Ω x) = k (j x) := fun x => j.liftNormal_commutes Ω x
  let e : Ω ≃ₐ[ℚ] Ω := AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)
  have he : ∀ x : L, e (algebraMap L Ω x) = k (j x) := hσ₀
  have hconj : ∀ σ : G ℚ Ω, galChar Ω A.m (e * σ * e⁻¹) = galChar Ω A.m σ := by
    intro σ
    rw [map_mul, map_mul, map_inv, mul_comm (galChar Ω A.m e), mul_assoc, mul_inv_cancel, mul_one]
  ext σ
  change (∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x) ↔ galChar Ω A.m σ ∈ A.H
  rw [← hconj σ, ← key]
  refine forall_congr' fun x => ?_
  rw [← he, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply,
    e.injective.eq_iff]
