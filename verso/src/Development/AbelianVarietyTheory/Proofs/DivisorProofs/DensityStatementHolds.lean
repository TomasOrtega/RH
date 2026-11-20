import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPointThrough
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsMaximalTensorProductOfIsLocalHom
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.InjectiveAlgebraMapOfDvrOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingPadicComplexInt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

open IsLocalRing in

/- English proof (translation)
Establish `hq : (q : T.V) ∈ maximalIdeal T.V`. Assume the negation of the conclusion as `h`. Establish `hu : IsUnit (q : T.V)`. Assume the negation of the conclusion as `h'`. Conclude with `h ((mem_maximalIdeal _).2 h')`.

Establish `hu' : IsUnit (q : 𝓞_ℂ_[q])` using `by simpa using hu.map kO`. Establish `h1` using `(PadicComplexInt.integers q).isUnit_iff_valuation_eq_one.1 hu'`. Rewrite `h1` using `[map_natCast]`. Establish `h2 : ‖(q : ℂ_[q])‖ = 1` using `by rw [← coe_valued, h1]; rfl`. Establish `h3 : (q : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] (q : ℚ_[q])` using `by simp`.

Rewrite `h2` using `[h3, norm_algebraMap', Padic.norm_p]`. Establish `: (1 : ℝ) < q` using `by exact_mod_cast (Fact.out : q.Prime).one_lt`. Conclude with `absurd h2 (ne_of_lt (inv_lt_one_of_one_lt₀ this))`. Assume the negation of the conclusion as `hne`. Establish `hc : IsCoprime (p : ℤ) (q : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes Fact.out Fact.out).2 hne)`.

Take `⟨a, b, hab⟩` from `hc`. Establish `h1 : ((a * p + b * q : ℤ) : T.V) ∈ maximalIdeal T.V`. Use `push_cast`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hq)`. Rewrite `h1` using `[hab, Int.cast_one]`.

Conclude with `(maximalIdeal.isMaximal T.V).ne_top ((Ideal.eq_top_iff_one _).2 h1)`.
-/
theorem eq_of_mem_maximalIdeal_of_padicComplexInt (T : CDVR) (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : (p : T.V) ∈ maximalIdeal T.V) (kO : T.V →+* 𝓞_ℂ_[q]) : p = q := by
  have hq : (q : T.V) ∈ maximalIdeal T.V := by
    by_contra h
    have hu : IsUnit (q : T.V) := by
      by_contra h'
      exact h ((mem_maximalIdeal _).2 h')
    have hu' : IsUnit (q : 𝓞_ℂ_[q]) := by simpa using hu.map kO
    have h1 := (PadicComplexInt.integers q).isUnit_iff_valuation_eq_one.1 hu'
    rw [map_natCast] at h1
    have h2 : ‖(q : ℂ_[q])‖ = 1 := by rw [← coe_valued, h1]; rfl
    have h3 : (q : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] (q : ℚ_[q]) := by simp
    rw [h3, norm_algebraMap', Padic.norm_p] at h2
    have : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
    exact absurd h2 (ne_of_lt (inv_lt_one_of_one_lt₀ this))
  by_contra hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes Fact.out Fact.out).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : ((a * p + b * q : ℤ) : T.V) ∈ maximalIdeal T.V := by
    push_cast
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hq)
  rw [hab, Int.cast_one] at h1
  exact (maximalIdeal.isMaximal T.V).ne_top ((Ideal.eq_top_iff_one _).2 h1)

/- English proof (translation)
Establish `hp0 : p ≠ 0` using `(Fact.out : p.Prime).ne_zero`. Take `⟨hdvr, hfin⟩` from `GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V hp0 hp`. Use `haveI := hdvr`. Set `O'` to `AdicCompletion (IsLocalRing.maximalIdeal V) V`. Establish `hinj0 : Function.Injective (algebraMap V O')` using `GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V`.

Use `haveI : CharZero V := inferInstance`. Use `haveI : CharZero O' := charZero_of_injective_algebraMap hinj0`. Use `haveI : IsLocalHom (algebraMap V O') := inferInstance`. Establish `hsp : Ideal.map (algebraMap V R) (IsLocalRing.maximalIdeal V) ≤ M`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Use `haveI : (Ideal.comap (algebraMap V R) M).IsPrime := Ideal.comap_isPrime _ _`. Establish `hne : Ideal.comap (algebraMap V R) M ≠ ⊥`. Introduce `h`. Establish `: ((p : V)) ∈ Ideal.comap (algebraMap V R) M`. Rewrite using `[Ideal.mem_comap, map_natCast]`.

Conclude with `hpM`. Rewrite `this` using `[h, Ideal.mem_bot]`. Conclude with `hp0 (by exact_mod_cast this)`. Establish `hmax` using `Ideal.IsPrime.isMaximal inferInstance hne`. Rewrite using `[IsLocalRing.eq_maximalIdeal hmax]`.

Take `⟨V', i1, i2, i3, i4, i5, φ, -, hφe, hφM⟩` from `GlobalTheory.exists_integral_point_of_complete_case (fun O B _ _ _ _ _ _ _ _ _ _ M hM hsp e he => GlobalTheory.exists_integral_point_through O B M hM hsp e he) V O' hinj0 R hinj M hM.ne_top hsp e he`. Take `⟨-, -, hcpl, hch, hfin'⟩` from `GlobalTheory.dvr_finite_over_complete_dvr O' V'`. Set `T : CDVR` to `{ V := V' }`. Establish `hT : T.FinRes` using `hfin' (Finite.of_surjective _ (AdicCompletion.residueField_map_bijective V).2)`. Take `⟨q, hq, k, kO, hk⟩` from `GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hT`.

Establish `hpT : (p : T.V) ∈ IsLocalRing.maximalIdeal T.V`. Use `hφM _ hpM` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Take `rfl` from `eq_of_mem_maximalIdeal_of_padicComplexInt T p q hpT kO`. Use `⟨T, kO, φ, hT, fun a b hab => ?_, hφe⟩` and prove the remaining obligations.

Apply `IsFractionRing.injective T.V T.Fr` to reduce the goal to its premises. Apply `k.injective` to reduce the goal to its premises. Rewrite using `[← hk, ← hk, hab]`.
-/
theorem exists_cdvr_point (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime]
    (hp : (p : F) ∈ V.nonunits) (R : Type) [CommRing R] [IsDomain R] [Algebra V R] [Algebra.FiniteType V R]
    (hinj : Function.Injective (algebraMap V R)) (M : Ideal R) (hM : M.IsMaximal) (hpM : (p : R) ∈ M) (e : R)
    (he : e ≠ 0) :
    ∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (φ : R →+* T.V), T.FinRes ∧ Function.Injective kO ∧ φ e ≠ 0 := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨hdvr, hfin⟩ := GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V hp0 hp
  haveI := hdvr
  let O' := AdicCompletion (IsLocalRing.maximalIdeal V) V
  have hinj0 : Function.Injective (algebraMap V O') := GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V
  haveI : CharZero V := inferInstance
  haveI : CharZero O' := charZero_of_injective_algebraMap hinj0
  haveI : IsLocalHom (algebraMap V O') := inferInstance
  have hsp : Ideal.map (algebraMap V R) (IsLocalRing.maximalIdeal V) ≤ M := by
    rw [Ideal.map_le_iff_le_comap]
    haveI : (Ideal.comap (algebraMap V R) M).IsPrime := Ideal.comap_isPrime _ _
    have hne : Ideal.comap (algebraMap V R) M ≠ ⊥ := by
      intro h
      have : ((p : V)) ∈ Ideal.comap (algebraMap V R) M := by
        rw [Ideal.mem_comap, map_natCast]; exact hpM
      rw [h, Ideal.mem_bot] at this
      exact hp0 (by exact_mod_cast this)
    have hmax := Ideal.IsPrime.isMaximal inferInstance hne
    rw [IsLocalRing.eq_maximalIdeal hmax]
  obtain ⟨V', i1, i2, i3, i4, i5, φ, -, hφe, hφM⟩ := GlobalTheory.exists_integral_point_of_complete_case
    (fun O B _ _ _ _ _ _ _ _ _ _ M hM hsp e he => GlobalTheory.exists_integral_point_through O B M hM hsp e he)
    V O' hinj0 R hinj M hM.ne_top hsp e he
  obtain ⟨-, -, hcpl, hch, hfin'⟩ := GlobalTheory.dvr_finite_over_complete_dvr O' V'
  let T : CDVR := { V := V' }
  have hT : T.FinRes := hfin' (Finite.of_surjective _ (AdicCompletion.residueField_map_bijective V).2)
  obtain ⟨q, hq, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hT
  have hpT : (p : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    have := hφM _ hpM
    rwa [map_natCast] at this
  obtain rfl := eq_of_mem_maximalIdeal_of_padicComplexInt T p q hpT kO
  refine ⟨T, kO, φ, hT, fun a b hab => ?_, hφe⟩
  apply IsFractionRing.injective T.V T.Fr
  apply k.injective
  rw [← hk, ← hk, hab]

/- English proof (translation)
Introduce `F _ _ V p _ hp X s Xw hX hflat hlft hXw hne R _ ξ hξ hsp`. Take `⟨x, ⟨y, rfl⟩, hx⟩` from `hsp`. Use `haveI : Nonempty (Sp R) := ⟨y⟩`. Use `haveI : IsIntegral (Sp R) := isIntegral_of_isOpenImmersion ξ`. Use `haveI : IsDomain R := (affine_isIntegral_iff (CommRingCat.of R)).1 inferInstance`.

Set `f : V →+* R` to `(Spec.preimage (ξ ≫ s)).hom`. Use `letI : Algebra V R := f.toAlgebra`. Use `haveI : Algebra.FiniteType V R := by`. Establish `h : LocallyOfFiniteType (ξ ≫ s)` using `inferInstance`. Rewrite `h` using `[← Spec.map_preimage (ξ ≫ s)]`.

Conclude with `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h`. Establish `hinj : Function.Injective (algebraMap V R)`. Establish `h : Flat (ξ ≫ s)` using `inferInstance`. Rewrite `h` using `[← Spec.map_preimage (ξ ≫ s)]`. Use `haveI : Module.Flat V R := (HasRingHomProperty.Spec_iff (P := @Flat)).1 h`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `h0`. Establish `hreg` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) (mem_nonZeroDivisors_of_ne_zero h0)`. Establish `h1 : a • (1 : R) = a • (0 : R)` using `by rw [Algebra.smul_def, _root_.mul_one, ha, smul_zero]`.

Conclude with `one_ne_zero (hreg h1)`. Establish `hopen : IsOpen (Set.range ξ)` using `ξ.isOpenEmbedding.isOpen_range`. Take `⟨_, ⟨z, rfl⟩, hz⟩` from `nonempty_preirreducible_inter hopen Xw.isOpen ⟨_, y, rfl⟩ hne`. Establish `hzO : z ∈ ξ ⁻¹ᵁ Xw` using `hz`. Take `⟨_, ⟨e, rfl⟩, hze, hsub⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hzO (ξ ⁻¹ᵁ Xw).isOpen`.

Establish `he : e ≠ 0`. Introduce and unpack `rfl`. Conclude with `(PrimeSpectrum.mem_basicOpen _ _).1 hze (Ideal.zero_mem _)`. Establish `hpy : (p : R) ∈ (y : PrimeSpectrum R).asIdeal`. Establish `h1 : y ∉ ξ ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤))` using `hx`.

Rewrite `h1` using `[Scheme.preimage_basicOpen_top, map_natCast]`. Establish `h2 : ((p : Γ(Sp R, ⊤))) = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (p : R)` using `(map_natCast _ _).symm`. Rewrite `h1` using `[h2, basicOpen_eq_of_affine]`. Assume the negation of the conclusion as `h3`. Conclude with `h1 ((PrimeSpectrum.mem_basicOpen _ _).2 h3)`.

Take `⟨M, hM, hyM⟩` from `Ideal.exists_le_maximal _ (y : PrimeSpectrum R).isPrime.ne_top`. Take `⟨T, kO, φ, hT, hkO, hφe⟩` from `exists_cdvr_point F V p hp R hinj M hM (hyM hpy) e he`. Use `⟨kO.comp φ, ⟨T, kO, spMap φ ≫ ξ, hT, hkO, sp_sp _ _ _⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`. Establish `hw : w = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ_[p])`.

Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use `haveI := (w : PrimeSpectrum ℂ_[p]).isPrime`. Conclude with `Ideal.eq_bot_of_prime _`. Substitute `hw` using the available equality. Establish `hinj2 : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO)` using `Subtype.val_injective.comp hkO`.

Rewrite using `[← sp_sp φ kO ξ, sp_sp kO (algebraMap 𝓞_ℂ_[p] ℂ_[p]) (spMap φ ≫ ξ), bot_map hinj2 (spMap φ ≫ ξ)]`. Establish `hq : (spMap φ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.V) ∈ PrimeSpectrum.basicOpen e` using `by show e ∉ Ideal.comap φ ⊥`. Simplify using `using hφe`. Conclude with `hsub hq`.
-/
theorem densSt : DensSt := by
  intro F _ _ V p _ hp X s Xw hX hflat hlft hXw hne R _ ξ hξ hsp
  obtain ⟨x, ⟨y, rfl⟩, hx⟩ := hsp
  haveI : Nonempty (Sp R) := ⟨y⟩
  haveI : IsIntegral (Sp R) := isIntegral_of_isOpenImmersion ξ
  haveI : IsDomain R := (affine_isIntegral_iff (CommRingCat.of R)).1 inferInstance
  let f : V →+* R := (Spec.preimage (ξ ≫ s)).hom
  letI : Algebra V R := f.toAlgebra
  haveI : Algebra.FiniteType V R := by
    have h : LocallyOfFiniteType (ξ ≫ s) := inferInstance
    rw [← Spec.map_preimage (ξ ≫ s)] at h
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  have hinj : Function.Injective (algebraMap V R) := by
    have h : Flat (ξ ≫ s) := inferInstance
    rw [← Spec.map_preimage (ξ ≫ s)] at h
    haveI : Module.Flat V R := (HasRingHomProperty.Spec_iff (P := @Flat)).1 h
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) (mem_nonZeroDivisors_of_ne_zero h0)
    have h1 : a • (1 : R) = a • (0 : R) := by rw [Algebra.smul_def, _root_.mul_one, ha, smul_zero]
    exact one_ne_zero (hreg h1)
  have hopen : IsOpen (Set.range ξ) := ξ.isOpenEmbedding.isOpen_range
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := nonempty_preirreducible_inter hopen Xw.isOpen ⟨_, y, rfl⟩ hne
  have hzO : z ∈ ξ ⁻¹ᵁ Xw := hz
  obtain ⟨_, ⟨e, rfl⟩, hze, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hzO (ξ ⁻¹ᵁ Xw).isOpen
  have he : e ≠ 0 := by
    rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hze (Ideal.zero_mem _)
  have hpy : (p : R) ∈ (y : PrimeSpectrum R).asIdeal := by
    have h1 : y ∉ ξ ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤)) := hx
    rw [Scheme.preimage_basicOpen_top, map_natCast] at h1
    have h2 : ((p : Γ(Sp R, ⊤))) = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (p : R) := (map_natCast _ _).symm
    rw [h2, basicOpen_eq_of_affine] at h1
    by_contra h3
    exact h1 ((PrimeSpectrum.mem_basicOpen _ _).2 h3)
  obtain ⟨M, hM, hyM⟩ := Ideal.exists_le_maximal _ (y : PrimeSpectrum R).isPrime.ne_top
  obtain ⟨T, kO, φ, hT, hkO, hφe⟩ := exists_cdvr_point F V p hp R hinj M hM (hyM hpy) e he
  refine ⟨kO.comp φ, ⟨T, kO, spMap φ ≫ ξ, hT, hkO, sp_sp _ _ _⟩, ?_⟩
  rintro _ ⟨w, rfl⟩
  have hw : w = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ_[p]) := by
    apply PrimeSpectrum.ext
    haveI := (w : PrimeSpectrum ℂ_[p]).isPrime
    exact Ideal.eq_bot_of_prime _
  subst hw
  have hinj2 : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO) := Subtype.val_injective.comp hkO
  rw [← sp_sp φ kO ξ, sp_sp kO (algebraMap 𝓞_ℂ_[p] ℂ_[p]) (spMap φ ≫ ξ), bot_map hinj2 (spMap φ ≫ ξ)]
  have hq : (spMap φ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.V) ∈ PrimeSpectrum.basicOpen e := by
    show e ∉ Ideal.comap φ ⊥
    simpa using hφe
  exact hsub hq

end GlobalTheory.FlatModel

end
