import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPointLengthFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoheightEqOneOfDimClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLineBundleSectionsGenerateIdealSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DimOfIsArithVar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ.VertBase

/- English proof (translation)
Take `⟨M, hM⟩` from `Ideal.exists_maximal R`. Establish `hP : (⟨M, hM.isPrime⟩ : PrimeSpectrum R) = ⟨⊥, Ideal.isPrime_bot⟩` using `Subsingleton.elim _ _`. Establish `hMb : M = ⊥` using `congrArg PrimeSpectrum.asIdeal hP`. Conclude with `Ring.isField_iff_maximal_bot.mpr (hMb ▸ hM)`.
-/
theorem isField_of_subsingleton_primeSpectrum {R : Type} [CommRing R] [IsDomain R]
    (h : Subsingleton (PrimeSpectrum R)) : IsField R := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal R
  have hP : (⟨M, hM.isPrime⟩ : PrimeSpectrum R) = ⟨⊥, Ideal.isPrime_bot⟩ := Subsingleton.elim _ _
  have hMb : M = ⊥ := congrArg PrimeSpectrum.asIdeal hP
  exact Ring.isField_iff_maximal_bot.mpr (hMb ▸ hM)

variable (Z : Scheme.{0}) [IsIntegral Z]

/- English proof (translation)
Establish `hle : Order.krullDim (IrreducibleCloseds Z) ≤ 0`. Establish `h0` using `hd`. Simplify using `only [topologicalKrullDim] at h0`. Rewrite using `[h0]`. Simplify using the standard rewrite rules.

Establish `hmax` using `Order.krullDim_nonpos_iff_forall_isMax.mp hle`. Set `C : IrreducibleCloseds Z` to `⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩`. Set `U : IrreducibleCloseds Z` to `⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩`. Establish `h1 : C ≤ U` using `fun _ _ => Set.mem_univ _`. Establish `h2 : U ≤ C` using `hmax C h1`.

Establish `hg : genericPoint Z ∈ closure ({x} : Set Z)` using `h2 (Set.mem_univ _)`. Establish `hs1 : x ⤳ genericPoint Z` using `specializes_iff_mem_closure.mpr hg`. Establish `hs2 : genericPoint Z ⤳ x` using `(genericPoint_spec Z).specializes (Set.mem_univ x)`. Conclude with `(hs1.antisymm hs2).eq`.
-/
theorem eq_genericPoint (hd : topologicalKrullDim Z = (0 : ℕ)) (x : Z) : x = genericPoint Z := by
  have hle : Order.krullDim (IrreducibleCloseds Z) ≤ 0 := by
    have h0 := hd
    simp only [topologicalKrullDim] at h0
    rw [h0]
    simp
  have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp hle
  let C : IrreducibleCloseds Z := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let U : IrreducibleCloseds Z := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  have h1 : C ≤ U := fun _ _ => Set.mem_univ _
  have h2 : U ≤ C := hmax C h1
  have hg : genericPoint Z ∈ closure ({x} : Set Z) := h2 (Set.mem_univ _)
  have hs1 : x ⤳ genericPoint Z := specializes_iff_mem_closure.mpr hg
  have hs2 : genericPoint Z ⤳ x := (genericPoint_spec Z).specializes (Set.mem_univ x)
  exact (hs1.antisymm hs2).eq

/- English proof (translation)
Take `⟨U, hU, hxU, -⟩` from `exists_isAffineOpen_mem_and_subset (show genericPoint Z ∈ (⊤ : Z.Opens) from Set.mem_univ _)`. Establish `hUt : U = ⊤` using `eq_top_iff.mpr fun y _ => by rw [eq_genericPoint Z hd y]; exact hxU`. Conclude with `hUt ▸ hU`.
-/
theorem isAffineOpen_top (hd : topologicalKrullDim Z = (0 : ℕ)) : IsAffineOpen (⊤ : Z.Opens) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint Z ∈ (⊤ : Z.Opens) from Set.mem_univ _)
  have hUt : U = ⊤ := eq_top_iff.mpr fun y _ => by rw [eq_genericPoint Z hd y]; exact hxU
  exact hUt ▸ hU

/- English proof (translation)
Establish `hA` using `isAffineOpen_top Z hd`. Establish `hsub : Subsingleton (PrimeSpectrum Γ(Z, ⊤))`. Prove the components needed by the constructor for the conclusion. Introduce `p q`. Conclude with `hA.fromSpec.isOpenEmbedding.injective ((eq_genericPoint Z hd _).trans (eq_genericPoint Z hd _).symm)`.

Conclude with `isField_of_subsingleton_primeSpectrum hsub`.
-/
theorem isField_top (hd : topologicalKrullDim Z = (0 : ℕ)) : IsField Γ(Z, ⊤) := by
  have hA := isAffineOpen_top Z hd
  have hsub : Subsingleton (PrimeSpectrum Γ(Z, ⊤)) := by
    constructor
    intro p q
    exact hA.fromSpec.isOpenEmbedding.injective
      ((eq_genericPoint Z hd _).trans (eq_genericPoint Z hd _).symm)
  exact isField_of_subsingleton_primeSpectrum hsub

/- English proof (translation)
Establish `hF` using `isField_top Z hd`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `h`.

Take `⟨b, hb⟩` from `hF.mul_inv_cancel h`. Establish `h1` using `congrArg ((IsLocalRing.residue (Z.presheaf.stalk (genericPoint Z))).comp (algebraMap Γ(Z, ⊤) Z.functionField)) hb`. Rewrite `h1` using `[map_mul, ha, zero_mul, map_one]`. Conclude with `zero_ne_one h1`. Introduce `y`.

Take `⟨t, rfl⟩` from `IsLocalRing.residue_surjective y`. Take `⟨U, hm, s, hs⟩` from `Z.presheaf.exists_germ_eq t`. Establish `hU : U = ⊤` using `eq_top_iff.mpr fun x _ => by rw [eq_genericPoint Z hd x]; exact hm`. Substitute `hU` using the available equality. Conclude with `⟨s, by rw [RingHom.comp_apply, ← hs]; rfl⟩`.
-/
theorem bijective_top (hd : topologicalKrullDim Z = (0 : ℕ)) :
    Function.Bijective ((IsLocalRing.residue (Z.presheaf.stalk (genericPoint Z))).comp
      (algebraMap Γ(Z, ⊤) Z.functionField)) := by
  have hF := isField_top Z hd
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel h
    have h1 := congrArg ((IsLocalRing.residue (Z.presheaf.stalk (genericPoint Z))).comp
      (algebraMap Γ(Z, ⊤) Z.functionField)) hb
    rw [map_mul, ha, zero_mul, map_one] at h1
    exact zero_ne_one h1
  · intro y
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨U, hm, s, hs⟩ := Z.presheaf.exists_germ_eq t
    have hU : U = ⊤ := eq_top_iff.mpr fun x _ => by rw [eq_genericPoint Z hd x]; exact hm
    subst hU
    exact ⟨s, by rw [RingHom.comp_apply, ← hs]; rfl⟩

/- English proof (translation)
Introduce `m n Z _ f _ p _ _ hd a`. Establish `hp : p.Prime` using `Fact.out`. Establish `hA` using `isAffineOpen_top Z hd`. Use `haveI : IsAffine (⊤ : Z.Opens) := hA`. Use `haveI : IsAffine Z := by first`.

Consider the case `exact IsAffine.of_isIso Z.topIso.inv`. Consider the case `exact isAffine_of_isIso Z.topIso.inv`. Consider the case `exact AlgebraicGeometry.isAffineOpen_top_iff.mp hA`. Consider the case `exact (AlgebraicGeometry.isAffineOpen_top_iff Z).mp hA`. Consider the case `exact IsAffine.of_isIso (Scheme.topIso Z).inv`.

Consider the case `exact hA.isAffine_of_top`. Rewrite using `[GlobalTheory.chi_structureModule_of_isAffine Z (ZMod p)]`. Establish `hb` using `bijective_top Z hd`. Establish `hRes : CharP (Z.residueField (genericPoint Z)) p` using `(RingHom.charP_iff_charP (((IsLocalRing.residue (Z.presheaf.stalk (genericPoint Z))).comp (algebraMap Γ(Z, ⊤) Z.functionField)).comp (algebraMap (ZMod p) Γ(Z, ⊤))) p).mp inferInstance`. Use `haveI hΩ : CharP ((MP ℤ m n).residueField (f (genericPoint Z))) p := (RingHom.charP_iff_charP (f.residueFieldMap (genericPoint Z)).hom p).mpr hRes`.

Establish `hcomap : (ptIdeal (f (genericPoint Z))).comap (C : ℤ →+* MRing (Bk n)) = Ideal.span {(p : ℤ)}`. Use extensionality with `z`. Rewrite using `[Ideal.mem_comap, Ideal.mem_span_singleton, ← CharP.intCast_eq_zero_iff ((MP ℤ m n).residueField (f (genericPoint Z))) p]`. Simplify using `only [ptIdeal, ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap, MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply, MvPolynomial.C_eq_zero, eq_intCast]`. Rewrite using `[map_intCast, ← map_intCast (MvPolynomial.C : (MP ℤ m n).residueField (f (genericPoint Z)) →+* MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField (f (genericPoint Z)))), MvPolynomial.C_eq_zero]`.

Establish `hchar : charOf (ptIdeal (f (genericPoint Z))) = p`. Establish `key : ∀ I : Ideal ℤ, I = Ideal.span {(p : ℤ)} → (Submodule.IsPrincipal.generator I).natAbs = p`. Introduce and unpack `I rfl`. Establish `hg` using `Submodule.IsPrincipal.span_singleton_generator (Ideal.span {(p : ℤ)})`. Establish `hass : Associated (Submodule.IsPrincipal.generator (Ideal.span {(p : ℤ)})) (p : ℤ)` using `Ideal.span_singleton_eq_span_singleton.mp hg`.

Rewrite using `[Int.natAbs_eq_iff_associated.mpr hass]`. Simplify using the standard rewrite rules. Conclude with `key _ hcomap`. Establish `hcl : topologicalKrullDim (closure ({genericPoint Z} : Set Z)) = (0 : ℕ)` using `(dim_closure_generic Z).trans hd`. Establish `hL` using `GlobalTheory.T.mixed_point_length_formula m n Z f (genericPoint Z) hcl a`.

Rewrite `hL` using `[hchar]`. Establish `hcard : Nat.card (Z.residueField (genericPoint Z)) = Nat.card Γ(Z, ⊤)` using `(Nat.card_eq_of_bijective _ hb).symm`. Rewrite `hL` using `[hcard]`. Establish `hlogp : Real.log p ≠ 0` using `(Real.log_pos (by exact_mod_cast hp.one_lt)).ne'`. Distinguish the cases in `hfin : Module.Finite (ZMod p) Γ(Z, ⊤)`.

Rewrite `hL` using `[Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, Nat.cast_pow, Real.log_pow]`. Establish `hg : (geoNum 0 (ptIdeal (f (genericPoint Z))) a : ℝ) = (Module.finrank (ZMod p) Γ(Z, ⊤) : ℝ)` using `mul_right_cancel₀ hlogp hL`. Conclude with `hg.symm` after adjusting the coercions. Rewrite using `[Module.finrank_of_not_finite hfin] haveI : Infinite Γ(Z, ⊤) := by`. Assume the negation of the conclusion as `hinf`.

Rewrite `hinf` using `[not_infinite_iff_finite]`. Conclude with `hfin Module.Finite.of_finite`. Rewrite `hL` using `[Nat.card_eq_zero_of_infinite, Nat.cast_zero, Real.log_zero]`. Establish `hg : (geoNum 0 (ptIdeal (f (genericPoint Z))) a : ℝ) = 0`. Break down `mul_eq_zero.mp hL with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h hlogp`. Conclude with `hg.symm` after adjusting the coercions.
-/
theorem chi_eq_geoNum : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n)
    [IsClosedImmersion f] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) Γ(Z, ⊤)],
    topologicalKrullDim Z = (0 : ℕ) → ∀ a : Fin 0 → Fin (m + 1) → ℤ,
      chi (ZMod p) (structureModule Z) = geoNum 0 (ptIdeal (f (genericPoint Z))) a := by
  intro m n Z _ f _ p _ _ hd a
  have hp : p.Prime := Fact.out
  have hA := isAffineOpen_top Z hd
  haveI : IsAffine (⊤ : Z.Opens) := hA
  haveI : IsAffine Z := by
    first
      | exact IsAffine.of_isIso Z.topIso.inv
      | exact isAffine_of_isIso Z.topIso.inv
      | exact AlgebraicGeometry.isAffineOpen_top_iff.mp hA
      | exact (AlgebraicGeometry.isAffineOpen_top_iff Z).mp hA
      | exact IsAffine.of_isIso (Scheme.topIso Z).inv
      | exact hA.isAffine_of_top
  rw [GlobalTheory.chi_structureModule_of_isAffine Z (ZMod p)]
  have hb := bijective_top Z hd
  have hRes : CharP (Z.residueField (genericPoint Z)) p :=
    (RingHom.charP_iff_charP (((IsLocalRing.residue (Z.presheaf.stalk (genericPoint Z))).comp
      (algebraMap Γ(Z, ⊤) Z.functionField)).comp (algebraMap (ZMod p) Γ(Z, ⊤))) p).mp inferInstance
  haveI hΩ : CharP ((MP ℤ m n).residueField (f (genericPoint Z))) p :=
    (RingHom.charP_iff_charP (f.residueFieldMap (genericPoint Z)).hom p).mpr hRes
  have hcomap : (ptIdeal (f (genericPoint Z))).comap (C : ℤ →+* MRing (Bk n)) =
      Ideal.span {(p : ℤ)} := by
    ext z
    rw [Ideal.mem_comap, Ideal.mem_span_singleton,
      ← CharP.intCast_eq_zero_iff ((MP ℤ m n).residueField (f (genericPoint Z))) p]
    simp only [ptIdeal, ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply, MvPolynomial.C_eq_zero, eq_intCast]
    rw [map_intCast, ← map_intCast (MvPolynomial.C : (MP ℤ m n).residueField (f (genericPoint Z)) →+*
      MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField (f (genericPoint Z)))), MvPolynomial.C_eq_zero]
  have hchar : charOf (ptIdeal (f (genericPoint Z))) = p := by
    have key : ∀ I : Ideal ℤ, I = Ideal.span {(p : ℤ)} →
        (Submodule.IsPrincipal.generator I).natAbs = p := by
      rintro I rfl
      have hg := Submodule.IsPrincipal.span_singleton_generator (Ideal.span {(p : ℤ)})
      have hass : Associated (Submodule.IsPrincipal.generator (Ideal.span {(p : ℤ)})) (p : ℤ) :=
        Ideal.span_singleton_eq_span_singleton.mp hg
      rw [Int.natAbs_eq_iff_associated.mpr hass]
      simp
    exact key _ hcomap
  have hcl : topologicalKrullDim (closure ({genericPoint Z} : Set Z)) = (0 : ℕ) :=
    (dim_closure_generic Z).trans hd
  have hL := GlobalTheory.T.mixed_point_length_formula m n Z f (genericPoint Z) hcl a
  rw [hchar] at hL
  have hcard : Nat.card (Z.residueField (genericPoint Z)) = Nat.card Γ(Z, ⊤) :=
    (Nat.card_eq_of_bijective _ hb).symm
  rw [hcard] at hL
  have hlogp : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  by_cases hfin : Module.Finite (ZMod p) Γ(Z, ⊤)
  · rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, Nat.cast_pow, Real.log_pow] at hL
    have hg : (geoNum 0 (ptIdeal (f (genericPoint Z))) a : ℝ) =
        (Module.finrank (ZMod p) Γ(Z, ⊤) : ℝ) := mul_right_cancel₀ hlogp hL
    exact_mod_cast hg.symm
  · rw [Module.finrank_of_not_finite hfin]
    haveI : Infinite Γ(Z, ⊤) := by
      by_contra hinf
      rw [not_infinite_iff_finite] at hinf
      exact hfin Module.Finite.of_finite
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, Real.log_zero] at hL
    have hg : (geoNum 0 (ptIdeal (f (genericPoint Z))) a : ℝ) = 0 := by
      rcases mul_eq_zero.mp hL with h | h
      · exact h
      · exact absurd h hlogp
    exact_mod_cast hg.symm

end GlobalTheory.CompanionTheory.MixZ.VertBase
