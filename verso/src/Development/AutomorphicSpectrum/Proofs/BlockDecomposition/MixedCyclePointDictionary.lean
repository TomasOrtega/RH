import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealHorizontalIffCharZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureDimIffArithmeticVarietyStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsHorizontal charOf)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ.PtDictProof

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

/- English proof (translation)
Rewrite using `[ptIdeal, ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap, MvPolynomial.aeval_C]`. Establish `h : (algebraMap ℤ (MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField x)) a) = MvPolynomial.C (a : (MP ℤ m n).residueField x)`. Simplify using the standard rewrite rules. Rewrite using `[h, MvPolynomial.C_eq_zero]`.
-/
theorem C_mem_ptIdeal_iff (x : MP ℤ m n) (a : ℤ) :
    (C a : MRing (Bk n)) ∈ ptIdeal x ↔ (a : (MP ℤ m n).residueField x) = 0 := by
  rw [ptIdeal, ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap,
    MvPolynomial.aeval_C]
  have h : (algebraMap ℤ (MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField x)) a) =
      MvPolynomial.C (a : (MP ℤ m n).residueField x) := by
    simp
  rw [h, MvPolynomial.C_eq_zero]

/- English proof (translation)
Rewrite using `[← Scheme.germ_residue, CommRingCat.hom_comp, RingHom.coe_comp]`. Use `Function.Injective.comp ?_ (germ_injective_of_isIntegral Z _ _)` and prove the remaining obligations. Conclude with `RingHom.injective (Z.residue (genericPoint Z)).hom`.
-/
theorem evaluation_generic_injective (Z : Scheme.{0}) [IsIntegral Z] :
    Function.Injective (Z.evaluation ⊤ (genericPoint Z) (Opens.mem_top _)).hom := by
  rw [← Scheme.germ_residue, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Injective.comp ?_ (germ_injective_of_isIntegral Z _ _)
  exact RingHom.injective (Z.residue (genericPoint Z)).hom

/- English proof (translation)
Establish `hg` using `(genericPoint_spec Z).image (f := j) j.isClosedEmbedding.continuous`. Establish `hcl : closure ({j (genericPoint Z)} : Set X) = Set.range j`. Establish `h1 : closure ({j (genericPoint Z)} : Set X) = closure (j '' Set.univ)` using `hg`. Rewrite using `[h1, Set.image_univ]`. Conclude with `j.isClosedEmbedding.isClosed_range.closure_eq`.

Rewrite using `[hcl]`. Conclude with `(IsHomeomorph.topologicalKrullDim_eq _ j.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm`.
-/
theorem dim_closure_image_generic {X Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ X) [IsClosedImmersion j] :
    topologicalKrullDim (closure ({j (genericPoint Z)} : Set X)) = topologicalKrullDim Z := by
  have hg := (genericPoint_spec Z).image (f := j) j.isClosedEmbedding.continuous
  have hcl : closure ({j (genericPoint Z)} : Set X) = Set.range j := by
    have h1 : closure ({j (genericPoint Z)} : Set X) = closure (j '' Set.univ) := hg
    rw [h1, Set.image_univ]
    exact j.isClosedEmbedding.isClosed_range.closure_eq
  rw [hcl]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    j.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h haveI : CharZero (Z.residueField (genericPoint Z)) := charZero_of_injective_ringHom (f := (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom) (RingHom.injective _)`. Conclude with `RingHom.charZero (Z.evaluation ⊤ (genericPoint Z) (Opens.mem_top _)).hom`. Introduce `h haveI : CharZero (Z.residueField (genericPoint Z)) := charZero_of_injective_ringHom (evaluation_generic_injective Z)`. Conclude with `RingHom.charZero (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom`.
-/
theorem charZero_residueField_iff {Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ MP ℤ m n) :
    CharZero ((MP ℤ m n).residueField (j (genericPoint Z))) ↔ CharZero Γ(Z, ⊤) := by
  constructor
  · intro h
    haveI : CharZero (Z.residueField (genericPoint Z)) :=
      charZero_of_injective_ringHom (f := (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom)
        (RingHom.injective _)
    exact RingHom.charZero (Z.evaluation ⊤ (genericPoint Z) (Opens.mem_top _)).hom
  · intro h
    haveI : CharZero (Z.residueField (genericPoint Z)) :=
      charZero_of_injective_ringHom (evaluation_generic_injective Z)
    exact RingHom.charZero (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom

/- English proof (translation)
Unfold `charOf`. Rewrite using `[← Int.prime_iff_natAbs_prime]`. Conclude with `Submodule.IsPrincipal.prime_generator_of_isPrime _ h`.
-/
theorem charOf_prime {P : Ideal (MRing (Bk n))} [P.IsPrime] (h : ¬ IsHorizontal P) : (charOf P).Prime := by
  unfold charOf
  rw [← Int.prime_iff_natAbs_prime]
  exact Submodule.IsPrincipal.prime_generator_of_isPrime _ h

/- English proof (translation)
Establish `hg` using `Submodule.IsPrincipal.generator_mem (P.comap (C : ℤ →+* MRing (Bk n)))`. Take `⟨c, hc⟩` from `Int.dvd_natAbs.mpr (dvd_refl (Submodule.IsPrincipal.generator (P.comap (C : ℤ →+* MRing (Bk n)))))`. Establish `hmem : ((charOf P : ℕ) : ℤ) ∈ P.comap (C : ℤ →+* MRing (Bk n))`. Unfold `charOf`. Rewrite using `[hc]`.

Conclude with `Ideal.mul_mem_right c _ hg`. Conclude with `Ideal.mem_comap.mp hmem`.
-/
theorem C_charOf_mem (P : Ideal (MRing (Bk n))) : (C ((charOf P : ℕ) : ℤ) : MRing (Bk n)) ∈ P := by
  have hg := Submodule.IsPrincipal.generator_mem (P.comap (C : ℤ →+* MRing (Bk n)))
  obtain ⟨c, hc⟩ := Int.dvd_natAbs.mpr
    (dvd_refl (Submodule.IsPrincipal.generator (P.comap (C : ℤ →+* MRing (Bk n)))))
  have hmem : ((charOf P : ℕ) : ℤ) ∈ P.comap (C : ℤ →+* MRing (Bk n)) := by
    unfold charOf
    rw [hc]
    exact Ideal.mul_mem_right c _ hg
  exact Ideal.mem_comap.mp hmem

/- English proof (translation)
Establish `h1` using `(C_mem_ptIdeal_iff (j (genericPoint Z)) _).mp (C_charOf_mem _)`. Establish `h2` using `congrArg (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom h1`. Apply `evaluation_generic_injective Z` to reduce the goal to its premises. Rewrite using `[map_natCast, map_zero]`. Simplify using `using h2`.
-/
theorem charOf_cast_eq_zero {Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ MP ℤ m n) :
    ((charOf (ptIdeal (j (genericPoint Z))) : ℕ) : Γ(Z, ⊤)) = 0 := by
  have h1 := (C_mem_ptIdeal_iff (j (genericPoint Z)) _).mp (C_charOf_mem _)
  have h2 := congrArg (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom h1
  apply evaluation_generic_injective Z
  rw [map_natCast, map_zero]
  simpa using h2

end GlobalTheory.CompanionTheory.MixZ.PtDictProof

namespace GlobalTheory.CompanionTheory.MixZ

open GlobalTheory.CompanionTheory.MixZ.PtDictProof in

/- English proof (translation)
Introduce `m n Z _ j _ d hd`. Establish `hP` using `isMultiProjPrime_ptIdeal m n (j (genericPoint Z))`. Use `haveI : (ptIdeal (j (genericPoint Z))).IsPrime := hP.1`. Establish `hH : IsHorizontal (ptIdeal (j (genericPoint Z))) ↔ CharZero Γ(Z, ⊤)` using `(ptIdeal_isHorizontal_iff m n _).trans (charZero_residueField_iff j)`. Use `⟨hP, hH, fun h => ?_, fun h => ⟨charOf_prime h, charOf_cast_eq_zero j⟩⟩` and prove the remaining obligations.

Establish `hc : CharZero ((MP ℤ m n).residueField (j (genericPoint Z)))` using `(ptIdeal_isHorizontal_iff m n _).mp h`. Establish `hdim : topologicalKrullDim (closure ({j (genericPoint Z)} : Set (MP ℤ m n))) = (d : ℕ)`. Rewrite using `[dim_closure_image_generic j, hd]`. Conclude with `(GlobalTheory.T.closure_dim_iff_arithmetic_variety m n _ d hc).mp hdim`.
-/
theorem ptDict : PtDict := by
  intro m n Z _ j _ d hd
  have hP := isMultiProjPrime_ptIdeal m n (j (genericPoint Z))
  haveI : (ptIdeal (j (genericPoint Z))).IsPrime := hP.1
  have hH : IsHorizontal (ptIdeal (j (genericPoint Z))) ↔ CharZero Γ(Z, ⊤) :=
    (ptIdeal_isHorizontal_iff m n _).trans (charZero_residueField_iff j)
  refine ⟨hP, hH, fun h => ?_, fun h => ⟨charOf_prime h, charOf_cast_eq_zero j⟩⟩
  have hc : CharZero ((MP ℤ m n).residueField (j (genericPoint Z))) :=
    (ptIdeal_isHorizontal_iff m n _).mp h
  have hdim : topologicalKrullDim (closure ({j (genericPoint Z)} : Set (MP ℤ m n))) = (d : ℕ) := by
    rw [dim_closure_image_generic j, hd]
  exact (GlobalTheory.T.closure_dim_iff_arithmetic_variety m n _ d hc).mp hdim

end GlobalTheory.CompanionTheory.MixZ
