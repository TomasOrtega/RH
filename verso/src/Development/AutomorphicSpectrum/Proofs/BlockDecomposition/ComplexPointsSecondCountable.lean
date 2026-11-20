import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section
namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

open Topology
open scoped CommRingCat.HomTopology

/- English proof (translation)
Take `⟨n, f, hf⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType ℤ A)`. Use `choose q hq using hf`. Establish `h` using `CommRingCat.HomTopology.isEmbedding_hom (CommRingCat.of ℂ) A`. Establish `hcoord : Continuous fun (φ : A ⟶ CommRingCat.of ℂ) (i : Fin n) => φ.hom (f (MvPolynomial.X i))` using `continuous_pi fun i => (continuous_apply (f (MvPolynomial.X i))).comp h.continuous`. Establish `hemb : IsEmbedding fun (φ : A ⟶ CommRingCat.of ℂ) (i : Fin n) => φ.hom (f (MvPolynomial.X i))`.

Use `IsEmbedding.of_comp (g := fun (z : Fin n → ℂ) (u : A) => MvPolynomial.aeval z (q u)) hcoord (continuous_pi fun u => ?_) ?_` and prove the remaining obligations. Simplify using `only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq] fun_prop`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `φ u`. Simplify using `only [Function.comp_apply]`.

Establish `e : (φ.hom.toIntAlgHom.comp f) = MvPolynomial.aeval fun i => φ.hom (f (MvPolynomial.X i))`. Use extensionality with `i`. Simplify using the standard rewrite rules. Use `congrArg (fun g => g (q u)) e` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, hq] at this`.

Conclude with `this.symm`. Conclude with `hemb.secondCountableTopology`.
-/
theorem secondCountable_hom_of_finiteType (A : CommRingCat.{0}) [Algebra.FiniteType ℤ A] :
    SecondCountableTopology (A ⟶ CommRingCat.of ℂ) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType ℤ A)
  choose q hq using hf
  have h := CommRingCat.HomTopology.isEmbedding_hom (CommRingCat.of ℂ) A
  have hcoord : Continuous fun (φ : A ⟶ CommRingCat.of ℂ) (i : Fin n) => φ.hom (f (MvPolynomial.X i)) :=
    continuous_pi fun i => (continuous_apply (f (MvPolynomial.X i))).comp h.continuous
  have hemb : IsEmbedding fun (φ : A ⟶ CommRingCat.of ℂ) (i : Fin n) => φ.hom (f (MvPolynomial.X i)) := by
    refine IsEmbedding.of_comp (g := fun (z : Fin n → ℂ) (u : A) => MvPolynomial.aeval z (q u))
      hcoord (continuous_pi fun u => ?_) ?_
    · simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
      fun_prop
    · convert h using 1
      ext φ u
      simp only [Function.comp_apply]
      have e : (φ.hom.toIntAlgHom.comp f) = MvPolynomial.aeval fun i => φ.hom (f (MvPolynomial.X i)) := by
        ext i
        simp
      have := congrArg (fun g => g (q u)) e
      simp only [AlgHom.comp_apply, hq] at this
      exact this.symm
  exact hemb.secondCountableTopology

/- English proof (translation)
Establish `h` using `p.finiteType_appLE (isAffineOpen_top _) hU (fun _ _ => trivial)`. Establish `h2 : ((p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).FiniteType` using `h.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.symm.surjective)`. Rewrite using `[← RingHom.finiteType_algebraMap]`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Conclude with `RingHom.ext_int _ _`.
-/
theorem finiteType_of_isAffineOpen {X : Scheme.{0}} (p : X ⟶ Sp ℤ) [LocallyOfFiniteType p] {U : X.Opens}
    (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  have h := p.finiteType_appLE (isAffineOpen_top _) hU (fun _ _ => trivial)
  have h2 : ((p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).FiniteType :=
    h.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.symm.surjective)
  rw [← RingHom.finiteType_algebraMap]
  convert h2 using 1
  exact RingHom.ext_int _ _

/- English proof (translation)
Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.isOpen) (fun x _ => by`. Take `⟨U, hU, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial`. Conclude with `Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩)`. Establish `hsc : ∀ i : t, SecondCountableTopology ({x : Sp ℂ ⟶ X | ⊤ ≤ x ⁻¹ᵁ i.1.1} : Set (Sp ℂ ⟶ X))` using `fun i => by`. Use `finiteType_of_isAffineOpen p i.1.2` as an intermediate fact.

Use `secondCountable_hom_of_finiteType Γ(X, i.1.1)` as an intermediate fact. Conclude with `(affineHomeomorph (C := ℂ) i.1.2).isEmbedding.secondCountableTopology`. Use `secondCountableTopology_of_countable_cover (U := fun i : t => {x : Sp ℂ ⟶ X | ⊤ ≤ x ⁻¹ᵁ i.1.1}) (fun i => isOpen_setOf_le_preimage _) (Set.eq_univ_of_forall fun x => ?_)` and prove the remaining obligations. Establish `hx` using `ht (Set.mem_univ (x (IsLocalRing.closedPoint ℂ)))`. Simplify using `only [Set.mem_iUnion] at hx`.

Take `⟨U, hU, hxU⟩` from `hx`. Conclude with `Set.mem_iUnion.2 ⟨⟨U, hU⟩, (le_preimage_iff x _).2 hxU⟩`.
-/
theorem secondCountable_points {X : Scheme.{0}} (p : X ⟶ Sp ℤ) [LocallyOfFiniteType p] [CompactSpace X] :
    SecondCountableTopology (Sp ℂ ⟶ X) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩)
  have hsc : ∀ i : t, SecondCountableTopology
      ({x : Sp ℂ ⟶ X | ⊤ ≤ x ⁻¹ᵁ i.1.1} : Set (Sp ℂ ⟶ X)) := fun i => by
    have := finiteType_of_isAffineOpen p i.1.2
    have := secondCountable_hom_of_finiteType Γ(X, i.1.1)
    exact (affineHomeomorph (C := ℂ) i.1.2).isEmbedding.secondCountableTopology
  refine secondCountableTopology_of_countable_cover (U := fun i : t => {x : Sp ℂ ⟶ X | ⊤ ≤ x ⁻¹ᵁ i.1.1})
    (fun i => isOpen_setOf_le_preimage _) (Set.eq_univ_of_forall fun x => ?_)
  have hx := ht (Set.mem_univ (x (IsLocalRing.closedPoint ℂ)))
  simp only [Set.mem_iUnion] at hx
  obtain ⟨U, hU, hxU⟩ := hx
  exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, (le_preimage_iff x _).2 hxU⟩

/- English proof (translation)
Take `⟨N, j, hj, e⟩` from `hX.isProjOver`. Establish `hN : IsProper (PSpace.str ℤ N)` using `isProper_str ℤ N`. Establish `hp : IsProper (i ≫ mpStr ℤ m n)`. Rewrite using `[← e]`. Use `infer_instance`.

Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace (i ≫ mpStr ℤ m n)`. Use `secondCountable_points (i ≫ mpStr ℤ m n)` as an intermediate fact. Conclude with `IsEmbedding.subtypeVal.secondCountableTopology`.
-/
theorem secondCountable_cxPts (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X]
    (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ) (hX : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D) :
    SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) := by
  obtain ⟨N, j, hj, e⟩ := hX.isProjOver
  have hN : IsProper (PSpace.str ℤ N) := isProper_str ℤ N
  have hp : IsProper (i ≫ mpStr ℤ m n) := by
    rw [← e]
    infer_instance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (i ≫ mpStr ℤ m n)
  have := secondCountable_points (i ≫ mpStr ℤ m n)
  exact IsEmbedding.subtypeVal.secondCountableTopology

end GlobalTheory.CompanionTheory.MixZ.ArchEq
