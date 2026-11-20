import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible

noncomputable section

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison

namespace UpperTheory.Gal.Seam

section Ring

variable (O : Type) [CommRing O] (ϖ : O) (n : ℕ)

private abbrev chartI : Ideal (MvPolynomial (Fin (n + 1)) O) :=
  Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1), MvPolynomial.X i) - MvPolynomial.C ϖ}

/- English proof (translation)
Establish `hs : Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1) = {0}`. Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `ext`. Simplify using `only [Fin.val_zero]`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `rfl`. Simplify using the standard rewrite rules.

Rewrite using `[hs, Finset.prod_singleton]`.
-/
private theorem prod_one_branch :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) O)) =
      MvPolynomial.X 0 := by
  have hs : Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      ext
      simp only [Fin.val_zero]
      omega
    · rintro rfl
      simp
  rw [hs, Finset.prod_singleton]

private def evalFirst : MvPolynomial (Fin (n + 1)) O →+* MvPolynomial (Fin n) O :=
  (MvPolynomial.aeval (Fin.cons (MvPolynomial.C ϖ) MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin n) O)).toRingHom

private def toPoly : (MvPolynomial (Fin (n + 1)) O ⧸ chartI O ϖ n) →+* MvPolynomial (Fin n) O :=
  Ideal.Quotient.lift _ (evalFirst O ϖ n) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [prod_one_branch]
    simp [evalFirst])

private def fromPoly : MvPolynomial (Fin n) O →+* (MvPolynomial (Fin (n + 1)) O ⧸ chartI O ϖ n) :=
  (Ideal.Quotient.mk _).comp (MvPolynomial.rename Fin.succ : MvPolynomial (Fin n) O →ₐ[O] _).toRingHom

/- English proof (translation)
Rewrite using `[Ideal.Quotient.eq]`. Apply `Ideal.subset_span` to reduce the goal to its premises. Rewrite using `[prod_one_branch]`. Both sides reduce to the same expression.
-/
private theorem mk_X_zero :
    Ideal.Quotient.mk (chartI O ϖ n) (MvPolynomial.X 0) = Ideal.Quotient.mk (chartI O ϖ n) (MvPolynomial.C ϖ) := by
  rw [Ideal.Quotient.eq]
  apply Ideal.subset_span
  rw [prod_one_branch]
  rfl

private def chartEquiv : (MvPolynomial (Fin (n + 1)) O ⧸ chartI O ϖ n) ≃+* MvPolynomial (Fin n) O :=
  RingEquiv.ofRingHom (toPoly O ϖ n) (fromPoly O ϖ n)
    (by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · simp [toPoly, fromPoly, evalFirst]
      · simp [toPoly, fromPoly, evalFirst])
    (by
      refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
      · simp [toPoly, fromPoly, evalFirst]
      · refine Fin.cases ?_ (fun j => ?_) i
        · simp [toPoly, fromPoly, evalFirst, mk_X_zero]
        · simp [toPoly, fromPoly, evalFirst])

/- English proof (translation)
Express the relevant statement in the definitionally equal form `toPoly O ϖ n (Ideal.Quotient.mk _ (MvPolynomial.C o)) = _`. Simplify using `[toPoly, evalFirst]`.
-/
private theorem chartEquiv_algebraMap (o : O) :
    chartEquiv O ϖ n (algebraMap O _ o) = MvPolynomial.C o := by
  change toPoly O ϖ n (Ideal.Quotient.mk _ (MvPolynomial.C o)) = _
  simp [toPoly, evalFirst]

end Ring

/- English proof (translation)
Introduce `l _ K _ M hs hp`. Use `⟨hp, ?_⟩` and prove the remaining obligations. Use `haveI : IsDiscreteValuationRing (OK l K) := OK_dvr`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (OK l K)`. Use `⟨ϖ, hϖ, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨_, ⟨V, hV, rfl⟩, hxV, -⟩` from `M.X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Set `e` to `(Scheme.ΓSpecIso (CommRingCat.of (OK l K))).commRingCatIsoToRingEquiv`. Establish `hsm : (M.p.appLE ⊤ V le_top).hom.Smooth` using `M.p.smooth_appLE (isAffineOpen_top _) hV le_top`. Set `φ : OK l K →+* Γ(M.X, V)` to `(M.p.appLE ⊤ V le_top).hom.comp e.symm.toRingHom`. Establish `hφ : φ.Smooth` using `RingHom.Smooth.propertyIsLocal.respectsIso.2 _ _ hsm`.

Use `algebraize [φ]`. Take `⟨r, hrx, hr⟩` from `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth (OK l K) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal`. Establish `hxr : x ∈ M.X.basicOpen r`. Establish `h1 : hV.primeIdealOf ⟨x, hxV⟩ ∈ hV.fromSpec ⁻¹ᵁ M.X.basicOpen r`. Rewrite using `[hV.fromSpec_preimage_basicOpen]`.

Conclude with `hrx`. Establish `h2 : hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) ∈ M.X.basicOpen r` using `h1`. Rewrite `h2` using `[hV.fromSpec_primeIdealOf]`. Then use the resulting hypothesis. Establish `hstd : ((Scheme.ΓSpecIso (CommRingCat.of (OK l K))).inv ≫ M.p.appLE ⊤ (M.X.basicOpen r) le_top).hom.IsStandardSmooth`. Use `hV.isLocalization_basicOpen r` as an intermediate fact.

Rewrite `hr` using `[← RingHom.isStandardSmooth_algebraMap]`. Use `RingHom.isStandardSmooth_respectsIso.1 _ (IsLocalization.algEquiv (.powers r) _ Γ(M.X, M.X.basicOpen r)).toRingEquiv hr` and compare the differences between its conclusion and the goal. Use extensionality with `a`. Use `dsimp`. Simplify using `only [IsScalarTower.algebraMap_apply (OK l K) Γ(M.X, V) (Localization _), IsLocalization.map_eq]`.

Simplify using `only [RingHom.algebraMap_toAlgebra, RingHomCompTriple.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]`. Rewrite using `[AlgEquiv.commutes]`. Use `first`. Consider the case `(rw [CommRingCat.comp_apply, ← Scheme.Hom.appLE_map (V := V) M.p le_top (homOfLE (M.X.basicOpen_le r)).op, CommRingCat.comp_apply]; rfl)`. Consider the case `(simp only [φ, e, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Iso.commRingCatIsoToRingEquiv_symm_apply, ← CommRingCat.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]; rfl)`.

Take `⟨k, g, hgC, hg⟩` from `hstd.exists_etale_mvPolynomial`. Use `⟨M.X.basicOpen r, hV.basicOpen r, hxr, k + 1, 1, le_rfl, by omega, g.comp (chartEquiv (OK l K) ϖ k).toRingHom, ?_, ?_⟩` and prove the remaining obligations. Conclude with `RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective (chartEquiv (OK l K) ϖ k).bijective) hg`. Rewrite using `[← hgC]`. Use extensionality with `a`.

Simplify using `[chartEquiv_algebraMap]`.
-/
theorem goodOf : GoodOf := by
  intro l _ K _ M hs hp
  refine ⟨hp, ?_⟩
  haveI : IsDiscreteValuationRing (OK l K) := OK_dvr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OK l K)
  refine ⟨ϖ, hϖ, fun x => ?_⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    M.X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let e := (Scheme.ΓSpecIso (CommRingCat.of (OK l K))).commRingCatIsoToRingEquiv
  have hsm : (M.p.appLE ⊤ V le_top).hom.Smooth :=
    M.p.smooth_appLE (isAffineOpen_top _) hV le_top
  let φ : OK l K →+* Γ(M.X, V) := (M.p.appLE ⊤ V le_top).hom.comp e.symm.toRingHom
  have hφ : φ.Smooth := RingHom.Smooth.propertyIsLocal.respectsIso.2 _ _ hsm
  algebraize [φ]
  obtain ⟨r, hrx, hr⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth (OK l K)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hxr : x ∈ M.X.basicOpen r := by
    have h1 : hV.primeIdealOf ⟨x, hxV⟩ ∈ hV.fromSpec ⁻¹ᵁ M.X.basicOpen r := by
      rw [hV.fromSpec_preimage_basicOpen]
      exact hrx
    have h2 : hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) ∈ M.X.basicOpen r := h1
    rwa [hV.fromSpec_primeIdealOf] at h2
  have hstd : ((Scheme.ΓSpecIso (CommRingCat.of (OK l K))).inv ≫
      M.p.appLE ⊤ (M.X.basicOpen r) le_top).hom.IsStandardSmooth := by
    have := hV.isLocalization_basicOpen r
    rw [← RingHom.isStandardSmooth_algebraMap] at hr
    convert RingHom.isStandardSmooth_respectsIso.1 _
      (IsLocalization.algEquiv (.powers r) _ Γ(M.X, M.X.basicOpen r)).toRingEquiv hr
    ext a
    dsimp
    simp only [IsScalarTower.algebraMap_apply (OK l K) Γ(M.X, V) (Localization _),
      IsLocalization.map_eq]
    simp only [RingHom.algebraMap_toAlgebra, RingHomCompTriple.comp_apply,
      ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
    rw [AlgEquiv.commutes]
    first
      | (rw [CommRingCat.comp_apply, ← Scheme.Hom.appLE_map (V := V) M.p le_top
            (homOfLE (M.X.basicOpen_le r)).op, CommRingCat.comp_apply]; rfl)
      | (simp only [φ, e, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
            Iso.commRingCatIsoToRingEquiv_symm_apply, ← CommRingCat.comp_apply,
            ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]; rfl)
  obtain ⟨k, g, hgC, hg⟩ := hstd.exists_etale_mvPolynomial
  refine ⟨M.X.basicOpen r, hV.basicOpen r, hxr, k + 1, 1, le_rfl, by omega,
    g.comp (chartEquiv (OK l K) ϖ k).toRingHom, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (chartEquiv (OK l K) ϖ k).bijective) hg
  · rw [← hgC]
    ext a
    simp [chartEquiv_algebraMap]

end UpperTheory.Gal.Seam
