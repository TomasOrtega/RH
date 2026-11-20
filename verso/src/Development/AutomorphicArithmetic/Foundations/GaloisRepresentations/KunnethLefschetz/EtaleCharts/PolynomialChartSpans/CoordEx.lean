import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover

noncomputable section
open CategoryTheory AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Introduce `R _ Z D _ z`. Take `⟨-, -, V, hV, hzV, -, -⟩` from `SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := D) (f := Z.hom) z`. Take `⟨s, hs, hsQ⟩` from `HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) Z.hom inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (by simp)`. Establish `hz : z ∈ ⨆ f : s, Z.left.basicOpen f.1` using `(hV.self_le_iSup_basicOpen_iff.mpr hs) hzV`. Rewrite `hz` using `[TopologicalSpace.Opens.mem_iSup]`.

Take `⟨⟨t, ht⟩, hzt⟩` from `hz`. Establish `hQ : RingHom.IsStandardSmoothOfRelativeDimension D _` using `hsQ t ht`. Establish `hle : Z.left.basicOpen t ≤ Z.hom ⁻¹ᵁ ⊤` using `by simp`. Establish `hVle : V ≤ Z.hom ⁻¹ᵁ ⊤` using `by simp`. Establish `key : RingHom.IsStandardSmoothOfRelativeDimension D (Z.hom.appLE ⊤ (Z.left.basicOpen t) hle).hom`.

Use `hV.isLocalization_basicOpen t` as an intermediate fact. Set `e` to `IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t) Γ(Z.left, Z.left.basicOpen t)`. Establish `h1 : (Z.hom.appLE ⊤ (Z.left.basicOpen t) hle).hom = (e : Localization.Away t ≃+* Γ(Z.left, Z.left.basicOpen t)).toRingHom.comp ((algebraMap _ (Localization.Away t)).comp (Z.hom.appLE ⊤ V hVle).hom)`. Use extensionality with `x`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]`.

Rewrite using `[RingHom.algebraMap_toAlgebra]`. Use `show _ = (Z.hom.appLE ⊤ V hVle ≫ Z.left.presheaf.map (homOfLE (Z.left.basicOpen_le t)).op).hom x`. Rewrite using `[Scheme.Hom.appLE_map]`. Rewrite using `[h1]`. Conclude with `RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ _ hQ`.

Establish `hR : RingHom.IsStandardSmoothOfRelativeDimension D (algebraMap R (Sec Z (Z.left.basicOpen t)))` using `RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv key`. Rewrite `hR` using `[RingHom.isStandardSmoothOfRelativeDimension_algebraMap]`. Take `⟨g, hg⟩` from `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial D R (Sec Z (Z.left.basicOpen t))`. Use `⟨Z.left.basicOpen t, fun i ↦ g (MvPolynomial.X i), hzt, hV.basicOpen t, ?_⟩` and prove the remaining obligations. Rewrite using `[← Function.comp_def g MvPolynomial.X, ← MvPolynomial.aeval_unique]` and apply the resulting hypothesis.
-/
theorem coordEx : CoordEx := by
  intro R _ Z D _ z
  obtain ⟨-, -, V, hV, hzV, -, -⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := D) (f := Z.hom) z
  obtain ⟨s, hs, hsQ⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) Z.hom inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (by simp)
  have hz : z ∈ ⨆ f : s, Z.left.basicOpen f.1 := (hV.self_le_iSup_basicOpen_iff.mpr hs) hzV
  rw [TopologicalSpace.Opens.mem_iSup] at hz
  obtain ⟨⟨t, ht⟩, hzt⟩ := hz
  have hQ : RingHom.IsStandardSmoothOfRelativeDimension D _ := hsQ t ht
  have hle : Z.left.basicOpen t ≤ Z.hom ⁻¹ᵁ ⊤ := by simp
  have hVle : V ≤ Z.hom ⁻¹ᵁ ⊤ := by simp
  have key : RingHom.IsStandardSmoothOfRelativeDimension D
      (Z.hom.appLE ⊤ (Z.left.basicOpen t) hle).hom := by
    have := hV.isLocalization_basicOpen t
    let e := IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t)
      Γ(Z.left, Z.left.basicOpen t)
    have h1 : (Z.hom.appLE ⊤ (Z.left.basicOpen t) hle).hom =
        (e : Localization.Away t ≃+* Γ(Z.left, Z.left.basicOpen t)).toRingHom.comp
          ((algebraMap _ (Localization.Away t)).comp (Z.hom.appLE ⊤ V hVle).hom) := by
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
      rw [RingHom.algebraMap_toAlgebra]
      show _ = (Z.hom.appLE ⊤ V hVle ≫
        Z.left.presheaf.map (homOfLE (Z.left.basicOpen_le t)).op).hom x
      rw [Scheme.Hom.appLE_map]
    rw [h1]
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ _ hQ
  have hR : RingHom.IsStandardSmoothOfRelativeDimension D
      (algebraMap R (Sec Z (Z.left.basicOpen t))) :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv key
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hR
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial D R
    (Sec Z (Z.left.basicOpen t))
  refine ⟨Z.left.basicOpen t, fun i ↦ g (MvPolynomial.X i), hzt, hV.basicOpen t, ?_⟩
  rwa [← Function.comp_def g MvPolynomial.X, ← MvPolynomial.aeval_unique]

end UpperTheory.Gal.KunnethLefschetz.G
