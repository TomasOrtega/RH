import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.ChartCut

/- English proof (translation)
Introduce `d P x W hxW`. Use `P.cl` as an intermediate fact. Use `P.smX` as an intermediate fact. Use `P.smZ` as an intermediate fact. Take `⟨T, hT, hxT, -⟩` from `exists_isAffineOpen_mem_and_subset (x := P.p.base x) (U := ⊤) trivial`.

Take `⟨V, hV, hxV, hVW⟩` from `exists_isAffineOpen_mem_and_subset (x := x) (U := W ⊓ P.p ⁻¹ᵁ T) ⟨hxW, hxT⟩`. Establish `e : V ≤ P.p ⁻¹ᵁ T` using `fun y hy => (hVW hy).2`. Use `⟨⟨V, hV⟩, hxV, fun y hy => (hVW hy).1, Γ(P.S, T), inferInstance, (P.p.appLE T V e).hom, ?_, ?_⟩` and prove the remaining obligations. Conclude with `HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension (P.e + d)) P.p P.smX ⟨T, hT⟩ ⟨V, hV⟩ e`. Establish `hV' : IsAffineOpen (P.ι ⁻¹ᵁ V)` using `hV.preimage P.ι`.

Establish `e2 : P.ι ⁻¹ᵁ V ≤ (P.ι ≫ P.p) ⁻¹ᵁ T` using `fun y hy => e hy`. Establish `h2` using `HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension P.e) (P.ι ≫ P.p) P.smZ ⟨T, hT⟩ ⟨P.ι ⁻¹ᵁ V, hV'⟩ e2`. Establish `hc : (P.ι ≫ P.p).appLE T (P.ι ⁻¹ᵁ V) e2 = P.p.appLE T V e ≫ P.ι.app V`. Rewrite using `[Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]`. Rewrite `h2` using `[hc]`.

Establish `hs : Function.Surjective (P.ι.app V).hom` using `P.ι.app_surjective V hV`. Establish `hk : P.ι.ker.ideal ⟨V, hV⟩ = RingHom.ker (P.ι.app V).hom` using `P.ι.ker_apply ⟨V, hV⟩`. Rewrite using `[hk]`. Set `eqv` to `RingHom.quotientKerEquivOfSurjective hs`. Establish `heq : (Ideal.Quotient.mk (RingHom.ker (P.ι.app V).hom)).comp (P.p.appLE T V e).hom = eqv.symm.toRingHom.comp ((P.p.appLE T V e ≫ P.ι.app V).hom)`.

Use extensionality with `a`. Simplify using `only [RingHom.comp_apply, CommRingCat.hom_comp]`. Apply `eqv.injective` to reduce the goal to its premises. Simplify using `[eqv]`. Rewrite using `[heq]`.

Conclude with `(RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso).left _ _ h2`.
-/
theorem LeafLoc_of : LeafLoc := by
  intro d P x W hxW
  have := P.cl; have := P.smX; have := P.smZ
  obtain ⟨T, hT, hxT, -⟩ := exists_isAffineOpen_mem_and_subset (x := P.p.base x) (U := ⊤) trivial
  obtain ⟨V, hV, hxV, hVW⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := W ⊓ P.p ⁻¹ᵁ T) ⟨hxW, hxT⟩
  have e : V ≤ P.p ⁻¹ᵁ T := fun y hy => (hVW hy).2
  refine ⟨⟨V, hV⟩, hxV, fun y hy => (hVW hy).1, Γ(P.S, T), inferInstance, (P.p.appLE T V e).hom, ?_, ?_⟩
  · exact HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension (P.e + d)) P.p P.smX ⟨T, hT⟩ ⟨V, hV⟩ e
  · have hV' : IsAffineOpen (P.ι ⁻¹ᵁ V) := hV.preimage P.ι
    have e2 : P.ι ⁻¹ᵁ V ≤ (P.ι ≫ P.p) ⁻¹ᵁ T := fun y hy => e hy
    have h2 := HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension P.e) (P.ι ≫ P.p) P.smZ
      ⟨T, hT⟩ ⟨P.ι ⁻¹ᵁ V, hV'⟩ e2
    have hc : (P.ι ≫ P.p).appLE T (P.ι ⁻¹ᵁ V) e2 = P.p.appLE T V e ≫ P.ι.app V := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    rw [hc] at h2
    have hs : Function.Surjective (P.ι.app V).hom := P.ι.app_surjective V hV
    have hk : P.ι.ker.ideal ⟨V, hV⟩ = RingHom.ker (P.ι.app V).hom := P.ι.ker_apply ⟨V, hV⟩
    rw [hk]
    let eqv := RingHom.quotientKerEquivOfSurjective hs
    have heq : (Ideal.Quotient.mk (RingHom.ker (P.ι.app V).hom)).comp (P.p.appLE T V e).hom =
        eqv.symm.toRingHom.comp ((P.p.appLE T V e ≫ P.ι.app V).hom) := by
      ext a
      simp only [RingHom.comp_apply, CommRingCat.hom_comp]
      apply eqv.injective
      simp [eqv]
    rw [heq]
    exact (RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso).left _ _ h2

end LateralTheory.CohomologicalPurity.ChartCut
