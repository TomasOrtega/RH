import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

namespace GlobalTheory.CompHS.Modif

/- English proof (translation)
Introduce `F _ Y p U D M hs hc hd`. Establish `: Smooth p` using `SmoothOfRelativeDimension.smooth D p`. Establish `: GeometricallyIntegral p` using `GlobalTheory.geometricallyIntegral_of_smooth p`. Establish `: Nonempty Y`. Take `⟨x⟩` from `(inferInstance : Nonempty (Sp F))`.

Take `⟨y, -⟩` from `p.surjective x`. Conclude with `⟨y⟩`. Take `⟨u, hu⟩` from `hd.nonempty`. Establish `: Surjective (U.ι ≫ p)` using `⟨fun x => ⟨⟨u, hu⟩, Subsingleton.elim _ _⟩⟩`. Establish `hU : GeometricallyIrreducible (U.ι ≫ p)` using `inferInstance`.

Establish `: IsIso (M.σ ∣_ U)` using `M.iso`. Establish `e : M.opn.ι ≫ M.str = (M.σ ∣_ U) ≫ (U.ι ≫ p)` using `by show (M.opn.ι ≫ M.σ) ≫ p = _`. Rewrite using `[← morphismRestrict_ι, Category.assoc]`. Establish `hO : GeometricallyIrreducible (M.opn.ι ≫ M.str)`. Establish `sq : IsPullback (M.σ ∣_ U) (M.opn.ι ≫ M.str) (U.ι ≫ p) (𝟙 _)` using `IsPullback.of_horiz_isIso ⟨by rw [e, Category.comp_id]⟩`.

Conclude with `MorphismProperty.of_isPullback sq hU`. Use `⟨fun K _ y Z fst snd h => ?_⟩` and prove the remaining obligations. Establish `hy : UniversallyOpen y` using `inferInstance`. Establish `hf : UniversallyOpen fst` using `MorphismProperty.of_isPullback h.flip hy`. Establish `hdense : Dense ((fst ⁻¹ᵁ M.opn : Z.Opens) : Set Z)` using `M.dense.preimage fst.isOpenMap`.

Establish `hsq : IsPullback (fst ∣_ M.opn) ((fst ⁻¹ᵁ M.opn).ι ≫ snd) (M.opn.ι ≫ M.str) y` using `(isPullback_morphismRestrict fst M.opn).paste_vert h`. Establish `: IrreducibleSpace (fst ⁻¹ᵁ M.opn)` using `hO.geometrically_irreducibleSpace y _ _ hsq`. Establish `hirr : IsIrreducible ((fst ⁻¹ᵁ M.opn : Z.Opens) : Set Z)`. Use `(IrreducibleSpace.isIrreducible_univ (fst ⁻¹ᵁ M.opn)).image _ (fst ⁻¹ᵁ M.opn).ι.continuous.continuousOn` as an intermediate fact. Rewrite `this` using `[Set.image_univ, Scheme.Opens.range_ι]`. Then use the resulting hypothesis.

Establish `: IrreducibleSpace Z`. Establish `hc` using `hirr.closure`. Rewrite `hc` using `[hdense.closure_eq]`. Conclude with `irreducibleSpace_def Z |>.mpr hc`. Conclude with `(connectedSpace_iff_univ).mpr (IrreducibleSpace.isIrreducible_univ Z).isConnected`.
-/
theorem geometricallyConnected_str : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (U : Y.Opens) (D : ℕ)
    (M : Modif p U D), SmoothOfRelativeDimension D p → GeometricallyConnected p → Dense (U : Set Y) →
    GeometricallyConnected M.str := by
  intro F _ Y p U D M hs hc hd
  have : Smooth p := SmoothOfRelativeDimension.smooth D p
  have : GeometricallyIntegral p := GlobalTheory.geometricallyIntegral_of_smooth p
  have : Nonempty Y := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (Sp F))
    obtain ⟨y, -⟩ := p.surjective x
    exact ⟨y⟩
  obtain ⟨u, hu⟩ := hd.nonempty
  have : Surjective (U.ι ≫ p) := ⟨fun x => ⟨⟨u, hu⟩, Subsingleton.elim _ _⟩⟩
  have hU : GeometricallyIrreducible (U.ι ≫ p) := inferInstance
  have : IsIso (M.σ ∣_ U) := M.iso
  have e : M.opn.ι ≫ M.str = (M.σ ∣_ U) ≫ (U.ι ≫ p) := by
    show (M.opn.ι ≫ M.σ) ≫ p = _
    rw [← morphismRestrict_ι, Category.assoc]
  have hO : GeometricallyIrreducible (M.opn.ι ≫ M.str) := by
    have sq : IsPullback (M.σ ∣_ U) (M.opn.ι ≫ M.str) (U.ι ≫ p) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [e, Category.comp_id]⟩
    exact MorphismProperty.of_isPullback sq hU
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have hy : UniversallyOpen y := inferInstance
  have hf : UniversallyOpen fst := MorphismProperty.of_isPullback h.flip hy
  have hdense : Dense ((fst ⁻¹ᵁ M.opn : Z.Opens) : Set Z) := M.dense.preimage fst.isOpenMap
  have hsq : IsPullback (fst ∣_ M.opn) ((fst ⁻¹ᵁ M.opn).ι ≫ snd) (M.opn.ι ≫ M.str) y :=
    (isPullback_morphismRestrict fst M.opn).paste_vert h
  have : IrreducibleSpace (fst ⁻¹ᵁ M.opn) :=
    hO.geometrically_irreducibleSpace y _ _ hsq
  have hirr : IsIrreducible ((fst ⁻¹ᵁ M.opn : Z.Opens) : Set Z) := by
    have := (IrreducibleSpace.isIrreducible_univ (fst ⁻¹ᵁ M.opn)).image _
      (fst ⁻¹ᵁ M.opn).ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at this
  have : IrreducibleSpace Z := by
    have hc := hirr.closure
    rw [hdense.closure_eq] at hc
    exact irreducibleSpace_def Z |>.mpr hc
  exact (connectedSpace_iff_univ).mpr (IrreducibleSpace.isIrreducible_univ Z).isConnected

end GlobalTheory.CompHS.Modif
