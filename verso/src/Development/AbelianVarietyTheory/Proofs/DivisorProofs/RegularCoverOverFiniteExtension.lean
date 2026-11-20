import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverFunctionFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointMorphismFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.RegCoverExt

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Spec.map (X.presheaf.stalkSpecializes h ≫ j.stalkMap _) ≫ _ = _`. Rewrite using `[Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]`.
-/
theorem SpecMap_fnMap_fromSpecStalk {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
    (h : j (genericPoint Y) ⤳ genericPoint X) :
    Spec.map (CommRingCat.ofHom (TrueGeo.SmallSec.fnMap j h)) ≫ X.fromSpecStalk (genericPoint X) =
      Y.fromSpecStalk (genericPoint Y) ≫ j := by
  change Spec.map (X.presheaf.stalkSpecializes h ≫ j.stalkMap _) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/- English proof (translation)
Use `h.isLocallyNoetherian` as an intermediate fact. Establish `: IsProper s` using `CommonModel.isProper_of_isProjOver h.isProjOver`. Use `h.charZero` as an intermediate fact. Establish `: CharZero X.functionField` using `charZero_of_injective_ringHom (f := (X.presheaf.germ ⊤ (genericPoint X) trivial).hom) (germ_injective_of_isIntegral X (U := ⊤) (genericPoint X) trivial)`. Establish `: CharZero F` using `charZero_of_injective_algebraMap (algebraMap X.functionField F).injective`.

Set `η` to `genericPoint X`. Set `α : X.presheaf.stalk η ⟶ CommRingCat.of F` to `CommRingCat.ofHom (algebraMap X.functionField F)`. Set `g : Spec (.of F) ⟶ X` to `Spec.map α ≫ X.fromSpecStalk η`. Establish `hfin : IsFinite g.fromNormalization`. Use `GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk s η α ?_` and prove the remaining obligations.

Establish `h2 : (algebraMap X.functionField F).FiniteType` using `(RingHom.finite_algebraMap.2 inferInstance).finiteType`. Conclude with `h2.essFiniteType`. Set `pt : Spec (.of F)` to `IsLocalRing.closedPoint (CommRingCat.of F)`. Establish `hgη : g pt = η`. Express the relevant statement in the definitionally equal form `X.fromSpecStalk η (Spec.map α pt) = η`.

Rewrite using `[show Spec.map α pt = IsLocalRing.closedPoint (X.presheaf.stalk η) from Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk η)) _ _]`. Conclude with `Scheme.fromSpecStalk_closedPoint`. Establish `hg0 : η ∈ Set.range g` using `⟨pt, hgη⟩`. Establish `: IsDominant g` using `⟨(dense_iff_closure_eq.2 (genericPoint_spec X)).mono (Set.singleton_subset_iff.2 hg0)⟩`. Establish `: IsDominant g.fromNormalization`.

Establish `: IsDominant (g.toNormalization ≫ g.fromNormalization)`. Rewrite using `[Scheme.Hom.toNormalization_fromNormalization]`. Use `infer_instance`. Conclude with `IsDominant.of_comp g.toNormalization g.fromNormalization`. Establish `hρs : Surjective g.fromNormalization` using `surjective_of_isDominant_of_isClosed_range _ g.fromNormalization.isClosedMap.isClosed_range`.

Establish `hdeg : 0 < g.fromNormalization.residueDegree (genericPoint g.normalization)`. Set `` to `(g.fromNormalization.residueFieldMap (genericPoint g.normalization)).hom.toAlgebra`. Establish `: Module.Finite (X.residueField (g.fromNormalization (genericPoint g.normalization))) (g.normalization.residueField (genericPoint g.normalization))` using `residueFieldMap_finite_of_locallyQuasiFinite g.fromNormalization _`. Conclude with `Module.finrank_pos`. Establish `hgen` using `apply_genericPoint_of_isDominant g.fromNormalization`.

Establish `hdim : topologicalKrullDim g.normalization = (D + 1 : ℕ)`. Rewrite using `[← h.dim_eq]`. Conclude with `le_antisymm (ProperCover.dim_le_of_residueDegree_pos g.fromNormalization hgen hdeg) (PosBaseChange.dim_le_of_isClosedMap g.fromNormalization.isClosedMap hρs.surj)`. Establish `hfl : Flat (g.fromNormalization ≫ s)` using `GlobalTheory.flat_fromNormalization_comp g ℚ s (spMap (algebraMap ℚ F)) (specZIsTerminal.hom_ext _ _)`. Take `⟨hη, ψ, hψ⟩` from `NormFnField.normalization_functionField X F g rfl`.

Use `⟨g.normalization, inferInstance, g.fromNormalization, hη, ψ, ⟨h.isDomain, h.finite, inferInstance, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin h.isProjOver, ?_, hdim⟩, hgen, hdeg.ne', hψ⟩` and prove the remaining obligations. Use `hfl using 1` and compare the differences between its conclusion and the goal. Conclude with `specZIsTerminal.hom_ext _ _`.
-/
theorem exists_isArithVar_extension (X : Scheme.{0}) (s : X ⟶ Sp ℤ) [IsIntegral X] (D : ℕ) (h : IsArithVar s D)
    (F : Type) [Field F] [Algebra X.functionField F] [FiniteDimensional X.functionField F] :
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (ν : Z ⟶ X) (hη : ν (genericPoint Z) ⤳ genericPoint X)
      (ψ : F →+* Z.functionField), IsArithVar (ν ≫ s) D ∧ ν (genericPoint Z) = genericPoint X ∧
      ν.residueDegree (genericPoint Z) ≠ 0 ∧
      ψ.comp (algebraMap X.functionField F) = TrueGeo.SmallSec.fnMap ν hη := by
  have := h.isLocallyNoetherian
  have : IsProper s := CommonModel.isProper_of_isProjOver h.isProjOver
  have := h.charZero
  have : CharZero X.functionField :=
    charZero_of_injective_ringHom (f := (X.presheaf.germ ⊤ (genericPoint X) trivial).hom)
      (germ_injective_of_isIntegral X (U := ⊤) (genericPoint X) trivial)
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap X.functionField F).injective
  let η := genericPoint X
  let α : X.presheaf.stalk η ⟶ CommRingCat.of F := CommRingCat.ofHom (algebraMap X.functionField F)
  let g : Spec (.of F) ⟶ X := Spec.map α ≫ X.fromSpecStalk η
  have hfin : IsFinite g.fromNormalization := by
    refine GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk s η α ?_
    have h2 : (algebraMap X.functionField F).FiniteType := (RingHom.finite_algebraMap.2 inferInstance).finiteType
    exact h2.essFiniteType
  let pt : Spec (.of F) := IsLocalRing.closedPoint (CommRingCat.of F)
  have hgη : g pt = η := by
    change X.fromSpecStalk η (Spec.map α pt) = η
    rw [show Spec.map α pt = IsLocalRing.closedPoint (X.presheaf.stalk η) from
      Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk η)) _ _]
    exact Scheme.fromSpecStalk_closedPoint
  have hg0 : η ∈ Set.range g := ⟨pt, hgη⟩
  have : IsDominant g := ⟨(dense_iff_closure_eq.2 (genericPoint_spec X)).mono
    (Set.singleton_subset_iff.2 hg0)⟩
  have : IsDominant g.fromNormalization := by
    have : IsDominant (g.toNormalization ≫ g.fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp g.toNormalization g.fromNormalization
  have hρs : Surjective g.fromNormalization :=
    surjective_of_isDominant_of_isClosed_range _ g.fromNormalization.isClosedMap.isClosed_range
  have hdeg : 0 < g.fromNormalization.residueDegree (genericPoint g.normalization) := by
    let := (g.fromNormalization.residueFieldMap (genericPoint g.normalization)).hom.toAlgebra
    have : Module.Finite (X.residueField (g.fromNormalization (genericPoint g.normalization)))
        (g.normalization.residueField (genericPoint g.normalization)) :=
      residueFieldMap_finite_of_locallyQuasiFinite g.fromNormalization _
    exact Module.finrank_pos
  have hgen := apply_genericPoint_of_isDominant g.fromNormalization
  have hdim : topologicalKrullDim g.normalization = (D + 1 : ℕ) := by
    rw [← h.dim_eq]
    exact le_antisymm (ProperCover.dim_le_of_residueDegree_pos g.fromNormalization hgen hdeg)
      (PosBaseChange.dim_le_of_isClosedMap g.fromNormalization.isClosedMap hρs.surj)
  have hfl : Flat (g.fromNormalization ≫ s) :=
    GlobalTheory.flat_fromNormalization_comp g ℚ s (spMap (algebraMap ℚ F)) (specZIsTerminal.hom_ext _ _)
  obtain ⟨hη, ψ, hψ⟩ := NormFnField.normalization_functionField X F g rfl
  refine ⟨g.normalization, inferInstance, g.fromNormalization, hη, ψ,
    ⟨h.isDomain, h.finite, inferInstance, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin h.isProjOver, ?_, hdim⟩,
    hgen, hdeg.ne', hψ⟩
  convert hfl using 1
  exact specZIsTerminal.hom_ext _ _

/- English proof (translation)
Introduce `H k _ X p _ h F _ _ _`. Take `⟨Z, _, ν, hη, ψ, hZ, hν, hνd, hψ⟩` from `exists_isArithVar_extension X _ 1 (ShFam.Pad.isArithVar_toSpZ h) F`. Take `⟨Y, _, ρ, hY, hr, hg, hd⟩` from `H Z _ 1 hZ`. Establish `hρ : ρ (genericPoint Y) ⤳ genericPoint Z` using `hg ▸ specializes_rfl`. Establish `key : Spec.map (CommRingCat.ofHom ((TrueGeo.SmallSec.fnMap ρ hρ).comp ψ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField F)) ≫ X.fromSpecStalk (genericPoint X) = Y.fromSpecStalk (genericPoint Y) ≫ ρ ≫ ν`.

Rewrite using `[← Category.assoc (Y.fromSpecStalk _), ← SpecMap_fnMap_fromSpecStalk ρ hρ, Category.assoc, ← SpecMap_fnMap_fromSpecStalk ν hη, ← hψ, ← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]`. Both sides reduce to the same expression. Use `⟨⟨Y, ρ ≫ ν, ⟨RegCoverExists.isArithVar_of_toSpZ h.isDomain h.finite ((ρ ≫ ν) ≫ p) hY, hr⟩, ?_, ?_⟩, Spec.map (CommRingCat.ofHom ((TrueGeo.SmallSec.fnMap ρ hρ).comp ψ)), ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.comp_apply, hg, hν]`. Rewrite using `[CurveDegreesCompare.residueDegree_comp, hg]`.

Conclude with `mul_ne_zero hνd hd`. Conclude with `key`.
-/
theorem exists_regCover_extension : GlobalTheory.Published.RegularAlteration → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∀ (F : Type) [Field F] [Algebra X.functionField F],
    FiniteDimensional X.functionField F → ∃ (C : RegCover p) (t : Sp C.Y.functionField ⟶ Sp F),
      t ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField F)) ≫ X.fromSpecStalk (genericPoint X) =
        C.Y.fromSpecStalk (genericPoint C.Y) ≫ C.ρ := by
  intro H k _ X p _ h F _ _ _
  obtain ⟨Z, _, ν, hη, ψ, hZ, hν, hνd, hψ⟩ :=
    exists_isArithVar_extension X _ 1 (ShFam.Pad.isArithVar_toSpZ h) F
  obtain ⟨Y, _, ρ, hY, hr, hg, hd⟩ := H Z _ 1 hZ
  have hρ : ρ (genericPoint Y) ⤳ genericPoint Z := hg ▸ specializes_rfl
  have key : Spec.map (CommRingCat.ofHom ((TrueGeo.SmallSec.fnMap ρ hρ).comp ψ)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField F)) ≫ X.fromSpecStalk (genericPoint X) =
        Y.fromSpecStalk (genericPoint Y) ≫ ρ ≫ ν := by
    rw [← Category.assoc (Y.fromSpecStalk _), ← SpecMap_fnMap_fromSpecStalk ρ hρ, Category.assoc,
      ← SpecMap_fnMap_fromSpecStalk ν hη, ← hψ, ← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
    rfl
  refine ⟨⟨Y, ρ ≫ ν, ⟨RegCoverExists.isArithVar_of_toSpZ h.isDomain h.finite ((ρ ≫ ν) ≫ p) hY, hr⟩, ?_, ?_⟩,
    Spec.map (CommRingCat.ofHom ((TrueGeo.SmallSec.fnMap ρ hρ).comp ψ)), ?_⟩
  · rw [Scheme.Hom.comp_apply, hg, hν]
  · rw [CurveDegreesCompare.residueDegree_comp, hg]
    exact mul_ne_zero hνd hd
  · exact key

end GlobalTheory.RegCoverExt

end
