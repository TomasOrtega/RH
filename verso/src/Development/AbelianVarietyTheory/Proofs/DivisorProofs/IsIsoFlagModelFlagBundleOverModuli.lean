import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFlagsUniqueFlagCoverPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagModelPointOfFlagBundleFieldPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.VarFlag

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y X Z hF C hT B j _ f hπ hB h _ hU hH`. Use `C.Y.isNormalScheme` as an intermediate fact. Establish `hN` using `GlobalTheory.IsNormalScheme.pred (GlobalTheory.VarFlag.Vo C).toScheme`. Establish `: IsLocallyNoetherian C.Y.X` using `LocallyOfFiniteType.isLocallyNoetherian C.Y.str`. Use `GlobalTheory.isIso_of_isProper_of_existsUnique_field_point _ _ _ inferInstance inferInstance hN inferInstance fun K _ w => ?_` and prove the remaining obligations.

Establish `hp : ∀ s, (w ≫ (GlobalTheory.VarFlag.Vo C).ι) s ∈ GlobalTheory.VarFlag.Vo C` using `fun s => by`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `(w s).2`. Take `⟨z₀, hz₀⟩` from `GlobalTheory.T.exists_flagModel_point_of_flagBundle_fieldPoint X Z hF C hT B j f hπ hB K _ hp`. Establish `e₀ : z₀ ≫ h = w ≫ (GlobalTheory.VarFlag.Vo C).ι` using `(hU K z₀).unique (hH K z₀) hz₀`.

Establish `P` using `(isPullback_morphismRestrict h (GlobalTheory.VarFlag.Vo C)).flip`. Use `⟨P.lift z₀ w e₀, P.lift_snd _ _ _, fun y hy => ?_⟩` and prove the remaining obligations. Apply `P.hom_ext` to reduce the goal to its premises. Rewrite using `[P.lift_fst]`. Establish `ey : (y ≫ (h ⁻¹ᵁ GlobalTheory.VarFlag.Vo C).ι) ≫ h = w ≫ (GlobalTheory.VarFlag.Vo C).ι`.

Rewrite using `[Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy]`. Establish `hr` using `hH K (y ≫ (h ⁻¹ᵁ GlobalTheory.VarFlag.Vo C).ι)`. Rewrite `hr` using `[ey]`. Use `GlobalTheory.T.flagBundle_point_flags_unique_flagCover_point X C hF hT K _ _ _ hp hr hz₀` as an intermediate fact. Conclude with `(cancel_mono (GlobalTheory.CompHS.inc₀ X Z)).1 this`.

Rewrite using `[P.lift_snd]`. Conclude with `hy`.
-/
theorem isIso_restrict_Vo : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (h : GlobalTheory.CompHS.Y₀ X Z ⟶ C.Y.X) [IsProper h], (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), ∃! p : Sp K ⟶ C.Y.X, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) (z ≫ h)) → IsIso (h ∣_ GlobalTheory.VarFlag.Vo C) := by
  intro E _ _ _ H Dw l Xo c Y X Z hF C hT B j _ f hπ hB h _ hU hH
  have := C.Y.isNormalScheme
  have hN := GlobalTheory.IsNormalScheme.pred (GlobalTheory.VarFlag.Vo C).toScheme
  have : IsLocallyNoetherian C.Y.X := LocallyOfFiniteType.isLocallyNoetherian C.Y.str
  refine GlobalTheory.isIso_of_isProper_of_existsUnique_field_point _ _ _ inferInstance inferInstance hN inferInstance
    fun K _ w => ?_
  have hp : ∀ s, (w ≫ (GlobalTheory.VarFlag.Vo C).ι) s ∈ GlobalTheory.VarFlag.Vo C := fun s => by
    rw [Scheme.Hom.comp_apply]; exact (w s).2
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.exists_flagModel_point_of_flagBundle_fieldPoint X Z hF C hT B j f hπ hB K _ hp
  have e₀ : z₀ ≫ h = w ≫ (GlobalTheory.VarFlag.Vo C).ι := (hU K z₀).unique (hH K z₀) hz₀
  have P := (isPullback_morphismRestrict h (GlobalTheory.VarFlag.Vo C)).flip
  refine ⟨P.lift z₀ w e₀, P.lift_snd _ _ _, fun y hy => ?_⟩
  apply P.hom_ext
  · rw [P.lift_fst]
    have ey : (y ≫ (h ⁻¹ᵁ GlobalTheory.VarFlag.Vo C).ι) ≫ h = w ≫ (GlobalTheory.VarFlag.Vo C).ι := by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy]
    have hr := hH K (y ≫ (h ⁻¹ᵁ GlobalTheory.VarFlag.Vo C).ι)
    rw [ey] at hr
    have := GlobalTheory.T.flagBundle_point_flags_unique_flagCover_point X C hF hT K _ _ _ hp hr hz₀
    exact (cancel_mono (GlobalTheory.CompHS.inc₀ X Z)).1 this
  · rw [P.lift_snd]; exact hy

end GlobalTheory.VarFlag
