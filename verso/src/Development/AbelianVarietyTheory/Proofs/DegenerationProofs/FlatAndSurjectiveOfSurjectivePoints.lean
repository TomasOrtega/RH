import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFormallyUnramifiedGrpEnd
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

open UnramifiedEndFlat in

/- English proof (translation)
Use `LocallyOfFiniteType.jacobsonSpace G.hom` as an intermediate fact. Establish `: IsLocallyNoetherian G'.left` using `LocallyOfFiniteType.isLocallyNoetherian G'.hom`. Establish `: LocallyOfFiniteType (φ.left ≫ G'.hom)` using `by rw [Over.w φ]; infer_instance`. Establish `: LocallyOfFiniteType φ.left` using `locallyOfFiniteType_of_comp _ G'.hom`. Establish `hξ : φ.left (genericPoint G.left) = genericPoint G'.left`.

Establish `h` using `(genericPoint_spec G.left).image φ.left.continuous`. Rewrite `h` using `[Set.image_univ, φ.left.denseRange.closure_range]`. Conclude with `h.eq (genericPoint_spec G'.left)`. Take `⟨W, hW, H⟩` from `IntDiv.exists_open_flat φ.left hξ`. Take `⟨y, hy, hyc⟩` from `nonempty_inter_closedPoints hW W.2.isLocallyClosed`.

Use `flat_of_closedPoints _ fun x hx => ?_` and prove the remaining obligations. Set `x' : 𝟙_ _ ⟶ G` to `Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2`. Set `y' : 𝟙_ _ ⟶ G` to `Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2`. Set `α` to `GrpObj.mulRight (A := G) (y'⁻¹ * x')`. Set `β` to `GrpObj.mulRight (A := G') ((y'⁻¹ * x') ≫ φ)`.

Establish `hαβ : α.hom ≫ φ = φ ≫ β.hom`. Simplify using `only [α, β]`. Generalize the expression as in `y'⁻¹ * x' = z`. Simplify using `[comp_lift_assoc]`. Establish `hα : y' ≫ α.hom = x'`.

Establish `: y' ≫ α.hom = y' * (y'⁻¹ * x')`. Simplify using `[α, comp_lift_assoc, Hom.mul_def]`. Rewrite using `[this, mul_inv_cancel_left]`. Establish `hα' : α.hom.left y = x`. Establish `h` using `congr(($hα).left (IsLocalRing.closedPoint K))`.

Rewrite using `[← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K), ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]`. Conclude with `h`. Establish `: IsIso α.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map α.hom))`. Establish `: IsIso β.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map β.hom))`. Establish `h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat`.

Rewrite using `[Scheme.Hom.stalkMap_comp]`. Conclude with `(Flat.stalkMap β.hom.left _).comp (H y hy)`. Rewrite `h1` using `[← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp]`. Rewrite using `[← hα']`. Conclude with `(RingHom.Flat.respectsIso.cancel_right_isIso (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1`.
-/
theorem flat_of_isDominant_grpHom (K : Type) [Field K] [IsAlgClosed K]
    (G G' : Over (Sp K)) [GrpObj G] [GrpObj G'] [IrreducibleSpace G.left] [IsIntegral G'.left]
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType G'.hom] (φ : G ⟶ G') [IsMonHom φ]
    [QuasiCompact φ.left] [IsDominant φ.left] : Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have : LocallyOfFiniteType (φ.left ≫ G'.hom) := by rw [Over.w φ]; infer_instance
  have : LocallyOfFiniteType φ.left := locallyOfFiniteType_of_comp _ G'.hom
  have hξ : φ.left (genericPoint G.left) = genericPoint G'.left := by
    have h := (genericPoint_spec G.left).image φ.left.continuous
    rw [Set.image_univ, φ.left.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec G'.left)
  obtain ⟨W, hW, H⟩ := IntDiv.exists_open_flat φ.left hξ
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
  refine flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
  let α := GrpObj.mulRight (A := G) (y'⁻¹ * x')
  let β := GrpObj.mulRight (A := G') ((y'⁻¹ * x') ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp only [α, β]
    generalize y'⁻¹ * x' = z
    simp [comp_lift_assoc]
  have hα : y' ≫ α.hom = x' := by
    have : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
      simp [α, comp_lift_assoc, Hom.mul_def]
    rw [this, mul_inv_cancel_left]
  have hα' : α.hom.left y = x := by
    have h := congr(($hα).left (IsLocalRing.closedPoint K))
    rw [← pointOfClosedPoint_apply G.hom x hx (IsLocalRing.closedPoint K),
      ← pointOfClosedPoint_apply G.hom y hyc (IsLocalRing.closedPoint K)]
    exact h
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap y).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp (H y hy)
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp h1

/- English proof (translation)
Introduce `k _ _ G G' _ _ ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ i _ hi`. Use `grpObj_geometricallyIntegral_of_smooth _ G` as an intermediate fact. Use `grpObj_geometricallyIntegral_of_smooth _ G'` as an intermediate fact. Establish `: IsIntegral G.left` using `GeometricallyIntegral.isIntegral_of_subsingleton G.hom`. Establish `: IsIntegral G'.left` using `GeometricallyIntegral.isIntegral_of_subsingleton G'.hom`.

Establish `: QuasiCompact (i.left ≫ G'.hom)` using `by rw [Over.w]; infer_instance`. Establish `: QuasiCompact i.left` using `.of_comp _ G'.hom`. Establish `: Surjective i.left` using `DivisiblePart.surjective_of_rationalPoints i hi`. Conclude with `⟨flat_of_isDominant_grpHom k G G' i, this⟩`.
-/
theorem flat_and_surjective_of_surjective_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'], SmConn G → SmConn G' → ∀ i : G ⟶ G', IsMonHom i → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ i = y) → Flat i.left ∧ Surjective i.left := by
  intro k _ _ G G' _ _ ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ i _ hi
  have := grpObj_geometricallyIntegral_of_smooth _ G
  have := grpObj_geometricallyIntegral_of_smooth _ G'
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  have : IsIntegral G'.left := GeometricallyIntegral.isIntegral_of_subsingleton G'.hom
  have : QuasiCompact (i.left ≫ G'.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact i.left := .of_comp _ G'.hom
  have : Surjective i.left := DivisiblePart.surjective_of_rationalPoints i hi
  exact ⟨flat_of_isDominant_grpHom k G G' i, this⟩

end GlobalTheory.SS
