import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOfIsClosedRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianOpen

/- English proof (translation)
Establish `sq : IsPullback (pullback.lift (pullback.fst f (h ≫ g)) (pullback.snd f (h ≫ g) ≫ h) (by rw [pullback.condition, Category.assoc])) (pullback.snd f (h ≫ g)) (pullback.snd f g) h` using `IsPullback.of_right (by rw [pullback.lift_fst]; exact IsPullback.of_hasPullback f (h ≫ g)) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f g)`. Conclude with `P.of_isPullback sq H`.
-/
theorem snd_comp (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] {X Y Z W : Scheme.{0}}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Y) (H : P (pullback.snd f g)) : P (pullback.snd f (h ≫ g)) := by
  have sq : IsPullback (pullback.lift (pullback.fst f (h ≫ g)) (pullback.snd f (h ≫ g) ≫ h)
      (by rw [pullback.condition, Category.assoc])) (pullback.snd f (h ≫ g)) (pullback.snd f g) h :=
    IsPullback.of_right (by rw [pullback.lift_fst]; exact IsPullback.of_hasPullback f (h ≫ g))
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f g)
  exact P.of_isPullback sq H

/- English proof (translation)
Rewrite using `[← pullbackLeftPullbackSndIso_hom_snd f g h]`. Conclude with `P.cancel_left_of_respectsIso _ _`.
-/
theorem snd_snd_iff (P : MorphismProperty Scheme.{0}) [P.RespectsIso] {X Y Z W : Scheme.{0}}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Y) : P (pullback.snd (pullback.snd f g) h) ↔ P (pullback.snd f (h ≫ g)) := by
  rw [← pullbackLeftPullbackSndIso_hom_snd f g h]
  exact P.cancel_left_of_respectsIso _ _

end GlobalTheory.AbelianOpen

open GlobalTheory.AbelianOpen in

/- English proof (translation)
Introduce `S _ _ K _ η hη G _ hG B _ φ hφ hB`. Use `hG.smooth` as an intermediate fact. Use `hG.separated` as an intermediate fact. Use `hG.quasiCompact` as an intermediate fact. Establish `hP0 : IsProper (pullback.snd G.hom η)`.

Use `hB.proper` as an intermediate fact. Rewrite `this` using `[← hφ.1.isoPullback_hom_snd]`. Conclude with `(MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp this`. Take `⟨e, he⟩` from `hη`. Establish `hP1 : IsProper (pullback.snd G.hom (S.fromSpecStalk (genericPoint S)))`.

Establish `: S.fromSpecStalk (genericPoint S) = e.inv ≫ η` using `by rw [← he, e.inv_hom_id_assoc]`. Rewrite using `[this]`. Conclude with `snd_comp @IsProper _ _ _ hP0`. Take `⟨V, hV, hxV, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens) (show genericPoint S ∈ (⊤ : S.Opens) from trivial)`. Establish `hV : IsAffineOpen V` using `hV`.

Use `haveI : Nonempty V := ⟨⟨_, hxV⟩⟩`. Use `haveI : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩`. Set `p : pullback G.hom hV.fromSpec ⟶ Sp Γ(S, V)` to `pullback.snd G.hom hV.fromSpec`. Establish `hUC : UniversallyClosed (pullback.snd p (spMap (algebraMap Γ(S, V) S.functionField)))`. It suffices to establish `h : IsProper (pullback.snd p (spMap (algebraMap Γ(S, V) S.functionField))) from h.toUniversallyClosed`.

Rewrite using `[snd_snd_iff @IsProper]`. Rewrite `hP1` using `[← hV.fromSpecStalk_eq_fromSpecStalk hxV]`. Conclude with `hP1`. Take `⟨s, hs⟩` from `GlobalTheory.ProperLimit.exists_finset_isProper Γ(S, V) S.functionField p`. Use `haveI := functionField_isFractionRing_of_isAffineOpen S V hV`.

Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors Γ(S, V)) s`. Set `f : Γ(S, V)` to `(b : Γ(S, V))`. Set `U : S.Opens` to `S.basicOpen f`. Establish `hU : IsAffineOpen U` using `hV.basicOpen f`. Establish `hinj : Function.Injective (algebraMap Γ(S, V) S.functionField)` using `IsFractionRing.injective _ _`.

Establish `hxU : genericPoint S ∈ U`. Use `(S.mem_basicOpen f (genericPoint S) hxV).2 ?_` and prove the remaining obligations. Use `isUnit_iff_ne_zero.2 fun h0 => nonZeroDivisors.coe_ne_zero b (hinj ?_)` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `h0`.

Use `haveI : Nonempty U := ⟨⟨_, hxU⟩⟩`. Use `letI : Algebra Γ(S, V) Γ(S, U) := (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom.toAlgebra`. Use `haveI : IsLocalization.Away f Γ(S, U) := hV.isLocalization_basicOpen f`. Set `τ : Γ(S, U) →ₐ[Γ(S, V)] S.functionField` to `{ (S.germToFunctionField U).hom with commutes' := fun r => TopCat.Presheaf.germ_res_apply S.presheaf (homOfLE (S.basicOpen_le f)) _ _ r }`. Establish `hτ : Function.Injective τ` using `S.germToFunctionField_injective U`.

Establish `hle : Algebra.adjoin Γ(S, V) (s : Set S.functionField) ≤ τ.range`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce `x hx`. Take `⟨a, ha⟩` from `hb x hx`. Establish `hfu : IsUnit (algebraMap Γ(S, V) Γ(S, U) f)` using `IsLocalization.Away.algebraMap_isUnit f`.

Use `⟨(hfu.unit⁻¹ : Γ(S, U)ˣ) * algebraMap _ _ a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `τ _ = x`. Rewrite using `[map_mul, AlgHom.commutes, ha, Algebra.smul_def, ← mul_assoc, ← AlgHom.commutes τ, ← map_mul]`. Express the relevant statement in the definitionally equal form `τ (↑hfu.unit⁻¹ * ↑hfu.unit) * x = x`. Rewrite using `[Units.inv_mul, map_one, one_mul]`.

Set `ψ : Algebra.adjoin Γ(S, V) (s : Set S.functionField) →ₐ[Γ(S, V)] Γ(S, U)` to `((AlgEquiv.ofInjective τ hτ).symm : τ.range →ₐ[Γ(S, V)] Γ(S, U)).comp (Subalgebra.inclusion hle)`. Establish `key : U.ι = (hU.isoSpec.hom ≫ spMap (ψ : Algebra.adjoin Γ(S, V) (s : Set S.functionField) →+* Γ(S, U))) ≫ spMap (algebraMap Γ(S, V) (Algebra.adjoin Γ(S, V) (s : Set S.functionField))) ≫ hV.fromSpec`. Rewrite using `[Category.assoc, ← Category.assoc (spMap _), ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]`. Use `erw [hV.map_fromSpec hU (homOfLE (S.basicOpen_le f)).op]`. Rewrite using `[← hU.isoSpec_inv_ι, Iso.hom_inv_id_assoc]`.

Establish `hProp : IsProper (pullback.snd G.hom U.ι)`. Rewrite using `[key]`. Apply `snd_comp @IsProper` to reduce the goal to its premises. Conclude with `(snd_snd_iff @IsProper _ _ _).mp hs`. Establish `hGU` using `IsSemiAbelian.pullback U.ι G hG`.

Conclude with `⟨U, hxU, ⟨hGU.comm, hGU.smooth, hProp, hGU.geomConnected⟩⟩`.
-/
theorem GlobalTheory.AbelianOpen.exists_open_isAbelianScheme : ∀ (S : Scheme.{0}) [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] (K : Type) [Field K] (η : Sp K ⟶ S),
    GlobalTheory.IsGenericPointHom η → ∀ (G : Over S) [GrpObj G], IsSemiAbelian G →
    ∀ (B : Over (Sp K)) [GrpObj B] (φ : B.left ⟶ G.left), IsGrpPullback B G η φ → IsAbelianScheme B →
    ∃ U : S.Opens, genericPoint S ∈ U ∧ IsAbelianScheme ((Over.pullback U.ι).obj G) := by
  intro S _ _ K _ η hη G _ hG B _ φ hφ hB
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact

  have hP0 : IsProper (pullback.snd G.hom η) := by
    have := hB.proper
    rw [← hφ.1.isoPullback_hom_snd] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mp this
  obtain ⟨e, he⟩ := hη
  have hP1 : IsProper (pullback.snd G.hom (S.fromSpecStalk (genericPoint S))) := by
    have : S.fromSpecStalk (genericPoint S) = e.inv ≫ η := by rw [← he, e.inv_hom_id_assoc]
    rw [this]
    exact snd_comp @IsProper _ _ _ hP0

  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show genericPoint S ∈ (⊤ : S.Opens) from trivial)
  have hV : IsAffineOpen V := hV
  haveI : Nonempty V := ⟨⟨_, hxV⟩⟩
  haveI : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let p : pullback G.hom hV.fromSpec ⟶ Sp Γ(S, V) := pullback.snd G.hom hV.fromSpec
  have hUC : UniversallyClosed (pullback.snd p (spMap (algebraMap Γ(S, V) S.functionField))) := by
    suffices h : IsProper (pullback.snd p (spMap (algebraMap Γ(S, V) S.functionField))) from h.toUniversallyClosed
    rw [snd_snd_iff @IsProper]
    rw [← hV.fromSpecStalk_eq_fromSpecStalk hxV] at hP1
    exact hP1
  obtain ⟨s, hs⟩ := GlobalTheory.ProperLimit.exists_finset_isProper Γ(S, V) S.functionField p
  haveI := functionField_isFractionRing_of_isAffineOpen S V hV
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors Γ(S, V)) s
  let f : Γ(S, V) := (b : Γ(S, V))
  let U : S.Opens := S.basicOpen f
  have hU : IsAffineOpen U := hV.basicOpen f
  have hinj : Function.Injective (algebraMap Γ(S, V) S.functionField) := IsFractionRing.injective _ _
  have hxU : genericPoint S ∈ U := by
    refine (S.mem_basicOpen f (genericPoint S) hxV).2 ?_
    refine isUnit_iff_ne_zero.2 fun h0 => nonZeroDivisors.coe_ne_zero b (hinj ?_)
    rw [map_zero]
    exact h0
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  letI : Algebra Γ(S, V) Γ(S, U) := (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom.toAlgebra
  haveI : IsLocalization.Away f Γ(S, U) := hV.isLocalization_basicOpen f
  let τ : Γ(S, U) →ₐ[Γ(S, V)] S.functionField :=
    { (S.germToFunctionField U).hom with
      commutes' := fun r => TopCat.Presheaf.germ_res_apply S.presheaf (homOfLE (S.basicOpen_le f)) _ _ r }
  have hτ : Function.Injective τ := S.germToFunctionField_injective U
  have hle : Algebra.adjoin Γ(S, V) (s : Set S.functionField) ≤ τ.range := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    obtain ⟨a, ha⟩ := hb x hx
    have hfu : IsUnit (algebraMap Γ(S, V) Γ(S, U) f) := IsLocalization.Away.algebraMap_isUnit f
    refine ⟨(hfu.unit⁻¹ : Γ(S, U)ˣ) * algebraMap _ _ a, ?_⟩
    change τ _ = x
    rw [map_mul, AlgHom.commutes, ha, Algebra.smul_def, ← mul_assoc,
      ← AlgHom.commutes τ, ← map_mul]
    change τ (↑hfu.unit⁻¹ * ↑hfu.unit) * x = x
    rw [Units.inv_mul, map_one, one_mul]
  let ψ : Algebra.adjoin Γ(S, V) (s : Set S.functionField) →ₐ[Γ(S, V)] Γ(S, U) :=
    ((AlgEquiv.ofInjective τ hτ).symm : τ.range →ₐ[Γ(S, V)] Γ(S, U)).comp (Subalgebra.inclusion hle)
  have key : U.ι = (hU.isoSpec.hom ≫ spMap (ψ : Algebra.adjoin Γ(S, V) (s : Set S.functionField) →+* Γ(S, U))) ≫
      spMap (algebraMap Γ(S, V) (Algebra.adjoin Γ(S, V) (s : Set S.functionField))) ≫ hV.fromSpec := by
    rw [Category.assoc, ← Category.assoc (spMap _), ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      AlgHom.comp_algebraMap]
    erw [hV.map_fromSpec hU (homOfLE (S.basicOpen_le f)).op]
    rw [← hU.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have hProp : IsProper (pullback.snd G.hom U.ι) := by
    rw [key]
    apply snd_comp @IsProper
    exact (snd_snd_iff @IsProper _ _ _).mp hs
  have hGU := IsSemiAbelian.pullback U.ι G hG
  exact ⟨U, hxU, ⟨hGU.comm, hGU.smooth, hProp, hGU.geomConnected⟩⟩
