import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusPart

/- English proof (translation)
Introduce `V _ _ _ G _ _ hG G₁ _ φ₁ h₁ hT Ω _ α G' _ φ h X _ _ _ i hi`. Take `⟨T⟩` from `hT`. Use `letI := T.addCommGroup`. Use `letI := T.grpB`. Use `haveI := T.free`.

Use `haveI := T.finite`. Use `T.i_hom` as an intermediate fact. Use `T.q_hom` as an intermediate fact. Use `T.isAbelian.proper` as an intermediate fact. Use `set a := algebraMap V (FractionRing V)`.

Establish `ef : spMap (α.comp a) = spMap α ≫ spMap a`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Set `ψ : G'.left ⟶ G₁.left` to `h₁.1.lift φ (G'.hom ≫ spMap α) (by`. Rewrite using `[Category.assoc, ← ef]`.

Conclude with `h.1.w)`. Establish `hψ : ψ ≫ φ₁ = φ` using `h₁.1.lift_fst _ _ _`. Establish `h₂ : IsGrpPullback G' G₁ (spMap α) ψ` using `h₁.cancel (h.congr ef hψ.symm) (h₁.1.lift_snd _ _ _)`. Take `⟨q', hq', hk⟩` from `exists_isKernel_pullTorus h₂ T.i T.q T.isKernel`. Establish `: IsProper ((Over.pullback (spMap α)).obj T.B).hom` using `inferInstanceAs (IsProper (pullback.snd _ _))`.

Establish `hiq : i ≫ q' = toUnit _ ≫ η[(Over.pullback (spMap α)).obj T.B]` using `splitTorus_hom_proper_trivial_local Ω X _ (i ≫ q') inferInstance`. Establish `: Mono (pullTorus h₂ T.i)` using `⟨fun x y e => hk.hom_ext e (toUnit_unique _ _)⟩`. Set `u'` to `hk.lift i (toUnit _) hiq`. Establish `hu' : u' ≫ pullTorus h₂ T.i = i` using `hk.lift_fst _ _ _`. Establish `: IsMonHom u'` using `Serre.isMonHom_of_mul_comp u' fun S x y => by`.

Rewrite using `[← cancel_mono (pullTorus h₂ T.i), MonObj.mul_comp (x ≫ u'), Category.assoc, Category.assoc, Category.assoc, hu', MonObj.mul_comp]`. Use `haveI : ConnectedSpace (Sp Ω) := SplitTorus.connectedSpace_of_isLocalRing Ω`. Take `⟨u, hu⟩` from `SplitTorus.exists_eq_torusMap u'`. Take `⟨e, he, heφ⟩` from `grpPullback_iso h₁ (isGrpPullback_pullback G (spMap a))`. Set `j₁ : splitTorus (Sp (FractionRing V)) X ⟶ G₁` to `SplitTorus.torusMap _ u ≫ T.i`.

Establish `: IsMonHom j₁` using `inferInstance`. Set `f` to `(SplitTorus.bcIso (spMap a) X).inv ≫ j₁ ≫ e.hom`. Establish `: IsMonHom f` using `inferInstance`. Take `⟨F, ⟨hF, hF'⟩, -⟩` from `homExtension_semiAbelian_dvr V (FractionRing V) (splitTorus (Sp V) X) G inferInstance hG f inferInstance`. Use `⟨F, hF, ?_⟩` and prove the remaining obligations.

Establish `hj₁ : pullTorus h₁ F = j₁`. Rewrite using `[eq_comm, eq_pullTorus_iff]`. Establish `k : f.left ≫ pullback.fst G.hom (spMap a) = pullback.fst (splitTorus (Sp V) X).hom (spMap a) ≫ F.left`. Rewrite using `[← hF']`. Conclude with `pullback.lift_fst _ _ _`.

Establish `k2` using `congrArg ((SplitTorus.bcIso (spMap a) X).hom.left ≫ ·) k`. Simplify using `only [f, Over.comp_left, Category.assoc, heφ] at k2`. Rewrite `k2` using `[← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp, SplitTorus.bcIso_hom_fst_assoc]`. Conclude with `k2`. Rewrite using `[← pullTorus_pullTorus h₂ h₁ h ef hψ.symm, hj₁, pullTorus_torusMap_comp, ← hu, hu']`.
-/
theorem extend_torus_hom_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (G₁ : Over (Sp (FractionRing V))) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left),
    IsGrpPullback G₁ G (spMap (algebraMap V (FractionRing V))) φ₁ → Nonempty (TorusExtension G₁) →
    ∀ (Ω : Type) [Field Ω] (α : FractionRing V →+* Ω) (G' : Over (Sp Ω)) [GrpObj G'] (φ : G'.left ⟶ G.left)
      (h : IsGrpPullback G' G (spMap (α.comp (algebraMap V (FractionRing V)))) φ)
      (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp Ω) X ⟶ G'), IsMonHom i →
      ∃ j : splitTorus (Sp V) X ⟶ G, IsMonHom j ∧ GlobalTheory.TorusPart.pullTorus h j = i := by
  intro V _ _ _ G _ _ hG G₁ _ φ₁ h₁ hT Ω _ α G' _ φ h X _ _ _ i hi
  obtain ⟨T⟩ := hT
  letI := T.addCommGroup; letI := T.grpB
  haveI := T.free; haveI := T.finite
  have := T.i_hom; have := T.q_hom; have := T.isAbelian.proper
  set a := algebraMap V (FractionRing V)
  have ef : spMap (α.comp a) = spMap α ≫ spMap a := by
    rw [← Spec.map_comp]; rfl

  let ψ : G'.left ⟶ G₁.left := h₁.1.lift φ (G'.hom ≫ spMap α) (by
    rw [Category.assoc, ← ef]; exact h.1.w)
  have hψ : ψ ≫ φ₁ = φ := h₁.1.lift_fst _ _ _
  have h₂ : IsGrpPullback G' G₁ (spMap α) ψ :=
    h₁.cancel (h.congr ef hψ.symm) (h₁.1.lift_snd _ _ _)

  obtain ⟨q', hq', hk⟩ := exists_isKernel_pullTorus h₂ T.i T.q T.isKernel
  have : IsProper ((Over.pullback (spMap α)).obj T.B).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  have hiq : i ≫ q' = toUnit _ ≫ η[(Over.pullback (spMap α)).obj T.B] :=
    splitTorus_hom_proper_trivial_local Ω X _ (i ≫ q') inferInstance
  have : Mono (pullTorus h₂ T.i) := ⟨fun x y e => hk.hom_ext e (toUnit_unique _ _)⟩
  let u' := hk.lift i (toUnit _) hiq
  have hu' : u' ≫ pullTorus h₂ T.i = i := hk.lift_fst _ _ _
  have : IsMonHom u' := Serre.isMonHom_of_mul_comp u' fun S x y => by
    rw [← cancel_mono (pullTorus h₂ T.i), MonObj.mul_comp (x ≫ u'), Category.assoc, Category.assoc,
      Category.assoc, hu', MonObj.mul_comp]
  haveI : ConnectedSpace (Sp Ω) := SplitTorus.connectedSpace_of_isLocalRing Ω
  obtain ⟨u, hu⟩ := SplitTorus.exists_eq_torusMap u'

  obtain ⟨e, he, heφ⟩ := grpPullback_iso h₁ (isGrpPullback_pullback G (spMap a))
  let j₁ : splitTorus (Sp (FractionRing V)) X ⟶ G₁ := SplitTorus.torusMap _ u ≫ T.i
  have : IsMonHom j₁ := inferInstance
  let f := (SplitTorus.bcIso (spMap a) X).inv ≫ j₁ ≫ e.hom
  have : IsMonHom f := inferInstance
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := homExtension_semiAbelian_dvr V (FractionRing V) (splitTorus (Sp V) X) G
    inferInstance hG f inferInstance
  refine ⟨F, hF, ?_⟩
  have hj₁ : pullTorus h₁ F = j₁ := by
    rw [eq_comm, eq_pullTorus_iff]
    have k : f.left ≫ pullback.fst G.hom (spMap a) =
        pullback.fst (splitTorus (Sp V) X).hom (spMap a) ≫ F.left := by
      rw [← hF']; exact pullback.lift_fst _ _ _
    have k2 := congrArg ((SplitTorus.bcIso (spMap a) X).hom.left ≫ ·) k
    simp only [f, Over.comp_left, Category.assoc, heφ] at k2
    rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp,
      SplitTorus.bcIso_hom_fst_assoc] at k2
    exact k2
  rw [← pullTorus_pullTorus h₂ h₁ h ef hψ.symm, hj₁, pullTorus_torusMap_comp, ← hu, hu']

end GlobalTheory.TorusPart
