import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

/- English proof (translation)
Introduce `R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a`. Use `⟨fun b b' hb hb' => ?_, fun h h' hh hh' => ?_⟩` and prove the remaining obligations. Take `⟨_, -, -, _⟩` from `hR`. Use `D₁.toPre.P.isAb.smooth` as an intermediate fact. Use `D₁.toPre.P.isAb.geomConnected` as an intermediate fact.

Use `D₁.toPre.P.isAb.proper` as an intermediate fact. Use `D₂.toPre.P.isAb.proper` as an intermediate fact. Use `(sec_eq_zero_and_hom_eq_of_thickenings R I (IsAdicComplete.le_jacobson_bot I) D₁.toPre.P.A).2 _ b b' fun e => ?_` and prove the remaining obligations. Use `(U₁.gt e).q_flat` as an intermediate fact. Use `(U₁.gt e).q_surj` as an intermediate fact.

Use `(U₁.gt e).q_affine` as an intermediate fact. Use `FlatQuotient.epi_of_flat_surjective (U₁.gt e).q` as an intermediate fact. Establish `k` using `congrArg (fun q => q.left ≫ pullback.fst D₂.toPre.P.A.hom (thick R I e)) ((cancel_epi _).1 ((hb e).symm.trans (hb' e)))`. Conclude with `(pullback.lift_fst _ _ _).symm.trans (k.trans (pullback.lift_fst _ _ _))`. Use `hR.2.2.2` as an intermediate fact.

Use `EndTorus.connectedSpace_thickening I 0` as an intermediate fact. Establish `: Mono (U₂.gt 0).i`. Establish `: Mono (η[thickObj R I 0 D₂.toPre.P.A])` using `⟨fun _ _ _ => toUnit_unique _ _⟩`. Conclude with `(MorphismProperty.monomorphisms _).of_isPullback (U₂.gt 0).isKernel.flip (.infer_property _)`. Take `⟨t, ht, e⟩` from `hh 0`.

Take `⟨t', ht', e'⟩` from `hh' 0`. Take `rfl : t = t'` from `(cancel_mono _).1 (e.symm.trans e')`. Use function extensionality and compare the values at `χ`. Conclude with `SplitTorusHom.charUnit_injective (S := Sp (R ⧸ I ^ (0 + 1))) (congrArg Units.val ((ht χ).symm.trans (ht' χ)))`.
-/
theorem over₀_onTorus_unique : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), (∀ b b' : D₁.toPre.P.A ⟶ D₂.toPre.P.A, Over₀ U₁ U₂ a b → Over₀ U₁ U₂ a b' → b = b') ∧ ∀ h h' : D₂.toPre.X → D₁.toPre.X, OnTorus U₁ U₂ a h → OnTorus U₁ U₂ a h' → h = h' := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a
  refine ⟨fun b b' hb hb' => ?_, fun h h' hh hh' => ?_⟩
  · obtain ⟨_, -, -, _⟩ := hR
    have := D₁.toPre.P.isAb.smooth
    have := D₁.toPre.P.isAb.geomConnected
    have := D₁.toPre.P.isAb.proper
    have := D₂.toPre.P.isAb.proper
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I (IsAdicComplete.le_jacobson_bot I) D₁.toPre.P.A).2 _ b b'
      fun e => ?_
    have := (U₁.gt e).q_flat
    have := (U₁.gt e).q_surj
    have := (U₁.gt e).q_affine
    have := FlatQuotient.epi_of_flat_surjective (U₁.gt e).q
    have k := congrArg (fun q => q.left ≫ pullback.fst D₂.toPre.P.A.hom (thick R I e))
      ((cancel_epi _).1 ((hb e).symm.trans (hb' e)))
    exact (pullback.lift_fst _ _ _).symm.trans (k.trans (pullback.lift_fst _ _ _))
  · have := hR.2.2.2
    have := EndTorus.connectedSpace_thickening I 0
    have : Mono (U₂.gt 0).i := by
      have : Mono (η[thickObj R I 0 D₂.toPre.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
      exact (MorphismProperty.monomorphisms _).of_isPullback (U₂.gt 0).isKernel.flip (.infer_property _)
    obtain ⟨t, ht, e⟩ := hh 0
    obtain ⟨t', ht', e'⟩ := hh' 0
    obtain rfl : t = t' := (cancel_mono _).1 (e.symm.trans e')
    funext χ
    exact SplitTorusHom.charUnit_injective (S := Sp (R ⧸ I ^ (0 + 1)))
      (congrArg Units.val ((ht χ).symm.trans (ht' χ)))

end GlobalTheory.Mum.Two
