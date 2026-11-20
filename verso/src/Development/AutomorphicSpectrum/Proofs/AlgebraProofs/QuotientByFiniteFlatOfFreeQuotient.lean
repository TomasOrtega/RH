import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatSubgroupSchemeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SeparatedOfFiniteSurjectiveQuotientStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormMapRestrictionCompatibleStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyOfFinitePresentationOfCancelStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormLineBundleDescentStatement

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR.QuotSide

section Act
variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [GrpObj A] (h : G ⟶ A) [IsMonHom h]

abbrev act : ModObj G A :=
  letI := ModObj.regular A
  Mod.scalarRestriction h A

/- English proof (translation)
Rewrite using `[Hom.mul_def]`. Express the relevant statement in the definitionally equal form `h ▷ A ≫ μ[A] = _`. Use `congr 1`.
-/
lemma act_smul : (act h).smul = (fst G A ≫ h) * snd G A := by
  rw [Hom.mul_def]
  change h ▷ A ≫ μ[A] = _
  congr 1

end Act

/- English proof (translation)
Introduce `R _ A _ L hA hL hamp B _ _ h hsub`. Use `hA.comm` as an intermediate fact. Use `hA.smooth` as an intermediate fact. Use `hA.proper` as an intermediate fact. Use `hA.geomConnected` as an intermediate fact.

Take `⟨_, hmon, hmono⟩` from `GlobalTheory.T.finite_flat_subgroup_scheme R A B h hsub`. Use `letI := act h`. Establish `hgam : (γ[sp (R₀` using `R) B, A] : sp (R₀ := R) B ⊗ A ⟶ A) = (fst _ A ≫ h) * snd _ A := act_smul h`. Establish `hsmul : ∀ {T : Over (Spec (CommRingCat.of R))} (g : T ⟶ sp (R₀` using `R) B) (x : T ⟶ A), g • x = (g ≫ h) * x := by`. Introduce `T g x`.

Rewrite using `[Hom.smul_def, hgam, comp_mul]`. Simplify using the standard rewrite rules. Establish `hample : GlobalTheory.IsAmpleLB L` using `GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A hL hamp`. Establish `hG : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFiniteLocallyFree (sp (R₀` using `R) B).hom := by`. Establish `e : (sp (R₀` using `R) B).hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) := rfl`.

Use `hsub.proj` as an intermediate fact. Use `hsub.fin` as an intermediate fact. Establish `: Module.FinitePresentation R B` using `Module.finitePresentation_of_projective R B`. Establish `hfp : (algebraMap R B).FinitePresentation` using `RingHom.finitePresentation_algebraMap.2 (Algebra.FinitePresentation.of_finitePresentation R B)`. Rewrite using `[e]`.

Use `⟨(IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance), Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance), ?_⟩` and prove the remaining obligations. Conclude with `(HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 hfp`. Establish `hfree : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFreeAction (sp (R₀` using `R) B) A := by`. Introduce `T g x hx`. Rewrite `hx` using `[hsmul]`.

Establish `h1 : g ≫ h = 1` using `mul_eq_right.mp hx`. Rewrite using `[← cancel_mono h, h1, MonObj.one_comp]`. Establish `horb : ∀ x : A.left, ∃ U : A.left.Opens, IsAffineOpen U ∧ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit (sp (R₀` using `R) B) A x ⊆ U := by`. Introduce `x`. Establish `hf : IsFinite (sp (R₀` using `R) B).hom := hG.1`.

Establish `hs : IsFinite (snd (sp (R₀` using `R) B) A).left := by`. Rewrite using `[Over.snd_left]`. Use `infer_instance`. Establish `hfin : (GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit (sp (R₀` using `R) B) A x).Finite := (Scheme.Hom.finite_preimage_singleton _ x).image _`. Take `⟨n, -, s, h₁, -, h₂⟩` from `hample.exists_affine_finite_subset hfin (U := ⊤) (fun _ _ => trivial)`.

Conclude with `⟨_, h₂, h₁⟩`. Take `⟨Y, q, -, hT⟩` from `hF _ (sp (R₀ := R) B) A hG hfree horb`. Take `⟨hq1, hq2, hq3⟩` from `hT.isFiniteLocallyFree hG`. Establish `hq4` using `hT.surjective`. Establish `hq : IsPullback ((fst _ A ≫ h) * snd _ A) (snd _ A) q q` using `hgam ▸ hT.1`.

Establish `hqc : QuasiCompact q.left` using `inferInstance`. Take `⟨inst, hcomm, hhom, hker⟩` from `GlobalTheory.AbelianQuotient.exists_grpObj h q hq`. Establish `hw : q.left ≫ Y.hom = A.hom` using `Over.w q`. Establish `hsnd : IsFinite (snd (sp (R₀` using `R) B) A).left := by`. Establish `hf : IsFinite (sp (R₀` using `R) B).hom := hG.1`.

Rewrite using `[Over.snd_left]`. Use `infer_instance`. Establish `hab : IsAbelianScheme Y`. Use `GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected` as an intermediate fact. Establish `: IsSeparated Y.hom` using `GlobalTheory.T.separated_of_finite_surjective_quotient q _ _ hq hsnd inferInstance hq1 hq4`.

Establish `: Flat (q.left ≫ Y.hom)` using `by rw [hw]; infer_instance`. Establish `: UniversallyClosed (q.left ≫ Y.hom)` using `by rw [hw]; infer_instance`. Establish `: GeometricallyReduced (q.left ≫ Y.hom)` using `by rw [hw]; infer_instance`. Establish `: GeometricallyConnected (q.left ≫ Y.hom)` using `by rw [hw]; infer_instance`. Use `GlobalTheory.flat_of_comp_of_flat_of_surjective q.left Y.hom` as an intermediate fact.

Use `UniversallyClosed.of_comp_surjective q.left Y.hom` as an intermediate fact. Use `GlobalTheory.AbelianQuotient.geometricallyReduced_of_comp q.left Y.hom` as an intermediate fact. Establish `: LocallyOfFinitePresentation Y.hom` using `GlobalTheory.T.locallyOfFinitePresentation_of_cancel q.left Y.hom hq1 hq2 hq3 hq4 (by rw [hw]; infer_instance)`. Conclude with `⟨hcomm, GlobalTheory.AbelianQuotient.smooth_of_grpObj_of_flat Y, ⟨⟩, GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp q.left Y.hom⟩`. Use `hab.proper` as an intermediate fact.

Take `⟨N, hN₁, hN₂⟩` from `GlobalTheory.T.norm_map_restriction_compatible q.left hq1 hq2 hq3`. Take `⟨L', hL', hN⟩` from `GlobalTheory.T.norm_line_bundle_descent q.left hq1 N hN₁ hN₂ L hL (by`. Introduce `y`. Take `⟨W, -, h₁, -, t⟩` from `hample.exists_affine_finite_subset_trivial hL (Scheme.Hom.finite_preimage_singleton q.left y) (U := ⊤) (fun _ _ => trivial)`. Conclude with `⟨W, fun x hx => h₁ hx, t⟩)`.

Use `⟨Y, inst, L', q, hab, hL', ?_, hhom, hq1, hq2, hq4, ?_⟩` and prove the remaining obligations. Establish `: CompactSpace A.left` using `QuasiCompact.compactSpace_of_compactSpace A.hom`. Establish `: CompactSpace Y.left` using `q.left.surjective.compactSpace q.left.continuous`. Use `(GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine Y hL').2 (GlobalTheory.isAmpleLB_of_forall_le hL' fun y U hy => ?_)` and prove the remaining obligations. Take `⟨n, hn, s, h₁, h₂, -⟩` from `hample.exists_affine_finite_subset (Scheme.Hom.finite_preimage_singleton q.left y) (U := q.left ⁻¹ᵁ U) (fun x hx => show q.left x ∈ U from (show q.left x = y from hx) ▸ hy)`.

Take `⟨σ, hσ⟩` from `hN n s`. Use `⟨n, hn, σ, (hσ y).2 fun x hx => h₁ hx, fun y' hy' => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `q.left.surjective y'`. Conclude with `h₂ ((hσ _).1 hy' x rfl)`. Introduce `S _ _ z`.

Establish `hhq : h ≫ q = 1` using `hker.w.trans Hom.one_def.symm`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Set `y : sp (R₀` to `R) S ⟶ sp (R₀ := R) B := hker.lift z (toUnit _) (by rw [hz, Hom.one_def])`. Establish `hy : y ≫ h = z` using `hker.lift_fst _ _ _`.

Take `⟨ψ, hψ⟩` from `Spec.map_surjective y.left`. Establish `hc : CommRingCat.ofHom (algebraMap R B) ≫ ψ = CommRingCat.ofHom (algebraMap R S)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hψ]`. Conclude with `Over.w y`.

Set `φ : B →ₐ[R] S` to `{ ψ.hom with commutes' := fun r => congr($hc r) }`. Establish `hφ : spMap φ = y` using `Over.OverMorphism.ext hψ`. Conclude with `⟨φ, by rw [hφ, hy]⟩`. Introduce and unpack `⟨φ, rfl⟩`. Rewrite using `[Category.assoc, hhq, comp_one]`.
-/
theorem quotientByFiniteFlat_of_freeQuotient (hF : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuotientScheme) :
    QuotientByFiniteFlatStatement := by
  intro R _ A _ L hA hL hamp B _ _ h hsub
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  obtain ⟨_, hmon, hmono⟩ := GlobalTheory.T.finite_flat_subgroup_scheme R A B h hsub
  letI := act h
  have hgam : (γ[sp (R₀ := R) B, A] : sp (R₀ := R) B ⊗ A ⟶ A) = (fst _ A ≫ h) * snd _ A := act_smul h
  have hsmul : ∀ {T : Over (Spec (CommRingCat.of R))} (g : T ⟶ sp (R₀ := R) B) (x : T ⟶ A),
      g • x = (g ≫ h) * x := by
    intro T g x
    rw [Hom.smul_def, hgam, comp_mul]
    simp
  have hample : GlobalTheory.IsAmpleLB L := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A hL hamp
  have hG : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFiniteLocallyFree (sp (R₀ := R) B).hom := by
    have e : (sp (R₀ := R) B).hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) := rfl
    have := hsub.proj
    have := hsub.fin
    have : Module.FinitePresentation R B := Module.finitePresentation_of_projective R B
    have hfp : (algebraMap R B).FinitePresentation :=
      RingHom.finitePresentation_algebraMap.2 (Algebra.FinitePresentation.of_finitePresentation R B)
    rw [e]
    refine ⟨(IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance),
      Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance), ?_⟩
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 hfp
  have hfree : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFreeAction (sp (R₀ := R) B) A := by
    intro T g x hx
    rw [hsmul] at hx
    have h1 : g ≫ h = 1 := mul_eq_right.mp hx
    rw [← cancel_mono h, h1, MonObj.one_comp]
  have horb : ∀ x : A.left, ∃ U : A.left.Opens, IsAffineOpen U ∧
      GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit (sp (R₀ := R) B) A x ⊆ U := by
    intro x
    have hf : IsFinite (sp (R₀ := R) B).hom := hG.1
    have hs : IsFinite (snd (sp (R₀ := R) B) A).left := by
      rw [Over.snd_left]; infer_instance
    have hfin : (GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit (sp (R₀ := R) B) A x).Finite :=
      (Scheme.Hom.finite_preimage_singleton _ x).image _
    obtain ⟨n, -, s, h₁, -, h₂⟩ := hample.exists_affine_finite_subset hfin
      (U := ⊤) (fun _ _ => trivial)
    exact ⟨_, h₂, h₁⟩
  obtain ⟨Y, q, -, hT⟩ := hF _ (sp (R₀ := R) B) A hG hfree horb
  obtain ⟨hq1, hq2, hq3⟩ := hT.isFiniteLocallyFree hG
  have hq4 := hT.surjective
  have hq : IsPullback ((fst _ A ≫ h) * snd _ A) (snd _ A) q q := hgam ▸ hT.1
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨inst, hcomm, hhom, hker⟩ := GlobalTheory.AbelianQuotient.exists_grpObj h q hq
  have hw : q.left ≫ Y.hom = A.hom := Over.w q
  have hsnd : IsFinite (snd (sp (R₀ := R) B) A).left := by
    have hf : IsFinite (sp (R₀ := R) B).hom := hG.1
    rw [Over.snd_left]; infer_instance
  have hab : IsAbelianScheme Y := by
    have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth
      hA.geomConnected
    have : IsSeparated Y.hom := GlobalTheory.T.separated_of_finite_surjective_quotient q _ _ hq hsnd inferInstance hq1 hq4
    have : Flat (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : UniversallyClosed (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : GeometricallyReduced (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : GeometricallyConnected (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have := GlobalTheory.flat_of_comp_of_flat_of_surjective q.left Y.hom
    have := UniversallyClosed.of_comp_surjective q.left Y.hom
    have := GlobalTheory.AbelianQuotient.geometricallyReduced_of_comp q.left Y.hom
    have : LocallyOfFinitePresentation Y.hom :=
      GlobalTheory.T.locallyOfFinitePresentation_of_cancel q.left Y.hom hq1 hq2 hq3 hq4 (by rw [hw]; infer_instance)
    exact ⟨hcomm, GlobalTheory.AbelianQuotient.smooth_of_grpObj_of_flat Y, ⟨⟩,
      GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp q.left Y.hom⟩
  have := hab.proper
  obtain ⟨N, hN₁, hN₂⟩ := GlobalTheory.T.norm_map_restriction_compatible q.left hq1 hq2 hq3
  obtain ⟨L', hL', hN⟩ := GlobalTheory.T.norm_line_bundle_descent q.left hq1 N hN₁ hN₂ L hL (by
    intro y
    obtain ⟨W, -, h₁, -, t⟩ := hample.exists_affine_finite_subset_trivial hL
      (Scheme.Hom.finite_preimage_singleton q.left y) (U := ⊤) (fun _ _ => trivial)
    exact ⟨W, fun x hx => h₁ hx, t⟩)
  refine ⟨Y, inst, L', q, hab, hL', ?_, hhom, hq1, hq2, hq4, ?_⟩
  · have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
    have : CompactSpace Y.left := q.left.surjective.compactSpace q.left.continuous
    refine (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine Y hL').2
      (GlobalTheory.isAmpleLB_of_forall_le hL' fun y U hy => ?_)
    obtain ⟨n, hn, s, h₁, h₂, -⟩ := hample.exists_affine_finite_subset
      (Scheme.Hom.finite_preimage_singleton q.left y) (U := q.left ⁻¹ᵁ U)
      (fun x hx => show q.left x ∈ U from (show q.left x = y from hx) ▸ hy)
    obtain ⟨σ, hσ⟩ := hN n s
    refine ⟨n, hn, σ, (hσ y).2 fun x hx => h₁ hx, fun y' hy' => ?_⟩
    obtain ⟨x, rfl⟩ := q.left.surjective y'
    exact h₂ ((hσ _).1 hy' x rfl)
  · intro S _ _ z
    have hhq : h ≫ q = 1 := hker.w.trans Hom.one_def.symm
    constructor
    · intro hz
      let y : sp (R₀ := R) S ⟶ sp (R₀ := R) B :=
        hker.lift z (toUnit _) (by rw [hz, Hom.one_def])
      have hy : y ≫ h = z := hker.lift_fst _ _ _
      obtain ⟨ψ, hψ⟩ := Spec.map_surjective y.left
      have hc : CommRingCat.ofHom (algebraMap R B) ≫ ψ = CommRingCat.ofHom (algebraMap R S) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hψ]
        exact Over.w y
      let φ : B →ₐ[R] S := { ψ.hom with
        commutes' := fun r => congr($hc r) }
      have hφ : spMap φ = y := Over.OverMorphism.ext hψ
      exact ⟨φ, by rw [hφ, hy]⟩
    · rintro ⟨φ, rfl⟩
      rw [Category.assoc, hhq, comp_one]

end GlobalTheory.CompanionTheory.Ar.GR.QuotSide
