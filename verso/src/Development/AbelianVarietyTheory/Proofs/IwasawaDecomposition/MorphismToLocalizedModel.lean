import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapIdOfCommonGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef

namespace GlobalTheory.TorRef

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Z R _ a b ω C _ hb ha F hF hj`. Use `haveI := c.fin`. Use `haveI : NumberField c.F := ⟨⟩`. Use `haveI : IsOpenImmersion (spMap b) := by`. Use `letI := b.toAlgebra`.

Conclude with `IsOpenImmersion.of_isLocalization (R := 𝓞 c.F) (S := R) a`. Establish `hω : spMap ω ≫ spMap b = spMap (algebraMap (𝓞 c.F) c.F)`. Rewrite using `[← hb]`. Conclude with `(Spec.map_comp (CommRingCat.ofHom b) (CommRingCat.ofHom ω)).symm`. Establish `hjs : Z.j ≫ Z.s = (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ spMap ω) ≫ spMap b`.

Express the relevant statement in the definitionally equal form `(Z.jQ ≫ pullback.fst _ _) ≫ Z.s = _`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, Z.jQ_over, Category.assoc, hω]`. Set `jX : Xo.XF c ⟶ pullback Z.s (spMap b)` to `pullback.lift Z.j _ hjs`. Establish `hjX : jX ≫ pullback.fst _ _ = Z.j` using `pullback.lift_fst _ _ _`. Establish `hjF : jX ≫ F = C.j` using `hj _ hjX`.

Take `⟨-, -, -, h₁, h₂, h₃, h₄⟩` from `GlobalTheory.genericPart_dense_proOpen (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open Z.jQ_dense`. Establish `sq : IsPullback (𝟙 _) jX Z.j (pullback.fst Z.s (spMap b))` using `IsPullback.of_horiz_isIso_mono ⟨by rw [hjX, Category.id_comp]⟩`. Establish `hpre : IsPreimmersion jX` using `MorphismProperty.of_isPullback sq h₁`. Establish `hfl : Flat jX` using `MorphismProperty.of_isPullback sq h₂`. Establish `hqc : QuasiCompact jX` using `MorphismProperty.of_isPullback sq h₄`.

Establish `hdom : IsDominant jX`. Prove the components needed by the constructor for the conclusion. Establish `e : Set.range jX = pullback.fst Z.s (spMap b) ⁻¹' Set.range Z.j`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨x, by rw [← hjX, Scheme.Hom.comp_apply]⟩`. Introduce and unpack `⟨x, hx⟩`. Conclude with `⟨x, (pullback.fst Z.s (spMap b)).isOpenEmbedding.injective (by rw [← hx, ← hjX, Scheme.Hom.comp_apply])⟩`. Use `haveI : IsDominant Z.j := h₃`.

Rewrite using `[DenseRange, e]`. Conclude with `(Z.j).denseRange.preimage (pullback.fst Z.s (spMap b)).isOpenEmbedding.isOpenMap`. Establish `hX : Geo.Tor.IsNormalScheme (pullback Z.s (spMap b)) ∧ ∃ z : pullback Z.s (spMap b) ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z`. Use `⟨fun y => ?_, pullback.fst _ _ ≫ Z.s ≫ spMap (algebraMap ℤ (𝓞 c.F)), ?_, ?_⟩` and prove the remaining obligations. Take `⟨_, _⟩` from `Z.normal (pullback.fst Z.s (spMap b) y)`.

Establish `e` using `(asIso ((pullback.fst Z.s (spMap b)).stalkMap y)).commRingCatIsoToRingEquiv`. Conclude with `⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩`. Establish `hprop : IsProper Z.s`. Take `⟨N, i, hi, e⟩` from `Z.proj`. Use `ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (𝓞 c.F) N` as an intermediate fact.

Rewrite using `[← e]`. Use `infer_instance`. Establish `: LocallyOfFiniteType (spMap (algebraMap ℤ (𝓞 c.F)))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]`. Conclude with `RingHom.finiteType_algebraMap.mpr inferInstance`.

Use `infer_instance`. Use `Z.flat` as an intermediate fact. Establish `: Flat (spMap (algebraMap ℤ (𝓞 c.F)))`. Rewrite using `[Flat.SpecMap_iff]`. Conclude with `RingHom.flat_algebraMap_iff.mpr inferInstance`.

Use `infer_instance`. Take `⟨_, _, _, _, _, m₁, -⟩` from `sabPull Out.CubePf.cubePull (pullback.fst Z.s (spMap b)) Z.t`. Take `⟨_, _, _, _, _, n, -⟩` from `sabPull Out.CubePf.cubePull F C.t`. Take `⟨a₁, ha₁⟩` from `LevelCover.sab_cancel m₁ Z.m jX hjX`. Take `⟨ν', hν'⟩` from `LevelCover.sab_cancel C.m0.toSABMap Z.m0.toSABMap (𝟙 _) (Category.id_comp _)`.

Take `⟨μ, hμ⟩` from `LevelCover.sab_comp ν' C.m (e := jX ≫ F) (by rw [Category.id_comp, hjF]; rfl)`. Take `⟨a₂, ha₂⟩` from `LevelCover.sab_cancel n μ jX rfl`. Take `⟨β, hβ⟩` from `GlobalTheory.exists_sabMap_id_of_common_generic GlobalTheory.homExtension_semiAbelian_dvr E H _ _ jX hX hpre hfl hdom hqc Z.oF.t _ _ a₁ a₂ Z.oF.proper`. Take `⟨m₂, hm₂⟩` from `LevelCover.sab_comp β n (Category.id_comp F)`. Use `⟨F, _, m₁, m₂, hF, hj, fun T g g₁ g₂ q₁ q₂ q₃ => ?_⟩` and prove the remaining obligations.

Establish `w₀ : ν'.φ ≫ C.oF.t.G.hom = Z.oF.t.G.hom` using `ν'.cart.1.w.trans (Category.comp_id _)`. Establish `s₂ : g₂ = g₁ ≫ ν'.φ`. Apply `C.m0.toSABMap.cart.1.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `g₂ ≫ C.m0.toSABMap.φ = (g₁ ≫ ν'.φ) ≫ C.m0.toSABMap.φ`. Rewrite using `[Category.assoc, hν', q₂]`.

Rewrite using `[Category.assoc, w₀, q₃]`. Establish `s₁ : g = g₁ ≫ a₁.φ`. Apply `m₁.cart.1.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `g ≫ m₁.φ = (g₁ ≫ a₁.φ) ≫ m₁.φ`. Rewrite using `[Category.assoc, ha₁, q₁]`.

Rewrite using `[← cancel_mono (pullback.fst Z.s (spMap b))]`. Establish `w₃` using `m₁.cart.1.w`. Simplify using `only [Category.assoc]`. Rewrite using `[← w₃, reassoc_of% q₁, reassoc_of% ha₁]`. Rewrite using `[hm₂, s₁, s₂]`.

Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% hβ, ha₂, hμ]`.
-/
theorem dominates_of_map_on_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R]
    (a : 𝓞 c.F) (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (C : Model Xo c ω), IsDedFrac ω →
    ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ a R _ b.toAlgebra →
    ∀ F : pullback Z.s (spMap b) ⟶ C.X, F ≫ C.s = pullback.snd _ _ →
    (∀ u : Xo.XF c ⟶ pullback Z.s (spMap b), u ≫ pullback.fst _ _ = Z.j → u ≫ F = C.j) → Dominates Z C b := by
  intro E _ _ _ H D l Xo c Z R _ a b ω C _ hb ha F hF hj
  haveI := c.fin
  haveI : NumberField c.F := ⟨⟩
  haveI : IsOpenImmersion (spMap b) := by
    letI := b.toAlgebra
    exact IsOpenImmersion.of_isLocalization (R := 𝓞 c.F) (S := R) a

  have hω : spMap ω ≫ spMap b = spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [← hb]
    exact (Spec.map_comp (CommRingCat.ofHom b) (CommRingCat.ofHom ω)).symm
  have hjs : Z.j ≫ Z.s = (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ spMap ω) ≫
      spMap b := by
    change (Z.jQ ≫ pullback.fst _ _) ≫ Z.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, Z.jQ_over, Category.assoc, hω]
  let jX : Xo.XF c ⟶ pullback Z.s (spMap b) := pullback.lift Z.j _ hjs
  have hjX : jX ≫ pullback.fst _ _ = Z.j := pullback.lift_fst _ _ _
  have hjF : jX ≫ F = C.j := hj _ hjX

  obtain ⟨-, -, -, h₁, h₂, h₃, h₄⟩ :=
    GlobalTheory.genericPart_dense_proOpen (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open Z.jQ_dense
  have sq : IsPullback (𝟙 _) jX Z.j (pullback.fst Z.s (spMap b)) :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [hjX, Category.id_comp]⟩
  have hpre : IsPreimmersion jX := MorphismProperty.of_isPullback sq h₁
  have hfl : Flat jX := MorphismProperty.of_isPullback sq h₂
  have hqc : QuasiCompact jX := MorphismProperty.of_isPullback sq h₄
  have hdom : IsDominant jX := by
    constructor
    have e : Set.range jX = pullback.fst Z.s (spMap b) ⁻¹' Set.range Z.j := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, by rw [← hjX, Scheme.Hom.comp_apply]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, (pullback.fst Z.s (spMap b)).isOpenEmbedding.injective (by rw [← hx, ← hjX, Scheme.Hom.comp_apply])⟩
    haveI : IsDominant Z.j := h₃
    rw [DenseRange, e]
    exact (Z.j).denseRange.preimage (pullback.fst Z.s (spMap b)).isOpenEmbedding.isOpenMap
  have hX : Geo.Tor.IsNormalScheme (pullback Z.s (spMap b)) ∧
      ∃ z : pullback Z.s (spMap b) ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z := by
    refine ⟨fun y => ?_, pullback.fst _ _ ≫ Z.s ≫ spMap (algebraMap ℤ (𝓞 c.F)), ?_, ?_⟩
    · obtain ⟨_, _⟩ := Z.normal (pullback.fst Z.s (spMap b) y)
      have e := (asIso ((pullback.fst Z.s (spMap b)).stalkMap y)).commRingCatIsoToRingEquiv
      exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
    · have hprop : IsProper Z.s := by
        obtain ⟨N, i, hi, e⟩ := Z.proj
        have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (𝓞 c.F) N
        rw [← e]; infer_instance
      have : LocallyOfFiniteType (spMap (algebraMap ℤ (𝓞 c.F))) := by
        rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
        exact RingHom.finiteType_algebraMap.mpr inferInstance
      infer_instance
    · have := Z.flat
      have : Flat (spMap (algebraMap ℤ (𝓞 c.F))) := by
        rw [Flat.SpecMap_iff]
        exact RingHom.flat_algebraMap_iff.mpr inferInstance
      infer_instance

  obtain ⟨_, _, _, _, _, m₁, -⟩ := sabPull Out.CubePf.cubePull (pullback.fst Z.s (spMap b)) Z.t
  obtain ⟨_, _, _, _, _, n, -⟩ := sabPull Out.CubePf.cubePull F C.t
  obtain ⟨a₁, ha₁⟩ := LevelCover.sab_cancel m₁ Z.m jX hjX
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel C.m0.toSABMap Z.m0.toSABMap (𝟙 _) (Category.id_comp _)
  obtain ⟨μ, hμ⟩ := LevelCover.sab_comp ν' C.m (e := jX ≫ F) (by rw [Category.id_comp, hjF]; rfl)
  obtain ⟨a₂, ha₂⟩ := LevelCover.sab_cancel n μ jX rfl
  obtain ⟨β, hβ⟩ := GlobalTheory.exists_sabMap_id_of_common_generic GlobalTheory.homExtension_semiAbelian_dvr E H _ _ jX hX hpre hfl
    hdom hqc Z.oF.t _ _ a₁ a₂ Z.oF.proper
  obtain ⟨m₂, hm₂⟩ := LevelCover.sab_comp β n (Category.id_comp F)
  refine ⟨F, _, m₁, m₂, hF, hj, fun T g g₁ g₂ q₁ q₂ q₃ => ?_⟩
  have w₀ : ν'.φ ≫ C.oF.t.G.hom = Z.oF.t.G.hom := ν'.cart.1.w.trans (Category.comp_id _)
  have s₂ : g₂ = g₁ ≫ ν'.φ := by
    apply C.m0.toSABMap.cart.1.hom_ext
    · change g₂ ≫ C.m0.toSABMap.φ = (g₁ ≫ ν'.φ) ≫ C.m0.toSABMap.φ
      rw [Category.assoc, hν', q₂]
    · rw [Category.assoc, w₀, q₃]
  have s₁ : g = g₁ ≫ a₁.φ := by
    apply m₁.cart.1.hom_ext
    · change g ≫ m₁.φ = (g₁ ≫ a₁.φ) ≫ m₁.φ
      rw [Category.assoc, ha₁, q₁]
    · rw [← cancel_mono (pullback.fst Z.s (spMap b))]
      have w₃ := m₁.cart.1.w
      simp only [Category.assoc]
      rw [← w₃, reassoc_of% q₁, reassoc_of% ha₁]
  rw [hm₂, s₁, s₂]
  simp only [Category.assoc]
  rw [reassoc_of% hβ, ha₂, hμ]

end GlobalTheory.TorRef
