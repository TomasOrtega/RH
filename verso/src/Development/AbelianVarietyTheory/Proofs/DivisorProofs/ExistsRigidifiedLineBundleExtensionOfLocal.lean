import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueGeneratorExtendDenseProOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPicardGlueFiniteDisjointCover
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundlePullOfIsLineBundleOnOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleOnOpenPullCompIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechLineBundleAmbientOfOpenImmersion

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PicGlue

namespace GlobalTheory.RigLBDense

/- English proof (translation)
Introduce `S Y U YU _ _ f _ _ j _ hj e fU hP σ σU hσ hσU L hL r hr hloc`. Use `haveI : IsOpenImmersion e := MorphismProperty.of_isPullback hP.flip ‹IsOpenImmersion j›`. Use `haveI : IsReduced S := isReduced_of_isReduced_stalk S`. Use `haveI : GeometricallyIntegral f := (GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected.1 f).1`. Use `GlobalTheory.DenseGlue.exists_glue j hj f hσ hP hσU hL ⟨r, hr⟩ ?_` and prove the remaining obligations.

Introduce `x hx`. Take `⟨W, hxW, N, hN, hagr⟩` from `hloc x hx`. Take `⟨M, hM, hMN⟩` from `exists_isOn_of_openImmersion Y _ (f ⁻¹ᵁ W).ι N hN`. Rewrite `hM` using `[Scheme.Opens.opensRange_ι]`. Use `⟨W, hxW, M, hM, ?_⟩` and prove the remaining obligations.

Set `T : YU.Opens` to `e ⁻¹ᵁ (f ⁻¹ᵁ W)`. Establish `hrange : Set.range (T.ι ≫ e) ⊆ Set.range (f ⁻¹ᵁ W).ι`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `z.2`.

Set `a : T.toScheme ⟶ (f ⁻¹ᵁ W).toScheme` to `IsOpenImmersion.lift (f ⁻¹ᵁ W).ι (T.ι ≫ e) hrange`. Establish `ha : a ≫ (f ⁻¹ᵁ W).ι = T.ι ≫ e` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hι : ∀ z, (f ⁻¹ᵁ W).ι z ∈ f ⁻¹ᵁ W` using `fun z => by`. Establish `: (f ⁻¹ᵁ W).ι z ∈ Set.range (f ⁻¹ᵁ W).ι` using `⟨z, rfl⟩`. Rewrite `this` using `[Scheme.Opens.range_ι]`. Then use the resulting hypothesis.

Establish `hg : ∀ z, (T.ι ≫ e) z ∈ f ⁻¹ᵁ W` using `fun z => z.2`. Establish `k₀ : (M.pull (f ⁻¹ᵁ W).ι).IsLB` using `pull_isLB_of_isOn Y _ _ M _ hM hι`. Establish `k₁ : ((M.pull (f ⁻¹ᵁ W).ι).pull a).IsLB` using `pull_isLB k₀ a`. Establish `k₂ : (M.pull (T.ι ≫ e)).IsLB` using `pull_isLB_of_isOn Y _ _ M _ hM hg`. Establish `i₁ : LBIso ((M.pull (f ⁻¹ᵁ W).ι).pull a) (M.pull (T.ι ≫ e))`.

Use `isOn_pull_comp Y _ _ (f ⁻¹ᵁ W) M (f ⁻¹ᵁ W).ι a hM hι` as an intermediate fact. Rewrite `this` using `[ha]`. Then use the resulting hypothesis. Establish `i₂ : LBIso ((M.pull (f ⁻¹ᵁ W).ι).pull a) (N.pull a)` using `LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ a a rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ a a rfl) hMN`. Establish `i₃ : LBIso (N.pull a) (L.pull T.ι)` using `hagr T a T.ι ha`. Conclude with `LBIso.trans k₂ k₁ (pull_isLB hL _) i₁.symm (LBIso.trans k₁ (pull_isLB hN a) (pull_isLB hL _) i₂ i₃)`.
-/
theorem exists_extension_of_local_ext : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S] [GlobalTheory.IsNormalScheme S] (f : Y ⟶ S) [Smooth f] [GeometricallyConnected f] (j : U ⟶ S) [IsOpenImmersion j], Dense (Set.range j) → ∀ (e : YU ⟶ Y) (fU : YU ⟶ U), IsPullback e fU f j → ∀ (σ : S ⟶ Y) (σU : U ⟶ YU), σ ≫ f = 𝟙 S → σU ≫ e = j ≫ σ → ∀ (L : LB YU), L.IsLB → ∀ (r : LB.Gen (L.pull σU)), r.IsGen → (∀ x : S, x ∉ Set.range j → ∃ W : S.Opens, x ∈ W ∧ ∃ N : LB ↑(f ⁻¹ᵁ W), N.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ ↑(f ⁻¹ᵁ W)) (b : T ⟶ YU), a ≫ (f ⁻¹ᵁ W).ι = b ≫ e → LBIso (N.pull a) (L.pull b)) → ∃ M : LB Y, M.IsLB ∧ LBIso (M.pull e) L := by
  intro S Y U YU _ _ f _ _ j _ hj e fU hP σ σU hσ hσU L hL r hr hloc
  haveI : IsOpenImmersion e := MorphismProperty.of_isPullback hP.flip ‹IsOpenImmersion j›
  haveI : IsReduced S := isReduced_of_isReduced_stalk S
  haveI : GeometricallyIntegral f := (GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected.1 f).1
  refine GlobalTheory.DenseGlue.exists_glue j hj f hσ hP hσU hL ⟨r, hr⟩ ?_
  intro x hx
  obtain ⟨W, hxW, N, hN, hagr⟩ := hloc x hx
  obtain ⟨M, hM, hMN⟩ := exists_isOn_of_openImmersion Y _ (f ⁻¹ᵁ W).ι N hN
  rw [Scheme.Opens.opensRange_ι] at hM
  refine ⟨W, hxW, M, hM, ?_⟩
  let T : YU.Opens := e ⁻¹ᵁ (f ⁻¹ᵁ W)
  have hrange : Set.range (T.ι ≫ e) ⊆ Set.range (f ⁻¹ᵁ W).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2
  let a : T.toScheme ⟶ (f ⁻¹ᵁ W).toScheme := IsOpenImmersion.lift (f ⁻¹ᵁ W).ι (T.ι ≫ e) hrange
  have ha : a ≫ (f ⁻¹ᵁ W).ι = T.ι ≫ e := IsOpenImmersion.lift_fac _ _ _
  have hι : ∀ z, (f ⁻¹ᵁ W).ι z ∈ f ⁻¹ᵁ W := fun z => by
    have : (f ⁻¹ᵁ W).ι z ∈ Set.range (f ⁻¹ᵁ W).ι := ⟨z, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  have hg : ∀ z, (T.ι ≫ e) z ∈ f ⁻¹ᵁ W := fun z => z.2
  have k₀ : (M.pull (f ⁻¹ᵁ W).ι).IsLB := pull_isLB_of_isOn Y _ _ M _ hM hι
  have k₁ : ((M.pull (f ⁻¹ᵁ W).ι).pull a).IsLB := pull_isLB k₀ a
  have k₂ : (M.pull (T.ι ≫ e)).IsLB := pull_isLB_of_isOn Y _ _ M _ hM hg
  have i₁ : LBIso ((M.pull (f ⁻¹ᵁ W).ι).pull a) (M.pull (T.ι ≫ e)) := by
    have := isOn_pull_comp Y _ _ (f ⁻¹ᵁ W) M (f ⁻¹ᵁ W).ι a hM hι
    rwa [ha] at this
  have i₂ : LBIso ((M.pull (f ⁻¹ᵁ W).ι).pull a) (N.pull a) := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ a a rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ a a rfl) hMN
  have i₃ : LBIso (N.pull a) (L.pull T.ι) := hagr T a T.ι ha
  exact LBIso.trans k₂ k₁ (pull_isLB hL _) i₁.symm (LBIso.trans k₁ (pull_isLB hN a) (pull_isLB hL _) i₂ i₃)

end GlobalTheory.RigLBDense
