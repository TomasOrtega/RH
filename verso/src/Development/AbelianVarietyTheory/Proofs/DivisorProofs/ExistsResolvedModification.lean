import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakResolutionOfPrincipalisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationExtendingMapFromOpenStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfOpenImmersionIntegralScheStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedSmoothProjModificationOffOStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QuotSetup

/- English proof (translation)
Use `⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩` and prove the remaining obligations. Establish `: ConnectedSpace ↥(pullback (p ≫ f) x)` using `GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)`. Set `q` to `(pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)`. Establish `: Surjective q` using `inferInstance`. Conclude with `q.surjective.connectedSpace q.continuous`.
-/
theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

/- English proof (translation)
The claim follows from `((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)`.
-/
theorem genericPoint_mem {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

/- English proof (translation)
Use `(genericPoint_spec X).image f.continuous` as an intermediate fact. Rewrite `this` using `[Set.image_univ, f.denseRange.closure_range]`. Conclude with `this.eq (genericPoint_spec Y)`.
-/
theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

/- English proof (translation)
Establish `h₁ : IsProper (f ≫ pZ)` using `hf ▸ ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1`. Establish `: IsProper pZ` using `((isProjOver_iff_isProper_and_exists_isAmpleLB pZ).1 hZ).1`. Establish `: IsProper f` using `IsProper.of_comp f pZ`. Establish `hc : closure {genericPoint Z} ⊆ Set.range f` using `f.isClosedMap.isClosed_range.closure_subset_iff.2 (by rintro _ rfl; exact ⟨y, hy⟩)`. Conclude with `⟨fun z => hc (by rw [(genericPoint_spec Z).def]; trivial)⟩`.
-/
theorem surjective_of_isProjOver {F : Type} [Field F] {Y Z : Scheme.{0}} [IsIntegral Z] (p : Y ⟶ Sp F)
    (pZ : Z ⟶ Sp F) (f : Y ⟶ Z) (hf : f ≫ pZ = p) (hp : IsProjOver p) (hZ : IsProjOver pZ) (y : Y)
    (hy : f y = genericPoint Z) : Surjective f := by
  have h₁ : IsProper (f ≫ pZ) := hf ▸ ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have : IsProper pZ := ((isProjOver_iff_isProper_and_exists_isAmpleLB pZ).1 hZ).1
  have : IsProper f := IsProper.of_comp f pZ
  have hc : closure {genericPoint Z} ⊆ Set.range f :=
    f.isClosedMap.isClosed_range.closure_subset_iff.2 (by rintro _ rfl; exact ⟨y, hy⟩)
  exact ⟨fun z => hc (by rw [(genericPoint_spec Z).def]; trivial)⟩

end GlobalTheory.QuotSetup

namespace GlobalTheory.QuotSetup

/- English proof (translation)
Introduce `hP F _ _ X X' W V _ _ _ sX n _ φ q sW i ℓ hsX hgc hφ hsW hqf hqs hw hi hℓ hℓi δ hδ N hN hNδ J v hv hgen`. Take `⟨j₀, hj₀⟩` from `hgen`. Take `⟨o₀⟩ : Nonempty (Sp ℂ)` from `inferInstance`. Use `haveI : Nonempty V := ⟨v j₀ o₀⟩`. Use `haveI : IsIntegral V := isIntegral_of_isOpenImmersion i`.

Use `haveI : Nonempty X := ⟨i (v j₀ o₀)⟩`. Establish `hpX : IsProper sX` using `((isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hsX).1`. Establish `hpX' : IsProper (φ ≫ sX)` using `((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hφ).1`. Establish `hpW : IsProper sW` using `((isProjOver_iff_isProper_and_exists_isAmpleLB sW).1 hsW).1`. Establish `hWgen : ∀ j o, (v j ≫ ℓ ≫ q) o = genericPoint W` using `fun j o => by`.

Rewrite using `[hv j j₀]`. Establish `h₁ : v j₀ o = genericPoint V` using `i.isOpenEmbedding.injective ((hj₀ o).trans (genericPoint_eq_of_isOpenImmersion i).symm)`. Simplify using `only [Scheme.Hom.comp_apply]`. Rewrite using `[h₁, genericPoint_eq_of_isOpenImmersion ℓ, map_genericPoint q]`. Establish `hdW : topologicalKrullDim W = n`.

Establish `hdX : topologicalKrullDim X = n` using `GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth sX n inferInstance`. Establish `hdV` using `GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme F X V sX i`. Establish `hdV'` using `GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme F X' V (φ ≫ sX) ℓ`. Establish `h₁` using `PosBaseChange.dim_le_of_isClosedMap q.isClosedMap q.surjective`. Establish `h₂` using `PosBaseChange.dim_le_of_isDiscrete q.continuous q.isDiscrete_preimage_singleton`.

Rewrite using `[← hdX, ← hdV, hdV']`. Conclude with `le_antisymm h₁ h₂`. Take `⟨W', s, UW, hW', hsm, hpj, hUW, hiso⟩` from `GlobalTheory.T.weak_resolution_of_principalisation hP F W sW n hsW hdW`. Use `haveI := hW'`. Use `haveI := hiso`.

Establish `hηUW : genericPoint W ∈ UW` using `genericPoint_mem UW hUW`. Set `O : V.Opens` to `(ℓ ≫ q) ⁻¹ᵁ UW`. Establish `hvO : ∀ j o, v j o ∈ O` using `fun j o => by show (ℓ ≫ q) (v j o) ∈ UW`. Rewrite using `[← Scheme.Hom.comp_apply, hWgen j o]`. Conclude with `hηUW`.

Set `U : X.Opens` to `i ''ᵁ O`. Establish `hUi : Set.range U.ι ⊆ Set.range i`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨y, -, rfl⟩`. Conclude with `⟨y, rfl⟩`.

Set `e : U.toScheme ⟶ V` to `IsOpenImmersion.lift i U.ι hUi`. Establish `he : e ≫ i = U.ι` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hc : Set.range (e ≫ ℓ ≫ q) ⊆ Set.range UW.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Establish `hx : i (e x) ∈ U` using `by rw [← Scheme.Hom.comp_apply, he]; exact x.2`. Take `⟨y, hy, hyx⟩` from `hx`. Rewrite `hy` using `[i.isOpenEmbedding.injective hyx]`. Conclude with `hy`. Set `c : U.toScheme ⟶ UW.toScheme` to `IsOpenImmersion.lift UW.ι (e ≫ ℓ ≫ q) hc`.

Establish `hcf : c ≫ UW.ι = e ≫ ℓ ≫ q` using `IsOpenImmersion.lift_fac _ _ _`. Set `b : UW.toScheme ⟶ W'` to `inv (s ∣_ UW) ≫ (s ⁻¹ᵁ UW).ι`. Establish `hb : b ≫ s = UW.ι` using `by simp [b, ← morphismRestrict_ι]`. Set `r₀ : U.toScheme ⟶ pullback q s` to `pullback.lift (e ≫ ℓ) (c ≫ b) (by rw [Category.assoc, Category.assoc, hb, hcf])`. Establish `hUne : (U : Set X).Nonempty` using `⟨i (v j₀ o₀), v j₀ o₀, hvO j₀ o₀, rfl⟩`.

Establish `ht : IsProjOver (pullback.snd q s ≫ s ≫ sW)` using `isProjOver_comp_of_isFinite _ hpj`. Establish `hr₀ : r₀ ≫ pullback.snd q s ≫ s ≫ sW = U.ι ≫ sX`. Simplify using `only [r₀, pullback.lift_snd_assoc, Category.assoc]`. Rewrite using `[reassoc_of% hb, reassoc_of% hcf, hw, reassoc_of% hℓi, reassoc_of% he]`. Take `⟨M, r, hMi, hrt, hrM⟩` from `GlobalTheory.T.exists_modification_extending_map_from_open hP F X (pullback q s) sX n (pullback.snd q s ≫ s ≫ sW) U r₀ inferInstance hsX ht hUne hr₀`.

Use `haveI := hMi`. Establish `hsep : IsSeparated sX` using `inferInstance`. Use `haveI : IsDominant M.opn.ι := ⟨show Dense (Set.range M.opn.ι) by rw [Scheme.Opens.range_ι]; exact M.dense⟩`. Establish `hσ : r ≫ pullback.fst q s ≫ φ = M.σ`. Use `ext_of_isDominant_of_isSeparated sX ?_ M.opn.ι ?_` and prove the remaining obligations.

Simplify using `only [Category.assoc]`. Rewrite using `[← hw, pullback.condition_assoc]`. Conclude with `hrt`. Rewrite using `[reassoc_of% hrM]`. Simplify using `only [r₀, pullback.lift_fst_assoc, Category.assoc]`.

Rewrite using `[hℓi, he, morphismRestrict_ι]`. Set `f : M.X ⟶ W'` to `r ≫ pullback.snd q s`. Establish `hfs : f ≫ s = (r ≫ pullback.fst q s) ≫ q`. Simplify using `only [f, Category.assoc, pullback.condition]`. Establish `hfp : f ≫ s ≫ sW = M.str`.

Simplify using `only [f, Category.assoc]`. Conclude with `hrt`. Establish `hvU : ∀ j, ⊤ ≤ (v j ≫ i) ⁻¹ᵁ U` using `fun j o _ => by show (v j ≫ i) o ∈ U`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `⟨v j o, hvO j o, rfl⟩`.

Use `choose z hz using fun j => (M.existsUnique_lift (v j ≫ i) (hvU j)).exists`. Establish `hzU : ∀ j, ⊤ ≤ z j ⁻¹ᵁ M.opn` using `fun j => by show ⊤ ≤ z j ⁻¹ᵁ (M.σ ⁻¹ᵁ U)`. Rewrite using `[← Scheme.Hom.comp_preimage, hz j]`. Conclude with `hvU j`. Establish `key : ∀ j, ∃ d : Sp ℂ ⟶ UW.toScheme, d ≫ UW.ι = v j ≫ ℓ ≫ q ∧ z j ≫ f = d ≫ b` using `fun j => by`.

Establish `hr : Set.range (z j) ⊆ Set.range M.opn.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨o, rfl⟩`. Conclude with `hzU j (Set.mem_univ o)`. Set `w` to `IsOpenImmersion.lift M.opn.ι (z j) hr`.

Establish `hw' : w ≫ M.opn.ι = z j` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hwe : w ≫ (M.σ ∣_ U) ≫ e = v j`. Rewrite using `[← cancel_mono i, Category.assoc, Category.assoc, he, morphismRestrict_ι, reassoc_of% hw', hz j]`. Use `⟨w ≫ (M.σ ∣_ U) ≫ c, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hcf, ← reassoc_of% hwe]`.

Simplify using `only [f, ← hw', Category.assoc]`. Rewrite using `[reassoc_of% hrM]`. Simplify using `only [r₀, pullback.lift_snd, Category.assoc]`. Use `choose d hd hzd using key`. Use `haveI : Nonempty UW.toScheme := ⟨⟨_, hηUW⟩⟩`.

Use `haveI : IsIntegral UW.toScheme := isIntegral_of_isOpenImmersion UW.ι`. Establish `hgen' : ∀ j o, (z j ≫ f) o = genericPoint W'` using `fun j o => by`. Establish `h₁ : d j o = genericPoint UW.toScheme`. Apply `UW.ι.isOpenEmbedding.injective` to reduce the goal to its premises. Rewrite using `[← Scheme.Hom.comp_apply, hd j, hWgen j o, genericPoint_eq_of_isOpenImmersion UW.ι]`.

Rewrite using `[hzd j, Scheme.Hom.comp_apply, h₁]`. Conclude with `genericPoint_eq_of_isOpenImmersion b`. Establish `hfsurj : Surjective f` using `surjective_of_isProjOver M.str (s ≫ sW) f hfp M.proj hpj (z j₀ o₀) (by rw [← Scheme.Hom.comp_apply]; exact hgen' j₀ o₀)`. Establish `hgcM : GeometricallyConnected M.str` using `GlobalTheory.T.geometricallyConnected_smoothProjModification_offOpen F X sX n U M hUne`. Establish `hgcW : GeometricallyConnected (s ≫ sW)`.

Rewrite `hgcM` using `[← hfp]`. Conclude with `geometricallyConnected_of_surjective f (s ≫ sW)`. Use `⟨W', hW', s ≫ sW, U, M, f, N.pull s, LB.isLB_pull hN s, hMi, hsm, hpj, hgcW, hfp, hfsurj, hUne, ?_, z, hzU, hz, fun j j' => ?_, hgen'⟩` and prove the remaining obligations. Rewrite using `[cls_pull hN s, ← pull_comp, hfs, pull_comp, hNδ, ← pull_comp, Category.assoc, hσ]`. Rewrite using `[hzd j, hzd j']`.

Use `congr 1`. Rewrite using `[← cancel_mono UW.ι, hd j, hd j', hv j j']`.
-/
theorem exists_resolved_modification : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (X X' W V : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral W] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (φ : X' ⟶ X) (q : X' ⟶ W) (sW : W ⟶ Sp F) (i : V ⟶ X) (ℓ : V ⟶ X'), IsProjOver sX → GeometricallyConnected sX → IsProjOver (φ ≫ sX) → IsProjOver sW → IsFinite q → Surjective q → q ≫ sW = φ ≫ sX → IsOpenImmersion i → IsOpenImmersion ℓ → ℓ ≫ φ = i → ∀ (δ : LB X) (hδ : δ.IsLB) (N : LB W) (hN : N.IsLB), CechPic.pull q (cls N hN) = CechPic.pull φ (cls δ hδ) → ∀ (J : Type) (v : J → (Sp ℂ ⟶ V)), (∀ j j', v j ≫ ℓ ≫ q = v j' ≫ ℓ ≫ q) → (∃ j, ∀ s, (v j ≫ i) s = genericPoint X) → ∃ (W' : Scheme.{0}) (_ : IsIntegral W') (pW : W' ⟶ Sp F) (U : X.Opens) (M : Modif sX U n) (f : M.X ⟶ W') (NW : LB W') (hNW : NW.IsLB), IsIntegral M.X ∧ SmoothOfRelativeDimension n pW ∧ IsProjOver pW ∧ GeometricallyConnected pW ∧ f ≫ pW = M.str ∧ Surjective f ∧ (U : Set X).Nonempty ∧ CechPic.pull f (cls NW hNW) = CechPic.pull M.σ (cls δ hδ) ∧ ∃ z : J → (Sp ℂ ⟶ M.X), (∀ j, ⊤ ≤ z j ⁻¹ᵁ M.opn) ∧ (∀ j, z j ≫ M.σ = v j ≫ i) ∧ (∀ j j', z j ≫ f = z j' ≫ f) ∧ (∀ j s, (z j ≫ f) s = genericPoint W') := by
  intro hP F _ _ X X' W V _ _ _ sX n _ φ q sW i ℓ hsX hgc hφ hsW hqf hqs hw hi hℓ hℓi δ hδ N hN hNδ J v hv hgen
  obtain ⟨j₀, hj₀⟩ := hgen
  obtain ⟨o₀⟩ : Nonempty (Sp ℂ) := inferInstance
  haveI : Nonempty V := ⟨v j₀ o₀⟩
  haveI : IsIntegral V := isIntegral_of_isOpenImmersion i
  haveI : Nonempty X := ⟨i (v j₀ o₀)⟩
  have hpX : IsProper sX := ((isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hsX).1
  have hpX' : IsProper (φ ≫ sX) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hφ).1
  have hpW : IsProper sW := ((isProjOver_iff_isProper_and_exists_isAmpleLB sW).1 hsW).1

  have hWgen : ∀ j o, (v j ≫ ℓ ≫ q) o = genericPoint W := fun j o => by
    rw [hv j j₀]
    have h₁ : v j₀ o = genericPoint V :=
      i.isOpenEmbedding.injective ((hj₀ o).trans (genericPoint_eq_of_isOpenImmersion i).symm)
    simp only [Scheme.Hom.comp_apply]
    rw [h₁, genericPoint_eq_of_isOpenImmersion ℓ, map_genericPoint q]

  have hdW : topologicalKrullDim W = n := by
    have hdX : topologicalKrullDim X = n := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth sX n inferInstance
    have hdV := GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme F X V sX i
    have hdV' := GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme F X' V (φ ≫ sX) ℓ
    have h₁ := PosBaseChange.dim_le_of_isClosedMap q.isClosedMap q.surjective
    have h₂ := PosBaseChange.dim_le_of_isDiscrete q.continuous q.isDiscrete_preimage_singleton
    rw [← hdX, ← hdV, hdV']
    exact le_antisymm h₁ h₂

  obtain ⟨W', s, UW, hW', hsm, hpj, hUW, hiso⟩ := GlobalTheory.T.weak_resolution_of_principalisation hP F W sW n hsW hdW
  haveI := hW'
  haveI := hiso
  have hηUW : genericPoint W ∈ UW := genericPoint_mem UW hUW

  let O : V.Opens := (ℓ ≫ q) ⁻¹ᵁ UW
  have hvO : ∀ j o, v j o ∈ O := fun j o => by
    show (ℓ ≫ q) (v j o) ∈ UW
    rw [← Scheme.Hom.comp_apply, hWgen j o]
    exact hηUW
  let U : X.Opens := i ''ᵁ O
  have hUi : Set.range U.ι ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  let e : U.toScheme ⟶ V := IsOpenImmersion.lift i U.ι hUi
  have he : e ≫ i = U.ι := IsOpenImmersion.lift_fac _ _ _
  have hc : Set.range (e ≫ ℓ ≫ q) ⊆ Set.range UW.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : i (e x) ∈ U := by rw [← Scheme.Hom.comp_apply, he]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rw [i.isOpenEmbedding.injective hyx] at hy
    exact hy
  let c : U.toScheme ⟶ UW.toScheme := IsOpenImmersion.lift UW.ι (e ≫ ℓ ≫ q) hc
  have hcf : c ≫ UW.ι = e ≫ ℓ ≫ q := IsOpenImmersion.lift_fac _ _ _
  let b : UW.toScheme ⟶ W' := inv (s ∣_ UW) ≫ (s ⁻¹ᵁ UW).ι
  have hb : b ≫ s = UW.ι := by simp [b, ← morphismRestrict_ι]
  let r₀ : U.toScheme ⟶ pullback q s :=
    pullback.lift (e ≫ ℓ) (c ≫ b) (by rw [Category.assoc, Category.assoc, hb, hcf])
  have hUne : (U : Set X).Nonempty := ⟨i (v j₀ o₀), v j₀ o₀, hvO j₀ o₀, rfl⟩
  have ht : IsProjOver (pullback.snd q s ≫ s ≫ sW) := isProjOver_comp_of_isFinite _ hpj
  have hr₀ : r₀ ≫ pullback.snd q s ≫ s ≫ sW = U.ι ≫ sX := by
    simp only [r₀, pullback.lift_snd_assoc, Category.assoc]
    rw [reassoc_of% hb, reassoc_of% hcf, hw, reassoc_of% hℓi, reassoc_of% he]
  obtain ⟨M, r, hMi, hrt, hrM⟩ :=
    GlobalTheory.T.exists_modification_extending_map_from_open hP F X (pullback q s) sX n (pullback.snd q s ≫ s ≫ sW) U r₀ inferInstance hsX ht hUne hr₀
  haveI := hMi
  have hsep : IsSeparated sX := inferInstance
  haveI : IsDominant M.opn.ι := ⟨show Dense (Set.range M.opn.ι) by rw [Scheme.Opens.range_ι]; exact M.dense⟩
  have hσ : r ≫ pullback.fst q s ≫ φ = M.σ := by
    refine ext_of_isDominant_of_isSeparated sX ?_ M.opn.ι ?_
    · simp only [Category.assoc]
      rw [← hw, pullback.condition_assoc]
      exact hrt
    · rw [reassoc_of% hrM]
      simp only [r₀, pullback.lift_fst_assoc, Category.assoc]
      rw [hℓi, he, morphismRestrict_ι]
  let f : M.X ⟶ W' := r ≫ pullback.snd q s
  have hfs : f ≫ s = (r ≫ pullback.fst q s) ≫ q := by
    simp only [f, Category.assoc, pullback.condition]
  have hfp : f ≫ s ≫ sW = M.str := by
    simp only [f, Category.assoc]; exact hrt

  have hvU : ∀ j, ⊤ ≤ (v j ≫ i) ⁻¹ᵁ U := fun j o _ => by
    show (v j ≫ i) o ∈ U
    rw [Scheme.Hom.comp_apply]
    exact ⟨v j o, hvO j o, rfl⟩
  choose z hz using fun j => (M.existsUnique_lift (v j ≫ i) (hvU j)).exists
  have hzU : ∀ j, ⊤ ≤ z j ⁻¹ᵁ M.opn := fun j => by
    show ⊤ ≤ z j ⁻¹ᵁ (M.σ ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, hz j]
    exact hvU j
  have key : ∀ j, ∃ d : Sp ℂ ⟶ UW.toScheme, d ≫ UW.ι = v j ≫ ℓ ≫ q ∧ z j ≫ f = d ≫ b := fun j => by
    have hr : Set.range (z j) ⊆ Set.range M.opn.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨o, rfl⟩
      exact hzU j (Set.mem_univ o)
    let w := IsOpenImmersion.lift M.opn.ι (z j) hr
    have hw' : w ≫ M.opn.ι = z j := IsOpenImmersion.lift_fac _ _ _
    have hwe : w ≫ (M.σ ∣_ U) ≫ e = v j := by
      rw [← cancel_mono i, Category.assoc, Category.assoc, he, morphismRestrict_ι, reassoc_of% hw', hz j]
    refine ⟨w ≫ (M.σ ∣_ U) ≫ c, ?_, ?_⟩
    · rw [Category.assoc, Category.assoc, hcf, ← reassoc_of% hwe]
    · simp only [f, ← hw', Category.assoc]
      rw [reassoc_of% hrM]
      simp only [r₀, pullback.lift_snd, Category.assoc]
  choose d hd hzd using key
  haveI : Nonempty UW.toScheme := ⟨⟨_, hηUW⟩⟩
  haveI : IsIntegral UW.toScheme := isIntegral_of_isOpenImmersion UW.ι
  have hgen' : ∀ j o, (z j ≫ f) o = genericPoint W' := fun j o => by
    have h₁ : d j o = genericPoint UW.toScheme := by
      apply UW.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hd j, hWgen j o, genericPoint_eq_of_isOpenImmersion UW.ι]
    rw [hzd j, Scheme.Hom.comp_apply, h₁]
    exact genericPoint_eq_of_isOpenImmersion b
  have hfsurj : Surjective f :=
    surjective_of_isProjOver M.str (s ≫ sW) f hfp M.proj hpj (z j₀ o₀) (by rw [← Scheme.Hom.comp_apply]; exact hgen' j₀ o₀)
  have hgcM : GeometricallyConnected M.str := GlobalTheory.T.geometricallyConnected_smoothProjModification_offOpen F X sX n U M hUne
  have hgcW : GeometricallyConnected (s ≫ sW) := by
    rw [← hfp] at hgcM
    exact geometricallyConnected_of_surjective f (s ≫ sW)
  refine ⟨W', hW', s ≫ sW, U, M, f, N.pull s, LB.isLB_pull hN s, hMi, hsm, hpj, hgcW, hfp, hfsurj, hUne, ?_,
    z, hzU, hz, fun j j' => ?_, hgen'⟩
  · rw [cls_pull hN s, ← pull_comp, hfs, pull_comp, hNδ, ← pull_comp, Category.assoc, hσ]
  · rw [hzd j, hzd j']
    congr 1
    rw [← cancel_mono UW.ι, hd j, hd j', hv j j']

end GlobalTheory.QuotSetup
