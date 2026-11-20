import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsTopologicalGroupComplexPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CompactSpacePointsPolAV
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.CompanionTheory.Ar.AVExp

open GlobalTheory.AbelianExp

attribute [local instance] GlobalTheory.AbelianExp.pointTopology

/- English proof (translation)
Establish `h1` using `@valAt'_rules`. Establish `h2` using `@existsUnique_point_of_ringHom`. Take `⟨N, -, M, s, hcov, H⟩` from `hL ⊤ (isAffineOpen_top _)`. Set `Y : Over (Sp ℂ)` to `Over.mk ((A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι)`. Set `φ : Y ⟶ A` to `Over.homMk (A.hom ⁻¹ᵁ ⊤).ι (morphismRestrict_ι A.hom ⊤).symm`.

Set `c₀ : ℂ →+* Γ((⊤ : (Sp ℂ).Opens).toScheme, ⊤)` to `((⊤ : (Sp ℂ).Opens).ι.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom`. Establish `hc₀ : Function.Surjective c₀`. Establish `: IsIso (⊤ : (Sp ℂ).Opens).ι` using `inferInstanceAs (IsIso (Sp ℂ).topIso.hom)`. Conclude with `(ConcreteCategory.bijective_of_isIso ((⊤ : (Sp ℂ).Opens).ι.app ⊤)).2.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2`. Establish `hY : @CompactSpace _ (PointsCompact.pointTopology Y)`.

Use `PointsCompact.compact_of_sections h1 h2 Y (Out.powOver A L ⊤ N) s hcov fun i => ⟨(H i).1, ?_⟩` and prove the remaining obligations. Take `⟨r, hr, hs⟩` from `(H i).2`. Use `⟨r, hr, ((A.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom.comp c₀, fun a => ?_, fun f => ?_⟩` and prove the remaining obligations. Use `Scheme.Hom.comp_appLE (A.hom ∣_ ⊤) (⊤ : (Sp ℂ).Opens).ι ⊤ (Out.nonzeroLocus (s i)) le_top` as an intermediate fact. Conclude with `(congrArg (fun u => u.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) this).symm`.

Take `⟨p, rfl⟩` from `hs f`. Take `⟨q, rfl⟩` from `MvPolynomial.map_surjective c₀ hc₀ p`. Conclude with `⟨q, (MvPolynomial.eval₂_map c₀ r _ q).symm⟩`. Use `letI := PointsCompact.pointTopology Y`. Use `letI := PointsCompact.pointTopology A`.

Establish `hsurj : Function.Surjective fun x : 𝟙_ (Over (Sp ℂ)) ⟶ Y => x ≫ φ`. Introduce `x`. Establish `hrange : Set.range x.left ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce `_ _`.

Discharge the goal by the elementary cases of `trivial`. Establish `hl` using `IsOpenImmersion.lift_fac (A.hom ⁻¹ᵁ ⊤).ι x.left hrange`. Use `⟨Over.homMk (IsOpenImmersion.lift (A.hom ⁻¹ᵁ ⊤).ι x.left hrange) ?_, ?_⟩` and prove the remaining obligations. Use `Over.w x` as an intermediate fact. Rewrite `this` using `[← hl, Category.assoc, ← morphismRestrict_ι]`.

Conclude with `this`. Use `ext1`. Conclude with `hl`. Conclude with `hsurj.compactSpace (PointsCompact.continuous_comp h1 φ)`.
-/
theorem compactSpace_points (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (hL : Out.RelAmple A L) :
    @CompactSpace _ (PointsCompact.pointTopology A) := by
  have h1 := @valAt'_rules
  have h2 := @existsUnique_point_of_ringHom
  obtain ⟨N, -, M, s, hcov, H⟩ := hL ⊤ (isAffineOpen_top _)
  let Y : Over (Sp ℂ) := Over.mk ((A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι)
  let φ : Y ⟶ A := Over.homMk (A.hom ⁻¹ᵁ ⊤).ι (morphismRestrict_ι A.hom ⊤).symm
  let c₀ : ℂ →+* Γ((⊤ : (Sp ℂ).Opens).toScheme, ⊤) :=
    ((⊤ : (Sp ℂ).Opens).ι.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hc₀ : Function.Surjective c₀ := by
    have : IsIso (⊤ : (Sp ℂ).Opens).ι := inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
    exact (ConcreteCategory.bijective_of_isIso ((⊤ : (Sp ℂ).Opens).ι.app ⊤)).2.comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2
  have hY : @CompactSpace _ (PointsCompact.pointTopology Y) := by
    refine PointsCompact.compact_of_sections h1 h2 Y (Out.powOver A L ⊤ N) s hcov
      fun i => ⟨(H i).1, ?_⟩
    obtain ⟨r, hr, hs⟩ := (H i).2
    refine ⟨r, hr, ((A.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom.comp c₀,
      fun a => ?_, fun f => ?_⟩
    · have := Scheme.Hom.comp_appLE (A.hom ∣_ ⊤) (⊤ : (Sp ℂ).Opens).ι ⊤
        (Out.nonzeroLocus (s i)) le_top
      exact (congrArg (fun u => u.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) this).symm
    · obtain ⟨p, rfl⟩ := hs f
      obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective c₀ hc₀ p
      exact ⟨q, (MvPolynomial.eval₂_map c₀ r _ q).symm⟩
  letI := PointsCompact.pointTopology Y
  letI := PointsCompact.pointTopology A
  have hsurj : Function.Surjective fun x : 𝟙_ (Over (Sp ℂ)) ⟶ Y => x ≫ φ := by
    intro x
    have hrange : Set.range x.left ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι := by
      rw [Scheme.Opens.range_ι]
      intro _ _
      trivial
    have hl := IsOpenImmersion.lift_fac (A.hom ⁻¹ᵁ ⊤).ι x.left hrange
    refine ⟨Over.homMk (IsOpenImmersion.lift (A.hom ⁻¹ᵁ ⊤).ι x.left hrange) ?_, ?_⟩
    · have := Over.w x
      rw [← hl, Category.assoc, ← morphismRestrict_ι] at this
      exact this
    · ext1
      exact hl
  exact hsurj.compactSpace (PointsCompact.continuous_comp h1 φ)

/- English proof (translation)
Take `⟨hfin, hflat⟩` from `GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA (Sp ℂ) A hA r hr`. Use `hA.smooth` as an intermediate fact. Use `hA.geomConnected` as an intermediate fact. Establish `: ConnectedSpace A.left` using `GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap`. Establish `: LocallyOfFinitePresentation ((Out.mulA A r).left ≫ A.hom)`.

Rewrite using `[Over.w]`. Use `infer_instance`. Establish `: LocallyOfFinitePresentation (Out.mulA A r).left` using `GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp _ A.hom`. Establish `hcl : IsClosed (Set.range (Out.mulA A r).left)` using `(Out.mulA A r).left.isClosedMap.isClosed_range`. Establish `hop : IsOpen (Set.range (Out.mulA A r).left)` using `(Out.mulA A r).left.isOpenMap.isOpen_range`.

Establish `hne : (Set.range (Out.mulA A r).left).Nonempty` using `Set.range_nonempty _`. Conclude with `⟨Set.range_eq_univ.1 (IsClopen.eq_univ ⟨hcl, hop⟩ hne)⟩`.
-/
theorem surjective_mulA (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) (r : ℕ) (hr : 1 ≤ r) :
    Surjective (Out.mulA A r).left := by
  obtain ⟨hfin, hflat⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA (Sp ℂ) A hA r hr
  have := hA.smooth
  have := hA.geomConnected
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap
  have : LocallyOfFinitePresentation ((Out.mulA A r).left ≫ A.hom) := by
    rw [Over.w]; infer_instance
  have : LocallyOfFinitePresentation (Out.mulA A r).left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp _ A.hom
  have hcl : IsClosed (Set.range (Out.mulA A r).left) := (Out.mulA A r).left.isClosedMap.isClosed_range
  have hop : IsOpen (Set.range (Out.mulA A r).left) := (Out.mulA A r).left.isOpenMap.isOpen_range
  have hne : (Set.range (Out.mulA A r).left).Nonempty := Set.range_nonempty _
  exact ⟨Set.range_eq_univ.1 (IsClopen.eq_univ ⟨hcl, hop⟩ hne)⟩

/- English proof (translation)
Take `⟨hfin, -⟩` from `GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA (Sp ℂ) A hA r hr`. Establish `hsurj` using `surjective_mulA A hA r hr`. Take `⟨t, ht⟩` from `H1.SectionDivision.exists_section (pullback.snd (Out.mulA A r).left a₀.left)`. Establish `hb' : (t ≫ pullback.fst (Out.mulA A r).left a₀.left) ≫ (Out.mulA A r).left = a₀.left`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]`.

Establish `hw : (t ≫ pullback.fst (Out.mulA A r).left a₀.left) ≫ A.hom = (𝟙_ (Over (Sp ℂ))).hom`. Rewrite using `[← Over.w (Out.mulA A r), ← Category.assoc, hb', Over.w a₀]`. Use `⟨Over.homMk _ hw, ?_⟩` and prove the remaining obligations. Establish `e : ∀ b : 𝟙_ (Over (Sp ℂ)) ⟶ A, b ^ r = b ≫ Out.mulA A r` using `fun b => (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 A) r b).symm`. Rewrite using `[e]`.

Conclude with `Over.OverMorphism.ext hb'`.
-/
theorem exists_div (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (a₀ : 𝟙_ (Over (Sp ℂ)) ⟶ A) (r : ℕ) (hr : 1 ≤ r) : ∃ b : 𝟙_ (Over (Sp ℂ)) ⟶ A, b ^ r = a₀ := by
  obtain ⟨hfin, -⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA (Sp ℂ) A hA r hr
  have hsurj := surjective_mulA A hA r hr
  obtain ⟨t, ht⟩ := H1.SectionDivision.exists_section (pullback.snd (Out.mulA A r).left a₀.left)
  have hb' : (t ≫ pullback.fst (Out.mulA A r).left a₀.left) ≫ (Out.mulA A r).left = a₀.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (Out.mulA A r).left a₀.left) ≫ A.hom = (𝟙_ (Over (Sp ℂ))).hom := by
    rw [← Over.w (Out.mulA A r), ← Category.assoc, hb', Over.w a₀]
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : 𝟙_ (Over (Sp ℂ)) ⟶ A, b ^ r = b ≫ Out.mulA A r := fun b =>
    (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 A) r b).symm
  rw [e]
  exact Over.OverMorphism.ext hb'

/- English proof (translation)
Introduce `A _ L g hA hL hdim`. Establish `hval` using `@valAt'_rules`. Establish `hprod` using `@holFamily_lift hval`. Establish `htop` using `@isTopologicalGroup_complexPoints hval`. Establish `hchart` using `@HolChart.exists_holomorphic_chart hval (@existsUnique_point_of_ringHom) (@exists_holomorphic_section_of_etale)`.

Use `hA.comm` as an intermediate fact. Use `htop A` as an intermediate fact. Use `compactSpace_points A L hL` as an intermediate fact. Establish `hpost` using `fun X x => (hval X x).2.2.2.1`. Establish `hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w` using `fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]`.

Take `⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩` from `hchart A g hdim 1`. Set `φ : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Fin g → ℂ)` to `chart t hW hσ ht ho`. Establish `hU1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U` using `hσ0 ▸ (ht 0 h0).1`. Establish `hφ : IsAnalyticGroupChart φ`. Use `⟨⟨0, h0, hσ0⟩, funext fun i => ?_, ?_⟩` and prove the remaining obligations.

Use `(ht 0 h0).2 i` as an intermediate fact. Rewrite `this` using `[hσ0]`. Then use the resulting hypothesis. Establish `hH` using `hmulHol _ (W ×ˢ W) _ _ (HolOn.comp hσ (hW.prod hW) differentiableOn_fst fun p hp => hp.1) (HolOn.comp hσ (hW.prod hW) differentiableOn_snd fun p hp => hp.2)`. Use `hH.analyticAt t (w := 0) ⟨h0, h0⟩ ?_` and prove the remaining obligations. Simplify `hU1` using `only [Prod.fst_zero, Prod.snd_zero, hσ0, _root_.mul_one]`.

Establish `hex0 : (hφ.exp 0).toMul = 1` using `by rw [map_zero]; rfl`. Establish `hsurj : Function.Surjective hφ.exp` using `hφ.exp_surjective fun n hn x => exists_div A hA x.toMul n (Nat.one_le_iff_ne_zero.mpr hn)`. Choose the witnesses or unpack the hypotheses as in `⟨W', large₂, hW', h0', hL', hLm, hLe⟩ : ∃ (W' : Set (Fin g → ℂ)) (large₂ : (Fin g → ℂ) → (Fin g → ℂ)), IsOpen W' ∧ 0 ∈ W' ∧ DifferentiableOn ℂ large₂ W' ∧ Set.MapsTo large₂ W' W ∧ ∀ᶠ v in 𝓝 0, (hφ.exp v).toMul = σ (large₂ v) := by`. Establish `ha` using `hφ.isLocalCommGroupLaw.analyticAt_logChart_symm`. Establish `h1 : ∀ᶠ v in 𝓝 0, hφ.isLocalCommGroupLaw.logChart.symm v ∈ W` using `ha.continuousAt.eventually (hW.mem_nhds (by simpa using h0))`.

Take `⟨W', h2, h3, h4⟩` from `eventually_nhds_iff.mp (ha.eventually_analyticAt.and h1)`. Conclude with `⟨W', _, h3, h4, fun v hv => (h2 v hv).1.differentiableAt.differentiableWithinAt, fun v hv => (h2 v hv).2, hφ.exp_eventuallyEq⟩`. Use `⟨⟨fun v => (hφ.exp v).toMul, fun z w => congrArg Additive.toMul (hφ.exp.map_add z w), hsurj, hφ.periodLattice, fun z => Iff.rfl, inferInstance, hφ.isZLattice_periodLattice.span_top, HolOn.of_local fun z => ?_, fun _ _ => 1, fun _ => differentiableOn_const _, fun _ _ _ => one_ne_z …` and prove the remaining obligations. Establish `hs : Continuous fun v : Fin g → ℂ => v - z` using `continuous_sub_right z`. Establish `hWz : IsOpen ((fun v => v - z) ⁻¹' W')` using `hW'.preimage hs`.

Use `⟨(fun v => v - z) ⁻¹' W', fun v => (hφ.exp z).toMul * σ (large₂ (v - z)), by simpa using h0', hmulHol _ _ _ _ (HolOn.const hWz _) (HolOn.comp (HolOn.comp hσ hW' hL' hLm) hWz (differentiableOn_id.sub_const z) fun v hv => hv), ?_⟩` and prove the remaining obligations. Use `filter_upwards [(hs.tendsto' z 0 (sub_self z)).eventually hLe] with v hv`. Rewrite using `[← hv, ← toMul_add, ← map_add, add_sub_cancel]`. Take `⟨e, he⟩` from `(hval _ _).2.1 _ hz`. Rewrite using `[he]`.

Simplify using the standard rewrite rules. Use `show ⊤ ≤ (hφ.exp 0).toMul.left ⁻¹ᵁ U`. Rewrite using `[hex0]` and apply the resulting hypothesis. Use `show ∀ D : Γ(A.left, U) →+ ℂ, _ → (∀ f f', D (f * f') = valAt' (hφ.exp 0).toMul.left U f * D f' + valAt' (hφ.exp 0).toMul.left U f' * D f) → _`. Rewrite using `[hex0]` and apply the resulting hypothesis.
-/
theorem exists_holUnif : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ), IsAbelianScheme A → Out.RelAmple A L → SmoothOfRelativeDimension g A.hom → ∃ u : HolUnif A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB A.left) g, ∃ (U : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 := by
  intro A _ L g hA hL hdim
  have hval := @valAt'_rules
  have hprod := @holFamily_lift hval
  have htop := @isTopologicalGroup_complexPoints hval
  have hchart := @HolChart.exists_holomorphic_chart hval (@existsUnique_point_of_ringHom)
    (@exists_holomorphic_section_of_etale)
  have := hA.comm
  have := htop A
  have := compactSpace_points A L hL
  have hpost := fun X x => (hval X x).2.2.2.1
  have hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E)
      (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w :=
    fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]
  obtain ⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩ := hchart A g hdim 1
  let φ : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Fin g → ℂ) :=
    chart t hW hσ ht ho
  have hU1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U := hσ0 ▸ (ht 0 h0).1
  have hφ : IsAnalyticGroupChart φ := by
    refine ⟨⟨0, h0, hσ0⟩, funext fun i => ?_, ?_⟩
    · have := (ht 0 h0).2 i
      rwa [hσ0] at this
    · have hH := hmulHol _ (W ×ˢ W) _ _
        (HolOn.comp hσ (hW.prod hW) differentiableOn_fst fun p hp => hp.1)
        (HolOn.comp hσ (hW.prod hW) differentiableOn_snd fun p hp => hp.2)
      refine hH.analyticAt t (w := 0) ⟨h0, h0⟩ ?_
      simpa only [Prod.fst_zero, Prod.snd_zero, hσ0, _root_.mul_one] using hU1
  have hex0 : (hφ.exp 0).toMul = 1 := by rw [map_zero]; rfl
  have hsurj : Function.Surjective hφ.exp := hφ.exp_surjective fun n hn x =>
    exists_div A hA x.toMul n (Nat.one_le_iff_ne_zero.mpr hn)

  obtain ⟨W', large₂, hW', h0', hL', hLm, hLe⟩ : ∃ (W' : Set (Fin g → ℂ))
      (large₂ : (Fin g → ℂ) → (Fin g → ℂ)), IsOpen W' ∧ 0 ∈ W' ∧ DifferentiableOn ℂ large₂ W' ∧
      Set.MapsTo large₂ W' W ∧ ∀ᶠ v in 𝓝 0, (hφ.exp v).toMul = σ (large₂ v) := by
    have ha := hφ.isLocalCommGroupLaw.analyticAt_logChart_symm
    have h1 : ∀ᶠ v in 𝓝 0, hφ.isLocalCommGroupLaw.logChart.symm v ∈ W :=
      ha.continuousAt.eventually (hW.mem_nhds (by simpa using h0))
    obtain ⟨W', h2, h3, h4⟩ := eventually_nhds_iff.mp (ha.eventually_analyticAt.and h1)
    exact ⟨W', _, h3, h4, fun v hv => (h2 v hv).1.differentiableAt.differentiableWithinAt,
      fun v hv => (h2 v hv).2, hφ.exp_eventuallyEq⟩
  refine ⟨⟨fun v => (hφ.exp v).toMul, fun z w => congrArg Additive.toMul (hφ.exp.map_add z w), hsurj,
    hφ.periodLattice, fun z => Iff.rfl, inferInstance, hφ.isZLattice_periodLattice.span_top,
    HolOn.of_local fun z => ?_, fun _ _ => 1, fun _ => differentiableOn_const _,
    fun _ _ _ => one_ne_zero, fun i j z hz => ?_⟩, U, t, hU, ?_, ?_, hφ.hasFDerivAt_chart_exp⟩
  · have hs : Continuous fun v : Fin g → ℂ => v - z := continuous_sub_right z
    have hWz : IsOpen ((fun v => v - z) ⁻¹' W') := hW'.preimage hs
    refine ⟨(fun v => v - z) ⁻¹' W', fun v => (hφ.exp z).toMul * σ (large₂ (v - z)), by simpa using h0',
      hmulHol _ _ _ _ (HolOn.const hWz _) (HolOn.comp (HolOn.comp hσ hW' hL' hLm) hWz
        (differentiableOn_id.sub_const z) fun v hv => hv), ?_⟩
    filter_upwards [(hs.tendsto' z 0 (sub_self z)).eventually hLe] with v hv
    rw [← hv, ← toMul_add, ← map_add, add_sub_cancel]
  · obtain ⟨e, he⟩ := (hval _ _).2.1 _ hz
    rw [he]
    simp
  · show ⊤ ≤ (hφ.exp 0).toMul.left ⁻¹ᵁ U
    rwa [hex0]
  · show ∀ D : Γ(A.left, U) →+ ℂ, _ → (∀ f f', D (f * f') =
      valAt' (hφ.exp 0).toMul.left U f * D f' + valAt' (hφ.exp 0).toMul.left U f' * D f) → _
    rwa [hex0]

end GlobalTheory.CompanionTheory.Ar.AVExp
