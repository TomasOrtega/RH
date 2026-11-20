import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsTopologicalGroupComplexPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CompactSpacePointsPolAV
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteMulByNatAbelianVarietyAlgClosed
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRingHomLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace GlobalTheory.RealMultChart

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => show x ≫ (toUnit B ≫ η[B]) = x ^ 0`. Rewrite using `[pow_zero, Hom.one_def, ← Category.assoc, toUnit_unique (x ≫ toUnit B) (toUnit T)]`. Consider the case `succ n ih => show x ≫ (lift (mulN B n) (𝟙 B) ≫ μ[B]) = x ^ (n + 1)`. Rewrite using `[pow_succ, Hom.mul_def, ← ih, ← Category.assoc, comp_lift, Category.comp_id]`.
-/
theorem comp_mulN {S : Scheme.{0}} (B : Over S) [GrpObj B] {T : Over S} (x : T ⟶ B) (n : ℕ) :
    x ≫ mulN B n = x ^ n := by
  induction n with
  | zero =>
    show x ≫ (toUnit B ≫ η[B]) = x ^ 0
    rw [pow_zero, Hom.one_def, ← Category.assoc, toUnit_unique (x ≫ toUnit B) (toUnit T)]
  | succ n ih =>
    show x ≫ (lift (mulN B n) (𝟙 B) ≫ μ[B]) = x ^ (n + 1)
    rw [pow_succ, Hom.mul_def, ← ih, ← Category.assoc, comp_lift, Category.comp_id]

/- English proof (translation)
Establish `h1` using `comp_mulN B (𝟙 B) n`. Rewrite `h1` using `[Category.id_comp]`. Rewrite using `[h1]`.
-/
theorem mulN_eq_mulA {S : Scheme.{0}} (B : Over S) [GrpObj B] (n : ℕ) : mulN B n = Out.mulA B n := by
  have h1 := comp_mulN B (𝟙 B) n
  rw [Category.id_comp] at h1
  rw [h1]

/- English proof (translation)
Establish `hn' : ((n : ℂ)) ≠ 0` using `Nat.cast_ne_zero.2 hn`. Establish `hsurj : Surjective (mulN B n).left` using `surjective_mulN_of_isAbelianScheme ℂ B hB n hn'`. Establish `hfin : IsFinite (mulN B n).left`. Rewrite using `[mulN_eq_mulA]`. Conclude with `MulFiniteAny.isFinite_mulA ℂ B hB n (Nat.one_le_iff_ne_zero.2 hn)`.

Take `⟨t, ht⟩` from `H1.SectionDivision.exists_section (pullback.snd (mulN B n).left a₀.left)`. Establish `hb' : (t ≫ pullback.fst (mulN B n).left a₀.left) ≫ (mulN B n).left = a₀.left`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]`. Establish `hw : (t ≫ pullback.fst (mulN B n).left a₀.left) ≫ B.hom = (𝟙_ (Over (Sp ℂ))).hom`. Rewrite using `[← Over.w (mulN B n), ← Category.assoc, hb', Over.w a₀]`.

Use `⟨Over.homMk _ hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← comp_mulN]`. Conclude with `Over.OverMorphism.ext hb'`.
-/
theorem exists_pow_eq (B : Over (Sp ℂ)) [GrpObj B] (hB : IsAbelianScheme B) (a₀ : 𝟙_ (Over (Sp ℂ)) ⟶ B)
    (n : ℕ) (hn : n ≠ 0) : ∃ b : 𝟙_ (Over (Sp ℂ)) ⟶ B, b ^ n = a₀ := by
  have hn' : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hsurj : Surjective (mulN B n).left := surjective_mulN_of_isAbelianScheme ℂ B hB n hn'
  have hfin : IsFinite (mulN B n).left := by
    rw [mulN_eq_mulA]
    exact MulFiniteAny.isFinite_mulA ℂ B hB n (Nat.one_le_iff_ne_zero.2 hn)
  obtain ⟨t, ht⟩ := H1.SectionDivision.exists_section (pullback.snd (mulN B n).left a₀.left)
  have hb' : (t ≫ pullback.fst (mulN B n).left a₀.left) ≫ (mulN B n).left = a₀.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (mulN B n).left a₀.left) ≫ B.hom = (𝟙_ (Over (Sp ℂ))).hom := by
    rw [← Over.w (mulN B n), ← Category.assoc, hb', Over.w a₀]
  refine ⟨Over.homMk _ hw, ?_⟩
  rw [← comp_mulN]
  exact Over.OverMorphism.ext hb'

/- English proof (translation)
Establish `h1 : PointsCompact.ValueRules` using `valAt'_rules`. Establish `h2 : PointsCompact.AffinePoints` using `existsUnique_point_of_ringHom`. Take `⟨N, -, M, s, hcov, H⟩` from `hL ⊤ (isAffineOpen_top _)`. Set `Y : Over (Sp ℂ)` to `Over.mk ((A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι)`. Set `φ : Y ⟶ A` to `Over.homMk (A.hom ⁻¹ᵁ ⊤).ι (morphismRestrict_ι A.hom ⊤).symm`.

Set `c₀ : ℂ →+* Γ((⊤ : (Sp ℂ).Opens).toScheme, ⊤)` to `((⊤ : (Sp ℂ).Opens).ι.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom`. Establish `hc₀ : Function.Surjective c₀`. Establish `: IsIso (⊤ : (Sp ℂ).Opens).ι` using `inferInstanceAs (IsIso (Sp ℂ).topIso.hom)`. Conclude with `(ConcreteCategory.bijective_of_isIso ((⊤ : (Sp ℂ).Opens).ι.app ⊤)).2.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2`. Establish `hY : @CompactSpace _ (PointsCompact.pointTopology Y)`.

Use `PointsCompact.compact_of_sections h1 h2 Y (Out.powOver A L ⊤ N) s hcov fun i => ⟨(H i).1, ?_⟩` and prove the remaining obligations. Take `⟨r, hr, hs⟩` from `(H i).2`. Use `⟨r, hr, ((A.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom.comp c₀, fun a => ?_, fun f => ?_⟩` and prove the remaining obligations. Use `Scheme.Hom.comp_appLE (A.hom ∣_ ⊤) (⊤ : (Sp ℂ).Opens).ι ⊤ (Out.nonzeroLocus (s i)) le_top` as an intermediate fact. Conclude with `(congrArg (fun u => u.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) this).symm`.

Take `⟨p, rfl⟩` from `hs f`. Take `⟨q, rfl⟩` from `MvPolynomial.map_surjective c₀ hc₀ p`. Conclude with `⟨q, (MvPolynomial.eval₂_map c₀ r _ q).symm⟩`. Use `letI := PointsCompact.pointTopology Y`. Use `letI := PointsCompact.pointTopology A`.

Establish `hsurj : Function.Surjective fun x : 𝟙_ (Over (Sp ℂ)) ⟶ Y => x ≫ φ`. Introduce `x`. Establish `hrange : Set.range x.left ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce `_ _`.

Discharge the goal by the elementary cases of `trivial`. Establish `hl` using `IsOpenImmersion.lift_fac (A.hom ⁻¹ᵁ ⊤).ι x.left hrange`. Use `⟨Over.homMk (IsOpenImmersion.lift (A.hom ⁻¹ᵁ ⊤).ι x.left hrange) ?_, ?_⟩` and prove the remaining obligations. Use `Over.w x` as an intermediate fact. Rewrite `this` using `[← hl, Category.assoc, ← morphismRestrict_ι]`.

Conclude with `this`. Use `ext1`. Conclude with `hl`. Conclude with `hsurj.compactSpace (PointsCompact.continuous_comp h1 φ)`.
-/
theorem compactSpace_points (A : Over (Sp ℂ)) (L : LB A.left) (hL : Out.RelAmple A L) :
    @CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) (PointsCompact.pointTopology A) := by
  have h1 : PointsCompact.ValueRules := valAt'_rules
  have h2 : PointsCompact.AffinePoints := existsUnique_point_of_ringHom
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
    refine PointsCompact.compact_of_sections h1 h2 Y (Out.powOver A L ⊤ N) s hcov fun i => ⟨(H i).1, ?_⟩
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

def trivLB (A : Over (Sp ℂ)) : LB A.left := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

open AbelianExp in

/- English proof (translation)
Establish `hval` using `@valAt'_rules`. Establish `hvalaff` using `@existsUnique_point_of_ringHom`. Establish `hprod` using `@holFamily_lift hval`. Establish `hchart` using `HolChart.exists_holomorphic_chart hval hvalaff exists_holomorphic_section_of_etale`. Use `letI := pointTopology A`.

Use `isTopologicalGroup_complexPoints hval A` as an intermediate fact. Establish `: CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A)` using `hcpt`. Establish `hpost` using `fun X x => (hval X x).2.2.2.1`. Establish `hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w` using `fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]`. Take `⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩` from `hchart A g hs 1`.

Set `φ : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Fin g → ℂ)` to `chart t hW hσ ht ho`. Establish `hU1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U` using `hσ0 ▸ (ht 0 h0).1`. Establish `hφ : IsAnalyticGroupChart φ`. Use `⟨⟨0, h0, hσ0⟩, funext fun i => ?_, ?_⟩` and prove the remaining obligations. Use `(ht 0 h0).2 i` as an intermediate fact.

Rewrite `this` using `[hσ0]`. Then use the resulting hypothesis. Establish `hH` using `hmulHol _ (W ×ˢ W) _ _ (HolOn.comp hσ (hW.prod hW) differentiableOn_fst fun p hp => hp.1) (HolOn.comp hσ (hW.prod hW) differentiableOn_snd fun p hp => hp.2)`. Use `hH.analyticAt t (w := 0) ⟨h0, h0⟩ ?_` and prove the remaining obligations. Simplify `hU1` using `only [Prod.fst_zero, Prod.snd_zero, hσ0, _root_.mul_one]`. Establish `hsurj : Function.Surjective hφ.exp` using `hφ.exp_surjective fun n hn x => hdiv x.toMul n hn`.

Choose the witnesses or unpack the hypotheses as in `⟨W', L, hW', h0', hL, hLm, hLe⟩ : ∃ (W' : Set (Fin g → ℂ)) (L : (Fin g → ℂ) → (Fin g → ℂ)), IsOpen W' ∧ 0 ∈ W' ∧ DifferentiableOn ℂ L W' ∧ Set.MapsTo L W' W ∧ ∀ᶠ v in 𝓝 0, (hφ.exp v).toMul = σ (L v) := by`. Establish `ha` using `hφ.isLocalCommGroupLaw.analyticAt_logChart_symm`. Establish `h1 : ∀ᶠ v in 𝓝 0, hφ.isLocalCommGroupLaw.logChart.symm v ∈ W` using `ha.continuousAt.eventually (hW.mem_nhds (by simpa using h0))`. Take `⟨W', h2, h3, h4⟩` from `eventually_nhds_iff.mp (ha.eventually_analyticAt.and h1)`. Conclude with `⟨W', _, h3, h4, fun v hv => (h2 v hv).1.differentiableAt.differentiableWithinAt, fun v hv => (h2 v hv).2, hφ.exp_eventuallyEq⟩`.

Use `⟨⟨fun v => (hφ.exp v).toMul, fun z w => congrArg Additive.toMul (hφ.exp.map_add z w), hsurj, hφ.periodLattice, fun z => Iff.rfl, inferInstance, hφ.isZLattice_periodLattice.span_top, HolOn.of_local fun z => ?_, fun _ _ => 1, fun _ => differentiableOn_const _, fun _ _ _ => one_ne_z …` and prove the remaining obligations. Establish `hs : Continuous fun v : Fin g → ℂ => v - z` using `continuous_sub_right z`. Establish `hWz : IsOpen ((fun v => v - z) ⁻¹' W')` using `hW'.preimage hs`. Use `⟨(fun v => v - z) ⁻¹' W', fun v => (hφ.exp z).toMul * σ (L (v - z)), by simpa using h0', hmulHol _ _ _ _ (HolOn.const hWz _) (HolOn.comp (HolOn.comp hσ hW' hL hLm) hWz (differentiableOn_id.sub_const z) fun v hv => hv), ?_⟩` and prove the remaining obligations. Use `filter_upwards [(hs.tendsto' z 0 (sub_self z)).eventually hLe] with v hv`.

Rewrite using `[← hv, ← toMul_add, ← map_add, add_sub_cancel]`. Take `⟨e, he⟩` from `(hval _ _).2.1 _ hz`. Rewrite using `[he]`. Use `show (1 : ℂ) = e (((1 : Γ(A.left, ⊤ ⊓ ⊤)ˣ)) : Γ(A.left, ⊤ ⊓ ⊤)) * 1`. Rewrite using `[Units.val_one]`.

Conclude with `((_root_.mul_one _).trans e.map_one).symm`.
-/
theorem exists_holUnif_of_compact (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ)
    (hs : SmoothOfRelativeDimension g A.hom)
    (hcpt : @CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) (PointsCompact.pointTopology A))
    (hdiv : ∀ (a : 𝟙_ (Over (Sp ℂ)) ⟶ A) (n : ℕ), n ≠ 0 → ∃ b, b ^ n = a) :
    Nonempty (HolUnif A (trivLB A) g) := by
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  have hprod := @holFamily_lift hval
  have hchart := HolChart.exists_holomorphic_chart hval hvalaff exists_holomorphic_section_of_etale
  letI := pointTopology A
  have := isTopologicalGroup_complexPoints hval A
  have : CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) := hcpt
  have hpost := fun X x => (hval X x).2.2.2.1
  have hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E)
      (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w :=
    fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]
  obtain ⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩ := hchart A g hs 1
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
  have hsurj : Function.Surjective hφ.exp := hφ.exp_surjective fun n hn x => hdiv x.toMul n hn
  obtain ⟨W', L, hW', h0', hL, hLm, hLe⟩ : ∃ (W' : Set (Fin g → ℂ))
      (L : (Fin g → ℂ) → (Fin g → ℂ)), IsOpen W' ∧ 0 ∈ W' ∧ DifferentiableOn ℂ L W' ∧
      Set.MapsTo L W' W ∧ ∀ᶠ v in 𝓝 0, (hφ.exp v).toMul = σ (L v) := by
    have ha := hφ.isLocalCommGroupLaw.analyticAt_logChart_symm
    have h1 : ∀ᶠ v in 𝓝 0, hφ.isLocalCommGroupLaw.logChart.symm v ∈ W :=
      ha.continuousAt.eventually (hW.mem_nhds (by simpa using h0))
    obtain ⟨W', h2, h3, h4⟩ := eventually_nhds_iff.mp (ha.eventually_analyticAt.and h1)
    exact ⟨W', _, h3, h4, fun v hv => (h2 v hv).1.differentiableAt.differentiableWithinAt,
      fun v hv => (h2 v hv).2, hφ.exp_eventuallyEq⟩
  refine ⟨⟨fun v => (hφ.exp v).toMul, fun z w => congrArg Additive.toMul (hφ.exp.map_add z w), hsurj,
    hφ.periodLattice, fun z => Iff.rfl, inferInstance, hφ.isZLattice_periodLattice.span_top,
    HolOn.of_local fun z => ?_, fun _ _ => 1, fun _ => differentiableOn_const _,
    fun _ _ _ => one_ne_zero, fun i j z hz => ?_⟩⟩
  · have hs : Continuous fun v : Fin g → ℂ => v - z := continuous_sub_right z
    have hWz : IsOpen ((fun v => v - z) ⁻¹' W') := hW'.preimage hs
    refine ⟨(fun v => v - z) ⁻¹' W', fun v => (hφ.exp z).toMul * σ (L (v - z)), by simpa using h0',
      hmulHol _ _ _ _ (HolOn.const hWz _) (HolOn.comp (HolOn.comp hσ hW' hL hLm) hWz
        (differentiableOn_id.sub_const z) fun v hv => hv), ?_⟩
    filter_upwards [(hs.tendsto' z 0 (sub_self z)).eventually hLe] with v hv
    rw [← hv, ← toMul_add, ← map_add, add_sub_cancel]
  · obtain ⟨e, he⟩ := (hval _ _).2.1 _ hz
    rw [he]
    show (1 : ℂ) = e (((1 : Γ(A.left, ⊤ ⊓ ⊤)ˣ)) : Γ(A.left, ⊤ ⊓ ⊤)) * 1
    rw [Units.val_one]
    exact ((_root_.mul_one _).trans e.map_one).symm

/- English proof (translation)
Take `⟨x, hx0, hx⟩` from `FractionalIdeal.exists_ne_zero_mem_isInteger (𝔠.ne_zero)`. Use `⟨⟨x • algebraMap (𝓞 F) F x, Submodule.smul_mem _ x hx⟩, fun τ => ?_⟩` and prove the remaining obligations. Establish `hx' : algebraMap (𝓞 F) F x ≠ 0` using `(map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).2 hx0`. Establish `hτ : τ (algebraMap (𝓞 F) F x) ≠ 0` using `(map_ne_zero τ).2 hx'`. Use `show 0 < τ (x • algebraMap (𝓞 F) F x)`.

Rewrite using `[Algebra.smul_def, map_mul]`. Conclude with `mul_self_pos.2 hτ`.
-/
theorem exists_isTotPos {F : Type} [Field F] [NumberField F] (𝔠 : FracId F) :
    ∃ c : 𝔠.elt, IsTotPos (c : F) := by
  obtain ⟨x, hx0, hx⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (𝔠.ne_zero)
  refine ⟨⟨x • algebraMap (𝓞 F) F x, Submodule.smul_mem _ x hx⟩, fun τ => ?_⟩
  have hx' : algebraMap (𝓞 F) F x ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).2 hx0
  have hτ : τ (algebraMap (𝓞 F) F x) ≠ 0 := (map_ne_zero τ).2 hx'
  show 0 < τ (x • algebraMap (𝓞 F) F x)
  rw [Algebra.smul_def, map_mul]
  exact mul_self_pos.2 hτ

end GlobalTheory.RealMultChart

namespace GlobalTheory.RealMult

open GlobalTheory.RealMultChart in

/- English proof (translation)
Introduce `F _ _ 𝔠 X`. Take `⟨c, hc⟩` from `exists_isTotPos 𝔠`. Establish `hcpt` using `compactSpace_points X.A (X.diag c) (X.pos c hc)`. Take `⟨u⟩` from `exists_holUnif_of_compact X.A (Module.finrank ℚ F) X.dim hcpt (fun a n hn => exists_pow_eq X.A X.ab a n hn)`. Take `⟨h₁, h₂⟩` from `TorusTransfer.tangent_bijective u X.dim`.

Establish `hlift : ∀ f : X.A ⟶ X.A, IsMonHom f → ∃ F' : (Fin (Module.finrank ℚ F) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ), ∀ z, u.ex (F' z) = u.ex z ≫ f` using `fun f hf => (existsUnique_linear_lift_of_isHolTo X.A X.ab _ _ _ u h₁ h₂ (fun z => u.ex z ≫ f) (fun z w => by simp only [u.ex_add]; exact MonObj.mul_comp _ _ f) (HomLinear.isHolTo_ex_comp u f)).exists`. Take `⟨Fa, hFa⟩` from `ArcModel.exists_ringHom_lift u X.rm.toRingAct hlift`. Conclude with `⟨_, u, Fa, hFa⟩`.
-/
theorem Obj.exists_holUnif_ringHom_lift : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)),
    ∃ (L : LB X.A.left) (u : HolUnif X.A L (Module.finrank ℚ F))
      (Fa : 𝓞 F →+* Module.End ℂ (Fin (Module.finrank ℚ F) → ℂ)),
      ∀ (a : 𝓞 F) (z : Fin (Module.finrank ℚ F) → ℂ), u.ex (Fa a z) = u.ex z ≫ X.rm.act a := by
  intro F _ _ 𝔠 X
  obtain ⟨c, hc⟩ := exists_isTotPos 𝔠
  have hcpt := compactSpace_points X.A (X.diag c) (X.pos c hc)
  obtain ⟨u⟩ := exists_holUnif_of_compact X.A (Module.finrank ℚ F) X.dim hcpt
    (fun a n hn => exists_pow_eq X.A X.ab a n hn)
  obtain ⟨h₁, h₂⟩ := TorusTransfer.tangent_bijective u X.dim
  have hlift : ∀ f : X.A ⟶ X.A, IsMonHom f →
      ∃ F' : (Fin (Module.finrank ℚ F) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ), ∀ z, u.ex (F' z) = u.ex z ≫ f :=
    fun f hf => (existsUnique_linear_lift_of_isHolTo X.A X.ab _ _ _ u h₁ h₂ (fun z => u.ex z ≫ f)
      (fun z w => by simp only [u.ex_add]; exact MonObj.mul_comp _ _ f) (HomLinear.isHolTo_ex_comp u f)).exists
  obtain ⟨Fa, hFa⟩ := ArcModel.exists_ringHom_lift u X.rm.toRingAct hlift
  exact ⟨_, u, Fa, hFa⟩

end GlobalTheory.RealMult
