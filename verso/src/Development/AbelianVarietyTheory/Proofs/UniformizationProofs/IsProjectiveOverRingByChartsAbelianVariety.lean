import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsPrincipalMapAwayOfHasProjectiveDimensionLE
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPwOfAffineLoci
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNonzeroLocusEqOfIsAffineOpenOfFactorial
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfFinite
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLbIsoPullAffineSpace
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinFlatChartOfOpenImmersion

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianProjective

section General

variable {S : Scheme.{0}}

/- English proof (translation)
Use `(IsPullback.of_right (h₁₁ := (π ▷ B).left) (v₁₁ := pullback.fst W.hom B.hom) (h₂₁ := π.left) (v₁₂ := pullback.fst V.hom B.hom) ?_ (Over.whiskerRight_left_fst π) (IsPullback.of_hasPullback V.hom B.hom).flip).flip` and prove the remaining obligations. Rewrite using `[Over.whiskerRight_left_snd, Over.w]`. Conclude with `(IsPullback.of_hasPullback W.hom B.hom).flip`.
-/
theorem isPullback_whiskerRight {W V : Over S} (π : W ⟶ V) (B : Over S) :
    IsPullback (fst W B).left (π ▷ B).left π.left (fst V B).left := by
  refine (IsPullback.of_right (h₁₁ := (π ▷ B).left) (v₁₁ := pullback.fst W.hom B.hom)
    (h₂₁ := π.left) (v₁₂ := pullback.fst V.hom B.hom) ?_ (Over.whiskerRight_left_fst π)
    (IsPullback.of_hasPullback V.hom B.hom).flip).flip
  rw [Over.whiskerRight_left_snd, Over.w]
  exact (IsPullback.of_hasPullback W.hom B.hom).flip

/- English proof (translation)
Use `IsPullback.of_right ?_ ?_ (isPullback_whiskerRight π B)` and prove the remaining obligations. Rewrite using `[← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, Over.id_left, Over.id_left]`. Conclude with `IsPullback.of_horiz_isIso ⟨by simp⟩`. Rewrite using `[← Over.comp_left, ← Over.comp_left]`. Use `congr 1`.

Use `ext1`. Simplify using the standard rewrite rules. Simplify using `[← Category.assoc]`.
-/
theorem isPullback_slice {W V B : Over S} (π : W ⟶ V) (y : 𝟙_ (Over S) ⟶ B) :
    IsPullback (lift (𝟙 W) (toUnit W ≫ y)).left π.left (π ▷ B).left (lift (𝟙 V) (toUnit V ≫ y)).left := by
  refine IsPullback.of_right ?_ ?_ (isPullback_whiskerRight π B)
  · rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, Over.id_left, Over.id_left]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    ext1
    · simp
    · simp [← Category.assoc]

/- English proof (translation)
Apply the tactic sequence `refine ⟨(toUnit B ≫ x)⁻¹ * 𝟙 B, ?_, ?_⟩ <;>`. Simplify using `[MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]`.
-/
theorem isIso_transl_left {B : Over S} [GrpObj B] (x : 𝟙_ (Over S) ⟶ B) :
    IsIso ((toUnit B ≫ x) * 𝟙 B) := by
  refine ⟨(toUnit B ≫ x)⁻¹ * 𝟙 B, ?_, ?_⟩ <;>
    simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]

/- English proof (translation)
Apply the tactic sequence `refine ⟨𝟙 B * (toUnit B ≫ x)⁻¹, ?_, ?_⟩ <;>`. Simplify using `[MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]`.
-/
theorem isIso_transl_right {B : Over S} [GrpObj B] (x : 𝟙_ (Over S) ⟶ B) :
    IsIso (𝟙 B * (toUnit B ≫ x)) := by
  refine ⟨𝟙 B * (toUnit B ≫ x)⁻¹, ?_, ?_⟩ <;>
    simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]

/- English proof (translation)
Take `⟨O, hO, hOw⟩` from `isDiscrete_iff_forall_exists_isOpen.mp (π.isDiscrete_preimage_singleton (π w)) w rfl`. Establish `hw : w ∈ O ∩ π ⁻¹' {π w}` using `by rw [hOw]; rfl`. Establish `hg : genericPoint W ∈ O ∩ π ⁻¹' {π w}` using `⟨(genericPoint_specializes w).mem_open hO hw.1, h.symm⟩`. Rewrite `hg` using `[hOw]`. Conclude with `hg.symm`.
-/
theorem eq_genericPoint {W V : Scheme.{0}} [IsIntegral W] (π : W ⟶ V) [IsFinite π] (w : W)
    (h : π w = π (genericPoint W)) : w = genericPoint W := by
  obtain ⟨O, hO, hOw⟩ := isDiscrete_iff_forall_exists_isOpen.mp (π.isDiscrete_preimage_singleton (π w)) w rfl
  have hw : w ∈ O ∩ π ⁻¹' {π w} := by rw [hOw]; rfl
  have hg : genericPoint W ∈ O ∩ π ⁻¹' {π w} :=
    ⟨(genericPoint_specializes w).mem_open hO hw.1, h.symm⟩
  rw [hOw] at hg
  exact hg.symm

/- English proof (translation)
Establish `: JacobsonSpace X.left` using `LocallyOfFiniteType.jacobsonSpace X.hom`. Take `⟨c, hcZ, hc⟩` from `nonempty_inter_closedPoints hne hZ`. Use `⟨Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc), fun p => ?_⟩` and prove the remaining obligations. Conclude with `(pointOfClosedPoint_apply X.hom c hc p).symm ▸ hcZ`.
-/
theorem exists_point {K : Type} [Field K] [IsAlgClosed K] (X : Over (Spec (CommRingCat.of K)))
    [LocallyOfFiniteType X.hom] {Z : Set X.left} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X, ∀ p, x.left p ∈ Z := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints hne hZ
  refine ⟨Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc), fun p => ?_⟩
  exact (pointOfClosedPoint_apply X.hom c hc p).symm ▸ hcZ

/- English proof (translation)
The claim follows from `have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth K f x uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing isPrincipal_map_away_of_hasProjectiveDimensionLE _`.
-/
theorem ufd_stalk {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    [Smooth f] (x : X) : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth K f x
  uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    isPrincipal_map_away_of_hasProjectiveDimensionLE _

/- English proof (translation)
Rewrite using `[HasRingHomProperty.Spec_iff (P := @Smooth)]`. Conclude with `RingHom.smooth_algebraMap.2 {}`.
-/
theorem smooth_affineSpace (K : Type) [Field K] (g : ℕ) :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.2 {}

end General

section Family

variable {K : Type} [Field K] {W V B : Over (Spec (CommRingCat.of K))}

/- English proof (translation)
Establish `e : 𝟙 B.left = (lift (toUnit B ≫ v) (𝟙 B)).left ≫ (snd V B).left`. Rewrite using `[← Over.comp_left, lift_snd, Over.id_left]`. Establish `H' : LBIso (N.pull (lift (toUnit B ≫ v) (𝟙 B)).left) (N₀.pull (𝟙 B.left))` using `LBIso.chartPull (GlobalTheory.chartPullPull N _) (chartPullSame N₀ _ _ _ _ fun _ => e) H`. Establish `H'' : LBIso N₀ (N.pull (lift (toUnit B ≫ v) (𝟙 B)).left)` using `LBIso.trans hN₀ (pull_isLB hN₀ _) (pull_isLB hN _) (LBIso.symm (GlobalTheory.lbIso_of_chartPull (GlobalTheory.chartPullPull N₀ (𝟙 _)) hN₀)) (LBIso.symm H')`. Take `⟨t, ht⟩` from `GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso hN₀ (pull_isLB hN _) H'' (GlobalTheory.secPull n _)`.

Conclude with `⟨t, ht.trans (GlobalTheory.nonzeroLocus_secPull n _)⟩`.
-/
theorem exists_sec_fibre {N : LB (V ⊗ B).left} {N₀ : LB B.left} (hN : N.IsLB) (hN₀ : N₀.IsLB)
    (H : LBIso N (N₀.pull (snd V B).left)) (n : N.Sec) (v : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ V) :
    ∃ t : N₀.Sec, nonzeroLocus t = (lift (toUnit B ≫ v) (𝟙 B)).left ⁻¹ᵁ nonzeroLocus n := by
  have e : 𝟙 B.left = (lift (toUnit B ≫ v) (𝟙 B)).left ≫ (snd V B).left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have H' : LBIso (N.pull (lift (toUnit B ≫ v) (𝟙 B)).left) (N₀.pull (𝟙 B.left)) :=
    LBIso.chartPull (GlobalTheory.chartPullPull N _) (chartPullSame N₀ _ _ _ _ fun _ => e) H
  have H'' : LBIso N₀ (N.pull (lift (toUnit B ≫ v) (𝟙 B)).left) :=
    LBIso.trans hN₀ (pull_isLB hN₀ _) (pull_isLB hN _)
      (LBIso.symm (GlobalTheory.lbIso_of_chartPull (GlobalTheory.chartPullPull N₀ (𝟙 _)) hN₀)) (LBIso.symm H')
  obtain ⟨t, ht⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso hN₀ (pull_isLB hN _) H'' (GlobalTheory.secPull n _)
  exact ⟨t, ht.trans (GlobalTheory.nonzeroLocus_secPull n _)⟩

variable [GrpObj B]

/- English proof (translation)
Introduce `b hb`. Establish `e₁ : lift (toUnit B ≫ w) (𝟙 B) ≫ π ▷ B = lift (toUnit B ≫ w ≫ π) (𝟙 B)` using `by simp`. Establish `e₂ : lift (toUnit B ≫ w) (𝟙 B) ≫ ((fst W B ≫ a) * snd W B) = (toUnit B ≫ w ≫ a) * 𝟙 B`. Simplify using `[MonObj.comp_mul]`. Establish `h` using `hO _ hb ((lift (toUnit B ≫ w) (𝟙 B)).left b) (by`.

Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, e₁])`. Rewrite using `[← e₂, Over.comp_left]`. Conclude with `h`.
-/
theorem fibre_le (π : W ⟶ V) (a : W ⟶ B) (U : B.left.Opens) (O : (V ⊗ B).left.Opens)
    (hO : ∀ x, x ∈ O → ∀ z, (π ▷ B).left z = x → z ∈ ((fst W B ≫ a) * snd W B).left ⁻¹ᵁ U)
    (w : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ W) :
    (lift (toUnit B ≫ w ≫ π) (𝟙 B)).left ⁻¹ᵁ O ≤ ((toUnit B ≫ w ≫ a) * 𝟙 B).left ⁻¹ᵁ U := by
  intro b hb
  have e₁ : lift (toUnit B ≫ w) (𝟙 B) ≫ π ▷ B = lift (toUnit B ≫ w ≫ π) (𝟙 B) := by simp
  have e₂ : lift (toUnit B ≫ w) (𝟙 B) ≫ ((fst W B ≫ a) * snd W B) = (toUnit B ≫ w ≫ a) * 𝟙 B := by
    simp [MonObj.comp_mul]
  have h := hO _ hb ((lift (toUnit B ≫ w) (𝟙 B)).left b) (by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e₁])
  rw [← e₂, Over.comp_left]
  exact h

/- English proof (translation)
Establish `hg : genericPoint W.left ∈ (π ≫ lift (𝟙 V) (toUnit V ≫ y)).left ⁻¹ᵁ O`. Use `hO _ fun z hz => ?_` and prove the remaining obligations. Take `⟨w', rfl, hw'⟩` from `Scheme.exists_preimage_of_isPullback (isPullback_slice π y) z (π.left (genericPoint W.left)) (by rw [hz, Over.comp_left, Scheme.Hom.comp_apply])`. Take `rfl` from `eq_genericPoint π.left w' hw'`. Establish `e : lift (𝟙 W) (toUnit W ≫ y) ≫ ((fst W B ≫ a) * snd W B) = a ≫ (𝟙 B * (toUnit B ≫ y))`.

Simplify using `[MonObj.comp_mul, ← Category.assoc]`. Use `isIso_transl_right y` as an intermediate fact. Establish `: IsIso (𝟙 B * (toUnit B ≫ y)).left` using `inferInstanceAs (IsIso ((Over.forget _).map (𝟙 B * (toUnit B ≫ y))))`. Express the relevant statement in the definitionally equal form `((lift (𝟙 W) (toUnit W ≫ y)).left ≫ ((fst W B ≫ a) * snd W B).left) _ ∈ U`. Rewrite using `[← Over.comp_left, e, Over.comp_left, genericPoint_eq_of_isOpenImmersion]`.

Conclude with `((genericPoint_spec B.left).mem_open_set_iff U.isOpen).2 (by simpa using hU)`. Take `⟨w, hw⟩` from `exists_point W (Z := ((π ≫ lift (𝟙 V) (toUnit V ≫ y)).left ⁻¹ᵁ O : W.left.Opens)) (TopologicalSpace.Opens.isOpen _).isLocallyClosed ⟨_, hg⟩`. Use `⟨w, fun p => ?_⟩` and prove the remaining obligations. Establish `e : y ≫ lift (toUnit B ≫ w ≫ π) (𝟙 B) = w ≫ π ≫ lift (𝟙 V) (toUnit V ≫ y)` using `by ext1`. Simplify using `[← Category.assoc]`.

Simplify using `[← Category.assoc]`. Establish `h` using `hw p`. Express the relevant statement in the definitionally equal form `(y.left ≫ (lift (toUnit B ≫ w ≫ π) (𝟙 B)).left) p ∈ O`. Rewrite using `[← Over.comp_left, e, Over.comp_left]`. Conclude with `h`.
-/
theorem exists_fibre_mem [IsAlgClosed K] [IsIntegral B.left] [IsIntegral W.left] [LocallyOfFiniteType W.hom]
    (π : W ⟶ V) [IsFinite π.left] (a : W ⟶ B) [IsOpenImmersion a.left] (U : B.left.Opens)
    (hU : (U : Set B.left).Nonempty) (O : (V ⊗ B).left.Opens)
    (hO : ∀ x, (∀ z, (π ▷ B).left z = x → z ∈ ((fst W B ≫ a) * snd W B).left ⁻¹ᵁ U) → x ∈ O)
    (y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B) :
    ∃ w : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ W,
      ∀ p, y.left p ∈ (lift (toUnit B ≫ w ≫ π) (𝟙 B)).left ⁻¹ᵁ O := by
  have hg : genericPoint W.left ∈ (π ≫ lift (𝟙 V) (toUnit V ≫ y)).left ⁻¹ᵁ O := by
    refine hO _ fun z hz => ?_
    obtain ⟨w', rfl, hw'⟩ := Scheme.exists_preimage_of_isPullback (isPullback_slice π y)
      z (π.left (genericPoint W.left)) (by rw [hz, Over.comp_left, Scheme.Hom.comp_apply])
    obtain rfl := eq_genericPoint π.left w' hw'
    have e : lift (𝟙 W) (toUnit W ≫ y) ≫ ((fst W B ≫ a) * snd W B) = a ≫ (𝟙 B * (toUnit B ≫ y)) := by
      simp [MonObj.comp_mul, ← Category.assoc]
    have := isIso_transl_right y
    have : IsIso (𝟙 B * (toUnit B ≫ y)).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (𝟙 B * (toUnit B ≫ y))))
    change ((lift (𝟙 W) (toUnit W ≫ y)).left ≫ ((fst W B ≫ a) * snd W B).left) _ ∈ U
    rw [← Over.comp_left, e, Over.comp_left, genericPoint_eq_of_isOpenImmersion]
    exact ((genericPoint_spec B.left).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  obtain ⟨w, hw⟩ := exists_point W (Z := ((π ≫ lift (𝟙 V) (toUnit V ≫ y)).left ⁻¹ᵁ O : W.left.Opens))
    (TopologicalSpace.Opens.isOpen _).isLocallyClosed ⟨_, hg⟩
  refine ⟨w, fun p => ?_⟩
  have e : y ≫ lift (toUnit B ≫ w ≫ π) (𝟙 B) = w ≫ π ≫ lift (𝟙 V) (toUnit V ≫ y) := by
    ext1
    · simp [← Category.assoc]
    · simp [← Category.assoc]
  have h := hw p
  change (y.left ≫ (lift (toUnit B ≫ w ≫ π) (𝟙 B)).left) p ∈ O
  rw [← Over.comp_left, e, Over.comp_left]
  exact h

end Family

/- English proof (translation)
Use `hB.smooth` as an intermediate fact. Use `hB.proper` as an intermediate fact. Establish `: GeometricallyIntegral B.hom` using `forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected`. Establish `: IsIntegral B.left` using `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian B.hom`. Establish `: IsLocallyNoetherian B.left` using `LocallyOfFiniteType.isLocallyNoetherian B.hom`.

Establish `: B.left.IsSeparated` using `⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint B.left)) isOpen_univ`. Take `⟨L, s, hL, hs⟩` from `GlobalTheory.exists_sec_nonzeroLocus_eq_of_isAffineOpen_of_factorial B.left (ufd_stalk B.hom) U hU ⟨_, hxU⟩`. Take `⟨g, W₀, V₀, π₀, hW, hfin, hflat, -, hπ⟩` from `GlobalTheory.Unif.exists_finite_flat_chart K B.left B.hom`. Set `A : Over (Spec (CommRingCat.of K))` to `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K))))`.

Establish `: Smooth A.hom` using `smooth_affineSpace K g`. Establish `: IsIntegral A.left` using `inferInstanceAs (IsIntegral (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))`. Establish `: IsAffine A.left` using `inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))`. Establish `: IsLocallyNoetherian A.left` using `LocallyOfFiniteType.isLocallyNoetherian A.hom`. Set `W : Over (Spec (CommRingCat.of K))` to `Over.mk (W₀.ι ≫ B.hom)`.

Set `V : Over (Spec (CommRingCat.of K))` to `Over.mk (V₀.ι ≫ A.hom)`. Set `π : W ⟶ V` to `Over.homMk π₀ hπ`. Set `a : W ⟶ B` to `Over.homMk W₀.ι rfl`. Set `j : V ⟶ A` to `Over.homMk V₀.ι rfl`. Establish `: IsFinite π.left` using `hfin`.

Establish `: Flat π.left` using `hflat`. Establish `: IsOpenImmersion a.left` using `inferInstanceAs (IsOpenImmersion W₀.ι)`. Establish `: IsOpenImmersion j.left` using `inferInstanceAs (IsOpenImmersion V₀.ι)`. Establish `: Nonempty W.left` using `⟨⟨hW.choose, hW.choose_spec⟩⟩`. Establish `: IsIntegral W.left` using `isIntegral_of_isOpenImmersion a.left`.

Establish `: LocallyOfFiniteType W.hom` using `inferInstanceAs (LocallyOfFiniteType (W₀.ι ≫ B.hom))`. Establish `: IsFinite (π ▷ B).left` using `MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›`. Establish `: Flat (π ▷ B).left` using `MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›`. Establish `hj : IsOpenImmersion (j ▷ B).left` using `MorphismProperty.of_isPullback (isPullback_whiskerRight j B) ‹_›`. Establish `: Smooth (A ⊗ B).hom` using `inferInstanceAs (Smooth (pullback.fst A.hom B.hom ≫ A.hom))`.

Establish `: QuasiCompact (A ⊗ B).hom` using `inferInstanceAs (QuasiCompact (pullback.fst A.hom B.hom ≫ A.hom))`. Establish `: IsLocallyNoetherian (A ⊗ B).left` using `LocallyOfFiniteType.isLocallyNoetherian (A ⊗ B).hom`. Establish `: CompactSpace (A ⊗ B).left` using `QuasiCompact.compactSpace_of_compactSpace (A ⊗ B).hom`. Establish `: IsIntegral (A ⊗ B).left` using `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst A.hom B.hom)`. Establish `: IsLocallyNoetherian (V ⊗ B).left` using `LocallyOfFiniteType.isLocallyNoetherian (j ▷ B).left`.

Take `⟨N, n, hN, hn⟩` from `GlobalTheory.FlatNorm.exists_norm_lb _ _ (π ▷ B).left (L.pull ((fst W B ≫ a) * snd W B).left) (GlobalTheory.secPull s _) (pull_isLB hL _)`. Rewrite `hn` using `[GlobalTheory.nonzeroLocus_secPull, hs]`. Take `⟨N', hN', hφ⟩` from `GlobalTheory.exists_lineBundle_extension _ _ (j ▷ B).left hj (ufd_stalk (A ⊗ B).hom) N hN`. Take `⟨N₀, hN₀, hψ⟩` from `GlobalTheory.exists_lbIso_pull_affineSpace K B (ufd_stalk B.hom) g N' hN'`. Establish `e : (snd V B).left = (j ▷ B).left ≫ (snd A B).left`.

Rewrite using `[← Over.comp_left, whiskerRight_snd]`. Establish `H : LBIso N (N₀.pull (snd V B).left)` using `LBIso.trans hN (pull_isLB hN' _) (pull_isLB hN₀ _) (LBIso.symm hφ) (LBIso.chartPull (GlobalTheory.chartPullPull N' _) (chartPullSame N₀ _ _ _ _ fun _ => e) hψ)`. Use `choose t ht using fun w : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ W => exists_sec_fibre hN hN₀ H n (w ≫ π)`. Use `⟨N₀, _, t, hN₀, ?_, fun w => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Establish `hc : ((⨆ i, nonzeroLocus (t i) : B.left.Opens) : Set B.left)ᶜ.Nonempty` using `Set.nonempty_compl.2 fun h => hne (TopologicalSpace.Opens.ext h)`. Take `⟨y, hy⟩` from `exists_point B (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed hc`. Take `⟨w, hw⟩` from `exists_fibre_mem π a U ⟨_, hxU⟩ (nonzeroLocus n) (fun x => (hn x).2) y`. Use `hy (IsLocalRing.closedPoint K) (TopologicalSpace.Opens.mem_iSup.2 ⟨w, ?_⟩)` and prove the remaining obligations. Rewrite using `[ht]`.

Conclude with `hw _`. Establish `hle : nonzeroLocus (t w) ≤ ((toUnit B ≫ w ≫ a) * 𝟙 B).left ⁻¹ᵁ U` using `(ht w).trans_le (fibre_le π a U (nonzeroLocus n) (fun x => (hn x).1) w)`. Use `isIso_transl_left (w ≫ a)` as an intermediate fact. Establish `: IsIso ((toUnit B ≫ w ≫ a) * 𝟙 B).left` using `inferInstanceAs (IsIso ((Over.forget _).map ((toUnit B ≫ w ≫ a) * 𝟙 B)))`. Establish `h` using `GlobalTheory.isAffineOpen_nonzeroLocus_inf hN₀ (t w) (hU.preimage ((toUnit B ≫ w ≫ a) * 𝟙 B).left)`.

Rewrite `h` using `[inf_eq_left.2 hle]`. Then use the resulting hypothesis.
-/
theorem exists_affine_loci (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B]
    (hB : IsAbelianScheme B) : ∃ (N₀ : LB B.left) (I : Type) (t : I → N₀.Sec), N₀.IsLB ∧
      (⨆ i, nonzeroLocus (t i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (t i)) := by
  have := hB.smooth
  have := hB.proper
  have : GeometricallyIntegral B.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian B.hom
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint B.left)) isOpen_univ
  obtain ⟨L, s, hL, hs⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_isAffineOpen_of_factorial B.left (ufd_stalk B.hom) U hU ⟨_, hxU⟩
  obtain ⟨g, W₀, V₀, π₀, hW, hfin, hflat, -, hπ⟩ := GlobalTheory.Unif.exists_finite_flat_chart K B.left B.hom
  let A : Over (Spec (CommRingCat.of K)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K))))
  have : Smooth A.hom := smooth_affineSpace K g
  have : IsIntegral A.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))
  have : IsAffine A.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  let W : Over (Spec (CommRingCat.of K)) := Over.mk (W₀.ι ≫ B.hom)
  let V : Over (Spec (CommRingCat.of K)) := Over.mk (V₀.ι ≫ A.hom)
  let π : W ⟶ V := Over.homMk π₀ hπ
  let a : W ⟶ B := Over.homMk W₀.ι rfl
  let j : V ⟶ A := Over.homMk V₀.ι rfl
  have : IsFinite π.left := hfin
  have : Flat π.left := hflat
  have : IsOpenImmersion a.left := inferInstanceAs (IsOpenImmersion W₀.ι)
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion V₀.ι)
  have : Nonempty W.left := ⟨⟨hW.choose, hW.choose_spec⟩⟩
  have : IsIntegral W.left := isIntegral_of_isOpenImmersion a.left
  have : LocallyOfFiniteType W.hom := inferInstanceAs (LocallyOfFiniteType (W₀.ι ≫ B.hom))
  have : IsFinite (π ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›
  have : Flat (π ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›
  have hj : IsOpenImmersion (j ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight j B) ‹_›
  have : Smooth (A ⊗ B).hom := inferInstanceAs (Smooth (pullback.fst A.hom B.hom ≫ A.hom))
  have : QuasiCompact (A ⊗ B).hom := inferInstanceAs (QuasiCompact (pullback.fst A.hom B.hom ≫ A.hom))
  have : IsLocallyNoetherian (A ⊗ B).left := LocallyOfFiniteType.isLocallyNoetherian (A ⊗ B).hom
  have : CompactSpace (A ⊗ B).left := QuasiCompact.compactSpace_of_compactSpace (A ⊗ B).hom
  have : IsIntegral (A ⊗ B).left :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst A.hom B.hom)
  have : IsLocallyNoetherian (V ⊗ B).left :=
    LocallyOfFiniteType.isLocallyNoetherian (j ▷ B).left
  obtain ⟨N, n, hN, hn⟩ := GlobalTheory.FlatNorm.exists_norm_lb _ _ (π ▷ B).left (L.pull ((fst W B ≫ a) * snd W B).left)
    (GlobalTheory.secPull s _) (pull_isLB hL _)
  rw [GlobalTheory.nonzeroLocus_secPull, hs] at hn
  obtain ⟨N', hN', hφ⟩ := GlobalTheory.exists_lineBundle_extension _ _ (j ▷ B).left hj (ufd_stalk (A ⊗ B).hom) N hN
  obtain ⟨N₀, hN₀, hψ⟩ := GlobalTheory.exists_lbIso_pull_affineSpace K B (ufd_stalk B.hom) g N' hN'
  have e : (snd V B).left = (j ▷ B).left ≫ (snd A B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have H : LBIso N (N₀.pull (snd V B).left) :=
    LBIso.trans hN (pull_isLB hN' _) (pull_isLB hN₀ _) (LBIso.symm hφ)
      (LBIso.chartPull (GlobalTheory.chartPullPull N' _) (chartPullSame N₀ _ _ _ _ fun _ => e) hψ)
  choose t ht using fun w : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ W => exists_sec_fibre hN hN₀ H n (w ≫ π)
  refine ⟨N₀, _, t, hN₀, ?_, fun w => ?_⟩
  · by_contra hne
    have hc : ((⨆ i, nonzeroLocus (t i) : B.left.Opens) : Set B.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h => hne (TopologicalSpace.Opens.ext h)
    obtain ⟨y, hy⟩ := exists_point B (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed hc
    obtain ⟨w, hw⟩ := exists_fibre_mem π a U ⟨_, hxU⟩ (nonzeroLocus n) (fun x => (hn x).2) y
    refine hy (IsLocalRing.closedPoint K) (TopologicalSpace.Opens.mem_iSup.2 ⟨w, ?_⟩)
    rw [ht]
    exact hw _
  · have hle : nonzeroLocus (t w) ≤ ((toUnit B ≫ w ≫ a) * 𝟙 B).left ⁻¹ᵁ U :=
      (ht w).trans_le (fibre_le π a U (nonzeroLocus n) (fun x => (hn x).1) w)
    have := isIso_transl_left (w ≫ a)
    have : IsIso ((toUnit B ≫ w ≫ a) * 𝟙 B).left :=
      inferInstanceAs (IsIso ((Over.forget _).map ((toUnit B ≫ w ≫ a) * 𝟙 B)))
    have h := GlobalTheory.isAffineOpen_nonzeroLocus_inf hN₀ (t w) (hU.preimage ((toUnit B ≫ w ≫ a) * 𝟙 B).left)
    rwa [inf_eq_left.2 hle] at h

/- English proof (translation)
Introduce `K _ _ B _ _ hB`. Use `hB.proper` as an intermediate fact. Establish `: CompactSpace B.left` using `QuasiCompact.compactSpace_of_compactSpace B.hom`. Take `⟨N₀, I, t, hN₀, hc, ha⟩` from `exists_affine_loci K B hB`. Take `⟨F, hF⟩` from `isCompact_univ.elim_finite_subcover (fun i => (nonzeroLocus (t i) : Set B.left)) (fun i => (nonzeroLocus (t i)).isOpen) fun x _ => by`.

Establish `hx : x ∈ ⨆ i, nonzeroLocus (t i)` using `by rw [hc]; trivial`. Conclude with `Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 hx)`. Establish `hne : F.Nonempty`. Take `⟨i, hi, -⟩` from `Set.mem_iUnion₂.1 (hF (Set.mem_univ (η[B].left (IsLocalRing.closedPoint K))))`. Conclude with `⟨i, hi⟩`.

Take `⟨m, hm⟩` from `Nat.exists_eq_succ_of_ne_zero hne.card_pos.ne'`. Set `e : Fin (m + 1) ≃ F` to `(F.equivFinOfCardEq hm).symm`. Take `⟨d, -, n', s, hs⟩` from `veryAmpleBy_pw_of_affine_loci K B.left B.hom N₀ m (fun k => t (e k)) hN₀ (top_unique fun x _ => by`. Take `⟨i, hi, hx⟩` from `Set.mem_iUnion₂.1 (hF (Set.mem_univ x))`. Use `TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm ⟨i, hi⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Equiv.apply_symm_apply]`. Conclude with `hx)`. Use `fun k => ha _`. Conclude with `⟨_, isLB_pw hN₀ _, n', s, hs⟩`.
-/
theorem isProjBy_of_isAbelianScheme : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom := by
  intro K _ _ B _ _ hB
  have := hB.proper
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  obtain ⟨N₀, I, t, hN₀, hc, ha⟩ := exists_affine_loci K B hB
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun i => (nonzeroLocus (t i) : Set B.left))
    (fun i => (nonzeroLocus (t i)).isOpen) fun x _ => by
      have hx : x ∈ ⨆ i, nonzeroLocus (t i) := by rw [hc]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 hx)
  have hne : F.Nonempty := by
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ (η[B].left (IsLocalRing.closedPoint K))))
    exact ⟨i, hi⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne.card_pos.ne'
  let e : Fin (m + 1) ≃ F := (F.equivFinOfCardEq hm).symm
  obtain ⟨d, -, n', s, hs⟩ := veryAmpleBy_pw_of_affine_loci K B.left B.hom N₀ m (fun k => t (e k)) hN₀
    (top_unique fun x _ => by
      obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
      refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm ⟨i, hi⟩, ?_⟩
      rw [Equiv.apply_symm_apply]
      exact hx)
    fun k => ha _
  exact ⟨_, isLB_pw hN₀ _, n', s, hs⟩

end GlobalTheory.AbelianProjective
