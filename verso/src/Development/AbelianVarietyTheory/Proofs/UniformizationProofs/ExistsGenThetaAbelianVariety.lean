import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw.CubeProj

open CubeGen

/- English proof (translation)
Take `⟨g, rfl⟩` from `Spec.map_surjective t`. Take `⟨H, hH, n, s, hs⟩` from `hf`. Establish `hH' : (H.pull φ).IsLB` using `DVR.linComb_isLB _ hH _ _`. Take `⟨w, hw⟩` from `GlobalTheory.PolBaseChange.lbIso_refl hH'`. Use `choose s' hs' using fun j => (GlobalTheory.SecPullIso.section_pull X X' φ H _ w hH hH' hw (s j)).1.exists`.

Use `⟨_, hH', n, s', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H n s hH hs R' g.hom X' f' φ h.w ?_ _ w s' hH' hw hs'⟩` and prove the remaining obligations. Establish `e : pullback.lift φ f' h.w = h.isoPullback.hom`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst, IsPullback.isoPullback_hom_fst]`. Rewrite using `[pullback.lift_snd, IsPullback.isoPullback_hom_snd]`.

Establish `: IsClosedImmersion (pullback.lift φ f' h.w)` using `by rw [e]; infer_instance`. Conclude with `this`.
-/
theorem isProjBy_baseChange {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} (hf : IsProjBy f) {φ : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
    {t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (h : IsPullback φ f' f t) : IsProjBy f' := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective t
  obtain ⟨H, hH, n, s, hs⟩ := hf
  have hH' : (H.pull φ).IsLB := DVR.linComb_isLB _ hH _ _
  obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl hH'
  choose s' hs' using fun j => (GlobalTheory.SecPullIso.section_pull X X' φ H _ w hH hH' hw (s j)).1.exists
  refine ⟨_, hH', n, s', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H n s hH hs R' g.hom X' f' φ h.w ?_
    _ w s' hH' hw hs'⟩
  have e : pullback.lift φ f' h.w = h.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  have : IsClosedImmersion (pullback.lift φ f' h.w) := by rw [e]; infer_instance
  exact this

/- English proof (translation)
Establish `hI` using `GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected`. Establish `hPerf` using `GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj`. Establish `hSegre` using `GlobalTheory.AbLaw.isProjBy_tensor`. Establish `hClosed` using `GlobalTheory.TrivLocus.isClosed_trivLocus`. Establish `hOpen` using `GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre hG GlobalTheory.AbLaw.Seesaw.seesaw (GlobalTheory.SmallExtLift.exists_gen_of_small_extension hG GlobalTheory.KuennethOne.kuenneth_injective)`.

Use `hA.geomConnected` as an intermediate fact. Establish `H` using `fibTriv_clopen M (thφ A (x3 A)) thε (x3 A 2).left (fun R _ j => by`. Take `⟨q, hq, q₀, q₁⟩` from `exists_cube_chart A j`. Establish `hB` using `isAb_baseChange hA (j ≫ A.hom)`. Establish `one` using `one_left_fst (A := A) (j ≫ A.hom)`.

Establish `pB : IsProjBy ((Over.pullback (j ≫ A.hom)).obj A).hom` using `isProjBy_baseChange hp (IsPullback.of_hasPullback A.hom (j ≫ A.hom))`. Set `B` to `(Over.pullback (j ≫ A.hom)).obj A`. Establish `: Smooth B.hom` using `hB.smooth`. Establish `: IsProper B.hom` using `hB.proper`. Establish `: GeometricallyConnected B.hom` using `hB.geomConnected`.

Establish `sm : Smooth (B ⊗ B).hom`. Express the relevant statement in the definitionally equal form `Smooth (pullback.fst B.hom B.hom ≫ B.hom)`. Use `infer_instance`. Establish `pr : IsProper (B ⊗ B).hom`. Express the relevant statement in the definitionally equal form `IsProper (pullback.fst B.hom B.hom ≫ B.hom)`.

Use `infer_instance`. Establish `gc : GeometricallyConnected (B ⊗ B).hom`. Express the relevant statement in the definitionally equal form `GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)`. Conclude with `GeometricallyConnected.comp _ _`. Establish `hN : (LB.LinComb M (fun k => q ≫ thφ A (x3 A) k) thε).IsLB` using `DVR.linComb_isLB _ hM _ _`.

Establish `pf` using `hPerf R _ _ sm (hSegre R B B pB pB)`. Use `⟨_, q, (B ⊗ B).hom, hq, hClosed R _ _ _ hN (pf _ hN) (pf _ (isLB_pw hN _)) pr (hI _ _ _ sm gc), fun F _ g Z π f' => hOpen R B hB _ hN (pf _ hN) ?_ ?_ F g Z π f'⟩` and prove the remaining obligations. Rewrite using `[triv_pull_comp_iff]`. Use `trivAt_of_formal hM _ (prod_face _ 1 (B.hom ≫ j ≫ A.hom) ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]`.

Conclude with `one B`. Rewrite using `[triv_pull_comp_iff]`. Use `trivAt_of_formal hM _ (prod_face _ 0 (B.hom ≫ j ≫ A.hom) ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]`. Conclude with `one B)`.

Establish `hclopen : IsClopen (fibTriv M (thφ A (x3 A)) thε (x3 A 2).left)` using `⟨H.2, by rw [H.1.antisymm (locTriv_subset _ _ _ _)]; exact isOpen_locTriv _ _ _ _⟩`. Establish `all : ∀ t, t ∈ fibTriv M (thφ A (x3 A)) thε (x3 A 2).left` using `fun t => by`. Establish `hr : Set.range ((Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t)) = {A.hom t}` using `Scheme.range_fromSpecResidueField _`. Take `⟨y, hy⟩` from `hr.ge rfl`. Set `g` to `(Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t) ≫ η[A].left`.

Establish `gw : g ≫ A.hom = (Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t)`. Rewrite using `[Category.assoc, Over.w]`. Conclude with `Category.comp_id _`. Use `(A.hom.isConnected_preimage_singleton (A.hom t)).isPreconnected.subset_isClopen hclopen ⟨g y, (congrArg (fun m : Spec ((Spec (CommRingCat.of R₀)).residueField (A.hom t)) ⟶ Spec (CommRingCat.of R₀) => m y) gw).trans hy, ?_⟩ rfl` and prove the remaining obligations. Conclude with `⟨(Spec (CommRingCat.of R₀)).residueField (A.hom t), inferInstance, g, _, _, _, ⟨y, rfl⟩, IsPullback.of_hasPullback (x3 A 2).left g, trivAt_of_formal hM _ (prod_face _ 2 (pullback.snd _ g ≫ (Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t)) (pullback.condition.trans (Categ …`.

Set `e : A ⟶ G3 A` to `lift 1 (lift 1 (𝟙 _))`. Establish `e₀ : e ≫ x3 A 0 = 1` using `by simp [e, x3]`. Establish `e₂ : e ≫ x3 A 2 = 𝟙 _` using `by simp [e, x3]`. Use `triv_of_local hM (thφ A (x3 A)) thε (x3 A 2).left e.left (congrArg (fun q => q.left) e₂) (fun Z b => prod_face _ 0 (b ≫ A.hom) ?_) (fun V => ?_) (fun s => H.1 (all s))` and prove the remaining obligations. Rewrite using `[Category.assoc, ← Over.comp_left, e₀, Category.assoc]`.

Both sides reduce to the same expression. Take `⟨q, hq, -⟩` from `exists_cube_chart A V.ι`. Establish `hB` using `isAb_baseChange hA (V.ι ≫ A.hom)`. Use `⟨_, q, _, hq, ?_⟩` and prove the remaining obligations. Rewrite using `[← Over.w (snd _ _)]`.

Conclude with `surj_comp (surj_snd hG hB _) (hG _ _ hB).2`.
-/
theorem exists_gen_theta_of_isProjBy (hG : GlobalFnsSt) (R₀ : Type) [CommRing R₀]
    (A : Over (Spec (CommRingCat.of R₀))) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (hp : IsProjBy A.hom) (M : LB A.left) (hM : M.IsLB) : ∃ t : LB.Gen (Theta A M), t.IsGen := by
  have hI := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have hPerf := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj
  have hSegre := GlobalTheory.AbLaw.isProjBy_tensor
  have hClosed := GlobalTheory.TrivLocus.isClosed_trivLocus
  have hOpen := GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre hG GlobalTheory.AbLaw.Seesaw.seesaw
    (GlobalTheory.SmallExtLift.exists_gen_of_small_extension hG GlobalTheory.KuennethOne.kuenneth_injective)
  have := hA.geomConnected
  have H := fibTriv_clopen M (thφ A (x3 A)) thε (x3 A 2).left (fun R _ j => by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_cube_chart A j
    have hB := isAb_baseChange hA (j ≫ A.hom)
    have one := one_left_fst (A := A) (j ≫ A.hom)
    have pB : IsProjBy ((Over.pullback (j ≫ A.hom)).obj A).hom :=
      isProjBy_baseChange hp (IsPullback.of_hasPullback A.hom (j ≫ A.hom))
    let B := (Over.pullback (j ≫ A.hom)).obj A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN : (LB.LinComb M (fun k => q ≫ thφ A (x3 A) k) thε).IsLB := DVR.linComb_isLB _ hM _ _
    have pf := hPerf R _ _ sm (hSegre R B B pB pB)
    refine ⟨_, q, (B ⊗ B).hom, hq, hClosed R _ _ _ hN (pf _ hN) (pf _ (isLB_pw hN _)) pr (hI _ _ _ sm gc),
      fun F _ g Z π f' => hOpen R B hB _ hN (pf _ hN) ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hM _ (prod_face _ 1 (B.hom ≫ j ≫ A.hom) ?_)
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hM _ (prod_face _ 0 (B.hom ≫ j ≫ A.hom) ?_)
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have hclopen : IsClopen (fibTriv M (thφ A (x3 A)) thε (x3 A 2).left) :=
    ⟨H.2, by rw [H.1.antisymm (locTriv_subset _ _ _ _)]; exact isOpen_locTriv _ _ _ _⟩
  have all : ∀ t, t ∈ fibTriv M (thφ A (x3 A)) thε (x3 A 2).left := fun t => by
    have hr : Set.range ((Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t)) = {A.hom t} := Scheme.range_fromSpecResidueField _
    obtain ⟨y, hy⟩ := hr.ge rfl
    let g := (Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t) ≫ η[A].left
    have gw : g ≫ A.hom = (Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t) := by
      rw [Category.assoc, Over.w]; exact Category.comp_id _
    refine (A.hom.isConnected_preimage_singleton (A.hom t)).isPreconnected.subset_isClopen hclopen
      ⟨g y, (congrArg (fun m : Spec ((Spec (CommRingCat.of R₀)).residueField (A.hom t)) ⟶ Spec (CommRingCat.of R₀) => m y) gw).trans hy, ?_⟩ rfl
    exact ⟨(Spec (CommRingCat.of R₀)).residueField (A.hom t), inferInstance, g, _, _, _, ⟨y, rfl⟩,
      IsPullback.of_hasPullback (x3 A 2).left g,
      trivAt_of_formal hM _ (prod_face _ 2 (pullback.snd _ g ≫ (Spec (CommRingCat.of R₀)).fromSpecResidueField (A.hom t))
        (pullback.condition.trans (Category.assoc _ _ _).symm))⟩
  let e : A ⟶ G3 A := lift 1 (lift 1 (𝟙 _))
  have e₀ : e ≫ x3 A 0 = 1 := by simp [e, x3]
  have e₂ : e ≫ x3 A 2 = 𝟙 _ := by simp [e, x3]
  refine triv_of_local hM (thφ A (x3 A)) thε (x3 A 2).left e.left (congrArg (fun q => q.left) e₂)
    (fun Z b => prod_face _ 0 (b ≫ A.hom) ?_) (fun V => ?_) (fun s => H.1 (all s))
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_cube_chart A V.ι
    have hB := isAb_baseChange hA (V.ι ≫ A.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2

/- English proof (translation)
Introduce `hG K _ _ B _ _ hB hp M hM` and use `exists_gen_theta_of_isProjBy hG K B hB hp M hM`.
-/
theorem exists_gen_theta_abelianVariety : GlobalFnsSt → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB → ∃ t : LB.Gen (Theta B M), t.IsGen :=
  fun hG K _ _ B _ _ hB hp M hM => exists_gen_theta_of_isProjBy hG K B hB hp M hM

end GlobalTheory.AbLaw.CubeProj
