import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAlongIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKTrivialOfPrincipalGenericFibreDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenThetaAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMaps
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.UU
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KTrivDvrSpread

/- English proof (translation)
Take `⟨U, hU, t, ht⟩` from `hs (g (IsLocalRing.closedPoint V))`. Establish `hU' : ⊤ ≤ g ⁻¹ᵁ U` using `(top_le_iff_cpt g U).2 hU`. Establish `hr : Set.range (pullback.fst G.hom g) ⊆ Set.range (G.hom ⁻¹ᵁ U).ι`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Use `show G.hom (pullback.fst G.hom g y) ∈ U`. Establish `e : G.hom (pullback.fst G.hom g y) = g (pullback.snd G.hom g y)`. Rewrite using `[← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]`. Rewrite using `[e]`. Conclude with `hU' trivial`.

Establish `hψ : IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι = pullback.fst G.hom g` using `IsOpenImmersion.lift_fac _ _ _`. Use `gen_chartPull (chartPullLinComb L (pullback.fst G.hom g) _ _ _ (IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr) fun k => ?_) t ht` and prove the remaining obligations. Use `fin_cases k`. Use `show (ι[(Over.pullback g).obj G]).left ≫ pullback.fst G.hom g = IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left`. Rewrite using `[← Category.assoc, hψ]`.

Conclude with `GlobalTheory.PolBaseChange.inv_comm (isGrpPullback_pullback G g)`. Use `show 𝟙 _ ≫ pullback.fst G.hom g = IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι`. Rewrite using `[hψ, Category.id_comp]`.
-/
theorem symGen_of_local {V : Type} [CommRing V] [IsLocalRing V] {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (L : LB G.left) (hs : Out.Sym G L) (g : Sp V ⟶ S) :
    ∃ t : LB.Gen (LB.LinComb (L.pull (pullback.fst G.hom g)) (K := Fin 2)
      ![(ι[(Over.pullback g).obj G]).left, 𝟙 ((Over.pullback g).obj G).left] ![1, -1]), t.IsGen := by
  obtain ⟨U, hU, t, ht⟩ := hs (g (IsLocalRing.closedPoint V))
  have hU' : ⊤ ≤ g ⁻¹ᵁ U := (top_le_iff_cpt g U).2 hU
  have hr : Set.range (pullback.fst G.hom g) ⊆ Set.range (G.hom ⁻¹ᵁ U).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show G.hom (pullback.fst G.hom g y) ∈ U
    have e : G.hom (pullback.fst G.hom g y) = g (pullback.snd G.hom g y) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [e]
    exact hU' trivial
  have hψ : IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι =
      pullback.fst G.hom g := IsOpenImmersion.lift_fac _ _ _
  refine gen_chartPull (chartPullLinComb L (pullback.fst G.hom g) _ _ _
    (IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr) fun k => ?_) t ht
  fin_cases k
  · show (ι[(Over.pullback g).obj G]).left ≫ pullback.fst G.hom g =
      IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left
    rw [← Category.assoc, hψ]
    exact GlobalTheory.PolBaseChange.inv_comm (isGrpPullback_pullback G g)
  · show 𝟙 _ ≫ pullback.fst G.hom g = IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι
    rw [hψ, Category.id_comp]

/- English proof (translation)
Introduce `S G _ _ L hG hL ha hR hS V _ _ _ g h`. Establish `hl` using `GlobalTheory.abelianSchemeLaws_all.1`. Establish `hp` using `isGrpPullback_pullback G g`. Establish `hLB : (L.pull (pullback.fst G.hom g)).IsLB` using `pull_isLB hL _`. Establish `hB : IsAbelianScheme ((Over.pullback g).obj G)` using `TLinPf.isAb_pullback g G hG`.

Use `hG.proper` as an intermediate fact. Establish `haB : Out.RelAmple ((Over.pullback g).obj G) (L.pull (pullback.fst G.hom g))` using `GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL ha (IsPullback.of_hasPullback G.hom g)`. Take `⟨d, -, n, s, hs⟩` from `(GlobalTheory.Unif.relAmple_iff_veryAmpleBy V ((Over.pullback g).obj G) _ hLB).1 haB`. Establish `hP : GlobalTheory.AbLaw.IsProjBy ((Over.pullback g).obj G).hom` using `⟨_, GlobalTheory.AbLaw.isLB_pw hLB _, n, s, hs⟩`. Take `⟨t, ht⟩` from `GlobalTheory.AbLaw.CubeProj.exists_gen_theta_of_isProjBy hl.globalFns V _ hB hP _ hLB`.

Take `⟨r, hr⟩` from `GlobalTheory.PolBaseChange.rigidified_pull hp hR`. Take `⟨u, hu⟩` from `symGen_of_local G L hS g`. Take `⟨M, hM⟩` from `GlobalTheory.AbPackage.exists_cp hl.globalFns hB ⟨L.pull (pullback.fst G.hom g), r, hLB, hr⟩ ⟨t, ht⟩ ⟨u, hu⟩`. Establish `hML : M.L.L = L.pull (pullback.fst G.hom g)` using `by rw [hM]`. Set `j` to `spMap (algebraMap V (FractionRing V))`.

Set `B` to `(Over.pullback g).obj G`. Establish `hq` using `isGrpPullback_pullback B j`. Establish `hA : IsAbelianScheme ((Over.pullback j).obj B)` using `TLinPf.isAb_pullback j B hB`. Use `hA.smooth` as an intermediate fact. Use `hA.geomConnected` as an intermediate fact.

Use `hB.proper` as an intermediate fact. Establish `: ConnectedSpace ((Over.pullback j).obj B).left` using `GeometricallyConnected.connectedSpace_of_subsingleton ((Over.pullback j).obj B).hom`. Take `⟨dim, hdim⟩` from `exists_dim_of_preconnected ((Over.pullback j).obj B).hom (eSec ((Over.pullback j).obj B) (IsLocalRing.closedPoint (FractionRing V)))`. Establish `hLA` using `pull_isLB hLB (pullback.fst B.hom j)`. Establish `hK : GlobalTheory.KTrivSpread.TrivAlong ((Over.pullback j).obj B) ((L.pull (pullback.fst G.hom g)).pull (pullback.fst B.hom j)) (𝟙 _)` using `GlobalTheory.KTrivSpread.TrivAlong.pull hq hLB ((GlobalTheory.KTrivSpread.TrivAlong.pull hp hL h).comp (𝟙 _))`.

Set `P : Out.PolAV (Sp (FractionRing V))` to `{ A := (Over.pullback j).obj B isAb := hA g := dim smoothDim := hdim L := (L.pull (pullback.fst G.hom g)).pull (pullback.fst B.hom j) isLB := hLA rigid := GlobalTheory.PolBaseChange.rigidified_pull hq ⟨r, hr⟩ sym := GlobalTheory.PolBaseChange.sym_pull hq (GlobalTheory.PolBaseChan …`. Establish `hw : LBIso P.L (M.L.L.pull (pullback.fst B.hom j))`. Rewrite using `[hML]`. Conclude with `GlobalTheory.PolBaseChange.lbIso_refl hLA`. Establish `hK' : Out.KTriv B M.L.L` using `GlobalTheory.KTrivSpread.kTriv_of_generic_fibre hl V (FractionRing V) P B M (pullback.fst B.hom j) hB hq hw (by rw [hML]; exact haB)`.

Rewrite `hK'` using `[hML]`. Conclude with `GlobalTheory.KTrivSpread.trivAlong_of_kTriv hp hL hK'`.
-/
theorem trivAlong_of_generic : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), IsAbelianScheme G → L.IsLB → Out.RelAmple G L → Out.Rigidified G L → Out.Sym G L → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (g : Sp V ⟶ S), GlobalTheory.KTrivSpread.TrivAlong G L (spMap (algebraMap V (FractionRing V)) ≫ g) → GlobalTheory.KTrivSpread.TrivAlong G L g := by
  intro S G _ _ L hG hL ha hR hS V _ _ _ g h
  have hl := GlobalTheory.abelianSchemeLaws_all.1
  have hp := isGrpPullback_pullback G g
  have hLB : (L.pull (pullback.fst G.hom g)).IsLB := pull_isLB hL _
  have hB : IsAbelianScheme ((Over.pullback g).obj G) := TLinPf.isAb_pullback g G hG
  have := hG.proper
  have haB : Out.RelAmple ((Over.pullback g).obj G) (L.pull (pullback.fst G.hom g)) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL ha (IsPullback.of_hasPullback G.hom g)
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V ((Over.pullback g).obj G) _ hLB).1 haB
  have hP : GlobalTheory.AbLaw.IsProjBy ((Over.pullback g).obj G).hom := ⟨_, GlobalTheory.AbLaw.isLB_pw hLB _, n, s, hs⟩
  obtain ⟨t, ht⟩ := GlobalTheory.AbLaw.CubeProj.exists_gen_theta_of_isProjBy hl.globalFns V _ hB hP _ hLB
  obtain ⟨r, hr⟩ := GlobalTheory.PolBaseChange.rigidified_pull hp hR
  obtain ⟨u, hu⟩ := symGen_of_local G L hS g
  obtain ⟨M, hM⟩ := GlobalTheory.AbPackage.exists_cp hl.globalFns hB ⟨L.pull (pullback.fst G.hom g), r, hLB, hr⟩
    ⟨t, ht⟩ ⟨u, hu⟩
  have hML : M.L.L = L.pull (pullback.fst G.hom g) := by rw [hM]
  let j := spMap (algebraMap V (FractionRing V))
  let B := (Over.pullback g).obj G
  have hq := isGrpPullback_pullback B j
  have hA : IsAbelianScheme ((Over.pullback j).obj B) := TLinPf.isAb_pullback j B hB
  have := hA.smooth
  have := hA.geomConnected
  have := hB.proper
  have : ConnectedSpace ((Over.pullback j).obj B).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton ((Over.pullback j).obj B).hom
  obtain ⟨dim, hdim⟩ := exists_dim_of_preconnected ((Over.pullback j).obj B).hom
    (eSec ((Over.pullback j).obj B) (IsLocalRing.closedPoint (FractionRing V)))
  have hLA := pull_isLB hLB (pullback.fst B.hom j)
  have hK : GlobalTheory.KTrivSpread.TrivAlong ((Over.pullback j).obj B)
      ((L.pull (pullback.fst G.hom g)).pull (pullback.fst B.hom j)) (𝟙 _) :=
    GlobalTheory.KTrivSpread.TrivAlong.pull hq hLB ((GlobalTheory.KTrivSpread.TrivAlong.pull hp hL h).comp (𝟙 _))
  let P : Out.PolAV (Sp (FractionRing V)) :=
    { A := (Over.pullback j).obj B
      isAb := hA
      g := dim
      smoothDim := hdim
      L := (L.pull (pullback.fst G.hom g)).pull (pullback.fst B.hom j)
      isLB := hLA
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hq ⟨r, hr⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hq (GlobalTheory.PolBaseChange.sym_pull hp hS)
      ample := GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hLB haB (IsPullback.of_hasPullback B.hom j)
      ktriv := kTriv_iff_forall.2 fun T x hx => hK T T.hom (Category.comp_id _) x hx }
  have hw : LBIso P.L (M.L.L.pull (pullback.fst B.hom j)) := by
    rw [hML]
    exact GlobalTheory.PolBaseChange.lbIso_refl hLA
  have hK' : Out.KTriv B M.L.L :=
    GlobalTheory.KTrivSpread.kTriv_of_generic_fibre hl V (FractionRing V) P B M (pullback.fst B.hom j) hB hq hw
      (by rw [hML]; exact haB)
  rw [hML] at hK'
  exact GlobalTheory.KTrivSpread.trivAlong_of_kTriv hp hL hK'

end GlobalTheory.KTrivDvrSpread
