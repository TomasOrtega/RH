import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnifPolarizationSquareIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationLineBundleUnifIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomExtDvrAndLaws
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordOfIsPullDegId
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TautologicalModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AdmissibleBasePowerSeries
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws5
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NatCastNeZeroOfIsUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigIsoOfIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.TwoUnifTors

set_option maxHeartbeats 1600000 in
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorRef in

/- English proof (translation)
Introduce `V _ _ _ _ hc A G G' _ _ _ _ hG hG' D D' U U'`. Establish `hCN : IsCN V` using `⟨inferInstance, inferInstance, hc, inferInstance⟩`. Establish `aV` using `admissibleBase_of_completeNormalLocalCharZero hCN`. Establish `hext` using `GlobalTheory.homExtDvr_and_laws.1`. Establish `m₁ : IsMonHom (U.gen.hom ≫ U'.gen.inv)` using `by haveI := U.gen_hom; haveI := U'.gen_hom; infer_instance`.

Establish `m₂ : IsMonHom (U'.gen.hom ≫ U.gen.inv)` using `by haveI := U.gen_hom; haveI := U'.gen_hom; infer_instance`. Take `⟨f, ⟨hfm, hfK⟩, -⟩` from `hext V G G' hG hG' (U.gen.hom ≫ U'.gen.inv) m₁`. Take `⟨g, ⟨hgm, hgK⟩, -⟩` from `hext V G' G hG' hG (U'.gen.hom ≫ U.gen.inv) m₂`. Establish `fg : f ≫ g = 𝟙 G`. Establish `u` using `hext V G G hG hG (𝟙 _) inferInstance`.

Use `u.unique ⟨inferInstance, ?_⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩` and prove the remaining obligations. Rewrite using `[Functor.map_comp, hfK, hgK]`. Simplify using the standard rewrite rules. Establish `gf : g ≫ f = 𝟙 G'`. Establish `u` using `hext V G' G' hG' hG' (𝟙 _) inferInstance`.

Use `u.unique ⟨inferInstance, ?_⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩` and prove the remaining obligations. Rewrite using `[Functor.map_comp, hfK, hgK]`. Simplify using the standard rewrite rules. Set `ψ : G ≅ G'` to `⟨f, g, fg, gf⟩`. Use `haveI : IsMonHom ψ.hom := hfm`.

Establish `hψK : (Over.pullback (jK V)).map ψ.hom ≫ U'.gen.hom = U.gen.hom`. Express the relevant statement in the definitionally equal form `(Over.pullback (jK V)).map f ≫ U'.gen.hom = U.gen.hom`. Rewrite using `[hfK]`. Simplify using the standard rewrite rules. Establish `hid : spMap (RingHom.id V) = 𝟙 (Sp V)` using `ReciprocityTheory.ChartRestriction.G.Geo.Tor.specOf_id V`.

Establish `hpb : IsGrpPullback G G' (spMap (RingHom.id V)) ψ.hom.left`. Rewrite using `[hid]`. Conclude with `isGrpPullback_of_iso ψ`. Take `⟨bc, mbc, hbc⟩` from `grpPullback_iso hpb (isGrpPullback_pullback G' (spMap (RingHom.id V)))`. Establish `he : eSec G ≫ bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V)) = spMap (RingHom.id V) ≫ eSec G'`.

Rewrite using `[hbc]`. Conclude with `GlobalTheory.PolBaseChange.eSec_comm hpb`. Set `L' : RigLB G` to `⟨U'.LG.L.pull (bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V))), rigPullOf (G' := G) (G := G') (bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V))) (spMap (RingHom.id V)) he U'.LG.L U'.LG.rig, pull_isLB U'.LG.isLB _, GlobalTheory.Proof.TautologicalModel.rigPullOf_i …`. Take `⟨wL, gL, rL⟩` from `GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap (RingHom.id V)) G' G _ he U'.LG L' (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U'.LG.isLB _))`. Establish `wA : LBIso (A.L.pull U.gen.hom.left) (U'.LG.L.pull (pullback.fst G.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V))))`.

Establish `k₁ : pullback.fst G.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V)) = ((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V)`. Rewrite using `[hbc]`. Conclude with `(pullback.lift_fst _ _ _).symm`. Establish `k₂ : U.gen.hom.left = ((Over.pullback (jK V)).map ψ.hom).left ≫ U'.gen.hom.left`. Rewrite using `[← Over.comp_left, hψK]`.

Rewrite using `[k₁, k₂]`. Establish `t₁ : LBIso (A.L.pull (((Over.pullback (jK V)).map ψ.hom).left ≫ U'.gen.hom.left)) ((A.L.pull U'.gen.hom.left).pull ((Over.pullback (jK V)).map ψ.hom).left)` using `LBIso.symm ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen A.isLB _ _⟩`. Establish `t₂ : LBIso ((A.L.pull U'.gen.hom.left).pull ((Over.pullback (jK V)).map ψ.hom).left) ((U'.LG.L.pull (pullback.fst G'.hom (jK V))).pull ((Over.pullback (jK V)).map ψ.hom).left)` using `GlobalTheory.RigidBundleGlue.LBIso.pull U'.ext _`. Establish `t₃ : LBIso ((U'.LG.L.pull (pullback.fst G'.hom (jK V))).pull ((Over.pullback (jK V)).map ψ.hom).left) (U'.LG.L.pull (((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V)))` using `⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen U'.LG.isLB _ _⟩`. Conclude with `(t₁.trans (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB (pull_isLB U'.LG.isLB _) _) t₂).trans (pull_isLB A.isLB _) (pull_isLB (pull_isLB U'.LG.isLB _) _) (pull_isLB U'.LG.isLB _) t₃`.

Take `⟨W, hW, hWψ⟩` from `GlobalTheory.psiOnExists V (maximalIdeal V) aV D'`. Establish `hWg : (specOf (RingHom.id V)).base (genericPoint (Spec (CommRingCat.of V))) ∈ W`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.specOf_id]`. Conclude with `hW`. Establish `hI : (maximalIdeal V).map (RingHom.id V) ≤ maximalIdeal V` using `by rw [Ideal.map_id]`.

Take `⟨D'', hD, U'', -, hgen, hPU⟩` from `GlobalTheory.UnifPullGuards.unifBaseChange_holds V V _ _ aV aV (RingHom.id V) hI D' A G' hG' U' W hWψ hWg G bc mbc A rfl U.gen U.gen_hom wA L' wL he gL rL`. Establish `h5 : Laws5` using `GlobalTheory.allSixLaws.2.2.2.2.1`. Establish `hUq : UnifUniqSt` using `GlobalTheory.allSixLaws.2.2.2.2.2.unifUniq`. Establish `hQ : QkPullExistsSt` using `qkPullExists GlobalTheory.allSixLaws.1.globalFns`. Establish `hLG : LBIso U''.LG.L U.LG.L`.

Use `GlobalTheory.FewAtTest.lbIso_of_generic hG U''.LG U.LG ?_` and prove the remaining obligations. Establish `e1` using `U''.ext`. Rewrite `e1` using `[hgen]`. Conclude with `LBIso.trans (pull_isLB U''.LG.isLB _) (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _) (LBIso.symm e1) U.ext`. Take `⟨wL₀, hwg₀, hwm₀⟩` from `GlobalTheory.RigLBIso.exists_rig_iso_of_iso _ G U''.LG U.LG hLG`.

Take `⟨hD₀, hlev₀, -⟩` from `hUq V (maximalIdeal V) aV D D'' A A G hG U U'' wL₀ hwg₀ hwm₀`. Establish `hpb₀ : IsGrpPullback G G (spMap (RingHom.id V)) (Iso.refl G).hom.left` using `by haveI : IsMonHom (Iso.refl G).hom := by show IsMonHom (𝟙 G); infer_instance`. Rewrite using `[hid]`. Conclude with `isGrpPullback_of_iso (Iso.refl G)`. Take `⟨bc₀, mbc₀, hbc₀⟩` from `grpPullback_iso hpb₀ (isGrpPullback_pullback G (spMap (RingHom.id V)))`.

Establish `hbc₀' : bc₀.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id V)) = 𝟙 _` using `hbc₀`. Establish `hPU₀ : IsPullUnif (RingHom.id V) hD₀ bc₀ U U''` using `isPullUnif_of_uniq U U'' hD₀ wL₀ hwg₀ hwm₀ hlev₀ bc₀ hbc₀'`. Establish `hbc' : bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V)) = ψ.hom.left` using `hbc`. Establish `k₁ : U.gen.inv ≫ (Over.pullback (jK V)).map ψ.hom = U'.gen.inv`. Rewrite using `[Iso.inv_comp_eq, ← hψK, Category.assoc, Iso.hom_inv_id, Category.comp_id]`.

Establish `k₂ : ((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V) = pullback.fst G.hom (jK V) ≫ ψ.hom.left` using `pullback.lift_fst _ _ _`. Use `⟨hD₀.xe.symm.trans hD.xe, fun y r r' hr hr' => ?_, ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `GlobalTheory.SameCoord.psiCoord_of_isPullDeg_id hD₀ (hD₀.xe.symm y) r (by rw [AddEquiv.apply_symm_apply]; exact hr)`. Take `⟨u', hu'⟩` from `GlobalTheory.SameCoord.psiCoord_of_isPullDeg_id hD (hD₀.xe.symm y) r' hr'`. Establish `h1 : Associated (u * r) (u' * r')` using `GlobalTheory.TorRef.psiCoord_associated hu hu'`.

Conclude with `((associated_unit_mul_left r u u.isUnit).symm.trans h1).trans (associated_unit_mul_left r' u' u'.isUnit)`. Introduce `K _ _ _ k q q' x hk hq hq'`. Take `⟨f, hf, -, hinj, -, -⟩` from `GlobalTheory.ZH.uTors_closed V hc A G D U K k hk`. Take `⟨f', hf', -, hinj', -, -⟩` from `GlobalTheory.ZH.uTors_closed V hc A G' D' U' K k hk`. Take `⟨f'', hf'', hsurj'', -, -, -⟩` from `GlobalTheory.ZH.uTors_closed V hc A G D'' U'' K k hk`.

Take `⟨w, hw⟩` from `U.ext`. Establish `hxk` using `(hq w hw).1`. Take `⟨q'', hq''⟩` from `hsurj'' x hxk`. Establish `hF : ∀ r : V, algebraMap (FractionRing V) K (algebraMap V (FractionRing V) r) = algebraMap (FractionRing V) K (algebraMap V (FractionRing V) ((RingHom.id V) r))` using `fun _ => rfl`. Take `⟨p, hp₁, hp₂⟩` from `hQ V V (RingHom.id V) D.toPre D''.toPre hD₀ K hF k q''`.

Establish `A₁ : QkToAkU U''.toUnifPre K k q'' (f p)` using `h5.qkBaseChange V V _ _ aV aV (RingHom.id V) D A G U G bc₀ mbc₀ A D'' hD₀ U'' hPU₀ K hF k hk p (f p) q'' (f p) hp₁ hp₂ (by rw [hbc₀', Category.comp_id, hgen]) ((hf p (f p)).2 rfl)`. Establish `hpx : f p = x` using `((hf'' q'' (f p)).1 A₁).trans hq''`. Take `⟨z, hz, -⟩` from `(hinj p q).1 (hpx.trans ((hf q x).1 hq))`. Take `⟨p', hp₁', hp₂'⟩` from `hQ V V (RingHom.id V) D'.toPre D''.toPre hD K hF k q''`. Establish `B₁ : QkToAkU U''.toUnifPre K k q'' (f' p')` using `h5.qkBaseChange V V _ _ aV aV (RingHom.id V) D' A G' U' G bc mbc A D'' hD U'' hPU K hF k hk p' (f' p') q'' (f' p') hp₁' hp₂' (by rw [hgen, hbc', ← k₂, ← k₁, Over.comp_left]; simp only [Category.assoc]) ((hf' p' (f' p')).2 rfl)`.

Establish `hpx' : f' p' = x` using `((hf'' q'' (f' p')).1 B₁).trans hq''`. Take `⟨z', hz', -⟩` from `(hinj' p' q').1 (hpx'.trans ((hf' q' x).1 hq'))`. Use `⟨z' - hD.xe (hD₀.xe.symm z), ?_⟩` and prove the remaining obligations. Use `show q'.y = hD.xe (hD₀.xe.symm q.y) + k • (z' - hD.xe (hD₀.xe.symm z))`. Rewrite using `[hz', hz]`.

Simplify using `only [map_add, map_nsmul]`. Rewrite using `[← hp₁, hp₁', AddEquiv.apply_symm_apply, smul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (A : PolAV (Sp (FractionRing V))) (G G' : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (D D' : DegData V (maximalIdeal V)) (U : Unif (maximalIdeal V) D A G) (U' : Unif (maximalIdeal V) D' A G'), ∃ ε : D.toPre.X ≃+ D'.toPre.X, (∀ y r r', PsiCoord D.toPre y r → PsiCoord D'.toPre (ε y) r' → Associated r r') ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (k : ℕ) (q : QkPt D.toPre K k) (q' : QkPt D'.toPre K k) (x : TFK (R := V) K ⟶ A.A), 1 ≤ k → QkToAkU U.toUnifPre K k q x → QkToAkU U'.toUnifPre K k q' x → CongMod k q'.y (ε q.y) := by
  intro V _ _ _ _ hc A G G' _ _ _ _ hG hG' D D' U U'
  have hCN : IsCN V := ⟨inferInstance, inferInstance, hc, inferInstance⟩
  have aV := admissibleBase_of_completeNormalLocalCharZero hCN

  have hext := GlobalTheory.homExtDvr_and_laws.1
  have m₁ : IsMonHom (U.gen.hom ≫ U'.gen.inv) := by
    haveI := U.gen_hom; haveI := U'.gen_hom; infer_instance
  have m₂ : IsMonHom (U'.gen.hom ≫ U.gen.inv) := by
    haveI := U.gen_hom; haveI := U'.gen_hom; infer_instance
  obtain ⟨f, ⟨hfm, hfK⟩, -⟩ := hext V G G' hG hG' (U.gen.hom ≫ U'.gen.inv) m₁
  obtain ⟨g, ⟨hgm, hgK⟩, -⟩ := hext V G' G hG' hG (U'.gen.hom ≫ U.gen.inv) m₂
  have fg : f ≫ g = 𝟙 G := by
    have u := hext V G G hG hG (𝟙 _) inferInstance
    refine u.unique ⟨inferInstance, ?_⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
    rw [Functor.map_comp, hfK, hgK]; simp
  have gf : g ≫ f = 𝟙 G' := by
    have u := hext V G' G' hG' hG' (𝟙 _) inferInstance
    refine u.unique ⟨inferInstance, ?_⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
    rw [Functor.map_comp, hfK, hgK]; simp
  let ψ : G ≅ G' := ⟨f, g, fg, gf⟩
  haveI : IsMonHom ψ.hom := hfm
  have hψK : (Over.pullback (jK V)).map ψ.hom ≫ U'.gen.hom = U.gen.hom := by
    change (Over.pullback (jK V)).map f ≫ U'.gen.hom = U.gen.hom
    rw [hfK]; simp

  have hid : spMap (RingHom.id V) = 𝟙 (Sp V) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.specOf_id V
  have hpb : IsGrpPullback G G' (spMap (RingHom.id V)) ψ.hom.left := by
    rw [hid]; exact isGrpPullback_of_iso ψ
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hpb (isGrpPullback_pullback G' (spMap (RingHom.id V)))
  have he : eSec G ≫ bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V)) =
      spMap (RingHom.id V) ≫ eSec G' := by
    rw [hbc]; exact GlobalTheory.PolBaseChange.eSec_comm hpb
  let L' : RigLB G := ⟨U'.LG.L.pull (bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V))),
    rigPullOf (G' := G) (G := G') (bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V))) (spMap (RingHom.id V))
      he U'.LG.L U'.LG.rig, pull_isLB U'.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G) (G := G') (bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V)))
      (spMap (RingHom.id V)) he U'.LG.L U'.LG.rig U'.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap (RingHom.id V)) G' G _ he U'.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U'.LG.isLB _))

  have wA : LBIso (A.L.pull U.gen.hom.left)
      (U'.LG.L.pull (pullback.fst G.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V)))) := by
    have k₁ : pullback.fst G.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V)) =
        ((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V) := by
      rw [hbc]; exact (pullback.lift_fst _ _ _).symm
    have k₂ : U.gen.hom.left = ((Over.pullback (jK V)).map ψ.hom).left ≫ U'.gen.hom.left := by
      rw [← Over.comp_left, hψK]
    rw [k₁, k₂]
    have t₁ : LBIso (A.L.pull (((Over.pullback (jK V)).map ψ.hom).left ≫ U'.gen.hom.left))
        ((A.L.pull U'.gen.hom.left).pull ((Over.pullback (jK V)).map ψ.hom).left) :=
      LBIso.symm ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen A.isLB _ _⟩
    have t₂ : LBIso ((A.L.pull U'.gen.hom.left).pull ((Over.pullback (jK V)).map ψ.hom).left)
        ((U'.LG.L.pull (pullback.fst G'.hom (jK V))).pull ((Over.pullback (jK V)).map ψ.hom).left) :=
      GlobalTheory.RigidBundleGlue.LBIso.pull U'.ext _
    have t₃ : LBIso ((U'.LG.L.pull (pullback.fst G'.hom (jK V))).pull ((Over.pullback (jK V)).map ψ.hom).left)
        (U'.LG.L.pull (((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V))) :=
      ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen U'.LG.isLB _ _⟩
    exact (t₁.trans (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _)
      (pull_isLB (pull_isLB U'.LG.isLB _) _) t₂).trans (pull_isLB A.isLB _)
      (pull_isLB (pull_isLB U'.LG.isLB _) _) (pull_isLB U'.LG.isLB _) t₃

  obtain ⟨W, hW, hWψ⟩ := GlobalTheory.psiOnExists V (maximalIdeal V) aV D'
  have hWg : (specOf (RingHom.id V)).base (genericPoint (Spec (CommRingCat.of V))) ∈ W := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.specOf_id]; exact hW
  have hI : (maximalIdeal V).map (RingHom.id V) ≤ maximalIdeal V := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', -, hgen, hPU⟩ := GlobalTheory.UnifPullGuards.unifBaseChange_holds V V _ _ aV aV (RingHom.id V) hI D' A G'
    hG' U' W hWψ hWg G bc mbc A rfl U.gen U.gen_hom wA L' wL he gL rL

  have h5 : Laws5 := GlobalTheory.allSixLaws.2.2.2.2.1
  have hUq : UnifUniqSt := GlobalTheory.allSixLaws.2.2.2.2.2.unifUniq
  have hQ : QkPullExistsSt := qkPullExists GlobalTheory.allSixLaws.1.globalFns

  have hLG : LBIso U''.LG.L U.LG.L := by
    refine GlobalTheory.FewAtTest.lbIso_of_generic hG U''.LG U.LG ?_
    have e1 := U''.ext
    rw [hgen] at e1
    exact LBIso.trans (pull_isLB U''.LG.isLB _) (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _) (LBIso.symm e1) U.ext
  obtain ⟨wL₀, hwg₀, hwm₀⟩ := GlobalTheory.RigLBIso.exists_rig_iso_of_iso _ G U''.LG U.LG hLG
  obtain ⟨hD₀, hlev₀, -⟩ := hUq V (maximalIdeal V) aV D D'' A A G hG U U'' wL₀ hwg₀ hwm₀
  have hpb₀ : IsGrpPullback G G (spMap (RingHom.id V)) (Iso.refl G).hom.left := by
    haveI : IsMonHom (Iso.refl G).hom := by show IsMonHom (𝟙 G); infer_instance
    rw [hid]; exact isGrpPullback_of_iso (Iso.refl G)
  obtain ⟨bc₀, mbc₀, hbc₀⟩ := grpPullback_iso hpb₀ (isGrpPullback_pullback G (spMap (RingHom.id V)))
  have hbc₀' : bc₀.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id V)) = 𝟙 _ := hbc₀
  have hPU₀ : IsPullUnif (RingHom.id V) hD₀ bc₀ U U'' :=
    isPullUnif_of_uniq U U'' hD₀ wL₀ hwg₀ hwm₀ hlev₀ bc₀ hbc₀'
  have hbc' : bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V)) = ψ.hom.left := hbc

  have k₁ : U.gen.inv ≫ (Over.pullback (jK V)).map ψ.hom = U'.gen.inv := by
    rw [Iso.inv_comp_eq, ← hψK, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have k₂ : ((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V) =
      pullback.fst G.hom (jK V) ≫ ψ.hom.left := pullback.lift_fst _ _ _
  refine ⟨hD₀.xe.symm.trans hD.xe, fun y r r' hr hr' => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := GlobalTheory.SameCoord.psiCoord_of_isPullDeg_id hD₀ (hD₀.xe.symm y) r
      (by rw [AddEquiv.apply_symm_apply]; exact hr)
    obtain ⟨u', hu'⟩ := GlobalTheory.SameCoord.psiCoord_of_isPullDeg_id hD (hD₀.xe.symm y) r' hr'
    have h1 : Associated (u * r) (u' * r') := GlobalTheory.TorRef.psiCoord_associated hu hu'
    exact ((associated_unit_mul_left r u u.isUnit).symm.trans h1).trans (associated_unit_mul_left r' u' u'.isUnit)
  · intro K _ _ _ k q q' x hk hq hq'
    obtain ⟨f, hf, -, hinj, -, -⟩ := GlobalTheory.ZH.uTors_closed V hc A G D U K k hk
    obtain ⟨f', hf', -, hinj', -, -⟩ := GlobalTheory.ZH.uTors_closed V hc A G' D' U' K k hk
    obtain ⟨f'', hf'', hsurj'', -, -, -⟩ := GlobalTheory.ZH.uTors_closed V hc A G D'' U'' K k hk
    obtain ⟨w, hw⟩ := U.ext
    have hxk := (hq w hw).1
    obtain ⟨q'', hq''⟩ := hsurj'' x hxk
    have hF : ∀ r : V, algebraMap (FractionRing V) K (algebraMap V (FractionRing V) r) =
        algebraMap (FractionRing V) K (algebraMap V (FractionRing V) ((RingHom.id V) r)) := fun _ => rfl

    obtain ⟨p, hp₁, hp₂⟩ := hQ V V (RingHom.id V) D.toPre D''.toPre hD₀ K hF k q''
    have A₁ : QkToAkU U''.toUnifPre K k q'' (f p) :=
      h5.qkBaseChange V V _ _ aV aV (RingHom.id V) D A G U G bc₀ mbc₀ A D'' hD₀ U'' hPU₀ K hF k hk p (f p) q''
        (f p) hp₁ hp₂ (by rw [hbc₀', Category.comp_id, hgen]) ((hf p (f p)).2 rfl)
    have hpx : f p = x := ((hf'' q'' (f p)).1 A₁).trans hq''
    obtain ⟨z, hz, -⟩ := (hinj p q).1 (hpx.trans ((hf q x).1 hq))

    obtain ⟨p', hp₁', hp₂'⟩ := hQ V V (RingHom.id V) D'.toPre D''.toPre hD K hF k q''
    have B₁ : QkToAkU U''.toUnifPre K k q'' (f' p') :=
      h5.qkBaseChange V V _ _ aV aV (RingHom.id V) D' A G' U' G bc mbc A D'' hD U'' hPU K hF k hk p' (f' p') q''
        (f' p') hp₁' hp₂' (by rw [hgen, hbc', ← k₂, ← k₁, Over.comp_left]; simp only [Category.assoc])
        ((hf' p' (f' p')).2 rfl)
    have hpx' : f' p' = x := ((hf'' q'' (f' p')).1 B₁).trans hq''
    obtain ⟨z', hz', -⟩ := (hinj' p' q').1 (hpx'.trans ((hf' q' x).1 hq'))
    refine ⟨z' - hD.xe (hD₀.xe.symm z), ?_⟩
    show q'.y = hD.xe (hD₀.xe.symm q.y) + k • (z' - hD.xe (hD₀.xe.symm z))
    rw [hz', hz]
    simp only [map_add, map_nsmul]
    rw [← hp₁, hp₁', AddEquiv.apply_symm_apply, smul_sub]
    abel

end GlobalTheory.TwoUnifTors
