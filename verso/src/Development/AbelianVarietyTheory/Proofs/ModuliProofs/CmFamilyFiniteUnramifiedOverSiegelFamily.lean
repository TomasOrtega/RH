import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelDataPullbackOfLevelMapStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivOmegaStd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverIffLocallyOfFiniteTypeAndExistsIsAmpl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsLocalizationOfLeClosure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfApplyEqGenericPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjectOfGenericFibreDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfIsProperOfLbIsoLam
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Direct
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Rigidity
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvrStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FamSiegel

/- English proof (translation)
Introduce `hL E _ _ _ H k _ T Y t A _ P y θ θ₂ x t' ν hp hP hθ hsq hiso hx`. Take `⟨φ, hφ₁, hφ₂⟩ : ∃ φ : t'.G.left ⟶ t.G.left, φ ≫ θ = ν.φ ≫ θ ∧ φ ≫ t.G.hom = t'.G.hom ≫ constPt x` from `⟨hθ.1.lift (ν.φ ≫ θ) (t'.G.hom ≫ constPt x) (by`. Rewrite using `[Category.assoc, hθ.1.w, ← Category.assoc, ν.cart.1.w, Category.assoc, hx, Category.assoc]),`. Use the proof step `hθ.1.lift_fst _ _ _, hθ.1.lift_snd _ _ _⟩`. Establish `hφ : IsGrpPullback t'.G t.G (constPt x) φ` using `hθ.cancel (by rw [hφ₁, ← hx]; exact ν.cart.comp hθ) hφ₂`.

Take `⟨φ₂, hφs⟩` from `(GlobalTheory.LamPull.lam_pull E H _ _ t t' (constPt x)).1 φ hφ₂`. Take `⟨ν₂, hνs⟩` from `(GlobalTheory.LamPull.lam_pull E H _ _ t t' x).1 ν.φ ν.cart.1.w`. Establish `hν` using `(GlobalTheory.LamPull.lam_pull E H _ _ t t' x).2 ν ν₂ hνs`. Establish `e : φ₂ ≫ θ₂ = ν₂ ≫ θ₂`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(φ₂ ≫ θ₂) ≫ (fst A A).left = (ν₂ ≫ θ₂) ≫ (fst A A).left`. Rewrite using `[Category.assoc, Category.assoc, hsq.1, ← Category.assoc, ← Category.assoc, hφs.1, hνs.1, Category.assoc, Category.assoc, hφ₁]`. Express the relevant statement in the definitionally equal form `(φ₂ ≫ θ₂) ≫ (snd A A).left = (ν₂ ≫ θ₂) ≫ (snd A A).left`. Rewrite using `[Category.assoc, Category.assoc, hsq.2, ← Category.assoc, ← Category.assoc, hφs.2, hνs.2, Category.assoc, Category.assoc, hφ₁]`. Establish `l : (abelian₂ t.G t.PP.L).IsLB` using `LB.isLB_linComb t.PP.isLB _ _`.

Establish `l' : (abelian₂ t'.G t'.PP.L).IsLB` using `LB.isLB_linComb t'.PP.isLB _ _`. Establish `key : ∀ a : (G2 t'.G).left ⟶ (G2 t.G).left, LBIso ((abelian₂ t.G t.PP.L).pull a) (P.pull (a ≫ θ₂))` using `fun a => (SiegelPullComp.iso_pull a hiso).trans (pull_isLB l _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (SiegelPullComp.iso_pull_pull hP θ₂ a)`. Establish `hlam : LBIso (abelian₂ t'.G t'.PP.L) ((abelian₂ t.G t.PP.L).pull φ₂)` using `(hν.trans l' (pull_isLB l _) (pull_isLB hP _) (key ν₂)).trans l' (pull_isLB hP _) (pull_isLB l _) (e ▸ (key φ₂).symm)`. Establish `hc : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ constPt x = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x`. Rewrite using `[constPt, ← Category.assoc]`.

Conclude with `(congrArg (· ≫ _) (TangentCrit.dualPt_dualBase k)).trans (Category.id_comp _)`. Take `⟨m, hm⟩` from `GlobalTheory.exists_sabMap_of_isProper_of_lbIso_lam hL E H _ _ t t' (constPt x) φ φ₂ hp hφ hφs hlam (GlobalTheory.EpsAct.main hL E H k T t x t' ν φ hp hφ fun Z j c hj => hθ.1.hom_ext (by rw [Category.assoc, Category.assoc, hφ₁]) (by rw [Category.assoc, Category.assoc, hφ₂, ν.cart …`. Conclude with `⟨m, by rw [hm, hφ₁]⟩`.
-/
theorem exists_sabMap_constPt : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] (T Y : Scheme.{0}) (t : SAB H T) (A : Over Y) (_ : GrpObj A) (P : LB (G2 A).left) (y : T ⟶ Y) (θ : t.G.left ⟶ A.left) (θ₂ : (G2 t.G).left ⟶ (G2 A).left) (x : Sp (DualNumber k) ⟶ T) (t' : SAB H (Sp (DualNumber k))) (ν : SABMap t' t x), IsProper t.G.hom → P.IsLB → IsGrpPullback t.G A y θ → IsSquare θ θ₂ → LBIso (abelian₂ t.G t.PP.L) (P.pull θ₂) → x ≫ y = constPt x ≫ y → ∃ ν' : SABMap t' t (constPt x), ν'.φ ≫ θ = ν.φ ≫ θ := by
  intro hL E _ _ _ H k _ T Y t A _ P y θ θ₂ x t' ν hp hP hθ hsq hiso hx
  obtain ⟨φ, hφ₁, hφ₂⟩ : ∃ φ : t'.G.left ⟶ t.G.left, φ ≫ θ = ν.φ ≫ θ ∧ φ ≫ t.G.hom = t'.G.hom ≫ constPt x :=
    ⟨hθ.1.lift (ν.φ ≫ θ) (t'.G.hom ≫ constPt x) (by
      rw [Category.assoc, hθ.1.w, ← Category.assoc, ν.cart.1.w, Category.assoc, hx, Category.assoc]),
      hθ.1.lift_fst _ _ _, hθ.1.lift_snd _ _ _⟩
  have hφ : IsGrpPullback t'.G t.G (constPt x) φ :=
    hθ.cancel (by rw [hφ₁, ← hx]; exact ν.cart.comp hθ) hφ₂
  obtain ⟨φ₂, hφs⟩ := (GlobalTheory.LamPull.lam_pull E H _ _ t t' (constPt x)).1 φ hφ₂
  obtain ⟨ν₂, hνs⟩ := (GlobalTheory.LamPull.lam_pull E H _ _ t t' x).1 ν.φ ν.cart.1.w
  have hν := (GlobalTheory.LamPull.lam_pull E H _ _ t t' x).2 ν ν₂ hνs
  have e : φ₂ ≫ θ₂ = ν₂ ≫ θ₂ := by
    apply pullback.hom_ext
    · change (φ₂ ≫ θ₂) ≫ (fst A A).left = (ν₂ ≫ θ₂) ≫ (fst A A).left
      rw [Category.assoc, Category.assoc, hsq.1, ← Category.assoc, ← Category.assoc, hφs.1, hνs.1, Category.assoc,
        Category.assoc, hφ₁]
    · change (φ₂ ≫ θ₂) ≫ (snd A A).left = (ν₂ ≫ θ₂) ≫ (snd A A).left
      rw [Category.assoc, Category.assoc, hsq.2, ← Category.assoc, ← Category.assoc, hφs.2, hνs.2, Category.assoc,
        Category.assoc, hφ₁]
  have l : (abelian₂ t.G t.PP.L).IsLB := LB.isLB_linComb t.PP.isLB _ _
  have l' : (abelian₂ t'.G t'.PP.L).IsLB := LB.isLB_linComb t'.PP.isLB _ _
  have key : ∀ a : (G2 t'.G).left ⟶ (G2 t.G).left, LBIso ((abelian₂ t.G t.PP.L).pull a) (P.pull (a ≫ θ₂)) := fun a =>
    (SiegelPullComp.iso_pull a hiso).trans (pull_isLB l _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _)
      (SiegelPullComp.iso_pull_pull hP θ₂ a)
  have hlam : LBIso (abelian₂ t'.G t'.PP.L) ((abelian₂ t.G t.PP.L).pull φ₂) :=
    (hν.trans l' (pull_isLB l _) (pull_isLB hP _) (key ν₂)).trans l' (pull_isLB hP _) (pull_isLB l _)
      (e ▸ (key φ₂).symm)
  have hc : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ constPt x =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x := by
    rw [constPt, ← Category.assoc]
    exact (congrArg (· ≫ _) (TangentCrit.dualPt_dualBase k)).trans (Category.id_comp _)
  obtain ⟨m, hm⟩ := GlobalTheory.exists_sabMap_of_isProper_of_lbIso_lam hL E H _ _ t t' (constPt x) φ φ₂ hp hφ hφs hlam
    (GlobalTheory.EpsAct.main hL E H k T t x t' ν φ hp hφ fun Z j c hj => hθ.1.hom_ext
      (by rw [Category.assoc, Category.assoc, hφ₁])
      (by rw [Category.assoc, Category.assoc, hφ₂, ν.cart.1.w, ← Category.assoc, ← Category.assoc, hj, Category.assoc,
        Category.assoc, hc]))
  exact ⟨m, by rw [hm, hφ₁]⟩

/- English proof (translation)
Introduce `hX hL hL₂ E _ _ _ H D n N MM sM tM lev g B _ ζ Y sY c bas V K _ _ _ _ _ _ sV y x tK ν lvK θ hN F hfl hx hlv hθ hl`. Establish `hK` using `(GlobalTheory.fullObj_pull E H D n N _ _ sM tM lev x).2 tK ν lvK hlv F.obj`. Rewrite `hK` using `[hx]`. Establish `hA` using `isGrpPullback_pullback c.A y`. Use `c.ab.smooth` as an intermediate fact.

Use `c.ab.proper` as an intermediate fact. Use `c.ab.geomConnected` as an intermediate fact. Establish `hab : IsAbelianScheme ((Over.pullback y).obj c.A)` using `⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) hA.1 ‹_›, MorphismProperty.of_isPullback (P := @IsProper) hA.1 ‹_›, MorphismProperty.of_isPullback (P := @GeometricallyConnected) hA.1 ‹_›⟩`. Take `⟨φ, hφ₁, hφ₂⟩ : ∃ φ : tK.G.left ⟶ ((Over.pullback y).obj c.A).left, φ ≫ pullback.fst _ _ = θ ∧ φ ≫ ((Over.pullback y).obj c.A).hom = tK.G.hom ≫ spMap (algebraMap V K)` from `⟨hA.1.lift θ _ (hθ.1.w.trans (Category.assoc _ _ _).symm), hA.1.lift_fst _ _ _, hA.1.lift_snd _ _ _⟩`. Take `⟨t, m, e, he, hmon, hamp, hkt⟩` from `GlobalTheory.T.exists_principallyPolarizedCM_extension_dvr hX hL hL₂ E H V K _ tK φ hab (hA.cancel (by rw [hφ₁]; exact hθ) hφ₂) hK.ample hK.ktriv`.

Establish `hψ : IsGrpPullback t.G c.A y (e.hom.left ≫ pullback.fst _ _)` using `((isGrpPullback_of_iso e).comp hA).congr (Category.id_comp _) rfl`. Establish `hθ' : m.φ ≫ e.hom.left ≫ pullback.fst _ _ = θ` using `by rw [← Category.assoc, he, hφ₁]`. Generalize the expression as in `e.hom.left ≫ pullback.fst c.A.hom y = ψ at hψ hθ'`. Establish `hex : ∀ a : D.La, ∃ s : 𝟙_ (Over (Sp V)) ⟶ t.G, s.left ≫ ψ = y ≫ (c.lev (bas.symm a)).left` using `fun a => ⟨Over.homMk (hψ.1.lift (y ≫ (c.lev (bas.symm a)).left) (𝟙 _) (by`. Rewrite using `[Category.assoc, Over.w]`.

Conclude with `(Category.comp_id _).trans (Category.id_comp _).symm))`. Use the proof step `(hψ.1.lift_snd _ _ _), hψ.1.lift_fst _ _ _⟩`. Use `choose lv hlv' using hex`. Set `U : Over.mk ((𝟙_ (Over (Sp V))).hom ≫ y) ⟶ 𝟙_ (Over Y)` to `toUnit _`. Establish `hU : U.left = y` using `(Category.comp_id _).symm.trans ((Over.w U).trans (Category.id_comp _))`.

Establish `hpush : ∀ a, pushHom hψ _ (lv a) = U ≫ c.lev (bas.symm a)` using `fun a => Over.OverMorphism.ext ((hlv' a).trans (by rw [Over.comp_left, hU]))`. Establish `hinj : Function.Injective (pushHom hψ (𝟙_ (Over (Sp V))))` using `fun a b h => Over.OverMorphism.ext (hψ.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))`. Establish `hadd : ∀ a b, lv (a + b) = lv a * lv b` using `fun a b => hinj (by`. Rewrite using `[map_mul, hpush, hpush, hpush, map_add, c.lev_add, MonObj.comp_mul])`. Establish `hker : ∀ a, lv (N • a) = 1` using `fun a => by`.

Establish `h0 : lv 0 = 1` using `by simpa using hadd 0 0`. Establish `hk : ∀ k : ℕ, lv (k • a) = lv a ^ k` using `fun k => by`. Proceed by induction on `k with`. Consider the case `zero => simpa using h0`. Consider the case `succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[hk, map_pow, map_one, hpush, ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one]`. Establish `hm : ∀ a, (lvK a).left ≫ m.φ = spMap (algebraMap V K) ≫ (lv a).left` using `fun a => ObjComp.sec_cancel hψ.1 m.cart.1.w (Over.w (lv a)) (Over.w (lvK a)) (hlv' a) (by`. Rewrite using `[hθ']`. Simplify using `using hl (bas.symm a))`.

Establish `hV` using `GlobalTheory.FullSpread.fullObj_of_genericFibre hL hL₂ E H D n N V K sV t lv tK m lvK hN (MorphismProperty.of_isPullback (P := @IsProper) hψ.1 ‹_›) hamp hkt hadd hker hm hK`. Take `⟨x', ⟨hx', m', hm'⟩, -⟩` from `F.rep _ sV t lv inferInstance inferInstance hfl hV`. Establish `: Flat (spMap (algebraMap V K))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors V))`.

Take `⟨m'', hm''⟩` from `ObjMaps.exists_sab_comp m' m`. Use `⟨x', (F.rep _ _ tK lvK inferInstance inferInstance inferInstance hK).unique ⟨by rw [Category.assoc, hx'], m'', fun a => ?_⟩ ⟨hx, ν, hlv⟩, hx'⟩` and prove the remaining obligations. Rewrite using `[hm'']`. Conclude with `ObjComp.sec_comp (hm' a) (hm a)`.
-/
theorem exists_extension : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (g : ℕ) (B : Type) [CommRing B] (ζ : B) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (c : SiegPre g N ζ sY) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (sV : Sp V ⟶ Sp (RZ H n N)) (y : Sp V ⟶ Y) (x : Sp K ⟶ MM) (tK : SAB H (Sp K)) (ν : SABMap tK tM x) (lvK : D.La → (𝟙_ (Over (Sp K)) ⟶ tK.G)) (θ : tK.G.left ⟶ c.A.left), 0 < N → FamCore D sM tM lev → Flat sV → x ≫ sM = spMap (algebraMap V K) ≫ sV → (∀ a, (lvK a).left ≫ ν.φ = x ≫ (lev a).left) → IsGrpPullback tK.G c.A (spMap (algebraMap V K) ≫ y) θ → (∀ u, (lvK (bas u)).left ≫ θ = (spMap (algebraMap V K) ≫ y) ≫ (c.lev u).left) → ∃ x' : Sp V ⟶ MM, spMap (algebraMap V K) ≫ x' = x ∧ x' ≫ sM = sV := by
  intro hX hL hL₂ E _ _ _ H D n N MM sM tM lev g B _ ζ Y sY c bas V K _ _ _ _ _ _ sV y x tK ν lvK θ hN F hfl hx hlv hθ hl
  have hK := (GlobalTheory.fullObj_pull E H D n N _ _ sM tM lev x).2 tK ν lvK hlv F.obj
  rw [hx] at hK
  have hA := isGrpPullback_pullback c.A y
  have := c.ab.smooth
  have := c.ab.proper
  have := c.ab.geomConnected
  have hab : IsAbelianScheme ((Over.pullback y).obj c.A) :=
    ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) hA.1 ‹_›,
      MorphismProperty.of_isPullback (P := @IsProper) hA.1 ‹_›,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hA.1 ‹_›⟩
  obtain ⟨φ, hφ₁, hφ₂⟩ : ∃ φ : tK.G.left ⟶ ((Over.pullback y).obj c.A).left, φ ≫ pullback.fst _ _ = θ ∧
      φ ≫ ((Over.pullback y).obj c.A).hom = tK.G.hom ≫ spMap (algebraMap V K) :=
    ⟨hA.1.lift θ _ (hθ.1.w.trans (Category.assoc _ _ _).symm), hA.1.lift_fst _ _ _, hA.1.lift_snd _ _ _⟩
  obtain ⟨t, m, e, he, hmon, hamp, hkt⟩ := GlobalTheory.T.exists_principallyPolarizedCM_extension_dvr hX hL hL₂ E H V K _ tK φ hab
    (hA.cancel (by rw [hφ₁]; exact hθ) hφ₂) hK.ample hK.ktriv
  have hψ : IsGrpPullback t.G c.A y (e.hom.left ≫ pullback.fst _ _) :=
    ((isGrpPullback_of_iso e).comp hA).congr (Category.id_comp _) rfl
  have hθ' : m.φ ≫ e.hom.left ≫ pullback.fst _ _ = θ := by rw [← Category.assoc, he, hφ₁]
  generalize e.hom.left ≫ pullback.fst c.A.hom y = ψ at hψ hθ'
  have hex : ∀ a : D.La, ∃ s : 𝟙_ (Over (Sp V)) ⟶ t.G, s.left ≫ ψ = y ≫ (c.lev (bas.symm a)).left := fun a =>
    ⟨Over.homMk (hψ.1.lift (y ≫ (c.lev (bas.symm a)).left) (𝟙 _) (by
      rw [Category.assoc, Over.w]; exact (Category.comp_id _).trans (Category.id_comp _).symm))
      (hψ.1.lift_snd _ _ _), hψ.1.lift_fst _ _ _⟩
  choose lv hlv' using hex
  let U : Over.mk ((𝟙_ (Over (Sp V))).hom ≫ y) ⟶ 𝟙_ (Over Y) := toUnit _
  have hU : U.left = y := (Category.comp_id _).symm.trans ((Over.w U).trans (Category.id_comp _))
  have hpush : ∀ a, pushHom hψ _ (lv a) = U ≫ c.lev (bas.symm a) := fun a =>
    Over.OverMorphism.ext ((hlv' a).trans (by rw [Over.comp_left, hU]))
  have hinj : Function.Injective (pushHom hψ (𝟙_ (Over (Sp V)))) := fun a b h =>
    Over.OverMorphism.ext (hψ.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  have hadd : ∀ a b, lv (a + b) = lv a * lv b := fun a b => hinj (by
    rw [map_mul, hpush, hpush, hpush, map_add, c.lev_add, MonObj.comp_mul])
  have hker : ∀ a, lv (N • a) = 1 := fun a => by
    have h0 : lv 0 = 1 := by simpa using hadd 0 0
    have hk : ∀ k : ℕ, lv (k • a) = lv a ^ k := fun k => by
      induction k with
      | zero => simpa using h0
      | succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]
    apply hinj
    rw [hk, map_pow, map_one, hpush, ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one]
  have hm : ∀ a, (lvK a).left ≫ m.φ = spMap (algebraMap V K) ≫ (lv a).left := fun a =>
    ObjComp.sec_cancel hψ.1 m.cart.1.w (Over.w (lv a)) (Over.w (lvK a)) (hlv' a) (by
      rw [hθ']; simpa using hl (bas.symm a))
  have hV := GlobalTheory.FullSpread.fullObj_of_genericFibre hL hL₂ E H D n N V K sV t lv tK m lvK hN
    (MorphismProperty.of_isPullback (P := @IsProper) hψ.1 ‹_›) hamp hkt hadd hker hm hK
  obtain ⟨x', ⟨hx', m', hm'⟩, -⟩ := F.rep _ sV t lv inferInstance inferInstance hfl hV
  have : Flat (spMap (algebraMap V K)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors V))
  obtain ⟨m'', hm''⟩ := ObjMaps.exists_sab_comp m' m
  refine ⟨x', (F.rep _ _ tK lvK inferInstance inferInstance inferInstance hK).unique
    ⟨by rw [Category.assoc, hx'], m'', fun a => ?_⟩ ⟨hx, ν, hlv⟩, hx'⟩
  rw [hm'']
  exact ObjComp.sec_comp (hm' a) (hm a)

end GlobalTheory.FamSiegel

namespace GlobalTheory.FamSiegel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

/- English proof (translation)
Take `⟨N, i, hi, -, hs⟩` from `h`. Use `isProper_str R N` as an intermediate fact. Rewrite using `[← hs]`. Use `infer_instance`.
-/
theorem locallyOfFiniteType_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (h : IsQProjOver s) :
    LocallyOfFiniteType s := by
  obtain ⟨N, i, hi, -, hs⟩ := h
  have := isProper_str R N
  rw [← hs]
  infer_instance

/- English proof (translation)
Take `⟨N, i, hi, -, hs⟩` from `h`. Use `isProper_str R N` as an intermediate fact. Rewrite using `[← hs]`. Use `infer_instance`.
-/
theorem isSeparated_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (h : IsQProjOver s) :
    IsSeparated s := by
  obtain ⟨N, i, hi, -, hs⟩ := h
  have := isProper_str R N
  rw [← hs]
  infer_instance

/- English proof (translation)
Establish `: ∀ x : X, _root_.IsReduced (X.presheaf.stalk x)` using `fun x => by`. Establish `hs : Function.Surjective (f.stalkMap x).hom` using `f.stalkMap_surjective x`. Establish `hi : Function.Injective (f.stalkMap x).hom`. Establish `hf` using `Flat.stalkMap f x`. Use `algebraize [(f.stalkMap x).hom]`.

Establish `: IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x))` using `inferInstanceAs (IsLocalHom (f.stalkMap x).hom)`. Use `Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)` as an intermediate fact. Conclude with `FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)`. Conclude with `isReduced_of_injective (RingEquiv.ofBijective _ ⟨hi, hs⟩).symm (RingEquiv.injective _)`. Conclude with `isReduced_of_isReduced_stalk X`.
-/
theorem isReduced_of_flat_preimmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] [IsPreimmersion f] [IsReduced Y] :
    IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have hs : Function.Surjective (f.stalkMap x).hom := f.stalkMap_surjective x
    have hi : Function.Injective (f.stalkMap x).hom := by
      have hf := Flat.stalkMap f x
      algebraize [(f.stalkMap x).hom]
      have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
        inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
      have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
      exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
    exact isReduced_of_injective (RingEquiv.ofBijective _ ⟨hi, hs⟩).symm (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk X

variable {MM : Scheme.{0}} {sM : MM ⟶ Sp (RZ H n N)} {tM : SAB H MM} {lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)}
  {g p : ℕ} {Ag : SiegelFamily g p N} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La}
  {O : Type} [CommRing O] {b : RZ H n N →+* O} {z : ZP p N →+* O}

/- English proof (translation)
Take `⟨θ, θ₂, hθ, hsq, hiso, hl⟩` from `GlobalTheory.SiegelDirect.direct E H D O _ _ t lv g p N Ag z bas w hw`. Establish `hs : w ≫ pullback.snd _ _ = pullback.snd sM (spMap b)`. Take `⟨_, _, _, -, -, -, -, h, -⟩` from `hw`. Conclude with `h`. Establish `hp : IsProper t.G.hom` using `MorphismProperty.of_isPullback (P := @IsProper) ν.cart.1 F.obj.proper`.

Use `TangentCrit.formallyUnramified_of_tangent w fun k _ _ x hx => ?_` and prove the remaining obligations. Establish `hx' : x ≫ w = constPt x ≫ w` using `hx.trans (by simp only [constPt, Category.assoc])`. Establish `hy : x ≫ w ≫ pullback.fst _ _ = constPt x ≫ w ≫ pullback.fst _ _`. Rewrite using `[← Category.assoc, hx', Category.assoc]`. Establish `h₂ : x ≫ pullback.snd sM (spMap b) = constPt x ≫ pullback.snd sM (spMap b)`.

Rewrite using `[← hs, ← Category.assoc, hx', Category.assoc]`. Take `⟨t', κ, lv', hlv'⟩` from `(GlobalTheory.fullObj_pull E H D n N _ _ (pullback.fst _ _ ≫ sM) t lv x).1`. Take `⟨κ', hκ'⟩` from `exists_sabMap_constPt hL E H k _ _ t Ag.univ.A inferInstance Ag.univ.P _ θ θ₂ x t' κ hp Ag.univ.isLB hθ hsq hiso hy`. Establish `hlv'' : ∀ a, (lv' a).left ≫ κ'.φ = constPt x ≫ (lv a).left` using `fun a => by`. Take `⟨u, rfl⟩` from `bas.surjective a`.

Use `ObjComp.sec_cancel hθ.1 κ'.cart.1.w (Over.w (lv (bas u))) (Over.w (lv' (bas u))) (hl u) ?_` and prove the remaining obligations. Rewrite using `[hκ', ← hy]`. Conclude with `ObjComp.sec_comp (hl u) (hlv' (bas u))`. Take `⟨m, hm⟩` from `ObjMaps.exists_sab_comp ν κ`. Establish `e' : constPt x ≫ pullback.fst sM (spMap b) = constPt (x ≫ pullback.fst _ _)`.

Simplify using `only [constPt, Category.assoc]`. Choose the witnesses or unpack the hypotheses as in `⟨m', hm'⟩ : ∃ m' : SABMap t' tM (constPt (x ≫ pullback.fst _ _)), m'.φ = κ'.φ ≫ ν.φ := by`. Rewrite using `[← e']`. Conclude with `ObjMaps.exists_sab_comp ν κ'`. Use `pullback.hom_ext ?_ h₂` and prove the remaining obligations.

Use `(F.unram k _ t' lv' m m' ?_ (fun a => ?_) fun a => ?_).trans e'.symm` and prove the remaining obligations. Rewrite using `[← e', Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, h₂, Category.assoc]`. Rewrite using `[hm]`. Conclude with `ObjComp.sec_comp (hlv a) (hlv' a)`. Rewrite using `[hm', ← e']`.

Conclude with `ObjComp.sec_comp (hlv a) (hlv'' a)`.
-/
theorem unramified (hL : Out.Laws) (F : FamCore D sM tM lev) {t : SAB H (pullback sM (spMap b))}
    (ν : SABMap t tM (pullback.fst _ _)) {lv : D.La → (𝟙_ (Over (pullback sM (spMap b))) ⟶ t.G)}
    (hlv : ∀ a, (lv a).left ≫ ν.φ = pullback.fst _ _ ≫ (lev a).left)
    {w : pullback sM (spMap b) ⟶ pullback Ag.s (spMap z)} [LocallyOfFiniteType w]
    (hw : SiegData (pullback.snd _ _) t lv Ag z bas w) : FormallyUnramified w := by
  obtain ⟨θ, θ₂, hθ, hsq, hiso, hl⟩ := GlobalTheory.SiegelDirect.direct E H D O _ _ t lv g p N Ag z bas w hw
  have hs : w ≫ pullback.snd _ _ = pullback.snd sM (spMap b) := by
    obtain ⟨_, _, _, -, -, -, -, h, -⟩ := hw
    exact h
  have hp : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) ν.cart.1 F.obj.proper
  refine TangentCrit.formallyUnramified_of_tangent w fun k _ _ x hx => ?_
  have hx' : x ≫ w = constPt x ≫ w := hx.trans (by simp only [constPt, Category.assoc])
  have hy : x ≫ w ≫ pullback.fst _ _ = constPt x ≫ w ≫ pullback.fst _ _ := by
    rw [← Category.assoc, hx', Category.assoc]
  have h₂ : x ≫ pullback.snd sM (spMap b) = constPt x ≫ pullback.snd sM (spMap b) := by
    rw [← hs, ← Category.assoc, hx', Category.assoc]
  obtain ⟨t', κ, lv', hlv'⟩ := (GlobalTheory.fullObj_pull E H D n N _ _ (pullback.fst _ _ ≫ sM) t lv x).1
  obtain ⟨κ', hκ'⟩ := exists_sabMap_constPt hL E H k _ _ t Ag.univ.A inferInstance Ag.univ.P _ θ θ₂ x t' κ hp Ag.univ.isLB hθ hsq
    hiso hy
  have hlv'' : ∀ a, (lv' a).left ≫ κ'.φ = constPt x ≫ (lv a).left := fun a => by
    obtain ⟨u, rfl⟩ := bas.surjective a
    refine ObjComp.sec_cancel hθ.1 κ'.cart.1.w (Over.w (lv (bas u))) (Over.w (lv' (bas u))) (hl u) ?_
    rw [hκ', ← hy]
    exact ObjComp.sec_comp (hl u) (hlv' (bas u))
  obtain ⟨m, hm⟩ := ObjMaps.exists_sab_comp ν κ
  have e' : constPt x ≫ pullback.fst sM (spMap b) = constPt (x ≫ pullback.fst _ _) := by
    simp only [constPt, Category.assoc]
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t' tM (constPt (x ≫ pullback.fst _ _)), m'.φ = κ'.φ ≫ ν.φ := by
    rw [← e']; exact ObjMaps.exists_sab_comp ν κ'
  refine pullback.hom_ext ?_ h₂
  refine (F.unram k _ t' lv' m m' ?_ (fun a => ?_) fun a => ?_).trans e'.symm
  · rw [← e', Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, h₂, Category.assoc]
  · rw [hm]; exact ObjComp.sec_comp (hlv a) (hlv' a)
  · rw [hm', ← e']; exact ObjComp.sec_comp (hlv a) (hlv'' a)

/- English proof (translation)
Take `⟨θ, θ₂, hθ, -, -, hl⟩` from `GlobalTheory.SiegelDirect.direct E H D O _ _ t lv g p N Ag z bas w hw`. Establish `hs : w ≫ pullback.snd _ _ = pullback.snd sM (spMap b)`. Take `⟨_, _, _, -, -, -, -, h, -⟩` from `hw`. Conclude with `h`. Use `isSeparated_of_qproj hq` as an intermediate fact.

Use `locallyOfFiniteType_of_qproj hq` as an intermediate fact. Use `F.flat` as an intermediate fact. Establish `: IsLocallyNoetherian (pullback Ag.s (spMap z))` using `LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Ag.s (spMap z))`. Use `GlobalTheory.ValuativeGeneric.isProper_of_lift_generic O _ _ w (pullback.snd _ _) inferInstance ?_ ?_` and prove the remaining obligations. Rewrite using `[hs]`.

Conclude with `(GlobalTheory.isQProjOver_finite_and_baseChange _ _ sM F.qproj).2 O b`. Introduce `V K _ _ _ _ _ _ _ x y hx hxy`. Establish `h₂ : x ≫ pullback.snd sM (spMap b) = spMap (algebraMap V K) ≫ y ≫ pullback.snd _ _`. Rewrite using `[← hs, ← Category.assoc, hxy, Category.assoc]`. Establish `hfl : Flat ((y ≫ pullback.snd _ _) ≫ spMap b)` using `GlobalTheory.GenericFlat.generic_charZero_and_flat.2 _ O b _ (pullback.snd sM (spMap b)) V K x _ hb inferInstance hx h₂`.

Take `⟨t', κ, lv', hlv'⟩` from `(GlobalTheory.fullObj_pull E H D n N _ _ (pullback.fst _ _ ≫ sM) t lv x).1`. Take `⟨m, hm⟩` from `ObjMaps.exists_sab_comp ν κ`. Establish `hy : x ≫ w ≫ pullback.fst _ _ = spMap (algebraMap V K) ≫ y ≫ pullback.fst _ _`. Rewrite using `[← Category.assoc, hxy, Category.assoc]`. Take `⟨x', hx₁, hx₂⟩` from `exists_extension hX hL hL₂ E H D n N MM sM tM lev g _ _ _ _ Ag.univ bas V K _ (y ≫ pullback.fst _ _) _ t' m lv' (κ.φ ≫ θ) hN F hfl (by rw [Category.assoc, pullback.condition, ← Category.assoc, h₂]; simp only [Category.assoc]) (fun a => by rw [hm]; exact ObjComp.sec_comp (hlv a) ( …`.

Use `⟨pullback.lift x' (y ≫ pullback.snd _ _) hx₂, pullback.hom_ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.lift_fst, hx₁]`. Rewrite using `[Category.assoc, pullback.lift_snd, h₂]`.
-/
theorem proper (hX : GlobalTheory.LN.HomExtSt) (hL : Out.Laws) (hL₂ : Out.Laws2) (hN : 0 < N) (F : FamCore D sM tM lev)
    [IsDedekindDomain (RZ H n N)] [IsDomain O] [IsNoetherianRing O] (hb : Function.Injective b)
    (hq : IsQProjOver Ag.s) {t : SAB H (pullback sM (spMap b))}
    (ν : SABMap t tM (pullback.fst _ _)) {lv : D.La → (𝟙_ (Over (pullback sM (spMap b))) ⟶ t.G)}
    (hlv : ∀ a, (lv a).left ≫ ν.φ = pullback.fst _ _ ≫ (lev a).left)
    {w : pullback sM (spMap b) ⟶ pullback Ag.s (spMap z)}
    (hw : SiegData (pullback.snd _ _) t lv Ag z bas w) : IsProper w := by
  obtain ⟨θ, θ₂, hθ, -, -, hl⟩ := GlobalTheory.SiegelDirect.direct E H D O _ _ t lv g p N Ag z bas w hw
  have hs : w ≫ pullback.snd _ _ = pullback.snd sM (spMap b) := by
    obtain ⟨_, _, _, -, -, -, -, h, -⟩ := hw
    exact h
  have := isSeparated_of_qproj hq
  have := locallyOfFiniteType_of_qproj hq
  have := F.flat
  have : IsLocallyNoetherian (pullback Ag.s (spMap z)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Ag.s (spMap z))
  refine GlobalTheory.ValuativeGeneric.isProper_of_lift_generic O _ _ w (pullback.snd _ _) inferInstance ?_ ?_
  · rw [hs]
    exact (GlobalTheory.isQProjOver_finite_and_baseChange _ _ sM F.qproj).2 O b
  intro V K _ _ _ _ _ _ _ x y hx hxy
  have h₂ : x ≫ pullback.snd sM (spMap b) = spMap (algebraMap V K) ≫ y ≫ pullback.snd _ _ := by
    rw [← hs, ← Category.assoc, hxy, Category.assoc]
  have hfl : Flat ((y ≫ pullback.snd _ _) ≫ spMap b) :=
    GlobalTheory.GenericFlat.generic_charZero_and_flat.2 _ O b _ (pullback.snd sM (spMap b)) V K x _ hb inferInstance hx h₂
  obtain ⟨t', κ, lv', hlv'⟩ := (GlobalTheory.fullObj_pull E H D n N _ _ (pullback.fst _ _ ≫ sM) t lv x).1
  obtain ⟨m, hm⟩ := ObjMaps.exists_sab_comp ν κ
  have hy : x ≫ w ≫ pullback.fst _ _ = spMap (algebraMap V K) ≫ y ≫ pullback.fst _ _ := by
    rw [← Category.assoc, hxy, Category.assoc]
  obtain ⟨x', hx₁, hx₂⟩ := exists_extension hX hL hL₂ E H D n N MM sM tM lev g _ _ _ _ Ag.univ bas V K _ (y ≫ pullback.fst _ _) _ t' m
    lv' (κ.φ ≫ θ) hN F hfl
    (by rw [Category.assoc, pullback.condition, ← Category.assoc, h₂]; simp only [Category.assoc])
    (fun a => by rw [hm]; exact ObjComp.sec_comp (hlv a) (hlv' a))
    (hy ▸ κ.cart.comp hθ) (fun u => hy ▸ ObjComp.sec_comp (hl u) (hlv' (bas u)))
  refine ⟨pullback.lift x' (y ≫ pullback.snd _ _) hx₂, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, pullback.lift_fst, hx₁]
  · rw [Category.assoc, pullback.lift_snd, h₂]

/- English proof (translation)
Use `F.flat` as an intermediate fact. Use `F.red` as an intermediate fact. Use `locallyOfFiniteType_of_qproj F.qproj` as an intermediate fact. Establish `hn : IsLocallyNoetherian (pullback sM (spMap b))` using `LocallyOfFiniteType.isLocallyNoetherian (pullback.snd sM (spMap b))`. Establish `hr : IsReduced (pullback sM (spMap b))` using `isReduced_of_flat_preimmersion (pullback.fst _ _)`.

Establish `ho` using `(GlobalTheory.fullObj_pull E H D n N _ _ sM tM lev _).2 t ν lv hlv F.obj`. Rewrite `ho` using `[pullback.condition]`. Take `⟨o, φ, φ₂, hpr, h₁, h₂, h₃, h₄⟩` from `GlobalTheory.exists_siegPre_of_fullObj hL hL₂ E H D n N p O b z _ (pullback.snd _ _) t lv g bas hodd hu hz hn (GlobalTheory.GenericFlat.generic_charZero_and_flat.1 O _ (pullback.snd sM (spMap b)) inferInstance) hbas ho`. Take `⟨f, ⟨hf, hf'⟩, -⟩` from `hA.2 _ _ o hr hn inferInstance hpr`. Establish `hw : SiegData (pullback.snd _ _) t lv Ag z bas (pullback.lift f _ hf)` using `⟨o, φ, φ₂, h₁, h₂, h₃, h₄, pullback.lift_snd _ _ _, by rw [pullback.lift_fst]; exact hf'⟩`.

Use `proper hX hL hL₂ hN F hb hA.1 ν hlv hw` as an intermediate fact. Use `unramified hL F ν hlv hw` as an intermediate fact. Use `TangentCrit.locallyQuasiFinite_of_formallyUnramified (pullback.lift f _ hf)` as an intermediate fact. Conclude with `⟨_, hw, .of_isProper_of_locallyQuasiFinite _, ‹_›⟩`.
-/
theorem core (hX : GlobalTheory.LN.HomExtSt) (hL : Out.Laws) (hL₂ : Out.Laws2) (hN : 0 < N) (hodd : Odd N)
    (F : FamCore D sM tM lev) [IsDedekindDomain (RZ H n N)] [IsDomain O] [CharZero O] [IsNoetherianRing O]
    (hb : Function.Injective b) [Flat (spMap b)] [IsPreimmersion (spMap b)] [Flat (spMap z)] (hu : IsUnit (N : O))
    (hz : z (zetaZP p N) = b (RZ.ze H n N)) (hbas : ∀ x y, D.EF (bas x) (bas y) = omegaStd x y) (hA : SiegRep Ag)
    {t : SAB H (pullback sM (spMap b))}
    (ν : SABMap t tM (pullback.fst _ _)) {lv : D.La → (𝟙_ (Over (pullback sM (spMap b))) ⟶ t.G)}
    (hlv : ∀ a, (lv a).left ≫ ν.φ = pullback.fst _ _ ≫ (lev a).left) :
    ∃ w : pullback sM (spMap b) ⟶ pullback Ag.s (spMap z),
      SiegData (pullback.snd _ _) t lv Ag z bas w ∧ IsFinite w ∧ FormallyUnramified w := by
  have := F.flat
  have := F.red
  have := locallyOfFiniteType_of_qproj F.qproj
  have hn : IsLocallyNoetherian (pullback sM (spMap b)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd sM (spMap b))
  have hr : IsReduced (pullback sM (spMap b)) := isReduced_of_flat_preimmersion (pullback.fst _ _)
  have ho := (GlobalTheory.fullObj_pull E H D n N _ _ sM tM lev _).2 t ν lv hlv F.obj
  rw [pullback.condition] at ho
  obtain ⟨o, φ, φ₂, hpr, h₁, h₂, h₃, h₄⟩ := GlobalTheory.exists_siegPre_of_fullObj hL hL₂ E H D n N p O b z _ (pullback.snd _ _) t lv g bas hodd hu hz hn
    (GlobalTheory.GenericFlat.generic_charZero_and_flat.1 O _ (pullback.snd sM (spMap b)) inferInstance) hbas ho
  obtain ⟨f, ⟨hf, hf'⟩, -⟩ := hA.2 _ _ o hr hn inferInstance hpr
  have hw : SiegData (pullback.snd _ _) t lv Ag z bas (pullback.lift f _ hf) :=
    ⟨o, φ, φ₂, h₁, h₂, h₃, h₄, pullback.lift_snd _ _ _, by rw [pullback.lift_fst]; exact hf'⟩
  have := proper hX hL hL₂ hN F hb hA.1 ν hlv hw
  have := unramified hL F ν hlv hw
  have := TangentCrit.locallyQuasiFinite_of_formallyUnramified (pullback.lift f _ hf)
  exact ⟨_, hw, .of_isProper_of_locallyQuasiFinite _, ‹_›⟩

/- English proof (translation)
Establish `eb : spMap c ≫ spMap b = spMap b'` using `by rw [← hb, ← Spec.map_comp]; rfl`. Establish `ez : spMap c ≫ spMap z = spMap z'` using `by rw [← hz, ← Spec.map_comp]; rfl`. Establish `hs : w ≫ pullback.snd _ _ = pullback.snd sM (spMap b)`. Take `⟨_, _, _, -, -, -, -, h, -⟩` from `hw`. Conclude with `h`.

Take `⟨r, hr₁, hr₂⟩ : ∃ r : T ⟶ pullback sM (spMap b), r ≫ pullback.fst _ _ = f ∧ r ≫ pullback.snd _ _ = sT ≫ spMap c` from `⟨pullback.lift f (sT ≫ spMap c) (by rw [Category.assoc, eb, hT.w]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩`. Establish `hr : IsPullback r sT (pullback.snd sM (spMap b)) (spMap c)` using `IsPullback.of_right (by rw [hr₁, eb]; exact hT) hr₂ (IsPullback.of_hasPullback _ _)`. Substitute `hr₁` using the available equality. Take `⟨κ', hκ'⟩` from `ObjMaps.exists_sab_cancel ν κ`. Establish `hl : ∀ a, (lvT a).left ≫ κ'.φ = r ≫ (lv a).left` using `fun a => ObjComp.sec_cancel ν.cart.1 κ'.cart.1.w (Over.w (lv a)) (Over.w (lvT a)) (hlv a) (by rw [← hκ']; exact hlvT a)`.

Establish `e : (r ≫ pullback.snd sM (spMap b)) ≫ spMap z = sT ≫ spMap z'` using `by rw [hr₂, Category.assoc, ez]`. Take `⟨w', hw₁, hw₂⟩ : ∃ w' : T ⟶ pullback Ag.s (spMap z'), w' ≫ pullback.fst _ _ = (r ≫ w) ≫ pullback.fst _ _ ∧ w' ≫ pullback.snd _ _ = sT` from `⟨pullback.lift ((r ≫ w) ≫ pullback.fst _ _) sT (by`. Rewrite using `[← e, ← hs]`. Simplify using `only [Category.assoc, pullback.condition]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩`. Take `⟨q, hq₁, hq₂⟩ : ∃ q : pullback Ag.s (spMap z') ⟶ pullback Ag.s (spMap z), q ≫ pullback.fst _ _ = pullback.fst _ _ ∧ q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap c` from `⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap c) (by rw [Category.assoc, ez, pullback.condition]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩`.

Establish `hq : IsPullback q (pullback.snd _ _) (pullback.snd Ag.s (spMap z)) (spMap c)` using `IsPullback.of_right (by rw [hq₁, ez]; exact IsPullback.of_hasPullback _ _) hq₂ (IsPullback.of_hasPullback _ _)`. Establish `hsq : IsPullback r w' w q`. Use `IsPullback.of_bot (by rw [hw₂, hs]; exact hr) (pullback.hom_ext ?_ ?_) hq` and prove the remaining obligations. Rewrite using `[Category.assoc w', hq₁, hw₁]`. Rewrite using `[Category.assoc, hs, hr₂, Category.assoc, hq₂, ← Category.assoc, hw₂]`.

Use `⟨w', ?_, MorphismProperty.of_isPullback (P := @IsFinite) hsq ‹_›, MorphismProperty.of_isPullback (P := @FormallyUnramified) hsq ‹_›⟩` and prove the remaining obligations. Take `⟨o, φ, φ₂, h₁, h₂, h₃, h₄, -, h₅⟩` from `GlobalTheory.T.siegelData_pullback_of_levelMap E H D O _ T _ r t tT κ' lv lvT g p N Ag z bas w hl hw`. Rewrite `h₅` using `[← hw₁]`. Unfold `SiegData`. Generalize the expression as in `(r ≫ pullback.snd sM (spMap b)) ≫ spMap z = s at e o φ φ₂ h₁ h₂ h₃ h₄ h₅`.

Substitute `e` using the available equality. Conclude with `⟨o, φ, φ₂, h₁, h₂, h₃, h₄, hw₂, h₅⟩`.
-/
theorem baseChange {O' : Type} [CommRing O'] (c : O →+* O') {b' : RZ H n N →+* O'} {z' : ZP p N →+* O'}
    (hb : c.comp b = b') (hz : c.comp z = z') {t : SAB H (pullback sM (spMap b))}
    (ν : SABMap t tM (pullback.fst _ _)) {lv : D.La → (𝟙_ (Over (pullback sM (spMap b))) ⟶ t.G)}
    (hlv : ∀ a, (lv a).left ≫ ν.φ = pullback.fst _ _ ≫ (lev a).left)
    {w : pullback sM (spMap b) ⟶ pullback Ag.s (spMap z)} (hw : SiegData (pullback.snd _ _) t lv Ag z bas w)
    [IsFinite w] [FormallyUnramified w] {T : Scheme.{0}} {sT : T ⟶ Sp O'} {f : T ⟶ MM} {tT : SAB H T}
    (κ : SABMap tT tM f) {lvT : D.La → (𝟙_ (Over T) ⟶ tT.G)} (hT : IsPullback f sT sM (spMap b'))
    (hlvT : ∀ a, (lvT a).left ≫ κ.φ = f ≫ (lev a).left) :
    ∃ w' : T ⟶ pullback Ag.s (spMap z'), SiegData sT tT lvT Ag z' bas w' ∧ IsFinite w' ∧ FormallyUnramified w' := by
  have eb : spMap c ≫ spMap b = spMap b' := by rw [← hb, ← Spec.map_comp]; rfl
  have ez : spMap c ≫ spMap z = spMap z' := by rw [← hz, ← Spec.map_comp]; rfl
  have hs : w ≫ pullback.snd _ _ = pullback.snd sM (spMap b) := by
    obtain ⟨_, _, _, -, -, -, -, h, -⟩ := hw
    exact h
  obtain ⟨r, hr₁, hr₂⟩ : ∃ r : T ⟶ pullback sM (spMap b), r ≫ pullback.fst _ _ = f ∧ r ≫ pullback.snd _ _ = sT ≫ spMap c :=
    ⟨pullback.lift f (sT ≫ spMap c) (by rw [Category.assoc, eb, hT.w]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hr : IsPullback r sT (pullback.snd sM (spMap b)) (spMap c) :=
    IsPullback.of_right (by rw [hr₁, eb]; exact hT) hr₂ (IsPullback.of_hasPullback _ _)
  subst hr₁
  obtain ⟨κ', hκ'⟩ := ObjMaps.exists_sab_cancel ν κ
  have hl : ∀ a, (lvT a).left ≫ κ'.φ = r ≫ (lv a).left := fun a =>
    ObjComp.sec_cancel ν.cart.1 κ'.cart.1.w (Over.w (lv a)) (Over.w (lvT a)) (hlv a) (by rw [← hκ']; exact hlvT a)
  have e : (r ≫ pullback.snd sM (spMap b)) ≫ spMap z = sT ≫ spMap z' := by rw [hr₂, Category.assoc, ez]
  obtain ⟨w', hw₁, hw₂⟩ : ∃ w' : T ⟶ pullback Ag.s (spMap z'),
      w' ≫ pullback.fst _ _ = (r ≫ w) ≫ pullback.fst _ _ ∧ w' ≫ pullback.snd _ _ = sT :=
    ⟨pullback.lift ((r ≫ w) ≫ pullback.fst _ _) sT (by
      rw [← e, ← hs]; simp only [Category.assoc, pullback.condition]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨q, hq₁, hq₂⟩ : ∃ q : pullback Ag.s (spMap z') ⟶ pullback Ag.s (spMap z),
      q ≫ pullback.fst _ _ = pullback.fst _ _ ∧ q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap c :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap c) (by rw [Category.assoc, ez, pullback.condition]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hq : IsPullback q (pullback.snd _ _) (pullback.snd Ag.s (spMap z)) (spMap c) :=
    IsPullback.of_right (by rw [hq₁, ez]; exact IsPullback.of_hasPullback _ _) hq₂ (IsPullback.of_hasPullback _ _)
  have hsq : IsPullback r w' w q := by
    refine IsPullback.of_bot (by rw [hw₂, hs]; exact hr) (pullback.hom_ext ?_ ?_) hq
    · rw [Category.assoc w', hq₁, hw₁]
    · rw [Category.assoc, hs, hr₂, Category.assoc, hq₂, ← Category.assoc, hw₂]
  refine ⟨w', ?_, MorphismProperty.of_isPullback (P := @IsFinite) hsq ‹_›,
    MorphismProperty.of_isPullback (P := @FormallyUnramified) hsq ‹_›⟩
  obtain ⟨o, φ, φ₂, h₁, h₂, h₃, h₄, -, h₅⟩ := GlobalTheory.T.siegelData_pullback_of_levelMap E H D O _ T _ r t tT κ' lv lvT g p N Ag z bas w hl hw
  rw [← hw₁] at h₅
  unfold SiegData
  generalize (r ≫ pullback.snd sM (spMap b)) ≫ spMap z = s at e o φ φ₂ h₁ h₂ h₃ h₄ h₅
  subst e
  exact ⟨o, φ, φ₂, h₁, h₂, h₃, h₄, hw₂, h₅⟩

/- English proof (translation)
Set `e : O ≃+* i.range` to `RingEquiv.ofBijective i.rangeRestrict ⟨fun _ _ h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩`. Conclude with `⟨e.symm.toRingHom.comp (Subring.inclusion h), fun x => congrArg Subtype.val (e.apply_symm_apply ⟨x, h x.2⟩)⟩`.
-/
theorem exists_lift_subring {O : Type} [CommRing O] {i : O →+* ℂ} (hi : Function.Injective i) {S : Subring ℂ}
    (h : S ≤ i.range) : ∃ c : S →+* O, ∀ x, i (c x) = x := by
  let e : O ≃+* i.range :=
    RingEquiv.ofBijective i.rangeRestrict ⟨fun _ _ h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  exact ⟨e.symm.toRingHom.comp (Subring.inclusion h), fun x => congrArg Subtype.val (e.apply_symm_apply ⟨x, h x.2⟩)⟩

/- English proof (translation)
Use `IsUnit.of_mul_eq_one ⟨_, h⟩ (Subtype.ext ?_)` and prove the remaining obligations. Simplify using `using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm : (m : ℂ) ≠ 0)`.
-/
theorem isUnit_natCast_of_inv_mem {S : Subring ℂ} {m : ℕ} (hm : m ≠ 0) (h : (m : ℂ)⁻¹ ∈ S) : IsUnit (m : S) := by
  refine IsUnit.of_mul_eq_one ⟨_, h⟩ (Subtype.ext ?_)
  simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm : (m : ℂ) ≠ 0)

end GlobalTheory.FamSiegel

open GlobalTheory.FamSiegel in

/- English proof (translation)
Introduce `hX hL hL₂ E _ _ _ H D n N MM sM tM lev _ hn hodd hj F hAg p hp hpn`. Take `⟨Ag, hA⟩` from `hAg p hp hpn`. Take `⟨bas₀, hbas₀⟩` from `GlobalTheory.ZM.exists_isSympBasis E H D`. Take `⟨-, bas, hbas⟩` from `GlobalTheory.ZM.sympBasis_std E H D _ bas₀ hbas₀`. Take `⟨hD, hO, h₁, h₂, h₃⟩` from `GlobalTheory.JoinRing.join_rings E H n N p hn hj hp hpn`.

Take `⟨j, -, hj⟩` from `hj`. Establish `hN : 0 < N` using `by rw [hj]; exact pow_pos hn.pos j`. Establish `hNo : Odd N` using `by rw [hj]; exact hodd.pow`. Use `⟨Ag, bas, hbas, fun O _ i z b hi hz hb T sT f tT κ lvT hT hlvT => ?_⟩` and prove the remaining obligations. Establish `hle : RZ H n N ⊔ ZP p N ≤ i.range` using `sup_le (fun x hx => ⟨b ⟨x, hx⟩, hb _⟩) fun x hx => ⟨z ⟨x, hx⟩, hz _⟩`.

Take `⟨S, l₁, l₂, hO, h₁, h₂, h₃, hle⟩ : ∃ (S : Subring ℂ) (l₁ : RZ H n N ≤ S) (l₂ : ZP p N ≤ S), IsNoetherianRing S ∧ Flat (spMap (Subring.inclusion l₁)) ∧ IsPreimmersion (spMap (Subring.inclusion l₁)) ∧ Flat (spMap (Subring.inclusion l₂)) ∧ S ≤ i.range` from `⟨_, le_sup_left, le_sup_right, hO, h₁, h₂, h₃, hle⟩`. Establish `hu : IsUnit (N : S)`. Use `(isUnit_natCast_of_inv_mem hn.ne_zero (l₁ (Subring.subset_closure (Or.inr (Or.inl rfl))))).pow j` as an intermediate fact. Rewrite `this` using `[← Nat.cast_pow, ← hj]`. Then use the resulting hypothesis. Take `⟨t, ν, lv, hlv⟩` from `(GlobalTheory.fullObj_pull E H D n N _ _ sM tM lev (pullback.fst sM (spMap (Subring.inclusion l₁)))).1`.

Take `⟨w, hw, _, _⟩` from `core (z := Subring.inclusion l₂) hX hL hL₂ hN hNo F (Subring.inclusion_injective l₁) hu (Subtype.ext rfl) hbas hA ν hlv`. Take `⟨c, hc⟩` from `exists_lift_subring hi hle`. Conclude with `baseChange c (RingHom.ext fun x => hi ((hc ⟨x, l₁ x.2⟩).trans (hb x).symm)) (RingHom.ext fun x => hi ((hc ⟨x, l₂ x.2⟩).trans (hz x).symm)) ν hlv hw κ hT hlvT`.
-/
theorem GlobalTheory.siegClause_of_famCore : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)), 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N = n ^ j) → FamCore D sM tM lev → (∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N, SiegRep Ag) → SiegClause D sM tM lev := by
  intro hX hL hL₂ E _ _ _ H D n N MM sM tM lev _ hn hodd hj F hAg p hp hpn
  obtain ⟨Ag, hA⟩ := hAg p hp hpn
  obtain ⟨bas₀, hbas₀⟩ := GlobalTheory.ZM.exists_isSympBasis E H D
  obtain ⟨-, bas, hbas⟩ := GlobalTheory.ZM.sympBasis_std E H D _ bas₀ hbas₀
  obtain ⟨hD, hO, h₁, h₂, h₃⟩ := GlobalTheory.JoinRing.join_rings E H n N p hn hj hp hpn
  obtain ⟨j, -, hj⟩ := hj
  have hN : 0 < N := by rw [hj]; exact pow_pos hn.pos j
  have hNo : Odd N := by rw [hj]; exact hodd.pow
  refine ⟨Ag, bas, hbas, fun O _ i z b hi hz hb T sT f tT κ lvT hT hlvT => ?_⟩
  have hle : RZ H n N ⊔ ZP p N ≤ i.range :=
    sup_le (fun x hx => ⟨b ⟨x, hx⟩, hb _⟩) fun x hx => ⟨z ⟨x, hx⟩, hz _⟩
  obtain ⟨S, l₁, l₂, hO, h₁, h₂, h₃, hle⟩ : ∃ (S : Subring ℂ) (l₁ : RZ H n N ≤ S) (l₂ : ZP p N ≤ S),
      IsNoetherianRing S ∧ Flat (spMap (Subring.inclusion l₁)) ∧ IsPreimmersion (spMap (Subring.inclusion l₁)) ∧
        Flat (spMap (Subring.inclusion l₂)) ∧ S ≤ i.range := ⟨_, le_sup_left, le_sup_right, hO, h₁, h₂, h₃, hle⟩
  have hu : IsUnit (N : S) := by
    have := (isUnit_natCast_of_inv_mem hn.ne_zero (l₁ (Subring.subset_closure (Or.inr (Or.inl rfl))))).pow j
    rwa [← Nat.cast_pow, ← hj] at this
  obtain ⟨t, ν, lv, hlv⟩ := (GlobalTheory.fullObj_pull E H D n N _ _ sM tM lev (pullback.fst sM (spMap (Subring.inclusion l₁)))).1
  obtain ⟨w, hw, _, _⟩ := core (z := Subring.inclusion l₂) hX hL hL₂ hN hNo F (Subring.inclusion_injective l₁) hu
    (Subtype.ext rfl) hbas hA ν hlv
  obtain ⟨c, hc⟩ := exists_lift_subring hi hle
  exact baseChange c (RingHom.ext fun x => hi ((hc ⟨x, l₁ x.2⟩).trans (hb x).symm))
    (RingHom.ext fun x => hi ((hc ⟨x, l₂ x.2⟩).trans (hz x).symm)) ν hlv hw κ hT hlvT
