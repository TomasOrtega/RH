import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpEighthPowerRelativeDimensionEqEightMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsBaseChangeIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.E8Fibration

/- English proof (translation)
Use `fin_cases k`. Establish `e` using `hB.2 T' x' y' (h ≫ x) (h ≫ y) (by rw [Over.comp_left, hx]) (by rw [Over.comp_left, hy]) show (x' * y').left ≫ φ = h.left ≫ (x * y).left`. Rewrite using `[← e, ← MonObj.comp_mul, Over.comp_left]`. Conclude with `hx`. Conclude with `hy`.

Use `show (1 : T' ⟶ B').left ≫ φ = h.left ≫ (1 : T ⟶ B).left`. Establish `e` using `hB.2 T' 1 1 (pushPt hB.1.w 1) (pushPt hB.1.w 1) rfl rfl`. Rewrite `e` using `[_root_.mul_one]`. Establish `e1 : pushPt hB.1.w (1 : T' ⟶ B') = 1`. Establish `: pushPt hB.1.w (1 : T' ⟶ B') * pushPt hB.1.w 1 = pushPt hB.1.w 1` using `Over.OverMorphism.ext e`.

Conclude with `mul_eq_left.1 this`. Establish `e2 : (pushPt hB.1.w (1 : T' ⟶ B')).left = (1 : T' ⟶ B').left ≫ φ` using `rfl`. Rewrite using `[← e2, e1, ← Over.comp_left, MonObj.comp_one]`.
-/
theorem lamPts_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B']
    {φ : B'.left ⟶ B.left} (hB : IsGrpPullback B' B f φ) {T' : Over S'} {T : Over S} (h : Over.mk (T'.hom ≫ f) ⟶ T)
    (x' y' : T' ⟶ B') (x y : T ⟶ B) (hx : x'.left ≫ φ = h.left ≫ x.left) (hy : y'.left ≫ φ = h.left ≫ y.left)
    (k : Fin 4) : lamPts x' y' k ≫ φ = h.left ≫ lamPts x y k := by
  fin_cases k
  · have e := hB.2 T' x' y' (h ≫ x) (h ≫ y) (by rw [Over.comp_left, hx]) (by rw [Over.comp_left, hy])
    show (x' * y').left ≫ φ = h.left ≫ (x * y).left
    rw [← e, ← MonObj.comp_mul, Over.comp_left]
  · exact hx
  · exact hy
  · show (1 : T' ⟶ B').left ≫ φ = h.left ≫ (1 : T ⟶ B).left
    have e := hB.2 T' 1 1 (pushPt hB.1.w 1) (pushPt hB.1.w 1) rfl rfl
    rw [_root_.mul_one] at e
    have e1 : pushPt hB.1.w (1 : T' ⟶ B') = 1 := by
      have : pushPt hB.1.w (1 : T' ⟶ B') * pushPt hB.1.w 1 = pushPt hB.1.w 1 := Over.OverMorphism.ext e
      exact mul_eq_left.1 this
    have e2 : (pushPt hB.1.w (1 : T' ⟶ B')).left = (1 : T' ⟶ B').left ≫ φ := rfl
    rw [← e2, e1, ← Over.comp_left, MonObj.comp_one]

/- English proof (translation)
Introduce `W gQ V V₁ _ _ _ _ Q hQ ρ hρ D e hS K _ ev`. Establish `hS'` using `hS`. Take `⟨pr₀, w, hmon, huniv, hw, -, -⟩` from `hS'`. Take `⟨P', φ, hφ, hg, hm, t, ht⟩` from `GlobalTheory.polBaseChange_holds _ _ (spMap ev) D.P`. Establish `hgp : IsGrpPullback P'.A D.P.A (spMap ev) φ` using `⟨hφ, fun T x y x₀ y₀ hx hy => by`.

Rewrite using `[(Over.OverMorphism.ext hx : x₀ = toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ.w y), ← hm]`. Use the proof step `rfl⟩`. Take `⟨i, hi, hiφ⟩` from `grpPullback_iso (isGrpPullback_pullback D.P.A (spMap ev)) hgp`. Use `haveI := hi`. Establish `hinv : i.inv.left ≫ pullback.fst D.P.A.hom (spMap ev) = φ`.

Rewrite using `[← hiφ, ← Category.assoc, ← Over.comp_left, i.inv_hom_id, Over.id_left, Category.id_comp]`. Establish `hQP : IsPPFib Q.B Q.g Q.M` using `⟨Q.isAb, Q.smoothDim, ⟨Q.cub⟩, Q.ample, Q.ktriv⟩`. Take `⟨M₁, hM₁, hP₁⟩` from `GlobalTheory.T.principallyPolarisedFibre_baseChange (spMap ρ) Q.B Q.g Q.M hQP`. Take `⟨M, hM, hP⟩` from `GlobalTheory.T.principallyPolarisedFibre_baseChange (spMap ev) _ Q.g M₁ hP₁`. Set `B₁` to `(Over.pullback (spMap ρ)).obj Q.B`.

Set `pr : Fin 8 → (P'.A ⟶ (Over.pullback (spMap ev)).obj B₁)` to `fun a => i.inv ≫ (Over.pullback (spMap ev)).map (pr₀ a)`. Establish `hpr : IsProd pr` using `GlobalTheory.T.eighthPowerProjections_baseChange_iso (spMap ev) pr₀ ⟨hmon, huniv⟩ P'.A i hi`. Use `⟨P', i.hom.left, (Over.pullback (spMap ev)).obj B₁, inferInstance, M, pr, ?_, isGrpPullback_of_iso i, ?_, hQ ▸ hP, hpr, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hg, GlobalTheory.T.sharpEighthPower_relative_dimension_eq_eight_mul W V V₁ Q ρ D e hS, hQ]`. Establish `ht' : LBIso (D.P.L.pull φ) P'.L` using `⟨t, ht⟩`.

Conclude with `LBIso.trans (pull_isLB D.P.isLB _) (pull_isLB (pull_isLB D.P.isLB _) _) (pull_isLB P'.isLB _) (GlobalTheory.GenSpread.lbIso_pull_pull D.P.isLB i.hom.left hiφ.symm) (GlobalTheory.GenSpread.lbIso_pullback ht' i.hom.left)`. Establish `ht' : LBIso (D.P.L.pull φ) P'.L` using `⟨t, ht⟩`. Establish `H : LBIso M.L (Q.M.L.pull (pullback.fst B₁.hom (spMap ev) ≫ pullback.fst Q.B.hom (spMap ρ)))`. Rewrite using `[hM, hM₁]`. Conclude with `LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull Q.M.isLB _ rfl)`.

Establish `hx : ∀ a, (pr a).left ≫ pullback.fst B₁.hom (spMap ev) = φ ≫ (pr₀ a).left` using `fun a => by show (i.inv ≫ (Over.pullback (spMap ev)).map (pr₀ a)).left ≫ _ = _`. Rewrite using `[Over.comp_left, Category.assoc]`. Simplify using `only [Over.pullback_map_left]`. Rewrite using `[pullback.lift_fst, ← Category.assoc, hinv]`. Establish `ha` using `GlobalTheory.ShapePull.iso_linComb_pull H (fun k : (Fin 8 × Fin 8) × Fin 4 => lamPts (pr k.1.1) (pr k.1.2) k.2) (fun k => lamPts (pr₀ k.1.1) (pr₀ k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)) φ (fun k => by`.

Rewrite using `[← Category.assoc, lamPts_pull (isGrpPullback_pullback B₁ (spMap ev)) (Over.homMk φ hφ.w) (pr k.1.1) (pr k.1.2) (pr₀ k.1.1) (pr₀ k.1.2) (hx _) (hx _) k.2, Category.assoc]`. Use the proof step `rfl)`. Establish `hb` using `GlobalTheory.GenSpread.lbIso_pullback (⟨w, hw⟩ : LBIso D.P.L _) φ`. Conclude with `LBIso.trans P'.isLB (pull_isLB D.P.isLB _) (LB.isLB_linComb M.isLB _ _) (LBIso.symm ht') (LBIso.trans (pull_isLB D.P.isLB _) (pull_isLB (LB.isLB_linComb Q.M.isLB _ _) _) (LB.isLB_linComb M.isLB _ _) hb (LBIso.symm ha))`. Introduce `n y hy q hq1 hq2`.

Establish `hw' : (q ≫ i.hom.left) ≫ P'.A.hom = (baseOver (Sp K)).hom`. Rewrite using `[Category.assoc, Over.w i.hom]`. Conclude with `hq2`. Use `⟨Over.homMk (q ≫ i.hom.left) hw', rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.Raynaud.pow_eq_one_iff_of_isGrpPullback hgp]`.

Set `c : Over.mk (spMap ev) ⟶ Over.mk ((baseOver (Sp K)).hom ≫ spMap ev)` to `Over.homMk (𝟙 _) (by simp)`. Set `c' : Over.mk ((baseOver (Sp K)).hom ≫ spMap ev) ⟶ Over.mk (spMap ev)` to `Over.homMk (𝟙 _) (by simp)`. Establish `hcc : c' ≫ c = 𝟙 _` using `by ext; simp [c, c']`. Establish `hy' : c ≫ pushPt hgp.1.w (Over.homMk (q ≫ i.hom.left) hw' : baseOver (Sp K) ⟶ P'.A) = y`. Use `ext`.

Use `show 𝟙 _ ≫ (q ≫ i.hom.left) ≫ φ = y.left`. Rewrite using `[Category.id_comp, Category.assoc, hiφ, hq1]`. Establish `h1 : c ≫ pushPt hgp.1.w (Over.homMk (q ≫ i.hom.left) hw' : baseOver (Sp K) ⟶ P'.A) ^ n = 1`. Rewrite using `[MonObj.comp_pow, hy', hy]`. Establish `h2` using `congrArg (c' ≫ ·) h1`.

Simplify using `only [← Category.assoc, hcc, Category.id_comp, MonObj.comp_one] at h2`. Conclude with `h2`.
-/
theorem fibre_exists : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (gQ : ℕ) (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]
  (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (K : Type) [Field K] (ev : V₁ →+* K),
  ∃ (P' : PolAV (Sp K)) (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ P'.A.left) (B : Over (Sp K)) (_ : GrpObj B)
    (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
    P'.g = 8 * gQ ∧ IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) P'.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (P'.L.pull ψ) ∧
    E8Fibration.IsPPFib B gQ M ∧ E8Fibration.IsProd pr ∧ E8Fibration.IsE8WeightedBundle W pr P'.L M.L ∧
    ∀ (n : ℕ) (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ n = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ y' : Out.baseOver (Sp K) ⟶ P'.A, y'.left = q ≫ ψ ∧ y' ^ n = 1 := by
  intro W gQ V V₁ _ _ _ _ Q hQ ρ hρ D e hS K _ ev
  have hS' := hS
  obtain ⟨pr₀, w, hmon, huniv, hw, -, -⟩ := hS'
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap ev) D.P
  have hgp : IsGrpPullback P'.A D.P.A (spMap ev) φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ.w y), ← hm]
    rfl⟩
  obtain ⟨i, hi, hiφ⟩ := grpPullback_iso (isGrpPullback_pullback D.P.A (spMap ev)) hgp
  haveI := hi
  have hinv : i.inv.left ≫ pullback.fst D.P.A.hom (spMap ev) = φ := by
    rw [← hiφ, ← Category.assoc, ← Over.comp_left, i.inv_hom_id, Over.id_left, Category.id_comp]

  have hQP : IsPPFib Q.B Q.g Q.M := ⟨Q.isAb, Q.smoothDim, ⟨Q.cub⟩, Q.ample, Q.ktriv⟩
  obtain ⟨M₁, hM₁, hP₁⟩ := GlobalTheory.T.principallyPolarisedFibre_baseChange (spMap ρ) Q.B Q.g Q.M hQP
  obtain ⟨M, hM, hP⟩ := GlobalTheory.T.principallyPolarisedFibre_baseChange (spMap ev) _ Q.g M₁ hP₁
  let B₁ := (Over.pullback (spMap ρ)).obj Q.B
  let pr : Fin 8 → (P'.A ⟶ (Over.pullback (spMap ev)).obj B₁) :=
    fun a => i.inv ≫ (Over.pullback (spMap ev)).map (pr₀ a)
  have hpr : IsProd pr := GlobalTheory.T.eighthPowerProjections_baseChange_iso (spMap ev) pr₀ ⟨hmon, huniv⟩ P'.A i hi
  refine ⟨P', i.hom.left, (Over.pullback (spMap ev)).obj B₁, inferInstance, M, pr, ?_, isGrpPullback_of_iso i, ?_,
    hQ ▸ hP, hpr, ?_, ?_⟩
  · rw [hg, GlobalTheory.T.sharpEighthPower_relative_dimension_eq_eight_mul W V V₁ Q ρ D e hS, hQ]
  · have ht' : LBIso (D.P.L.pull φ) P'.L := ⟨t, ht⟩
    exact LBIso.trans (pull_isLB D.P.isLB _) (pull_isLB (pull_isLB D.P.isLB _) _) (pull_isLB P'.isLB _)
      (GlobalTheory.GenSpread.lbIso_pull_pull D.P.isLB i.hom.left hiφ.symm) (GlobalTheory.GenSpread.lbIso_pullback ht' i.hom.left)
  · have ht' : LBIso (D.P.L.pull φ) P'.L := ⟨t, ht⟩
    have H : LBIso M.L (Q.M.L.pull (pullback.fst B₁.hom (spMap ev) ≫ pullback.fst Q.B.hom (spMap ρ))) := by
      rw [hM, hM₁]
      exact LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull Q.M.isLB _ rfl)
    have hx : ∀ a, (pr a).left ≫ pullback.fst B₁.hom (spMap ev) = φ ≫ (pr₀ a).left := fun a => by
      show (i.inv ≫ (Over.pullback (spMap ev)).map (pr₀ a)).left ≫ _ = _
      rw [Over.comp_left, Category.assoc]
      simp only [Over.pullback_map_left]
      rw [pullback.lift_fst, ← Category.assoc, hinv]
    have ha := GlobalTheory.ShapePull.iso_linComb_pull H (fun k : (Fin 8 × Fin 8) × Fin 4 => lamPts (pr k.1.1) (pr k.1.2) k.2)
      (fun k => lamPts (pr₀ k.1.1) (pr₀ k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)) φ
      (fun k => by
        rw [← Category.assoc, lamPts_pull (isGrpPullback_pullback B₁ (spMap ev)) (Over.homMk φ hφ.w) (pr k.1.1) (pr k.1.2)
          (pr₀ k.1.1) (pr₀ k.1.2) (hx _) (hx _) k.2, Category.assoc]
        rfl)
    have hb := GlobalTheory.GenSpread.lbIso_pullback (⟨w, hw⟩ : LBIso D.P.L _) φ
    exact LBIso.trans P'.isLB (pull_isLB D.P.isLB _) (LB.isLB_linComb M.isLB _ _) (LBIso.symm ht')
      (LBIso.trans (pull_isLB D.P.isLB _) (pull_isLB (LB.isLB_linComb Q.M.isLB _ _) _) (LB.isLB_linComb M.isLB _ _)
        hb (LBIso.symm ha))
  · intro n y hy q hq1 hq2
    have hw' : (q ≫ i.hom.left) ≫ P'.A.hom = (baseOver (Sp K)).hom := by
      rw [Category.assoc, Over.w i.hom]
      exact hq2
    refine ⟨Over.homMk (q ≫ i.hom.left) hw', rfl, ?_⟩
    rw [← GlobalTheory.Raynaud.pow_eq_one_iff_of_isGrpPullback hgp]
    let c : Over.mk (spMap ev) ⟶ Over.mk ((baseOver (Sp K)).hom ≫ spMap ev) := Over.homMk (𝟙 _) (by simp)
    let c' : Over.mk ((baseOver (Sp K)).hom ≫ spMap ev) ⟶ Over.mk (spMap ev) := Over.homMk (𝟙 _) (by simp)
    have hcc : c' ≫ c = 𝟙 _ := by ext; simp [c, c']
    have hy' : c ≫ pushPt hgp.1.w (Over.homMk (q ≫ i.hom.left) hw' : baseOver (Sp K) ⟶ P'.A) = y := by
      ext
      show 𝟙 _ ≫ (q ≫ i.hom.left) ≫ φ = y.left
      rw [Category.id_comp, Category.assoc, hiφ, hq1]
    have h1 : c ≫ pushPt hgp.1.w (Over.homMk (q ≫ i.hom.left) hw' : baseOver (Sp K) ⟶ P'.A) ^ n = 1 := by
      rw [MonObj.comp_pow, hy', hy]
    have h2 := congrArg (c' ≫ ·) h1
    simp only [← Category.assoc, hcc, Category.id_comp, MonObj.comp_one] at h2
    exact h2

end GlobalTheory.Poinc.Sep.E8Fibration
