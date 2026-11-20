import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecSq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNeZeroClosedFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionPrimitiveTwistTorusExtensionStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.EffSpecial

/- English proof (translation)
Take `⟨u, hu⟩` from `h`. Take `⟨t, b, hb⟩` from `hs`. Use `⟨DVR.secOfIso t hu hA hB, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Use `push_neg at hn`.

Use `hb (fn_ext fun y hy => ?_)` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_chart hA y`. Establish `e` using `(DVR.secOfIso_spec t hu hA hB a b).symm`. Rewrite `e` using `[hn a]`. Establish `e'` using `(DVR.isoCand_rs u t a b le_rfl).symm.trans ((congrArg (DVR.rs le_rfl) (e.trans (map_zero _))).trans (map_zero _))`.

Establish `e''` using `(Units.mul_right_eq_zero _).1 e'`. Establish `hm : (𝟙 Y : Y ⟶ Y) y ∈ A.U a ⊓ B.U b` using `⟨ha, hy⟩`. Use `(gs_res (𝟙 Y) y inf_le_right hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) e'').trans ?_)` and prove the remaining obligations. Rewrite using `[gs_eq _ y _ hm, gs_eq _ y _ hy, map_zero, map_zero, map_zero, map_zero]`.
-/
theorem exists_sec_of_lbIso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B)
    (hs : ∃ s : LB.Sec B, ∃ j, s.f j ≠ 0) : ∃ s : LB.Sec A, ∃ j, s.f j ≠ 0 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨t, b, hb⟩ := hs
  refine ⟨DVR.secOfIso t hu hA hB, ?_⟩
  by_contra hn
  push_neg at hn
  refine hb (fn_ext fun y hy => ?_)
  obtain ⟨a, ha⟩ := exists_chart hA y
  have e := (DVR.secOfIso_spec t hu hA hB a b).symm
  rw [hn a] at e
  have e' := (DVR.isoCand_rs u t a b le_rfl).symm.trans ((congrArg (DVR.rs le_rfl) (e.trans (map_zero _))).trans
    (map_zero _))
  have e'' := (Units.mul_right_eq_zero _).1 e'
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ A.U a ⊓ B.U b := ⟨ha, hy⟩
  refine (gs_res (𝟙 Y) y inf_le_right hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) e'').trans ?_)
  rw [gs_eq _ y _ hm, gs_eq _ y _ hy, map_zero, map_zero, map_zero, map_zero]

/- English proof (translation)
Take `⟨w, hw⟩` from `h`. Use `⟨⟨fun p => w.s p ^ t⟩, fun p q => ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (· ^ t) (hw p q)`. Simplify using `only [mul_zpow, ← map_zpow] at e`. Use `e.trans (congrArg₂ (· * ·) ?_ rfl)` and prove the remaining obligations.

Conclude with `(mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))`.
-/
theorem lbIso_pw {Y : Scheme.{0}} {A B : LB Y} (h : LBIso A B) (t : ℤ) : LBIso (AbLaw.pw A t) (AbLaw.pw B t) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨fun p => w.s p ^ t⟩, fun p q => ?_⟩
  have e := congrArg (· ^ t) (hw p q)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  exact (mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm
    ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))

/- English proof (translation)
Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 hy`. Use `⟨j, fun e => ?_⟩` and prove the remaining obligations. Rewrite `hj` using `[e, Scheme.basicOpen_zero]`. Conclude with `hj`.
-/
theorem ne_zero_of_mem {Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) {y : Y} (hy : y ∈ nonzeroLocus s) :
    ∃ j, s.f j ≠ 0 := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine ⟨j, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hj
  exact hj

/- English proof (translation)
Establish `hm : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal`. Rewrite using `[zero_add, pow_one]`. Use `infer_instance`. Use `letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V ^ (0 + 1))`. Use `forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth hB.geomConnected` as an intermediate fact.

Conclude with `GeometricallyIntegral.geometrically_isIntegral (f := B.hom) _ _ _ (IsPullback.of_id_fst (f := B.hom))`.
-/
theorem isIntegral_special {V : Type} [CommRing V] [IsLocalRing V]
    (B : Over (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))))) [GrpObj B]
    (hB : IsAbelianScheme B) : IsIntegral B.left := by
  have hm : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V ^ (0 + 1))
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth hB.geomConnected
  exact GeometricallyIntegral.geometrically_isIntegral (f := B.hom) _ _ _ (IsPullback.of_id_fst (f := B.hom))

/- English proof (translation)
Introduce `hL V _ _ _ A G _ _ s t`. Use `s.cdvr.1` as an intermediate fact. Use `s.semi.smooth` as an intermediate fact. Use `s.semi.separated` as an intermediate fact. Use `s.semi.quasiCompact` as an intermediate fact.

Use `s.semi.geomConnected` as an intermediate fact. Take `⟨d, hd, n, a, ha, -⟩` from `(GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ A.A A.L A.isLB).1 A.ample`. Establish `hP` using `s.P.L.isLB`. Establish `h₁ : ∃ σ : LB.Sec ((AbLaw.pw s.P.L.L d).pull (pullback.fst G.hom (jK V))), ∃ j, σ.f j ≠ 0`. Establish `iso : LBIso ((AbLaw.pw s.P.L.L d).pull (pullback.fst G.hom (jK V))) ((AbLaw.pw A.L d).pull s.gen.hom.left)`.

Rewrite using `[TrivLocus.pull_pw, TrivLocus.pull_pw]`. Conclude with `lbIso_pw (LBIso.symm ⟨s.wA, s.wA_gen⟩) d`. Take `⟨w, hw⟩` from `iso`. Set `y : ((Over.pullback (jK V)).obj G).left` to `s.gen.inv.left (eSec A.A (IsLocalRing.closedPoint (FractionRing V)))`. Establish `hy : s.gen.hom.left y ∈ ⨆ i, nonzeroLocus (a i)` using `by rw [ha]; trivial`.

Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hy`. Take `⟨⟨σ, hσ, -⟩, H⟩` from `SecPullIso.section_pull _ _ s.gen.hom.left _ _ w (isLB_pw A.isLB d) (pull_isLB (isLB_pw hP d) _) hw (a i)`. Conclude with `⟨σ, ne_zero_of_mem σ (y := y) (by rw [H σ hσ]; exact hi)⟩`. Establish `h₂` using `GlobalTheory.SpreadSec.exists_ne_zero_closed_fibre V G _ (isLB_pw hP d) h₁`. Take `⟨w, hw⟩` from `(t.l 0).lev`.

Establish `hM` using `(t.l 0).D.M.L.isLB`. Establish `hE` using `(t.l 0).Pe.L.isLB`. Establish `h₃ : ∃ σ : LB.Sec ((AbLaw.pw (t.l 0).D.M.L.L d).pull (t.l 0).Q.q.left), ∃ j, σ.f j ≠ 0`. Use `exists_sec_of_lbIso (pull_isLB (isLB_pw hM d) _) (pull_isLB (isLB_pw hP d) _) ?_ h₂` and prove the remaining obligations. Rewrite using `[TrivLocus.pull_pw, TrivLocus.pull_pw]`.

Conclude with `lbIso_pw (LBIso.trans (pull_isLB hM _) hE (pull_isLB hP _) (LBIso.symm ⟨_, (t.l 0).D.map.gen⟩) ⟨w, hw.gen⟩) d`. Establish `hm : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal`. Rewrite using `[zero_add, pow_one]`. Use `infer_instance`. Establish `: IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))`.

Use `letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V ^ (0 + 1))`. Use `inferInstance`. Take `⟨O, hO, hu, h₄⟩` from `GlobalTheory.T.exists_section_primitive_twist_torus_extension hL.globalFns _ _ _ (t.l 0).Q _ (isLB_pw hM d) h₃`. Use `isIntegral_special (t.l 0).Q.B (t.l 0).Q.isAb` as an intermediate fact. Take `⟨σ, hσ⟩` from `SymSec.exists_sec_sq _ (t.l 0).Q.B (t.l 0).D.M d O hO hu h₄`.

Conclude with `⟨2 * d, σ, by omega, hσ⟩`.
-/
theorem exists_sec_special : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ t : Tower s, ∃ (k : ℕ) (σ : LB.Sec (pw (t.l 0).D.M.L.L k)), 1 ≤ k ∧ ∃ j, σ.f j ≠ 0 := by
  intro hL V _ _ _ A G _ _ s t
  have := s.cdvr.1
  have := s.semi.smooth
  have := s.semi.separated
  have := s.semi.quasiCompact
  have := s.semi.geomConnected
  obtain ⟨d, hd, n, a, ha, -⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ A.A A.L A.isLB).1 A.ample
  have hP := s.P.L.isLB

  have h₁ : ∃ σ : LB.Sec ((AbLaw.pw s.P.L.L d).pull (pullback.fst G.hom (jK V))), ∃ j, σ.f j ≠ 0 := by
    have iso : LBIso ((AbLaw.pw s.P.L.L d).pull (pullback.fst G.hom (jK V)))
        ((AbLaw.pw A.L d).pull s.gen.hom.left) := by
      rw [TrivLocus.pull_pw, TrivLocus.pull_pw]
      exact lbIso_pw (LBIso.symm ⟨s.wA, s.wA_gen⟩) d
    obtain ⟨w, hw⟩ := iso
    let y : ((Over.pullback (jK V)).obj G).left :=
      s.gen.inv.left (eSec A.A (IsLocalRing.closedPoint (FractionRing V)))
    have hy : s.gen.hom.left y ∈ ⨆ i, nonzeroLocus (a i) := by rw [ha]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨⟨σ, hσ, -⟩, H⟩ := SecPullIso.section_pull _ _ s.gen.hom.left _ _ w (isLB_pw A.isLB d)
      (pull_isLB (isLB_pw hP d) _) hw (a i)
    exact ⟨σ, ne_zero_of_mem σ (y := y) (by rw [H σ hσ]; exact hi)⟩

  have h₂ := GlobalTheory.SpreadSec.exists_ne_zero_closed_fibre V G _ (isLB_pw hP d) h₁
  obtain ⟨w, hw⟩ := (t.l 0).lev
  have hM := (t.l 0).D.M.L.isLB
  have hE := (t.l 0).Pe.L.isLB
  have h₃ : ∃ σ : LB.Sec ((AbLaw.pw (t.l 0).D.M.L.L d).pull (t.l 0).Q.q.left), ∃ j, σ.f j ≠ 0 := by
    refine exists_sec_of_lbIso (pull_isLB (isLB_pw hM d) _) (pull_isLB (isLB_pw hP d) _) ?_ h₂
    rw [TrivLocus.pull_pw, TrivLocus.pull_pw]
    exact lbIso_pw (LBIso.trans (pull_isLB hM _) hE (pull_isLB hP _)
      (LBIso.symm ⟨_, (t.l 0).D.map.gen⟩) ⟨w, hw.gen⟩) d

  have hm : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V ^ (0 + 1))
    inferInstance
  obtain ⟨O, hO, hu, h₄⟩ := GlobalTheory.T.exists_section_primitive_twist_torus_extension hL.globalFns _ _ _ (t.l 0).Q _ (isLB_pw hM d) h₃
  have := isIntegral_special (t.l 0).Q.B (t.l 0).Q.isAb
  obtain ⟨σ, hσ⟩ := SymSec.exists_sec_sq _ (t.l 0).Q.B (t.l 0).D.M d O hO hu h₄
  exact ⟨2 * d, σ, by omega, hσ⟩

end GlobalTheory.UU.EffSpecial
