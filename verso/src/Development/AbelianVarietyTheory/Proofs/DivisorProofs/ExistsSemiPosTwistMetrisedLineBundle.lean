import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAmpleGloballyGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSemipositiveWeightOfGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightsDifferBySmoothFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosFubiniStudyPowerAddSmoothFnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosRegPull

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

/- English proof (translation)
Introduce `i c y hy ξ` and use `by have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (E.U i)) have e : (fun v => (χ.φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] fun v => (χ'.φ (j i) (c.e.symm v) : ℂ) := eventually_of_mem (ho.mem_nhds (mem_over c.e hy.1 hy.2)) fun v hv => by simp only [he i _ hv.2] rw [Reciproc …`.
-/
theorem semiPosReg_of_eqOn_charts {E E' : LB X} (χ : Weight p σ E) {χ' : Weight p σ E'}
    (h : χ'.SemiPosReg D) (j : E.ι → E'.ι)
    (hj : ∀ i y, y ∈ ptsIn p σ (E.U i) → y ∈ ptsIn p σ (E'.U (j i)))
    (he : ∀ i y, y ∈ ptsIn p σ (E.U i) → χ.φ i y = χ'.φ (j i) y) : χ.SemiPosReg D := fun i c y hy ξ => by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (E.U i))
  have e : (fun v => (χ.φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] fun v => (χ'.φ (j i) (c.e.symm v) : ℂ) :=
    eventually_of_mem (ho.mem_nhds (mem_over c.e hy.1 hy.2)) fun v hv => by
      simp only [he i _ hv.2]
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e]
  exact h (j i) c y ⟨hy.1, hj i y hy.2⟩ ξ

/- English proof (translation)
Take `⟨t₀, ht⟩` from `GlobalTheory.TwistGen.twist_generated k X p H _ s hH hs L hL`. Take `⟨m, hm⟩ : ∃ m : ℕ, t₀ ≤ m` from `⟨t₀.toNat, by omega⟩`. Take `⟨n, u, hu⟩` from `ht m hm`. Establish `hP : (lbPow H m).IsLB` using `DVR.linComb_isLB H hH _ _`. Establish `hT : (CechPic.tens L (lbPow H m)).IsLB` using `isLB_tens hL hP`.

Establish `e : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) = cls L hL - cls (AbLaw.pw H (-(m : ℤ))) (AbLaw.isLB_pw hH _)` using `cls_div hL (AbLaw.isLB_pw hH _) (AbLaw.isLB_tw hL hH _)`. Establish `e' : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) = cls _ hT`. Rewrite using `[e, GlobalTheory.AmpleStabFinite.cls_pw hH, cls_tens hL hP, cls_lbPow hH, neg_zsmul, natCast_zsmul, sub_neg_eq_add]`. Take `⟨v, hv⟩` from `exists_generating_secs_of_cls_eq _ _ _ _ hT e' _ u hu`. Conclude with `⟨m, _, v, hv⟩`.
-/
theorem exists_generating_secs_tens_lbPow {H L : LB X} (hH : H.IsLB) (hL : L.IsLB) {N : ℕ}
    {s : Fin (N + 1) → H.Sec} (hs : AbLaw.VeryAmpleBy p H s) :
    ∃ (m n : ℕ) (u : Fin n → (CechPic.tens L (lbPow H m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated k X p H _ s hH hs L hL
  obtain ⟨m, hm⟩ : ∃ m : ℕ, t₀ ≤ m := ⟨t₀.toNat, by omega⟩
  obtain ⟨n, u, hu⟩ := ht m hm
  have hP : (lbPow H m).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens L (lbPow H m)).IsLB := isLB_tens hL hP
  have e : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) =
      cls L hL - cls (AbLaw.pw H (-(m : ℤ))) (AbLaw.isLB_pw hH _) :=
    cls_div hL (AbLaw.isLB_pw hH _) (AbLaw.isLB_tw hL hH _)
  have e' : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) = cls _ hT := by
    rw [e, GlobalTheory.AmpleStabFinite.cls_pw hH, cls_tens hL hP, cls_lbPow hH, neg_zsmul, natCast_zsmul, sub_neg_eq_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hT e' _ u hu
  exact ⟨m, _, v, hv⟩

/- English proof (translation)
Introduce and unpack `F _ X p σ ⟨N, ι, hι, hp⟩ D A`. Set `O : MLine (PSpace.str F N) σ` to `MLine.ofHerm (ProjSpace.hermitianTwistingSheaf F N) σ`. Establish `hO : O.φ.SemiPosReg N` using `Weight.semiPosReg_fsBasis (ProjSpace.O1_isLB F N) _ (ProjSpace.iSup_nonzeroLocus_coord F N) 1 (by simp)`. Establish `hsm : SmoothOfRelativeDimension N (PSpace.str F N)` using `inferInstance`. Set `H : MLine p σ` to `O.pull ι hp`.

Establish `hH : H.φ.SemiPosReg D` using `GlobalTheory.Weight.semiPosReg_pull F _ _ _ _ σ ι hp N D hsm _ _ O.cInf hO`. Establish `hpow (m : ℕ) : (H.φ.pow m).SemiPosReg D` using `Weight.SemiPosReg.of_mul _ H.cInf hH ((m : ℤ) : ℝ) (by positivity) (fun j => j PUnit.unit) (fun _ _ h => mem_pow_iff.1 h) fun j y => H.φ.zpow_φ (m : ℤ) j y`. Establish `hva : ∃ s : Fin (N + 1) → H.B.Sec, AbLaw.VeryAmpleBy p H.B s`. Substitute `hp` using the available equality. Conclude with `⟨_, ProjSpace.veryAmpleBy_secPull_coord ι⟩`.

Take `⟨s, hs⟩` from `hva`. Take `⟨m, hgen⟩` from `exists_generating_secs_tens_lbPow H.φ.isLB A.φ.isLB hs`. Take `⟨φ₁, hφ₁, hφ₁'⟩` from `GlobalTheory.weight_cInf_semiPos_of_generated F X p σ _ (A.φ.tens (H.φ.pow m)).isLB hgen`. Take `⟨u, hu, hu'⟩` from `GlobalTheory.T.smooth_weights_differ_by_smooth_function F X p σ _ φ₁ (A.φ.tens (H.φ.pow m)) hφ₁ (A.cInf.tens (H.cInf.zpow m))`. Take `⟨v, hv, hv'⟩` from `GlobalTheory.ClosedExt.exists_extension F _ X (PSpace.str F N) p σ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩ ι hp u hu`.

Take `⟨m', hm'⟩` from `GlobalTheory.T.exists_semiPos_fubiniStudy_power_add_smooth_fn F σ N v hv`. Establish `hwc : ((O.φ.pow m').addFn v).IsCInf` using `(O.cInf.zpow m').addFn hv`. Establish `hw : (((O.φ.pow m').addFn v).pull ι hp).SemiPosReg D` using `GlobalTheory.Weight.semiPosReg_pull F _ _ _ _ σ ι hp N D hsm _ _ hwc (hm' m' le_rfl)`. Use `⟨⟨_, (H.φ.pow m).tens (H.φ.pow m'), (H.cInf.zpow m).tens (H.cInf.zpow m')⟩, Weight.SemiPosReg.tens (H.cInf.zpow m) (H.cInf.zpow m') (hpow m) (hpow m'), ?_⟩` and prove the remaining obligations. Use `semiPosReg_of_eqOn_charts (A.φ.tens ((H.φ.pow m).tens (H.φ.pow m'))) (Weight.SemiPosReg.tens hφ₁ (hwc.pull ι hp) (hφ₁' D) hw) (fun i => ((i.1, i.2.1), i.2.2)) (fun i y hy => ?_) fun i y hy => ?_` and prove the remaining obligations.

Take `⟨h₁, h₂⟩` from `mem_ptsIn_inf.1 hy`. Take `⟨h₂, h₃⟩` from `mem_ptsIn_inf.1 h₂`. Use `mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨h₁, h₂⟩, ?_⟩` and prove the remaining obligations. Establish `h₄` using `mem_pow_iff.1 h₃`. Conclude with `mem_ptsIn.2 (Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun b => Set.mem_iInter.1 (mem_ptsIn.1 h₄) b)`.

Take `⟨h₁, h₂⟩` from `mem_ptsIn_inf.1 hy`. Take `⟨h₂, h₃⟩` from `mem_ptsIn_inf.1 h₂`. Establish `e₁ : A.φ.φ i.1 y + (H.φ.pow m).φ i.2.1 y = φ₁.φ (i.1, i.2.1) y + u y` using `hu' (i.1, i.2.1) y (mem_ptsIn_inf.2 ⟨h₁, h₂⟩)`. Establish `e₂ : (H.φ.pow m').φ i.2.2 y = (O.φ.pow m').φ (i.2.2 PUnit.unit) (ptMap ι hp σ y)` using `(H.φ.zpow_φ m' i.2.2 y).trans ((congrArg (_ * ·) (O.φ.pull_φ ι hp (i.2.2 PUnit.unit) y)).trans (O.φ.zpow_φ m' (i.2.2 PUnit.unit) _).symm)`. Establish `e₃ : (((O.φ.pow m').addFn v).pull ι hp).φ i.2.2 y = (O.φ.pow m').φ (i.2.2 PUnit.unit) (ptMap ι hp σ y) + v (ptMap ι hp σ y)` using `((O.φ.pow m').addFn v).pull_φ ι hp i.2.2 y`.

Express the relevant statement in the definitionally equal form `A.φ.φ i.1 y + ((H.φ.pow m).φ i.2.1 y + (H.φ.pow m').φ i.2.2 y) = φ₁.φ (i.1, i.2.1) y + (((O.φ.pow m').addFn v).pull ι hp).φ i.2.2 y`. Rewrite using `[e₃, hv', e₂, ← add_assoc, e₁]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_semiPosReg_tens : ∀ (F : Type) [Field F] (X : Scheme.{0}) (p : X ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → ∀ (D : ℕ) (A : MLine p σ), ∃ Q : MLine p σ, Q.φ.SemiPosReg D ∧ (A.tens Q).φ.SemiPosReg D := by
  rintro F _ X p σ ⟨N, ι, hι, hp⟩ D A
  let O : MLine (PSpace.str F N) σ := MLine.ofHerm (ProjSpace.hermitianTwistingSheaf F N) σ
  have hO : O.φ.SemiPosReg N := Weight.semiPosReg_fsBasis (ProjSpace.O1_isLB F N) _
    (ProjSpace.iSup_nonzeroLocus_coord F N) 1 (by simp)
  have hsm : SmoothOfRelativeDimension N (PSpace.str F N) := inferInstance
  let H : MLine p σ := O.pull ι hp
  have hH : H.φ.SemiPosReg D := GlobalTheory.Weight.semiPosReg_pull F _ _ _ _ σ ι hp N D hsm _ _ O.cInf hO
  have hpow (m : ℕ) : (H.φ.pow m).SemiPosReg D :=
    Weight.SemiPosReg.of_mul _ H.cInf hH ((m : ℤ) : ℝ) (by positivity) (fun j => j PUnit.unit)
      (fun _ _ h => mem_pow_iff.1 h) fun j y => H.φ.zpow_φ (m : ℤ) j y
  have hva : ∃ s : Fin (N + 1) → H.B.Sec, AbLaw.VeryAmpleBy p H.B s := by
    subst hp
    exact ⟨_, ProjSpace.veryAmpleBy_secPull_coord ι⟩
  obtain ⟨s, hs⟩ := hva
  obtain ⟨m, hgen⟩ := exists_generating_secs_tens_lbPow H.φ.isLB A.φ.isLB hs
  obtain ⟨φ₁, hφ₁, hφ₁'⟩ := GlobalTheory.weight_cInf_semiPos_of_generated F X p σ _ (A.φ.tens (H.φ.pow m)).isLB hgen
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.smooth_weights_differ_by_smooth_function F X p σ _ φ₁ (A.φ.tens (H.φ.pow m)) hφ₁ (A.cInf.tens (H.cInf.zpow m))
  obtain ⟨v, hv, hv'⟩ := GlobalTheory.ClosedExt.exists_extension F _ X (PSpace.str F N) p σ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩ ι hp u hu
  obtain ⟨m', hm'⟩ := GlobalTheory.T.exists_semiPos_fubiniStudy_power_add_smooth_fn F σ N v hv
  have hwc : ((O.φ.pow m').addFn v).IsCInf := (O.cInf.zpow m').addFn hv
  have hw : (((O.φ.pow m').addFn v).pull ι hp).SemiPosReg D :=
    GlobalTheory.Weight.semiPosReg_pull F _ _ _ _ σ ι hp N D hsm _ _ hwc (hm' m' le_rfl)
  refine ⟨⟨_, (H.φ.pow m).tens (H.φ.pow m'), (H.cInf.zpow m).tens (H.cInf.zpow m')⟩,
    Weight.SemiPosReg.tens (H.cInf.zpow m) (H.cInf.zpow m') (hpow m) (hpow m'), ?_⟩
  refine semiPosReg_of_eqOn_charts (A.φ.tens ((H.φ.pow m).tens (H.φ.pow m')))
    (Weight.SemiPosReg.tens hφ₁ (hwc.pull ι hp) (hφ₁' D) hw)
    (fun i => ((i.1, i.2.1), i.2.2)) (fun i y hy => ?_) fun i y hy => ?_
  · obtain ⟨h₁, h₂⟩ := mem_ptsIn_inf.1 hy
    obtain ⟨h₂, h₃⟩ := mem_ptsIn_inf.1 h₂
    refine mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨h₁, h₂⟩, ?_⟩
    have h₄ := mem_pow_iff.1 h₃
    exact mem_ptsIn.2 (Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun b => Set.mem_iInter.1 (mem_ptsIn.1 h₄) b)
  · obtain ⟨h₁, h₂⟩ := mem_ptsIn_inf.1 hy
    obtain ⟨h₂, h₃⟩ := mem_ptsIn_inf.1 h₂
    have e₁ : A.φ.φ i.1 y + (H.φ.pow m).φ i.2.1 y = φ₁.φ (i.1, i.2.1) y + u y :=
      hu' (i.1, i.2.1) y (mem_ptsIn_inf.2 ⟨h₁, h₂⟩)
    have e₂ : (H.φ.pow m').φ i.2.2 y = (O.φ.pow m').φ (i.2.2 PUnit.unit) (ptMap ι hp σ y) :=
      (H.φ.zpow_φ m' i.2.2 y).trans ((congrArg (_ * ·) (O.φ.pull_φ ι hp (i.2.2 PUnit.unit) y)).trans
        (O.φ.zpow_φ m' (i.2.2 PUnit.unit) _).symm)
    have e₃ : (((O.φ.pow m').addFn v).pull ι hp).φ i.2.2 y =
        (O.φ.pow m').φ (i.2.2 PUnit.unit) (ptMap ι hp σ y) + v (ptMap ι hp σ y) :=
      ((O.φ.pow m').addFn v).pull_φ ι hp i.2.2 y
    change A.φ.φ i.1 y + ((H.φ.pow m).φ i.2.1 y + (H.φ.pow m').φ i.2.2 y) =
      φ₁.φ (i.1, i.2.1) y + (((O.φ.pow m').addFn v).pull ι hp).φ i.2.2 y
    rw [e₃, hv', e₂, ← add_assoc, e₁]
    ring

end GlobalTheory.Mix
