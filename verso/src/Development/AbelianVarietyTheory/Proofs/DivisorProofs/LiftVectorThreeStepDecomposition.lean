import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppAtMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorIsThetaFunctionTwoStepModel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameIntegralIffPartsConjHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionAdjointFrameConjHalfTwoParts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentSumSubsetAndConjugateFlip
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.LiftThreeStep

/- English proof (translation)
Set `g : Pl D.host.E → ℂ` to `fun PP => if h : LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ k else 0`. Establish `key : ∀ Q : Finset (Pl D.host.E), omegaQ Q r ξ k y = ∏ PP ∈ Q, g PP`. Introduce `Q`. Unfold `omegaQ`. Distinguish the cases in `h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det`.

Rewrite using `[dif_pos h, ← Finset.prod_attach Q g]`. Use `Finset.prod_congr rfl fun PP _ => ?_` and prove the remaining obligations. Simplify using `only [g]`. Rewrite using `[dif_pos (h PP.1 PP.2)]`. Rewrite using `[dif_neg h]`.

Take `⟨PP, hPP⟩` from `not_forall.1 h`. Take `⟨hQ, hn⟩` from `Classical.not_imp.1 hPP`. Use `(Finset.prod_eq_zero hQ ?_).symm` and prove the remaining obligations. Simplify using `only [g]`. Rewrite using `[dif_neg hn]`.

Rewrite using `[key, key, key, Finset.prod_union hd]`.
-/
theorem omegaQ_union {D : D7} {a b : ℕ} {Sa St : Finset (Pl D.host.E)} (hd : Disjoint Sa St) (r : ℕ)
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaQ (Sa ∪ St) r ξ k y = omegaQ Sa r ξ k y * omegaQ St r ξ k y := by
  let g : Pl D.host.E → ℂ := fun PP =>
    if h : LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ k else 0
  have key : ∀ Q : Finset (Pl D.host.E), omegaQ Q r ξ k y = ∏ PP ∈ Q, g PP := by
    intro Q
    unfold omegaQ
    by_cases h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
    · rw [dif_pos h, ← Finset.prod_attach Q g]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp only [g]
      rw [dif_pos (h PP.1 PP.2)]
    · rw [dif_neg h]
      obtain ⟨PP, hPP⟩ := not_forall.1 h
      obtain ⟨hQ, hn⟩ := Classical.not_imp.1 hPP
      refine (Finset.prod_eq_zero hQ ?_).symm
      simp only [g]
      rw [dif_neg hn]
  rw [key, key, key, Finset.prod_union hd]

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

/- English proof (translation)
Establish `hA` using `GlobalTheory.ConjHalfSplitInt.frMapAdj_int_iff D _ _ (R.βV i) (R.βW i) Sa St ea et hg hq hd he`. Establish `hB` using `GlobalTheory.TwoStepRed.redM_twoStep D _ _ (R.βV i) (R.βW i) Sa St ea et hg hq hd he`. Establish `heg` using `GlobalTheory.PlaceVec.idemSum_mul_self hg`. Establish `heQ` using `GlobalTheory.PlaceVec.idemSum_mul_self hq`. Establish `hcg : ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D ea) (cA D ea • x)` using `fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heg]) x`.

Establish `hcQ : ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D et) (cA D et • x)` using `fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heQ]) x`. Use function extensionality and compare the values at `x`. Rewrite using `[GlobalTheory.TwoStepModel.tensorHalf_apply]`. Unfold `adjDat`. Establish `hc : cA D (ea + et) = cA D et + cA D ea` using `by rw [map_add, add_comm]`.

Distinguish the cases in `hx : IsHalf (cA D (ea + et)) x`. Establish `hx' : IsHalf (cA D et + cA D ea) x` using `hc ▸ hx`. Rewrite using `[if_pos hx', mul_one]`. Distinguish the cases in `hi : IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)`. Take `⟨i1, i2⟩` from `(hA x hx).1 hi`.

Take `⟨r1, r2⟩` from `hB x hx hi`. Rewrite using `[if_pos (And.intro hx hi), if_pos (And.intro (hcQ x) i2), if_pos (And.intro (hcg x) i1), omegaQ_union hd, mul_comm]`. Use `congr 1`. Conclude with `GlobalTheory.PlaceVec.omegaQ_congr St _ ξ _ fun PP hPP => (r2 PP hPP).symm`. Conclude with `GlobalTheory.PlaceVec.omegaQ_congr Sa _ ξ _ fun PP hPP => (r1 PP hPP).symm`.

Establish `c1 : ¬ (IsHalf (cA D (ea + et)) x ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x))` using `fun h => hi h.2`. Rewrite using `[if_neg c1]`. Use `mt (hA x hx).2 hi` as an intermediate fact. Break down `not_and_or.1 this with h | h` into its components or cases. Establish `c3 : ¬ (IsHalf (cA D ea) (cA D ea • x) ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) (cA D ea • x)))` using `fun h' => h h'.2`.

Rewrite using `[if_neg c3, mul_zero]`. Establish `c2 : ¬ (IsHalf (cA D et) (cA D et • x) ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) (cA D et • x)))` using `fun h' => h h'.2`. Rewrite using `[if_neg c2, zero_mul]`. Establish `c1 : ¬ (IsHalf (cA D (ea + et)) x ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x))` using `fun h => hx h.1`. Establish `hx' : ¬ IsHalf (cA D et + cA D ea) x` using `hc ▸ hx`.

Rewrite using `[if_neg c1, if_neg hx', mul_zero]`.
-/
theorem adjDat_union {Sa St : Finset (Pl D.host.E)} {ea et : AE D} (hg : IsIdemSum ea Sa) (hq : IsIdemSum et St)
    (hd : Disjoint Sa St) (he : IsIdemSum (ea + et) (Sa ∪ St)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    adjDat R i (Sa ∪ St) ξ (cA D (ea + et)) =
      GlobalTheory.TwoStepModel.tensorHalf (cA D et) (cA D ea) (adjDat R i Sa ξ (cA D ea)) (adjDat R i St ξ (cA D et)) := by
  have hA := GlobalTheory.ConjHalfSplitInt.frMapAdj_int_iff D _ _ (R.βV i) (R.βW i) Sa St ea et hg hq hd he
  have hB := GlobalTheory.TwoStepRed.redM_twoStep D _ _ (R.βV i) (R.βW i) Sa St ea et hg hq hd he
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hcg : ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D ea) (cA D ea • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heg]) x
  have hcQ : ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D et) (cA D et • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heQ]) x
  funext x
  rw [GlobalTheory.TwoStepModel.tensorHalf_apply]
  unfold adjDat
  have hc : cA D (ea + et) = cA D et + cA D ea := by rw [map_add, add_comm]
  by_cases hx : IsHalf (cA D (ea + et)) x
  · have hx' : IsHalf (cA D et + cA D ea) x := hc ▸ hx
    rw [if_pos hx', mul_one]
    by_cases hi : IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)
    · obtain ⟨i1, i2⟩ := (hA x hx).1 hi
      obtain ⟨r1, r2⟩ := hB x hx hi
      rw [if_pos (And.intro hx hi), if_pos (And.intro (hcQ x) i2), if_pos (And.intro (hcg x) i1), omegaQ_union hd, mul_comm]
      congr 1
      · exact GlobalTheory.PlaceVec.omegaQ_congr St _ ξ _ fun PP hPP => (r2 PP hPP).symm
      · exact GlobalTheory.PlaceVec.omegaQ_congr Sa _ ξ _ fun PP hPP => (r1 PP hPP).symm
    · have c1 : ¬ (IsHalf (cA D (ea + et)) x ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)) := fun h => hi h.2
      rw [if_neg c1]
      have := mt (hA x hx).2 hi
      rcases not_and_or.1 this with h | h
      · have c3 : ¬ (IsHalf (cA D ea) (cA D ea • x) ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) (cA D ea • x))) :=
          fun h' => h h'.2
        rw [if_neg c3, mul_zero]
      · have c2 : ¬ (IsHalf (cA D et) (cA D et • x) ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) (cA D et • x))) :=
          fun h' => h h'.2
        rw [if_neg c2, zero_mul]
  · have c1 : ¬ (IsHalf (cA D (ea + et)) x ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)) := fun h => hx h.1
    have hx' : ¬ IsHalf (cA D et + cA D ea) x := hc ▸ hx
    rw [if_neg c1, if_neg hx', mul_zero]

end

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i t _ Sa St hd hU eg ea et fg hg ha ht hfg`. Take `⟨⟨hψ, -⟩, e, he, -⟩` from `hC.thP.vP i t`. Establish `hSV` using `GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))`. Establish `hSW` using `GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))`. Take `⟨eQ, hq⟩` from `(GlobalTheory.IdemFlip.idemSum_sub_and_flip D e _ (R.Q t) he Finset.subset_union_right).1`.

Establish `h2 : ThAt R i (cA D eQ) fg (adjDat R i (R.Q t) (R.xiR t) (cA D eQ)) (R.vP i t)` using `GlobalTheory.ConjTwist.isThetaAt_vP_twoStep D G Pl0 T0 A Ks R F hC hG i t eg eQ fg hg hq hfg`. Rewrite `hq`, `h2` using `[← hU]`. Establish `hsum : eQ = ea + et`. Rewrite using `[← GlobalTheory.ExportSeries.idem_eq hq, ← GlobalTheory.ExportSeries.idem_eq ha, ← GlobalTheory.ExportSeries.idem_eq ht]`. Conclude with `Finset.sum_union hd`.

Substitute `hsum` using the available equality. Establish `hea` using `GlobalTheory.PlaceVec.idemSum_mul_self ha`. Establish `het` using `GlobalTheory.PlaceVec.idemSum_mul_self ht`. Establish `hee` using `GlobalTheory.PlaceVec.idemSum_mul_self hq`. Establish `hat : ea * et = 0`.

Use `GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_` and prove the remaining obligations. Use `push_cast`. Take the linear combination `hee - hea - het`. Establish `hca : cA D ea * cA D ea = cA D ea` using `by rw [← map_mul, hea]`. Establish `hct : cA D et * cA D et = cA D et` using `by rw [← map_mul, het]`.

Establish `hta : cA D et * cA D ea = 0` using `by rw [← map_mul, mul_comm, hat, map_zero]`. Establish `hat' : cA D ea * cA D et = 0` using `by rw [mul_comm, hta]`. Establish `hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True), a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True)` using `fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu`. Establish `hinfa : infPart D (cA D ea) = 0` using `GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ha)`. Establish `hinft : infPart D (cA D et) = 0` using `GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ht)`.

Establish `hSB : ∀ (Q : Finset (Pl D.host.E)) (a : AE D), infPart D a = 0 → IsSBHalf a (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (adjDat R i Q (R.xiR t) a)` using `fun Q a hinf => GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinf (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _) Q (fun y => omegaQ Q (Wc D …`. Take `⟨⟨Te, hTe1⟩, hTe2⟩` from `h2`. Establish `hc : cA D (ea + et) = cA D et + cA D ea` using `by rw [map_add, add_comm]`. Establish `hc' : cA D (ea + et) = cA D ea + cA D et` using `map_add _ _ _`. Establish `hm1` using `GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hct hca hta hΛ (hSB Sa _ hinfa) (hc ▸ hTe1)`.

Establish `hm2` using `GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hca hct hat' hΛ (hc' ▸ hTe1)`. Use `⟨_, ⟨⟨_, hm2⟩, fun T' hT' => ?_⟩, ⟨_, hm1⟩, fun T' hT' => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hca hinfa hm2 hT' (hSB Sa _ hinfa)`. Rewrite using `[hTe2 Te hTe1, adjDat_union R i ha ht hd hq (R.xiR t)]`. Conclude with `GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hct hinft hm1 hT' (hSB St _ hinft)`.
-/
theorem thetaVector_three_step_decomposition : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Disjoint Sa St → Sa ∪ St = R.Q t → ∀ (eg ea et : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ gA : WO (Vc D i) (Wc D i) → ℂ, ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) gA ∧ ThAt R i (cA D et) gA (adjDat R i St (R.xiR t) (cA D et)) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i t _ Sa St hd hU eg ea et fg hg ha ht hfg
  obtain ⟨⟨hψ, -⟩, e, he, -⟩ := hC.thP.vP i t
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  obtain ⟨eQ, hq⟩ := (GlobalTheory.IdemFlip.idemSum_sub_and_flip D e _ (R.Q t) he Finset.subset_union_right).1
  have h2 : ThAt R i (cA D eQ) fg (adjDat R i (R.Q t) (R.xiR t) (cA D eQ)) (R.vP i t) :=
    GlobalTheory.ConjTwist.isThetaAt_vP_twoStep D G Pl0 T0 A Ks R F hC hG i t eg eQ fg hg hq hfg
  rw [← hU] at hq h2
  have hsum : eQ = ea + et := by
    rw [← GlobalTheory.ExportSeries.idem_eq hq, ← GlobalTheory.ExportSeries.idem_eq ha, ← GlobalTheory.ExportSeries.idem_eq ht]
    exact Finset.sum_union hd
  subst hsum
  have hea := GlobalTheory.PlaceVec.idemSum_mul_self ha
  have het := GlobalTheory.PlaceVec.idemSum_mul_self ht
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hat : ea * et = 0 := by
    refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
    push_cast
    linear_combination hee - hea - het
  have hca : cA D ea * cA D ea = cA D ea := by rw [← map_mul, hea]
  have hct : cA D et * cA D et = cA D et := by rw [← map_mul, het]
  have hta : cA D et * cA D ea = 0 := by rw [← map_mul, mul_comm, hat, map_zero]
  have hat' : cA D ea * cA D et = 0 := by rw [mul_comm, hta]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True),
      a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) :=
    fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  have hinfa : infPart D (cA D ea) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ha)
  have hinft : infPart D (cA D et) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ht)
  have hSB : ∀ (Q : Finset (Pl D.host.E)) (a : AE D), infPart D a = 0 →
      IsSBHalf a (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (adjDat R i Q (R.xiR t) a) :=
    fun Q a hinf => GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinf (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
      Q (fun y => omegaQ Q (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  obtain ⟨⟨Te, hTe1⟩, hTe2⟩ := h2
  have hc : cA D (ea + et) = cA D et + cA D ea := by rw [map_add, add_comm]
  have hc' : cA D (ea + et) = cA D ea + cA D et := map_add _ _ _
  have hm1 := GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hct hca hta hΛ (hSB Sa _ hinfa) (hc ▸ hTe1)
  have hm2 := GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hca hct hat' hΛ (hc' ▸ hTe1)
  refine ⟨_, ⟨⟨_, hm2⟩, fun T' hT' => ?_⟩, ⟨_, hm1⟩, fun T' hT' => ?_⟩
  · exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hca hinfa hm2 hT' (hSB Sa _ hinfa)
  · rw [hTe2 Te hTe1, adjDat_union R i ha ht hd hq (R.xiR t)]
    exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hct hinft hm1 hT' (hSB St _ hinft)

end GlobalTheory.LiftThreeStep

end
