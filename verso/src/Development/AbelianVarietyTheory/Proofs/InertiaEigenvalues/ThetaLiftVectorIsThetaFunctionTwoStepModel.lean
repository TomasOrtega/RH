import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompTensorHalf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesDisjointTwistPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameIntegralIffPartsConjHalfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionAdjointFrameConjHalfTwoPartsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.TwoStepModel

open GlobalTheory.ExportSeries

/- English proof (translation)
Establish `hA` using `GlobalTheory.T.adjointFrame_integral_iff_parts_conj_half D S T βS βT Pg Q eg eQ hg hq hd he`. Establish `hB` using `GlobalTheory.T.reduction_adjointFrame_conj_half_two_parts D S T βS βT Pg Q eg eQ hg hq hd he`. Establish `heg` using `GlobalTheory.PlaceVec.idemSum_mul_self hg`. Establish `heQ` using `GlobalTheory.PlaceVec.idemSum_mul_self hq`. Establish `hcg : ∀ x : WO S T, IsHalf (cA D eg) (cA D eg • x)` using `fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heg]) x`.

Establish `hcQ : ∀ x : WO S T, IsHalf (cA D eQ) (cA D eQ • x)` using `fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heQ]) x`. Use function extensionality and compare the values at `x`. Rewrite using `[tensorHalf_apply]`. Establish `hc : cA D (eg + eQ) = cA D eQ + cA D eg` using `by rw [map_add, add_comm]`. Distinguish the cases in `hx : IsHalf (cA D (eg + eQ)) x`.

Establish `hx' : IsHalf (cA D eQ + cA D eg) x` using `hc ▸ hx`. Rewrite using `[if_pos hx', mul_one]`. Distinguish the cases in `hi : IsIntM (frMapAdj S T βS βT x)`. Take `⟨i1, i2⟩` from `(hA x hx).1 hi`. Take `⟨r1, r2⟩` from `hB x hx hi`.

Establish `c1 : IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x)` using `⟨hx, hi⟩`. Establish `c2 : IsHalf (cA D eQ) (cA D eQ • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x))` using `⟨hcQ x, i2⟩`. Establish `c3 : IsHalf (cA D eg) (cA D eg • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eg • x))` using `⟨hcg x, i1⟩`. Rewrite using `[if_pos c1, if_pos c2, if_pos c3, mul_comm]`. Use `congr 1`.

Conclude with `GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => (r2 PP hPP).symm`. Conclude with `GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => (r1 PP hPP).symm`. Establish `c1 : ¬ (IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x))` using `fun h => hi h.2`. Rewrite using `[if_neg c1]`. Use `mt (hA x hx).2 hi` as an intermediate fact.

Break down `not_and_or.1 this with h | h` into its components or cases. Establish `c3 : ¬ (IsHalf (cA D eg) (cA D eg • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eg • x)))` using `fun h' => h h'.2`. Rewrite using `[if_neg c3, mul_zero]`. Establish `c2 : ¬ (IsHalf (cA D eQ) (cA D eQ • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x)))` using `fun h' => h h'.2`. Rewrite using `[if_neg c2, zero_mul]`.

Establish `c1 : ¬ (IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x))` using `fun h => hx h.1`. Establish `hx' : ¬ IsHalf (cA D eQ + cA D eg) x` using `hc ▸ hx`. Rewrite using `[if_neg c1, if_neg hx', mul_zero]`.
-/
theorem datum_eq_tensorHalf {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {Pg Q : Finset (Pl D.host.E)} {eg eQ : AE D} (hg : IsIdemSum eg Pg) (hq : IsIdemSum eQ Q) (hd : Disjoint Pg Q)
    (he : IsIdemSum (eg + eQ) (Pg ∪ Q)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    (fun x => if IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x) then
        omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
          omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) else 0) =
      tensorHalf (cA D eQ) (cA D eg)
        (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj S T βS βT x) then
          omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) else 0)
        (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj S T βS βT x) then
          omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) else 0) := by
  have hA := GlobalTheory.T.adjointFrame_integral_iff_parts_conj_half D S T βS βT Pg Q eg eQ hg hq hd he
  have hB := GlobalTheory.T.reduction_adjointFrame_conj_half_two_parts D S T βS βT Pg Q eg eQ hg hq hd he
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hcg : ∀ x : WO S T, IsHalf (cA D eg) (cA D eg • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heg]) x
  have hcQ : ∀ x : WO S T, IsHalf (cA D eQ) (cA D eQ • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heQ]) x
  funext x
  rw [tensorHalf_apply]
  have hc : cA D (eg + eQ) = cA D eQ + cA D eg := by rw [map_add, add_comm]
  by_cases hx : IsHalf (cA D (eg + eQ)) x
  · have hx' : IsHalf (cA D eQ + cA D eg) x := hc ▸ hx
    rw [if_pos hx', mul_one]
    by_cases hi : IsIntM (frMapAdj S T βS βT x)
    · obtain ⟨i1, i2⟩ := (hA x hx).1 hi
      obtain ⟨r1, r2⟩ := hB x hx hi
      have c1 : IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x) := ⟨hx, hi⟩
      have c2 : IsHalf (cA D eQ) (cA D eQ • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x)) := ⟨hcQ x, i2⟩
      have c3 : IsHalf (cA D eg) (cA D eg • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eg • x)) := ⟨hcg x, i1⟩
      rw [if_pos c1, if_pos c2, if_pos c3, mul_comm]
      congr 1
      · exact GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => (r2 PP hPP).symm
      · exact GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => (r1 PP hPP).symm
    · have c1 : ¬ (IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x)) := fun h => hi h.2
      rw [if_neg c1]
      have := mt (hA x hx).2 hi
      rcases not_and_or.1 this with h | h
      · have c3 : ¬ (IsHalf (cA D eg) (cA D eg • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eg • x))) := fun h' => h h'.2
        rw [if_neg c3, mul_zero]
      · have c2 : ¬ (IsHalf (cA D eQ) (cA D eQ • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x))) := fun h' => h h'.2
        rw [if_neg c2, zero_mul]
  · have c1 : ¬ (IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x)) := fun h => hx h.1
    have hx' : ¬ IsHalf (cA D eQ + cA D eg) x := hc ▸ hx
    rw [if_neg c1, if_neg hx', mul_zero]

end GlobalTheory.TwoStepModel

namespace GlobalTheory.ConjTwist

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hC _hG i t eg eQ fg hg hq hfg`. Take `⟨⟨hψ, -⟩, e, he, hTe⟩` from `hC.thP.vP i t`. Establish `hSV` using `GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))`. Establish `hSW` using `GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))`. Establish `hd` using `GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces R F hC t`.

Establish `hsum : e = eg + eQ`. Rewrite using `[← GlobalTheory.ExportSeries.idem_eq he, ← GlobalTheory.ExportSeries.idem_eq hg, ← GlobalTheory.ExportSeries.idem_eq hq]`. Conclude with `Finset.sum_union hd`. Substitute `hsum` using the available equality. Establish `heg` using `GlobalTheory.PlaceVec.idemSum_mul_self hg`.

Establish `heQ` using `GlobalTheory.PlaceVec.idemSum_mul_self hq`. Establish `hee` using `GlobalTheory.PlaceVec.idemSum_mul_self he`. Establish `hgQ : eg * eQ = 0`. Use `GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_` and prove the remaining obligations. Use `push_cast`.

Take the linear combination `hee - heg - heQ`. Establish `hcg : cA D eg * cA D eg = cA D eg` using `by rw [← map_mul, heg]`. Establish `hcQ : cA D eQ * cA D eQ = cA D eQ` using `by rw [← map_mul, heQ]`. Establish `hQg : cA D eQ * cA D eg = 0` using `by rw [← map_mul, mul_comm, hgQ, map_zero]`. Establish `hgQ' : cA D eg * cA D eQ = 0` using `by rw [mul_comm, hQg]`.

Establish `hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True), a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True)` using `fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu`. Establish `hinfg : infPart D (cA D eg) = 0` using `GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)`. Establish `hinfQ : infPart D (cA D eQ) = 0` using `GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hq)`. Establish `hSBg` using `GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _) R.Pg (fun y => omegaK R.Pg y) fun y y' h = …`. Establish `hSBQ` using `GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinfQ (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _) (R.Q t) (fun y => omegaQ (R.Q t) (Wc D i). …`.

Take `⟨⟨Te, hTe1⟩, hTe2⟩` from `hTe`. Establish `hc : cA D (eg + eQ) = cA D eQ + cA D eg` using `by rw [map_add, add_comm]`. Establish `hc' : cA D (eg + eQ) = cA D eg + cA D eQ` using `map_add _ _ _`. Establish `hm1` using `GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hcQ hcg hQg hΛ hSBg (hc ▸ hTe1)`. Establish `hm2` using `GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hcg hcQ hgQ' hΛ (hc' ▸ hTe1)`.

Establish `hbase` using `hfg.2 _ hm2`. Simplify using `only [LinearMap.comp_apply] at hbase`. Rewrite `hm1` using `[← hbase]`. Use `⟨⟨_, hm1⟩, fun T' hT' => ?_⟩` and prove the remaining obligations. Rewrite using `[hTe2 Te hTe1, GlobalTheory.TwoStepModel.datum_eq_tensorHalf (R.βV i) (R.βW i) hg hq hd he (R.xiR t)]`.

Conclude with `GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hcQ hinfQ hm1 hT' hSBQ`.
-/
theorem isThetaAt_vP_twoStep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0) (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ (R.Q t) → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _hG i t eg eQ fg hg hq hfg
  obtain ⟨⟨hψ, -⟩, e, he, hTe⟩ := hC.thP.vP i t
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hd := GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces R F hC t
  have hsum : e = eg + eQ := by
    rw [← GlobalTheory.ExportSeries.idem_eq he, ← GlobalTheory.ExportSeries.idem_eq hg, ← GlobalTheory.ExportSeries.idem_eq hq]
    exact Finset.sum_union hd
  subst hsum
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hgQ : eg * eQ = 0 := by
    refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
    push_cast
    linear_combination hee - heg - heQ
  have hcg : cA D eg * cA D eg = cA D eg := by rw [← map_mul, heg]
  have hcQ : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, heQ]
  have hQg : cA D eQ * cA D eg = 0 := by rw [← map_mul, mul_comm, hgQ, map_zero]
  have hgQ' : cA D eg * cA D eQ = 0 := by rw [mul_comm, hQg]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True),
      a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) :=
    fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  have hinfg : infPart D (cA D eg) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
  have hinfQ : infPart D (cA D eQ) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hq)
  have hSBg := GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    R.Pg (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h
  have hSBQ := GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinfQ (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    (R.Q t) (fun y => omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  obtain ⟨⟨Te, hTe1⟩, hTe2⟩ := hTe
  have hc : cA D (eg + eQ) = cA D eQ + cA D eg := by rw [map_add, add_comm]
  have hc' : cA D (eg + eQ) = cA D eg + cA D eQ := map_add _ _ _
  have hm1 := GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hcQ hcg hQg hΛ hSBg (hc ▸ hTe1)
  have hm2 := GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hcg hcQ hgQ' hΛ (hc' ▸ hTe1)
  have hbase := hfg.2 _ hm2
  simp only [LinearMap.comp_apply] at hbase
  rw [← hbase] at hm1
  refine ⟨⟨_, hm1⟩, fun T' hT' => ?_⟩
  rw [hTe2 Te hTe1, GlobalTheory.TwoStepModel.datum_eq_tensorHalf (R.βV i) (R.βW i) hg hq hd he (R.xiR t)]
  exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hcQ hinfQ hm1 hT' hSBQ

end GlobalTheory.ConjTwist

end
