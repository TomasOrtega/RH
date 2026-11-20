import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecomp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KappaOffDiagonal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormAll

noncomputable section

open scoped Classical
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.LoopBPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X}

/- English proof (translation)
Take `⟨hm, hex, huniq⟩` from `KappaOffDiagonal.fundOf_spec (Closed.FundExistsC_holds D X Y u u') s`. Use `⟨hm, fun r _ => ?_⟩` and prove the remaining obligations. Take `⟨q, hq, hqr⟩` from `hex r`. Use `⟨q, ⟨hq, hqr⟩, fun q' hq' => ?_⟩` and prove the remaining obligations. Establish `hmem : q' * q⁻¹ ∈ TermOp.ROinf s` using `(TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin).mul_mem hq'.1 ((TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin).inv_mem hq)`.

Establish `e : q' * q⁻¹ * (q * r) = q' * r` using `by group`. Establish `h1` using `huniq (q * r) hqr (q' * q⁻¹) hmem (by rw [e]; exact hq'.2)`. Conclude with `mul_inv_eq_one.1 h1`.
-/
theorem isFundR_fundOf {u u' : D.what₂.Word} (s : TT Y u u') : LoopTerm.IsFundR s (TermOp.FundOf s) := by
  obtain ⟨hm, hex, huniq⟩ := KappaOffDiagonal.fundOf_spec (Closed.FundExistsC_holds D X Y u u') s
  refine ⟨hm, fun r _ => ?_⟩
  obtain ⟨q, hq, hqr⟩ := hex r
  refine ⟨q, ⟨hq, hqr⟩, fun q' hq' => ?_⟩
  have hmem : q' * q⁻¹ ∈ TermOp.ROinf s :=
    (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin).mul_mem hq'.1
      ((TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin).inv_mem hq)
  have e : q' * q⁻¹ * (q * r) = q' * r := by group
  have h1 := huniq (q * r) hqr (q' * q⁻¹) hmem (by rw [e]; exact hq'.2)
  exact mul_inv_eq_one.1 h1

/- English proof (translation)
Introduce `s hrel hG`. Establish `hAt` using `LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u'`. Establish `hRD` using `Pf.RowForm.RealDecompL.realDecompC_of X Y u u' hAt`. Take `⟨hpt, g, hg, g', hg', hdec⟩` from `Pf.RowForm.realDecompC_gamW X Y u u' hRD s hrel hG`. Take `⟨μw, hH, hmap⟩` from `NGPin.pinned_at X u u' (NGPin.pinHaarEx_of_place NGPin.placeHaar_holds) hpt`.

Take `⟨w0, hw0⟩` from `hAt s.toTerm hG hrel`. Establish `hw : s.toTerm.atPt (PairVal.ptOf s.toTerm)` using `PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩`. Use `⟨⟨PairVal.ptOf s.toTerm, μw.map (fun y => g * y * g⁻¹), TermOp.FundOf s⟩, hw, ?_, isFundR_fundOf s⟩` and prove the remaining obligations. Conclude with `⟨RealObj.gamW X u u' (PairVal.ptOf s.toTerm), g, g', μw, NGPin.isPtRep_gamW X u u' hpt, hg, hg', hdec, hH, hmap, rfl⟩`.
-/
theorem pinAll_holds (u u' : D.what₂.Word) : LoopTerm.PinAll (Y := Y) u u' := by
  intro s hrel hG
  have hAt := LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u'
  have hRD := Pf.RowForm.RealDecompL.realDecompC_of X Y u u' hAt
  obtain ⟨hpt, g, hg, g', hg', hdec⟩ := Pf.RowForm.realDecompC_gamW X Y u u' hRD s hrel hG
  obtain ⟨μw, hH, hmap⟩ := NGPin.pinned_at X u u' (NGPin.pinHaarEx_of_place NGPin.placeHaar_holds) hpt
  obtain ⟨w0, hw0⟩ := hAt s.toTerm hG hrel
  have hw : s.toTerm.atPt (PairVal.ptOf s.toTerm) := PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  refine ⟨⟨PairVal.ptOf s.toTerm, μw.map (fun y => g * y * g⁻¹), TermOp.FundOf s⟩, hw, ?_, isFundR_fundOf s⟩
  exact ⟨RealObj.gamW X u u' (PairVal.ptOf s.toTerm), g, g', μw, NGPin.isPtRep_gamW X u u' hpt, hg, hg', hdec, hH,
    hmap, rfl⟩

section Covol

open Set TermOp TermOp.Vanish

/- English proof (translation)
Establish `hs0 : q ∈ ROset X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin` using `hq`. Take `⟨z, n, hz, hzs, hn, hn'⟩` from `hs0`. Establish `hl : RatLink X (s.pt⁻¹ * z * s.pt) (s.lin⁻¹ * n * s.lin)` using `ratLink_mul X (ratLink_mul X (ratLink_inv X s.rep.2.1) hz) s.rep.2.1`. Establish `hs2` using `Pf.nLamNinf_holds D X u' s.lam' _ _ hl hn'`. Rewrite `hs2` using `[Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, ← hzs]`.

Conclude with `⟨hzs ▸ Pf.nLamNinf_holds D X u s.lam z n hz hn, hs2⟩`.
-/
theorem roinf_sub_rset {u u' : D.what₂.Word} (s : TT Y u u') {q : X.B.I.Ginf} (hq : q ∈ ROinf s) : q ∈ Rset s := by
  have hs0 : q ∈ ROset X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin := hq
  obtain ⟨z, n, hz, hzs, hn, hn'⟩ := hs0
  have hl : RatLink X (s.pt⁻¹ * z * s.pt) (s.lin⁻¹ * n * s.lin) :=
    ratLink_mul X (ratLink_mul X (ratLink_inv X s.rep.2.1) hz) s.rep.2.1
  have hs2 := Pf.nLamNinf_holds D X u' s.lam' _ _ hl hn'
  rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, ← hzs] at hs2
  exact ⟨hzs ▸ Pf.nLamNinf_holds D X u s.lam z n hz hn, hs2⟩

/- English proof (translation)
Unfold `RealObj.stCoord Formalism.L2.SG.HidaSetting.hJ`. Use `continuous_pi fun v => continuous_pi fun p => continuous_const.mul ?_` and prove the remaining obligations. Use `Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_const ?_)` and prove the remaining obligations. Use `Continuous.matrix_mulVec ?_ continuous_const` and prove the remaining obligations. Conclude with `Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply v).comp ((continuous_const.mul continuous_id).mul continuous_const)))`.
-/
theorem stCoord_cont (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) :
    Continuous (RealObj.stCoord X u' w γ) := by
  unfold RealObj.stCoord Formalism.L2.SG.HidaSetting.hJ
  refine continuous_pi fun v => continuous_pi fun p => continuous_const.mul ?_
  refine Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_const ?_)
  refine Continuous.matrix_mulVec ?_ continuous_const
  exact Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply v).comp
    ((continuous_const.mul continuous_id).mul continuous_const)))

/- English proof (translation)
Establish `e : RealObj.muStab X w = Measure.pi fun _ => Measure.pi fun _ => ((D.host.ka / (X.B.g : ℝ) / Real.pi).toNNReal) • (volume : Measure ℂ)` using `rfl`. Rewrite using `[e]`. Conclude with `hC.measure_lt_top`.
-/
theorem muStab_compact (w : Point D.host.E (D.R.rS + 1)) {C : Set (InfinitePlace X.B.I.F → RealObj.FreeE w → ℂ)}
    (hC : IsCompact C) : RealObj.muStab X w C < ⊤ := by
  have e : RealObj.muStab X w = Measure.pi fun _ => Measure.pi fun _ =>
      ((D.host.ka / (X.B.g : ℝ) / Real.pi).toNNReal) • (volume : Measure ℂ) := rfl
  rw [e]
  exact hC.measure_lt_top

/- English proof (translation)
Introduce `s hrel hG w μR K hw hP hK`. Take `⟨γw, g, g', μw, hrep, hg, hg', hdec, hH, hmap, rfl⟩` from `hP`. Take `⟨hσ, h0, hconc, hinvw⟩` from `hH`. Take `⟨hKm, hKu⟩` from `hK`. Use `TermOp.Vanish.ROsub_countable X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin` as an intermediate fact.

Establish `hcc : Continuous fun y : X.B.I.Ginf => g * y * g⁻¹` using `(continuous_const.mul continuous_id).mul continuous_const`. Establish `hcm` using `hcc.measurable`. Establish `hRm : MeasurableSet (Rset s)` using `(Pf.rClosedC_holds D X Y u u' s).measurableSet`. Establish `hRc : (μw.map fun y => g * y * g⁻¹) (Rset s)ᶜ = 0`. Rewrite using `[Measure.map_apply hcm hRm.compl]`.

Conclude with `measure_mono_null (fun y hy hySt => hy (LoopTerm.stInf_conj hg hg' hdec hySt)) hconc`. Establish `hinv : ∀ q ∈ TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin, (μw.map fun y => g * y * g⁻¹).map (fun x => q * x) = μw.map fun y => g * y * g⁻¹`. Introduce `q hq`. Establish `hq'` using `LoopTerm.stInf_conj_inv hg hg' hdec (roinf_sub_rset s hq)`. Rewrite using `[Measure.map_map (measurable_const_mul q) hcm]`.

Establish `e : (fun x => q * x) ∘ (fun y => g * y * g⁻¹) = (fun y => g * y * g⁻¹) ∘ (fun y => (g⁻¹ * q * g) * y)`. Use function extensionality and compare the values at `y`. Simplify using `only [Function.comp]`. Use `group`. Rewrite using `[e, ← Measure.map_map hcm (measurable_const_mul _), hinvw _ hq']`.

Establish `hpre : ∀ q ∈ TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin, ∀ B, MeasurableSet B → (μw.map fun y => g * y * g⁻¹) ((fun x => q * x) ⁻¹' B) = (μw.map fun y => g * y * g⁻¹) B`. Introduce `q hq B hB`. Rewrite using `[← Measure.map_apply (measurable_const_mul q) hB, hinv q hq]`. Establish `hpos : (μw.map fun y => g * y * g⁻¹) K ≠ 0`. Introduce `hK0`.

Establish `hd` using `Pf.FormAllPf.decomp (μw.map fun y => g * y * g⁻¹) (Rset s) hRc (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) Set.univ K MeasurableSet.univ hKm hKu`. Establish `hz : (μw.map fun y => g * y * g⁻¹) Set.univ = 0`. Rewrite using `[hd]`. Establish `: ∀ q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin, (μw.map fun y => g * y * g⁻¹) (Set.univ ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K) = 0`. Introduce `q`.

Rewrite using `[Set.univ_inter, hpre q q.2 K hKm, hK0]`. Simplify using `only [this, tsum_zero]`. Rewrite `hz` using `[Measure.measure_univ_eq_zero, Measure.map_eq_zero_iff hcm.aemeasurable]`. Conclude with `h0 hz`. Take `⟨K0, hK0c, hK0⟩` from `rational_cocompact_holds D X Y u u' s`.

Establish `hK0m : MeasurableSet K0` using `hK0c.isClosed.measurableSet`. Establish `h1 : (μw.map fun y => g * y * g⁻¹) K ≤ ∑' q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin, (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0)`. Combine the equalities or inequalities in the displayed calculation. Use `measure_mono fun r hr => ?_` and prove the remaining obligations. Take `⟨q, hq, hqr⟩` from `hK0 r hr.2`.

Conclude with `Set.mem_iUnion.2 ⟨⟨q, hq⟩, hr.1, hqr⟩`. Use `_ ≤ _ := measure_iUnion_le _`. Establish `h2 : ∀ q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin, (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) = (μw.map fun y => g * y * g⁻¹) (K0 ∩ (fun x => ((q⁻¹ : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) : X.B.I.Ginf) * …`. Introduce `q`. Establish `hB : MeasurableSet (K0 ∩ (fun x => ((q⁻¹ : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) : X.B.I.Ginf) * x) ⁻¹' K)` using `hK0m.inter (hKm.preimage (measurable_const_mul _))`.

Rewrite using `[← hpre q q.2 _ hB]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Subgroup.coe_inv, inv_mul_cancel_left]`. Conclude with `and_comm`.

Establish `h3` using `Pf.FormAllPf.decomp (μw.map fun y => g * y * g⁻¹) (Rset s) hRc (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) K0 K hK0m hKm hKu`. Establish `h4 : ∑' q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin, (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) = (μw.map fun y => g * y * g⁻¹) K0`. Rewrite using `[h3]`. Repeatedly rewrite using `[h2]`. Conclude with `(Equiv.inv (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin)).tsum_eq (fun q => (μw.map fun y => g * y * g⁻¹) (K0 ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K))`.

Establish `hC : IsCompact ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0)`. Establish `e : (fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0 = (fun k => g⁻¹ * k * g) '' K0`. Use extensionality with `y`. Simplify using `only [Set.mem_preimage, Set.mem_image]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy; exact ⟨g * y * g⁻¹, hy, by group⟩`. Introduce and unpack `⟨k, hk, rfl⟩`. Use `hk using 1` and compare the differences between its conclusion and the goal. Use `group`. Rewrite using `[e]`.

Conclude with `hK0c.image ((continuous_const.mul continuous_id).mul continuous_const)`. Establish `hfin : (μw.map fun y => g * y * g⁻¹) K0 < ⊤`. Rewrite using `[Measure.map_apply hcm hK0m]`. Establish `hsc` using `stCoord_cont u' w γw`. Establish `hI : IsCompact (RealObj.stCoord X u' w γw '' ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0))` using `hC.image hsc`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hmap, Measure.map_apply hsc.measurable hI.isClosed.measurableSet]`. Use `_ < ⊤ := muStab_compact w hI`. Conclude with `ENNReal.toReal_pos hpos (lt_of_le_of_lt (h1.trans_eq h4) hfin).ne`.
-/
theorem covolPos_holds (u u' : D.what₂.Word) : LoopTerm.CovolPos (Y := Y) u u' := by
  intro s hrel hG w μR K hw hP hK
  obtain ⟨γw, g, g', μw, hrep, hg, hg', hdec, hH, hmap, rfl⟩ := hP
  obtain ⟨hσ, h0, hconc, hinvw⟩ := hH
  obtain ⟨hKm, hKu⟩ := hK
  have := TermOp.Vanish.ROsub_countable X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin
  have hcc : Continuous fun y : X.B.I.Ginf => g * y * g⁻¹ := (continuous_const.mul continuous_id).mul continuous_const
  have hcm := hcc.measurable
  have hRm : MeasurableSet (Rset s) := (Pf.rClosedC_holds D X Y u u' s).measurableSet
  have hRc : (μw.map fun y => g * y * g⁻¹) (Rset s)ᶜ = 0 := by
    rw [Measure.map_apply hcm hRm.compl]
    exact measure_mono_null (fun y hy hySt => hy (LoopTerm.stInf_conj hg hg' hdec hySt)) hconc
  have hinv : ∀ q ∈ TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹).map (fun x => q * x) = μw.map fun y => g * y * g⁻¹ := by
    intro q hq
    have hq' := LoopTerm.stInf_conj_inv hg hg' hdec (roinf_sub_rset s hq)
    rw [Measure.map_map (measurable_const_mul q) hcm]
    have e : (fun x => q * x) ∘ (fun y => g * y * g⁻¹) =
        (fun y => g * y * g⁻¹) ∘ (fun y => (g⁻¹ * q * g) * y) := by
      funext y; simp only [Function.comp]; group
    rw [e, ← Measure.map_map hcm (measurable_const_mul _), hinvw _ hq']
  have hpre : ∀ q ∈ TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin, ∀ B, MeasurableSet B →
      (μw.map fun y => g * y * g⁻¹) ((fun x => q * x) ⁻¹' B) = (μw.map fun y => g * y * g⁻¹) B := by
    intro q hq B hB
    rw [← Measure.map_apply (measurable_const_mul q) hB, hinv q hq]

  have hpos : (μw.map fun y => g * y * g⁻¹) K ≠ 0 := by
    intro hK0
    have hd := Pf.FormAllPf.decomp (μw.map fun y => g * y * g⁻¹) (Rset s) hRc
      (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) Set.univ K MeasurableSet.univ hKm hKu
    have hz : (μw.map fun y => g * y * g⁻¹) Set.univ = 0 := by
      rw [hd]
      have : ∀ q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
          (μw.map fun y => g * y * g⁻¹) (Set.univ ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K) = 0 := by
        intro q
        rw [Set.univ_inter, hpre q q.2 K hKm, hK0]
      simp only [this, tsum_zero]
    rw [Measure.measure_univ_eq_zero, Measure.map_eq_zero_iff hcm.aemeasurable] at hz
    exact h0 hz

  obtain ⟨K0, hK0c, hK0⟩ := rational_cocompact_holds D X Y u u' s
  have hK0m : MeasurableSet K0 := hK0c.isClosed.measurableSet
  have h1 : (μw.map fun y => g * y * g⁻¹) K ≤ ∑' q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) := by
    calc (μw.map fun y => g * y * g⁻¹) K = (μw.map fun y => g * y * g⁻¹) (K ∩ Rset s) :=
          (measure_inter_conull hRc).symm
      _ ≤ (μw.map fun y => g * y * g⁻¹) (⋃ q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
            K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) := by
          refine measure_mono fun r hr => ?_
          obtain ⟨q, hq, hqr⟩ := hK0 r hr.2
          exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hr.1, hqr⟩
      _ ≤ _ := measure_iUnion_le _
  have h2 : ∀ q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) =
        (μw.map fun y => g * y * g⁻¹) (K0 ∩ (fun x => ((q⁻¹ : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) :
          X.B.I.Ginf) * x) ⁻¹' K) := by
    intro q
    have hB : MeasurableSet (K0 ∩ (fun x => ((q⁻¹ : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) :
        X.B.I.Ginf) * x) ⁻¹' K) := hK0m.inter (hKm.preimage (measurable_const_mul _))
    rw [← hpre q q.2 _ hB]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Subgroup.coe_inv, inv_mul_cancel_left]
    exact and_comm
  have h3 := Pf.FormAllPf.decomp (μw.map fun y => g * y * g⁻¹) (Rset s) hRc
    (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) K0 K hK0m hKm hKu
  have h4 : ∑' q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) =
        (μw.map fun y => g * y * g⁻¹) K0 := by
    rw [h3]
    simp_rw [h2]
    exact (Equiv.inv (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin)).tsum_eq
      (fun q => (μw.map fun y => g * y * g⁻¹) (K0 ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K))
  have hC : IsCompact ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0) := by
    have e : (fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0 = (fun k => g⁻¹ * k * g) '' K0 := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hy; exact ⟨g * y * g⁻¹, hy, by group⟩
      · rintro ⟨k, hk, rfl⟩; convert hk using 1; group
    rw [e]
    exact hK0c.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hfin : (μw.map fun y => g * y * g⁻¹) K0 < ⊤ := by
    rw [Measure.map_apply hcm hK0m]
    have hsc := stCoord_cont u' w γw
    have hI : IsCompact (RealObj.stCoord X u' w γw '' ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0)) := hC.image hsc
    calc μw ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0)
        ≤ μw (RealObj.stCoord X u' w γw ⁻¹' (RealObj.stCoord X u' w γw '' ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0))) :=
          measure_mono (Set.subset_preimage_image _ _)
      _ = RealObj.muStab X w (RealObj.stCoord X u' w γw '' ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0)) := by
          rw [← hmap, Measure.map_apply hsc.measurable hI.isClosed.measurableSet]
      _ < ⊤ := muStab_compact w hI
  exact ENNReal.toReal_pos hpos (lt_of_le_of_lt (h1.trans_eq h4) hfin).ne

end Covol

end Formalism.L2.SG.Pf.LoopBPin
