import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCountE
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfAll
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.NatSmulMulEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ExplicitFormulaBoundHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DegreeRatioFormulaStatement

noncomputable section

open scoped Classical InnerProductSpace ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2

set_option linter.dupNamespace false

namespace Formalism.L2.SG.ThmSOwn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Record

variable (D : D7) (large₂ : SizeData₂ D)

def ClKppOff : Prop := ∀ u u' : D.what₂.Word, u ≠ u' → AdmissibleBoundsFromSource.Kpp D u u' = 0

def ClKppDiag : Prop := ∀ u, hsNormSq (AdmissibleBoundsFromSource.Kpp D u u) ≤ AdmissibleBoundsFromSource.du D u * AdmissibleBoundsFromSource.xK D

def ClOff : Prop :=
  ∀ u u' : D.what₂.Word, u ≠ u' →
    hsNormSq (Kmat D.s u u' - AdmissibleBoundsFromSource.Kpp D u u') ≤ (1 + AdmissibleBoundsFromSource.eta0 D large₂) * AdmissibleBoundsFromSource.du D u * AdmissibleBoundsFromSource.du D u' / AdmissibleBoundsFromSource.Dst D

def ClDiag : Prop :=
  ∀ u, hsNormSq (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) ≤
    AdmissibleBoundsFromSource.Gam D * AdmissibleBoundsFromSource.du D u ^ 2 / AdmissibleBoundsFromSource.Dst D

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem Theorem_E_iff_lift : AdmissibleBoundsFromSource.Conclusion1 D large₂ ↔ ClKppOff D ∧ ClKppDiag D ∧ ClOff D large₂ ∧ ClDiag D := Iff.rfl

end Record

section Family

variable {eps : ℝ}

def HypOwn (Fm : FamP eps) (C0 : ℝ) (Q : ∀ D : D7, SizeData₂ D → Prop) : Prop :=
  OwnEv Fm fun C' Cl x i =>
    AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu → Q (Fm.D x i) (Fm.L x i)

/- English proof (translation)
The claim follows from `((h1.and h2).and (h3.and h4)).mono fun _ _ _ _ h hH => ⟨(h.1.1 hH), (h.1.2 hH), (h.2.1 hH), (h.2.2 hH)⟩`.
-/
theorem thmSOwn_of_clauses {Fm : FamP eps} {C0 : ℝ}
    (h1 : HypOwn Fm C0 fun D _ => ClKppOff D) (h2 : HypOwn Fm C0 fun D _ => ClKppDiag D)
    (h3 : HypOwn Fm C0 fun D L => ClOff D L) (h4 : HypOwn Fm C0 fun D _ => ClDiag D) :
    ThmSOwn Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 :=
  ((h1.and h2).and (h3.and h4)).mono fun _ _ _ _ h hH => ⟨(h.1.1 hH), (h.1.2 hH), (h.2.1 hH), (h.2.2 hH)⟩

end Family

section Closed

def caZero : AdmissibleBoundsFromSource.AdmC where
  A5 := 0
  cL := 0
  cN := 0
  CN := 0
  CE := 0
  CA := 0
  CA' := 0
  Ce := 0
  n7 := 0
  A7 := 0
  C7 := 0
  cb7 := 0
  c7 := 0
  ep0 := 0
  CV := 0
  C1 := 0
  C2 := 0
  c5 := 0

/- English proof (translation)
The claim follows from `closed_of_large (linkThresholds (fun _ => caZero) c30) (hRes.and (hRows.and (hK1.and (hK2.and (hK3.and (hK4.and (S30.and A30))))))) fun Fm CH hL h a0 => by obtain ⟨-, g2, g3, g4⟩ := link_thresholds_spec Fm CH (fun _ => caZero) c30 hL obtain ⟨a1, a2, k1, k2, k3, k4, a6, a7⟩ := h e …`.
-/
theorem linkS_concrete (𝒞 : FamClass) (C0 : ℝ) (c30 : List ℝ → CountingConstants) (h1 : 1 ≤ C0)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm)
    (hRows : Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut, PlaceDegreeData.RowsTie (Fm.D x i) X)
    (hK1 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppOff D)
    (hK2 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppDiag D)
    (hK3 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D L => ClOff D L)
    (hK4 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClDiag D)
    (S30 : Closed 𝒞 fun Fm _ => PlaceDegreeData.KudlaFamilyStatement Fm (c30 Fm.cOut).Cres (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).Cb
      (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (A30 : Closed 𝒞 fun Fm _ => PlaceDegreeData.AdmF Fm (c30 Fm.cOut).Cres) :
    Closed 𝒞 fun Fm _ => TuSize Fm → Formalism.MainNotions.LinkS Fm C0 :=
  closed_of_large (linkThresholds (fun _ => caZero) c30)
    (hRes.and (hRows.and (hK1.and (hK2.and (hK3.and (hK4.and (S30.and A30)))))))
    fun Fm CH hL h a0 => by
      obtain ⟨-, g2, g3, g4⟩ := link_thresholds_spec Fm CH (fun _ => caZero) c30 hL
      obtain ⟨a1, a2, k1, k2, k3, k4, a6, a7⟩ := h
      exact linkS_of_kudla_family Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 _ _ _ _ _ _ _ h1 (hc30 Fm).1 (hc30 Fm).2 g2 g3
        (standing_hypotheses_hold_family Fm C0 h1 ⟨g4, a0, a1⟩) a2 (thmSOwn_of_clauses k1 k2 k3 k4) a6 a7

end Closed

section Iso
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {Word Tau : Type} {hc : Word → Tau → HCParam R}
  {s s' : Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc}

def conjE (I : SIso s s') (u u' : Word) : (s.Cu u' →L[ℂ] s.Cu u) ≃L[ℂ] (s'.Cu u' →L[ℂ] s'.Cu u) :=
  ContinuousLinearEquiv.arrowCongr (I.eCu u').toContinuousLinearEquiv (I.eCu u).toContinuousLinearEquiv

/- English proof (translation)
Simplify using `[conjE]`.
-/
theorem conjE_apply (I : SIso s s') (u u' : Word) (A : s.Cu u' →L[ℂ] s.Cu u) (x : s.Cu u') :
    conjE I u u' A (I.eCu u' x) = I.eCu u (A x) := by
  simp [conjE]

/- English proof (translation)
Use extensionality with `y`. Take `⟨x, rfl⟩` from `(I.eCu u').surjective y`. Rewrite using `[conjE_apply, I.aTerm_eq]`.
-/
theorem conjE_aTerm (I : SIso s s') (u u' : Word) (t : s.Term u u') :
    conjE I u u' (s.aTerm u u' t) = s'.aTerm u u' (I.eT u u' t) := by
  ext y
  obtain ⟨x, rfl⟩ := (I.eCu u').surjective y
  rw [conjE_apply, I.aTerm_eq]

/- English proof (translation)
Unfold `KOf`. Rewrite using `[ContinuousLinearEquiv.map_tsum]`. Simplify using `only [conjE_aTerm]`. Conclude with `Equiv.tsum_eq ((I.eT u u').subtypeEquiv hΦ) (fun t' : Φ' => s'.aTerm u u' t'.1)`.
-/
theorem conjE_KOf (I : SIso s s') (u u' : Word) (Φ : Set (s.Term u u')) (Φ' : Set (s'.Term u u'))
    (hΦ : ∀ t, t ∈ Φ ↔ I.eT u u' t ∈ Φ') : conjE I u u' (KOf s u u' Φ) = KOf s' u u' Φ' := by
  unfold KOf
  rw [ContinuousLinearEquiv.map_tsum]
  simp only [conjE_aTerm]
  exact Equiv.tsum_eq ((I.eT u u').subtypeEquiv hΦ) (fun t' : Φ' => s'.aTerm u u' t'.1)

/- English proof (translation)
Use extensionality with `y`. Take `⟨x, rfl⟩` from `(I.eCu u').surjective y`. Rewrite using `[conjE_apply, Formalism.L2.SG.Pf.kmat_iso s s' I u u' x]`.
-/
theorem conjE_Kmat [Fintype Tau] (I : SIso s s') (u u' : Word) : conjE I u u' (Kmat s u u') = Kmat s' u u' := by
  ext y
  obtain ⟨x, rfl⟩ := (I.eCu u').surjective y
  rw [conjE_apply, Formalism.L2.SG.Pf.kmat_iso s s' I u u' x]

/- English proof (translation)
Use extensionality with `y`. Take `⟨x, rfl⟩` from `(I.eCu u).surjective y`. Rewrite using `[conjE_apply]`. Both sides reduce to the same expression.
-/
theorem conjE_id (I : SIso s s') (u : Word) :
    conjE I u u (ContinuousLinearMap.id ℂ (s.Cu u)) = ContinuousLinearMap.id ℂ (s'.Cu u) := by
  ext y
  obtain ⟨x, rfl⟩ := (I.eCu u).surjective y
  rw [conjE_apply]; rfl

/- English proof (translation)
Use `FiniteDimensional.complete ℂ (s'.Cu u)` as an intermediate fact. Conclude with `Formalism.L2.SG.Pf.hsNormSq_of_iso A (conjE I u u' A) (I.eCu u') (I.eCu u) (fun y => (I.eCu u).norm_map y) (conjE_apply I u u' A)`.
-/
theorem hsNormSq_conjE (I : SIso s s') (u u' : Word) (A : s.Cu u' →L[ℂ] s.Cu u) :
    hsNormSq (conjE I u u' A) = hsNormSq A := by
  have := FiniteDimensional.complete ℂ (s'.Cu u)
  exact Formalism.L2.SG.Pf.hsNormSq_of_iso A (conjE I u u' A) (I.eCu u') (I.eCu u) (fun y => (I.eCu u).norm_map y)
    (conjE_apply I u u' A)

end Iso

section SOf

open Formalism.L2.SG.Full

variable {D : D7} {X : HidaSetting D} {Y : Full X} (hF : FinX Y) {u u' : D.what₂.Word}

abbrev aM (Y : Full X) (u u' : D.what₂.Word) (s : TT Y u u') : CM (Y.cs u') →L[ℂ] CM (Y.cs u) :=
  aTerm (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s

include hF in
/- English proof (translation)
Use `Summable.of_norm_bounded (hA.1.mul_left (Module.finrank ℂ (CM (Y.cs u')) : ℝ)) fun s => ?_` and prove the remaining obligations. Distinguish the cases in `h : s ∈ S`. Rewrite using `[Set.indicator_of_mem h]`. Conclude with `Formalism.L2.SG.Pf.opNorm_le_hs _`. Rewrite using `[Set.indicator_of_notMem h, norm_zero]`.

Check the signs of the components of the expression.
-/
theorem summable_ind_aM (hA : (Y.tO u u').AbsConv) (S : Set (TT Y u u')) :
    Summable (S.indicator (aM Y u u')) := by
  refine Summable.of_norm_bounded (hA.1.mul_left (Module.finrank ℂ (CM (Y.cs u')) : ℝ)) fun s => ?_
  by_cases h : s ∈ S
  · rw [Set.indicator_of_mem h]; exact Formalism.L2.SG.Pf.opNorm_le_hs _
  · rw [Set.indicator_of_notMem h, norm_zero]; positivity

/- English proof (translation)
Set `f : TT Y u u' → (ColT (hF.shInj u') →L[ℂ] ColT (hF.shInj u))` to `S.indicator (aT hF u u')`. Establish `hfe : ∀ s, f s = Formalism.L2.SG.Pf.trAdd (hF.shBij u) (hF.shBij u') (S.indicator (aM Y u u') s)` using `fun s => by`. Distinguish the cases in `h : s ∈ S`. Simplify using `only [f, Set.indicator_of_mem h]`. Both sides reduce to the same expression.

Simplify using `only [f, Set.indicator_of_notMem h]`. Conclude with `(map_zero (Formalism.L2.SG.Pf.trAdd (hF.shBij u) (hF.shBij u'))).symm`. Establish `hsum : HasSum f (tr (hF.shBij u) (hF.shBij u') (∑' s, S.indicator (aM Y u u') s))`. Use `(summable_ind_aM hF hA S).hasSum.map (Formalism.L2.SG.Pf.trAdd (hF.shBij u) (hF.shBij u')) (Formalism.L2.SG.Pf.continuous_trAdd _ _)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Conclude with `funext hfe`. Both sides reduce to the same expression. Set `e` to `Equiv.sigmaFiberEquiv (fun s : TT Y u u' => s.toTerm)`. Establish `h2` using `(e.hasSum_iff (f := f)).2 hsum`. Establish `h3 : HasSum (fun t : RT Y u u' => Φ'.indicator (aR hF u u') t) (tr (hF.shBij u) (hF.shBij u') (∑' s, S.indicator (aM Y u u') s))`.

Use `h2.sigma fun t => ?_` and prove the remaining obligations. Use `letI : Fintype {x : TT Y u u' // x.toTerm = t} := hF.fibFT t`. Distinguish the cases in `ht : t ∈ Φ'`. Rewrite using `[Set.indicator_of_mem ht]`. Establish `hc : ∀ c : {x : TT Y u u' // x.toTerm = t}, (f ∘ e) ⟨t, c⟩ = aT hF u u' c.1` using `fun c => by`.

Establish `hm : c.1 ∈ S` using `(hS c.1).2 (by rw [c.2]; exact ht)`. Simplify using `only [Function.comp, e, Equiv.sigmaFiberEquiv_apply, f, Set.indicator_of_mem hm]`. Simplify using `only [hc]`. Unfold `aR`. Conclude with `hasSum_fintype _`.

Rewrite using `[Set.indicator_of_notMem ht]`. Establish `hc : ∀ c : {x : TT Y u u' // x.toTerm = t}, (f ∘ e) ⟨t, c⟩ = 0` using `fun c => by`. Establish `hm : c.1 ∉ S` using `fun h => ht (by have h' := (hS c.1).1 h; rwa [c.2] at h')`. Simplify using `only [Function.comp, e, Equiv.sigmaFiberEquiv_apply, f, Set.indicator_of_notMem hm]`. Simplify using `only [hc]`.

Conclude with `hasSum_zero`. Unfold `KOf`. Conclude with `(tsum_subtype Φ' (aR hF u u')).trans h3.tsum_eq`.
-/
theorem kof_sOf (hA : (Y.tO u u').AbsConv) (S : Set (TT Y u u')) (Φ' : Set (RT Y u u'))
    (hS : ∀ s : TT Y u u', s ∈ S ↔ s.toTerm ∈ Φ') :
    KOf (sOf hF) u u' Φ' = tr (hF.shBij u) (hF.shBij u') (∑' s, S.indicator (aM Y u u') s) := by
  let f : TT Y u u' → (ColT (hF.shInj u') →L[ℂ] ColT (hF.shInj u)) := S.indicator (aT hF u u')
  have hfe : ∀ s, f s = Formalism.L2.SG.Pf.trAdd (hF.shBij u) (hF.shBij u') (S.indicator (aM Y u u') s) := fun s => by
    by_cases h : s ∈ S
    · simp only [f, Set.indicator_of_mem h]; rfl
    · simp only [f, Set.indicator_of_notMem h]; exact (map_zero (Formalism.L2.SG.Pf.trAdd (hF.shBij u) (hF.shBij u'))).symm
  have hsum : HasSum f (tr (hF.shBij u) (hF.shBij u') (∑' s, S.indicator (aM Y u u') s)) := by
    have := (summable_ind_aM hF hA S).hasSum.map (Formalism.L2.SG.Pf.trAdd (hF.shBij u) (hF.shBij u'))
      (Formalism.L2.SG.Pf.continuous_trAdd _ _)
    convert this using 1
    · exact funext hfe
    · rfl
  let e := Equiv.sigmaFiberEquiv (fun s : TT Y u u' => s.toTerm)
  have h2 := (e.hasSum_iff (f := f)).2 hsum
  have h3 : HasSum (fun t : RT Y u u' => Φ'.indicator (aR hF u u') t)
      (tr (hF.shBij u) (hF.shBij u') (∑' s, S.indicator (aM Y u u') s)) := by
    refine h2.sigma fun t => ?_
    letI : Fintype {x : TT Y u u' // x.toTerm = t} := hF.fibFT t
    by_cases ht : t ∈ Φ'
    · rw [Set.indicator_of_mem ht]
      have hc : ∀ c : {x : TT Y u u' // x.toTerm = t}, (f ∘ e) ⟨t, c⟩ = aT hF u u' c.1 := fun c => by
        have hm : c.1 ∈ S := (hS c.1).2 (by rw [c.2]; exact ht)
        simp only [Function.comp, e, Equiv.sigmaFiberEquiv_apply, f, Set.indicator_of_mem hm]
      simp only [hc]
      unfold aR
      exact hasSum_fintype _
    · rw [Set.indicator_of_notMem ht]
      have hc : ∀ c : {x : TT Y u u' // x.toTerm = t}, (f ∘ e) ⟨t, c⟩ = 0 := fun c => by
        have hm : c.1 ∉ S := fun h => ht (by have h' := (hS c.1).1 h; rwa [c.2] at h')
        simp only [Function.comp, e, Equiv.sigmaFiberEquiv_apply, f, Set.indicator_of_notMem hm]
      simp only [hc]
      exact hasSum_zero
  unfold KOf
  exact (tsum_subtype Φ' (aR hF u u')).trans h3.tsum_eq

include hF in

/- English proof (translation)
Establish `hc : Continuous (Formalism.L2.SG.PackageTie.hsEmb (Wq` using `CM (Y.cs u')) (Wp := CM (Y.cs u))) := LinearMap.continuous_of_finiteDimensional _`. Establish `h` using `(summable_ind_aM hF hA S).hasSum.map (Formalism.L2.SG.PackageTie.hsEmb (Wq := CM (Y.cs u')) (Wp := CM (Y.cs u))).toAddMonoidHom hc`. Establish `h' : HasSum (fun s => S.indicator (Y.tO u u').op s) (Formalism.L2.SG.PackageTie.hsEmb (∑' s, S.indicator (aM Y u u') s))`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `s`.

Distinguish the cases in `hs : s ∈ S`. Simplify using `only [Function.comp, Set.indicator_of_mem hs]`. Both sides reduce to the same expression. Simplify using `only [Function.comp, Set.indicator_of_notMem hs, map_zero]`. Both sides reduce to the same expression.

Conclude with `h'.tsum_eq.symm`.
-/
theorem hsEmb_tsum (hA : (Y.tO u u').AbsConv) (S : Set (TT Y u u')) :
    Formalism.L2.SG.PackageTie.hsEmb (∑' s, S.indicator (aM Y u u') s) = (Y.tO u u').part S := by
  have hc : Continuous (Formalism.L2.SG.PackageTie.hsEmb (Wq := CM (Y.cs u')) (Wp := CM (Y.cs u))) :=
    LinearMap.continuous_of_finiteDimensional _
  have h := (summable_ind_aM hF hA S).hasSum.map
    (Formalism.L2.SG.PackageTie.hsEmb (Wq := CM (Y.cs u')) (Wp := CM (Y.cs u))).toAddMonoidHom hc
  have h' : HasSum (fun s => S.indicator (Y.tO u u').op s)
      (Formalism.L2.SG.PackageTie.hsEmb (∑' s, S.indicator (aM Y u u') s)) := by
    convert h using 1
    funext s
    by_cases hs : s ∈ S
    · simp only [Function.comp, Set.indicator_of_mem hs]; rfl
    · simp only [Function.comp, Set.indicator_of_notMem hs, map_zero]
    · rfl
  exact h'.tsum_eq.symm

include hF in

/- English proof (translation)
Use `finiteDimensional_colT (hF.shBij u)` as an intermediate fact. Use `FiniteDimensional.complete ℂ (ColT (hF.shInj u))` as an intermediate fact. Rewrite using `[Formalism.L2.SG.PackageTie.norm_hsEmb_sq]`. Conclude with `(Formalism.L2.SG.Pf.hsNormSq_of_semi (tr (hF.shBij u) (hF.shBij u') A) A (Formalism.L2.SG.Pf.shTAdd (hF.shInj u')) (fun c x => shT_smul _ c x) (fun x y => (inner_colT _ y x).symm) (hF.shBij u').2 (shT (hF.shInj u)) Formalism.L2.SG.Pf.norm_shT (fun x => (shT_tr _ _ A x).symm)).sym …`.
-/
theorem hsNormSq_tr [FiniteDimensional ℂ (ColT (hF.shInj u'))] (A : CM (Y.cs u') →L[ℂ] CM (Y.cs u)) :
    hsNormSq (tr (hF.shBij u) (hF.shBij u') A) = ‖Formalism.L2.SG.PackageTie.hsEmb A‖ ^ 2 := by
  have := finiteDimensional_colT (hF.shBij u)
  have := FiniteDimensional.complete ℂ (ColT (hF.shInj u))
  rw [Formalism.L2.SG.PackageTie.norm_hsEmb_sq]
  exact (Formalism.L2.SG.Pf.hsNormSq_of_semi (tr (hF.shBij u) (hF.shBij u') A) A (Formalism.L2.SG.Pf.shTAdd (hF.shInj u'))
    (fun c x => shT_smul _ c x) (fun x y => (inner_colT _ y x).symm) (hF.shBij u').2
    (shT (hF.shInj u)) Formalism.L2.SG.Pf.norm_shT (fun x => (shT_tr _ _ A x).symm)).symm

include hF in
/- English proof (translation)
Use `ext1 T`. Rewrite using `[tr_apply, ContinuousLinearMap.id_apply, shInv_shT]`. Both sides reduce to the same expression.
-/
theorem tr_id (u : D.what₂.Word) :
    tr (hF.shBij u) (hF.shBij u) (ContinuousLinearMap.id ℂ (CM (Y.cs u))) = ContinuousLinearMap.id ℂ _ := by
  ext1 T
  rw [tr_apply, ContinuousLinearMap.id_apply, shInv_shT]; rfl

include hF in
/- English proof (translation)
The claim follows from `map_sub (Formalism.L2.SG.Pf.trAdd (hF.shBij u) (hF.shBij u')) A B`.
-/
theorem tr_sub (A B : CM (Y.cs u') →L[ℂ] CM (Y.cs u)) :
    tr (hF.shBij u) (hF.shBij u') (A - B) = tr (hF.shBij u) (hF.shBij u') A - tr (hF.shBij u) (hF.shBij u') B :=
  map_sub (Formalism.L2.SG.Pf.trAdd (hF.shBij u) (hF.shBij u')) A B

end SOf

section Clauses

open Formalism.L2.SG.Full

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF))

def PhiC (u u' : D.what₂.Word) : Set (RT Y u u') := {t | (sOf hF).Gterm t = 0 ∧ ¬ (sOf hF).isId t}

/- English proof (translation)
Establish `e : ((sOf hF).Gterm s.toTerm = 0) ↔ s.toTerm.G = 0`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `congrArg Subtype.val h`. Introduce `h`.

Conclude with `Subtype.ext h`. Apply the tactic sequence `have hG : (Y.tO u u').G s = 0 ↔ s.toTerm.G = 0 := by show (if s.toTerm.G = 0 then (0 : ℝ) else 1) = 0 ↔ _ split_ifs with h <;> simp [h]`. Use `show ((Y.tO u u').G s = 0 ∧ ¬ (Y.tO u u').isId s) ↔ ((sOf hF).Gterm s.toTerm = 0 ∧ ¬ (sOf hF).isId s.toTerm)`. Conclude with `and_congr (hG.trans e.symm) Iff.rfl`.
-/
theorem mem_degSet_iff {u u' : D.what₂.Word} (s : TT Y u u') :
    s ∈ (Y.tO u u').degSet ↔ s.toTerm ∈ PhiC (hF := hF) u u' := by
  have e : ((sOf hF).Gterm s.toTerm = 0) ↔ s.toTerm.G = 0 := by
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  have hG : (Y.tO u u').G s = 0 ↔ s.toTerm.G = 0 := by
    show (if s.toTerm.G = 0 then (0 : ℝ) else 1) = 0 ↔ _
    split_ifs with h <;> simp [h]
  show ((Y.tO u u').G s = 0 ∧ ¬ (Y.tO u u').isId s) ↔
    ((sOf hF).Gterm s.toTerm = 0 ∧ ¬ (sOf hF).isId s.toTerm)
  exact and_congr (hG.trans e.symm) Iff.rfl

/- English proof (translation)
Use `show (D.s.Gterm t = 0 ∧ ¬ D.s.isId t) ↔ ((sOf hF).Gterm (hI.eT u u' t) = 0 ∧ ¬ (sOf hF).isId (hI.eT u u' t))`. Rewrite using `[hI.Gterm t, hI.isId t]`.
-/
theorem mem_PhiC_iff {u u' : D.what₂.Word} (t : D.s.Term u u') :
    t ∈ {t : D.s.Term u u' | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} ↔ hI.eT u u' t ∈ PhiC (hF := hF) u u' := by
  show (D.s.Gterm t = 0 ∧ ¬ D.s.isId t) ↔
    ((sOf hF).Gterm (hI.eT u u' t) = 0 ∧ ¬ (sOf hF).isId (hI.eT u u' t))
  rw [hI.Gterm t, hI.isId t]

/- English proof (translation)
Rewrite using `[show AdmissibleBoundsFromSource.Kpp D u u' = KOf D.s u u' {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} from rfl, conjE_KOf hI u u' _ (PhiC (hF := hF) u u') (mem_PhiC_iff hI), kof_sOf hF hA _ _ mem_degSet_iff]`.
-/
theorem conjE_Kpp {u u' : D.what₂.Word} (hA : (Y.tO u u').AbsConv) :
    conjE hI u u' (AdmissibleBoundsFromSource.Kpp D u u') =
      tr (hF.shBij u) (hF.shBij u') (∑' s, (Y.tO u u').degSet.indicator (aM Y u u') s) := by
  rw [show AdmissibleBoundsFromSource.Kpp D u u' = KOf D.s u u' {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} from rfl,
    conjE_KOf hI u u' _ (PhiC (hF := hF) u u') (mem_PhiC_iff hI), kof_sOf hF hA _ _ mem_degSet_iff]

include hI in

/- English proof (translation)
Use `finiteDimensional_colT (hF.shBij u')` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hsNormSq_Kpp {u u' : D.what₂.Word} (hA : (Y.tO u u').AbsConv) :
    hsNormSq (AdmissibleBoundsFromSource.Kpp D u u') = ‖(Y.tO u u').part (Y.tO u u').degSet‖ ^ 2 := by
  have := finiteDimensional_colT (hF.shBij u')
  calc hsNormSq (AdmissibleBoundsFromSource.Kpp D u u') = hsNormSq (conjE hI u u' (AdmissibleBoundsFromSource.Kpp D u u')) := (hsNormSq_conjE hI u u' _).symm
    _ = hsNormSq (tr (hF.shBij u) (hF.shBij u') (∑' s, (Y.tO u u').degSet.indicator (aM Y u u') s)) :=
      congrArg hsNormSq (conjE_Kpp hI hA)
    _ = _ := (hsNormSq_tr hF _).trans (congrArg (fun z => ‖z‖ ^ 2) (hsEmb_tsum hF hA _))

/- English proof (translation)
Establish `hb : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0` using `fun i => by`. Use `congrArg (fun v => (WithLp.ofLp v) i) h` as an intermediate fact. Simplify `this` using `[Formalism.L2.SG.PackageTie.hsEmb]`. Apply `ContinuousLinearMap.coe_injective` to reduce the goal to its premises. Conclude with `(stdOrthonormalBasis ℂ Wq).toBasis.ext (f₁ := (A : Wq →ₗ[ℂ] Wp)) (f₂ := 0) (fun i => by`.

Rewrite using `[OrthonormalBasis.coe_toBasis]`. Conclude with `hb i)`.
-/
theorem hsEmb_eq_zero {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (A : Wq →L[ℂ] Wp) (h : Formalism.L2.SG.PackageTie.hsEmb A = 0) : A = 0 := by
  have hb : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := fun i => by
    have := congrArg (fun v => (WithLp.ofLp v) i) h
    simpa [Formalism.L2.SG.PackageTie.hsEmb] using this
  apply ContinuousLinearMap.coe_injective
  exact (stdOrthonormalBasis ℂ Wq).toBasis.ext (f₁ := (A : Wq →ₗ[ℂ] Wp)) (f₂ := 0) (fun i => by
    rw [OrthonormalBasis.coe_toBasis]; exact hb i)

include hI in

/- English proof (translation)
Establish `h0 : ∀ t ∈ PhiC (hF` using `hF) u u', aR hF u u' t = 0 := by`. Introduce `t ht`. Use `letI := hF.fibFT t`. Unfold `aR`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations.

Establish `hm : c.1 ∈ (Y.tO u u').degSet` using `(mem_degSet_iff c.1).2 (c.2 ▸ ht)`. Establish `ha : aM Y u u' c.1 = 0` using `hsEmb_eq_zero _ (hZ c.1 hm)`. Unfold `aT`. Rewrite using `[show aTerm (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') c.1 = aM Y u u' c.1 from rfl, ha]`. Conclude with `map_zero (Formalism.L2.SG.Pf.trAdd (hF.shBij u) (hF.shBij u'))`.

Establish `hK : KOf (sOf hF) u u' (PhiC (hF` using `hF) u u') = 0 := by`. Unfold `KOf`. Conclude with `(tsum_congr (fun t : PhiC (hF := hF) u u' => (h0 t.1 t.2 : (sOf hF).aTerm u u' t.1 = 0))).trans tsum_zero`. Establish `h1` using `conjE_KOf hI u u' _ (PhiC (hF := hF) u u') (mem_PhiC_iff hI)`. Rewrite `h1` using `[hK]`.

Conclude with `(conjE hI u u').map_eq_zero_iff.1 h1`.
-/
theorem kpp_zero {u u' : D.what₂.Word} (hZ : Formalism.L2.SG.RowsOther.KppTermZero (Y.tO u u')) : AdmissibleBoundsFromSource.Kpp D u u' = 0 := by
  have h0 : ∀ t ∈ PhiC (hF := hF) u u', aR hF u u' t = 0 := by
    intro t ht
    letI := hF.fibFT t
    unfold aR
    refine Finset.sum_eq_zero fun c _ => ?_
    have hm : c.1 ∈ (Y.tO u u').degSet := (mem_degSet_iff c.1).2 (c.2 ▸ ht)
    have ha : aM Y u u' c.1 = 0 := hsEmb_eq_zero _ (hZ c.1 hm)
    unfold aT
    rw [show aTerm (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') c.1 = aM Y u u' c.1 from rfl, ha]
    exact map_zero (Formalism.L2.SG.Pf.trAdd (hF.shBij u) (hF.shBij u'))
  have hK : KOf (sOf hF) u u' (PhiC (hF := hF) u u') = 0 := by
    unfold KOf
    exact (tsum_congr (fun t : PhiC (hF := hF) u u' => (h0 t.1 t.2 : (sOf hF).aTerm u u' t.1 = 0))).trans tsum_zero
  have h1 := conjE_KOf hI u u' _ (PhiC (hF := hF) u u') (mem_PhiC_iff hI)
  rw [hK] at h1
  exact (conjE hI u u').map_eq_zero_iff.1 h1

end Clauses

section Clauses2

open Formalism.L2.SG.Full

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF))

include hI in

/- English proof (translation)
Rewrite using `[kpp_zero hI hZ, sub_zero, Formalism.L2.SG.Pf.isoNorm D.s (sOf hF) hI u u', Formalism.L2.SG.Pf.normTie hF u u' (Formalism.L2.SG.Pf.dimTie X u) (Formalism.L2.SG.Pf.dimTie X u') hE hA hId (Formalism.L2.SG.RowsOther.kppOff_of_termZero _ hZ)]`.
-/
theorem hsNormSq_off {u u' : D.what₂.Word}
    (hE : Formalism.L2.SG.TermOp.KExpansion (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK (Y.Dt u) (Y.Dt u'))
    (hA : (Y.tO u u').AbsConv) (hId : (Y.tO u u').IdDegenerate) (hZ : Formalism.L2.SG.RowsOther.KppTermZero (Y.tO u u')) :
    hsNormSq (Kmat D.s u u' - AdmissibleBoundsFromSource.Kpp D u u') = ‖(Y.tO u u').K0‖ ^ 2 := by
  rw [kpp_zero hI hZ, sub_zero, Formalism.L2.SG.Pf.isoNorm D.s (sOf hF) hI u u',
    Formalism.L2.SG.Pf.normTie hF u u' (Formalism.L2.SG.Pf.dimTie X u) (Formalism.L2.SG.Pf.dimTie X u') hE hA hId
      (Formalism.L2.SG.RowsOther.kppOff_of_termZero _ hZ)]

include hI in

/- English proof (translation)
Take `⟨K, hsum, hK⟩` from `hE`. Establish `hKm` using `Formalism.L2.SG.Pf.kmat_eq hF (Formalism.L2.SG.Pf.dimTie X u) (Formalism.L2.SG.Pf.dimTie X u) K hK`. Use `finiteDimensional_colT (hF.shBij u)` as an intermediate fact. Establish `hs : ∀ S : Set (TT Y u u), Summable (S.indicator (Y.tO u u).op)` using `fun S => Summable.of_norm_bounded hA.1 fun t => by`. Distinguish the cases in `h : t ∈ S`.

Rewrite using `[Set.indicator_of_mem h]`. Rewrite using `[Set.indicator_of_notMem h, norm_zero]`. Conclude with `norm_nonneg _`. Establish `hKK : (Y.tO u u).K = Formalism.L2.SG.PackageTie.hsEmb K` using `(hsum.map (Formalism.L2.SG.PackageTie.hsEmb (Wq := CM (Y.cs u)) (Wp := CM (Y.cs u))) (LinearMap.continuous_of_finiteDimensional _)).tsum_eq`. Use `set P := ∑' s, (Y.tO u u).degSet.indicator (aM Y u u) s with hPdef`.

Establish `hconj : conjE hI u u (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) = tr (hF.shBij u) (hF.shBij u) (K - P - ContinuousLinearMap.id ℂ (CM (Y.cs u)))`. Rewrite using `[map_sub, map_sub, conjE_Kmat, conjE_Kpp hI hA, conjE_id, hKm]`. Conclude with `(show tr (hF.shBij u) (hF.shBij u) (K - P - ContinuousLinearMap.id ℂ (CM (Y.cs u))) = tr (hF.shBij u) (hF.shBij u) K - tr (hF.shBij u) (hF.shBij u) P - ContinuousLinearMap.id ℂ _ by`. Rewrite using `[tr_sub hF, tr_sub hF, tr_id hF u]).symm`. Establish `hP : Formalism.L2.SG.PackageTie.hsEmb P = (Y.tO u u).part (Y.tO u u).degSet` using `hsEmb_tsum hF hA _`.

Establish `hemb : Formalism.L2.SG.PackageTie.hsEmb (K - P - ContinuousLinearMap.id ℂ (CM (Y.cs u))) = (Y.tO u u).K0 - Formalism.L2.SG.RowsConc.oneC X Y u`. Rewrite using `[map_sub, map_sub, hP, ← hKK, Formalism.L2.SG.PackageTie.K_eq_parts hs hId]`. Unfold `Formalism.FourierDecayAlt.PB.Terms.K0 Formalism.L2.SG.RowsConc.oneC`. Normalize the expressions using the abelian group laws. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hsNormSq_diag {u : D.what₂.Word}
    (hE : Formalism.L2.SG.TermOp.KExpansion (X.Fu u) (X.Fu u) (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) Y.hK (Y.Dt u) (Y.Dt u))
    (hA : (Y.tO u u).AbsConv) (hId : (Y.tO u u).IdDegenerate) :
    hsNormSq (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) =
      ‖(Y.tO u u).K0 - Formalism.L2.SG.RowsConc.oneC X Y u‖ ^ 2 := by
  obtain ⟨K, hsum, hK⟩ := hE
  have hKm := Formalism.L2.SG.Pf.kmat_eq hF (Formalism.L2.SG.Pf.dimTie X u) (Formalism.L2.SG.Pf.dimTie X u) K hK
  have := finiteDimensional_colT (hF.shBij u)
  have hs : ∀ S : Set (TT Y u u), Summable (S.indicator (Y.tO u u).op) := fun S =>
    Summable.of_norm_bounded hA.1 fun t => by
      by_cases h : t ∈ S
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, norm_zero]; exact norm_nonneg _
  have hKK : (Y.tO u u).K = Formalism.L2.SG.PackageTie.hsEmb K :=
    (hsum.map (Formalism.L2.SG.PackageTie.hsEmb (Wq := CM (Y.cs u)) (Wp := CM (Y.cs u)))
      (LinearMap.continuous_of_finiteDimensional _)).tsum_eq
  set P := ∑' s, (Y.tO u u).degSet.indicator (aM Y u u) s with hPdef
  have hconj : conjE hI u u (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) =
      tr (hF.shBij u) (hF.shBij u) (K - P - ContinuousLinearMap.id ℂ (CM (Y.cs u))) := by
    rw [map_sub, map_sub, conjE_Kmat, conjE_Kpp hI hA, conjE_id, hKm]
    exact (show tr (hF.shBij u) (hF.shBij u) (K - P - ContinuousLinearMap.id ℂ (CM (Y.cs u))) =
      tr (hF.shBij u) (hF.shBij u) K - tr (hF.shBij u) (hF.shBij u) P - ContinuousLinearMap.id ℂ _ by
        rw [tr_sub hF, tr_sub hF, tr_id hF u]).symm
  have hP : Formalism.L2.SG.PackageTie.hsEmb P = (Y.tO u u).part (Y.tO u u).degSet := hsEmb_tsum hF hA _
  have hemb : Formalism.L2.SG.PackageTie.hsEmb (K - P - ContinuousLinearMap.id ℂ (CM (Y.cs u))) =
      (Y.tO u u).K0 - Formalism.L2.SG.RowsConc.oneC X Y u := by
    rw [map_sub, map_sub, hP, ← hKK, Formalism.L2.SG.PackageTie.K_eq_parts hs hId]
    unfold Formalism.FourierDecayAlt.PB.Terms.K0 Formalism.L2.SG.RowsConc.oneC
    abel
  calc hsNormSq (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u))
      = hsNormSq (conjE hI u u (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u))) :=
        (hsNormSq_conjE hI u u _).symm
    _ = hsNormSq (tr (hF.shBij u) (hF.shBij u) (K - P - ContinuousLinearMap.id ℂ (CM (Y.cs u)))) :=
        congrArg hsNormSq hconj
    _ = _ := (hsNormSq_tr hF _).trans (congrArg (fun z => ‖z‖ ^ 2) hemb)

end Clauses2

section Family

open Formalism.L2.SG.Full

structure ConcK (D : D7) : Type 1 where
  X : HidaSetting D
  Y : Full X
  hF : FinX Y
  hI : SIso D.s (sOf hF)
  tie : Formalism.L2.SG.RowsConc.ConcTie X Y

def CSelF {eps : ℝ} (Fm : FamP eps) : Type 1 :=
  Σ' x0 : ℝ, ∀ x (_ : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, ConcK (Fm.D x i)

def CSel (𝒞 : FamClass) : Type 1 := ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → CSelF Fm

def KExpTied : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    Formalism.L2.SG.TermOp.KExpansion (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK (Y.Dt u) (Y.Dt u')

/- English proof (translation)
Introduce `D X Y u u' hT`. Establish `f1` using `hFo D X Y u hT.1 hT.2.2.2.2.1`. Establish `f2` using `hFo D X Y u' hT.1 hT.2.2.2.2.1`. Establish `hFE` using `hF D X Y u u'`. Establish `hOO` using `hO D X Y u u' f1 f2 hFE`.

Conclude with `hK D X Y u u' f1 f2 (hIn D X Y u hT.2.2.2.2.2.1 f1) (hIn D X Y u' hT.2.2.2.2.2.1 f2) hFE hOO (hOF D X Y u u' hFE hOO) (hAW D X Y u u' hOO) (hA D X Y u u' f1 f2 hFE hOO)`.
-/
theorem kExpTied_of_full (hFo : Formalism.L2.SG.Full.FoldOKC) (hIn : Formalism.L2.SG.Full.InHHC) (hF : Formalism.L2.SG.Full.FundExistsC)
    (hO : Formalism.L2.SG.Full.OOIntAllC) (hOF : Formalism.L2.SG.Full.OOFundIndepC) (hAW : Formalism.L2.SG.Full.AmpWellDefC)
    (hA : Formalism.L2.SG.Full.AbsConvC) (hK : Formalism.L2.SG.Full.KExpansionC) : KExpTied := by
  intro D X Y u u' hT
  have f1 := hFo D X Y u hT.1 hT.2.2.2.2.1
  have f2 := hFo D X Y u' hT.1 hT.2.2.2.2.1
  have hFE := hF D X Y u u'
  have hOO := hO D X Y u u' f1 f2 hFE
  exact hK D X Y u u' f1 f2 (hIn D X Y u hT.2.2.2.2.2.1 f1) (hIn D X Y u' hT.2.2.2.2.2.1 f2) hFE hOO
    (hOF D X Y u u' hFE hOO) (hAW D X Y u u' hOO) (hA D X Y u u' f1 f2 hFE hOO)

def TheoremSDifferentWords {eps : ℝ} (Fm : FamP eps) (C0 : ℝ) (c : CSelF Fm) : Prop :=
  OwnEv Fm fun C' Cl x i =>
    AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
    ∀ (hx : Fm.x1 < x) (h0 : c.1 ≤ x) (u u' : (Fm.D x i).what₂.Word), u ≠ u' →
      ‖((c.2 x hx h0 i).Y.tO u u').K0‖ ^ 2 ≤ (1 + ((Fm.L x i).sc.b ^ 6)⁻¹) *
        (((Fm.D x i).duS u : ℝ) * ((Fm.D x i).duS u') / (Fm.D x i).what₂.Dstar)

/- English proof (translation)
Take `⟨a, ha, hQ⟩` from `hQ`. Use `⟨a, ha, fun e he hle => ?_⟩` and prove the remaining obligations. Take `⟨K, hK⟩` from `hQ e he hle`. Use `⟨K.sup ⟨0, fun _ => 0, thm, th⟩, fun Fm CH hc hL => ?_⟩` and prove the remaining obligations. Take `⟨hL1, hL2⟩` from `(Fm.large_sup K _ CH).1 hL`.

Establish `hs` using `le_sC'_sCl hL2`. Conclude with `h Fm CH hc (hK Fm CH hc hL1) (hL2.2.2.1 Fm.CGam (by simp [FamP.cMid])) hs.1 hs.2`.
-/
theorem closed_with {𝒞 : FamClass} {Q P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (hQ : Closed 𝒞 Q) (thm th : List ℝ → ℝ)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), 𝒞 Fm → Q Fm CH → thm Fm.cOut ≤ Fm.CGam →
      th (Fm.cOut ++ Fm.cMid CH) ≤ sC' Fm → th (Fm.cOut ++ Fm.cMid CH) ≤ sCl Fm → P Fm CH) : Closed 𝒞 P := by
  obtain ⟨a, ha, hQ⟩ := hQ
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := hQ e he hle
  refine ⟨K.sup ⟨0, fun _ => 0, thm, th⟩, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup K _ CH).1 hL
  have hs := le_sC'_sCl hL2
  exact h Fm CH hc (hK Fm CH hc hL1) (hL2.2.2.1 Fm.CGam (by simp [FamP.cMid])) hs.1 hs.2

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => trivial⟩⟩`.
-/
theorem closed_true (𝒞 : FamClass) : Closed 𝒞 fun _ _ => True :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => trivial⟩⟩

/- English proof (translation)
The claim follows from `closed_with (closed_true 𝒞) thm th fun Fm CH hc _ => h Fm CH hc`.
-/
theorem closed_of_th {𝒞 : FamClass} {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (thm th : List ℝ → ℝ)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), 𝒞 Fm → thm Fm.cOut ≤ Fm.CGam →
      th (Fm.cOut ++ Fm.cMid CH) ≤ sC' Fm → th (Fm.cOut ++ Fm.cMid CH) ≤ sCl Fm → P Fm CH) : Closed 𝒞 P :=
  closed_with (closed_true 𝒞) thm th fun Fm CH hc _ => h Fm CH hc

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cOut_CYL {eps : ℝ} (Fm : FamP eps) : Fm.cOut.getD 6 0 = Fm.CYL := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cOut_CTu {eps : ℝ} (Fm : FamP eps) : Fm.cOut.getD 13 0 = Fm.CTu := rfl

variable (C0 : ℝ)

def closedThreshold (hC : Formalism.L2.SG.RowsConc.KppOffC) (l : List ℝ) : ℝ :=
  max 3 (max (hC (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0).choose
    (hC (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0).choose_spec.choose)

/- English proof (translation)
Use `closed_of_th (fun _ => 0) (closedThreshold C0 hC) fun Fm CH hc _ h1 h2 => ⟨max (sel Fm hc).1 (Fm.x1 + 1), fun x hx i hH => ?_⟩` and prove the remaining obligations. Establish `hx1 : Fm.x1 < x` using `by have := le_trans (le_max_right _ _) hx; linarith`. Establish `c` using `(sel Fm hc).2 x hx1 (le_trans (le_max_left _ _) hx) i`. Establish `hs` using `(hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose_spec`. Establish `e : closedThreshold C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose)` using `rfl`.

Rewrite `h1`, `h2` using `[e]`. Establish `hC' : 1 ≤ sC' Fm` using `le_trans (by norm_num) (le_trans (le_max_left _ _) h1)`. Establish `hK2` using `Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'`. Introduce `u u' hne`. Conclude with `kpp_zero c.hI (hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1)) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u u' hK2 c.tie hne)`.
-/
theorem hypOwn_kppOff (hC : Formalism.L2.SG.RowsConc.KppOffC) {𝒞 : FamClass}
    (sel : CSel 𝒞) :
    Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppOff D := by
  refine closed_of_th (fun _ => 0) (closedThreshold C0 hC) fun Fm CH hc _ h1 h2 => ⟨max (sel Fm hc).1 (Fm.x1 + 1), fun x hx i hH => ?_⟩
  have hx1 : Fm.x1 < x := by have := le_trans (le_max_right _ _) hx; linarith
  have c := (sel Fm hc).2 x hx1 (le_trans (le_max_left _ _) hx) i
  have hs := (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose_spec
  have e : closedThreshold C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose
      (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose) := rfl
  rw [e] at h1 h2
  have hC' : 1 ≤ sC' Fm := le_trans (by norm_num) (le_trans (le_max_left _ _) h1)
  have hK2 := Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'
  intro u u' hne
  exact kpp_zero c.hI (hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1))
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u u' hK2 c.tie hne)

def quadratic_base_change_GL3 (hC : Formalism.L2.SG.RowsConc.KppDiagC) (l : List ℝ) : ℝ :=
  max 3 (max (hC (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0).choose
    (hC (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0).choose_spec.choose)

/- English proof (translation)
Use `closed_of_th (fun _ => 0) (quadratic_base_change_GL3 C0 hC) fun Fm CH hc _ h1 h2 => ⟨max (sel Fm hc).1 (Fm.x1 + 1), fun x hx i hH => ?_⟩` and prove the remaining obligations. Establish `hx1 : Fm.x1 < x` using `by have := le_trans (le_max_right _ _) hx; linarith`. Establish `c` using `(sel Fm hc).2 x hx1 (le_trans (le_max_left _ _) hx) i`. Establish `hs` using `(hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose_spec`. Establish `e : quadratic_base_change_GL3 C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose)` using `rfl`.

Rewrite `h1`, `h2` using `[e]`. Establish `hC' : 1 ≤ sC' Fm` using `le_trans (by norm_num) (le_trans (le_max_left _ _) h1)`. Establish `hK2` using `Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'`. Introduce `u`. Establish `hA` using `hAbs _ c.X c.Y u u c.tie`.

Establish `hd` using `(hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1)) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u hK2 c.tie hA).2`. Unfold `Formalism.L2.SG.RowsOther.KppDiag at hd`. Rewrite `hd` using `[c.tie.2.2.1 u]`. Rewrite using `[hsNormSq_Kpp c.hI hA]`. Unfold `AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.xK`.

Conclude with `hd`.
-/
theorem hypOwn_kppDiag (hC : Formalism.L2.SG.RowsConc.KppDiagC) (hAbs : Formalism.L2.SG.RowsConc.AbsConvTied) {𝒞 : FamClass}
    (sel : CSel 𝒞) :
    Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppDiag D := by
  refine closed_of_th (fun _ => 0) (quadratic_base_change_GL3 C0 hC) fun Fm CH hc _ h1 h2 => ⟨max (sel Fm hc).1 (Fm.x1 + 1), fun x hx i hH => ?_⟩
  have hx1 : Fm.x1 < x := by have := le_trans (le_max_right _ _) hx; linarith
  have c := (sel Fm hc).2 x hx1 (le_trans (le_max_left _ _) hx) i
  have hs := (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose_spec
  have e : quadratic_base_change_GL3 C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose
      (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose) := rfl
  rw [e] at h1 h2
  have hC' : 1 ≤ sC' Fm := le_trans (by norm_num) (le_trans (le_max_left _ _) h1)
  have hK2 := Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'
  intro u
  have hA := hAbs _ c.X c.Y u u c.tie
  have hd := (hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1))
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u hK2 c.tie hA).2
  unfold Formalism.L2.SG.RowsOther.KppDiag at hd
  rw [c.tie.2.2.1 u] at hd
  rw [hsNormSq_Kpp c.hI hA]
  unfold AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.xK
  exact hd

end Family

def DiagCW : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ CB C4 : ℝ, 0 ≤ CB ∧ 0 ≤ C4 ∧ ∀ CG : ℝ, max CB C4 + 1 ≤ CG → ∃ C'₀ Cl₀ : ℝ,
    ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoParameterConditions D large₂ Cl Cg CT →
      Formalism.L2.SG.RowsConc.ConcTie X Y → (Y.tO u u).AbsConv → large₂.CGam = CG →
      Formalism.L2.SG.RowsOther.DiagRow (Y.tO u u) (Formalism.L2.SG.RowsConc.oneC X Y u) (D.mem u).A.GamP
        (Formalism.L2.SG.RowsConc.ddC X Y u u)

/- English proof (translation)
Introduce `Cg cb Cw cT CT C0 A`. Take `⟨CB, C4, h1, h2, C'₀, Cl₀, H⟩` from `h Cg cb Cw cT CT C0 A`. Conclude with `⟨CB, C4, h1, h2, fun CG hG => ⟨C'₀, Cl₀, fun C' Cl a b D large₂ X Y u h3 h4 h5 h6 h7 => H C' Cl a b D large₂ X Y u h3 h4 h5 h6 (h7 ▸ hG)⟩⟩`.
-/
theorem diagCW_of (h : Formalism.L2.SG.RowsConc.DiagC) : DiagCW := by
  intro Cg cb Cw cT CT C0 A
  obtain ⟨CB, C4, h1, h2, C'₀, Cl₀, H⟩ := h Cg cb Cw cT CT C0 A
  exact ⟨CB, C4, h1, h2, fun CG hG => ⟨C'₀, Cl₀, fun C' Cl a b D large₂ X Y u h3 h4 h5 h6 h7 =>
    H C' Cl a b D large₂ X Y u h3 h4 h5 h6 (h7 ▸ hG)⟩⟩

section Family2

open Formalism.L2.SG.Full

variable (C0 : ℝ)

def cDiag (hC : DiagCW) (l : List ℝ) :=
  hC (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0 1

def thmD (hC : DiagCW) (l : List ℝ) : ℝ :=
  max (cDiag C0 hC l).choose (cDiag C0 hC l).choose_spec.choose + 1

def thD (hC : DiagCW) (l : List ℝ) : ℝ :=
  if h : thmD C0 hC (l.take 16) ≤ l.getD 17 0 then
    max 3 (max ((cDiag C0 hC (l.take 16)).choose_spec.choose_spec.2.2 (l.getD 17 0) h).choose
      ((cDiag C0 hC (l.take 16)).choose_spec.choose_spec.2.2 (l.getD 17 0) h).choose_spec.choose)
  else 3

/- English proof (translation)
Use `closed_of_th (thmD C0 hC) (thD C0 hC) fun Fm CH hc hm h1 h2 => ⟨max (sel Fm hc).1 (Fm.x1 + 1), fun x hx i hH => ?_⟩` and prove the remaining obligations. Establish `hx1 : Fm.x1 < x` using `by have := le_trans (le_max_right _ _) hx; linarith`. Establish `c` using `(sel Fm hc).2 x hx1 (le_trans (le_max_left _ _) hx) i`. Establish `e0 : (Fm.cOut ++ Fm.cMid CH).take 16 = Fm.cOut` using `rfl`. Establish `e17 : (Fm.cOut ++ Fm.cMid CH).getD 17 0 = Fm.CGam` using `rfl`.

Establish `hm' : thmD C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16) ≤ (Fm.cOut ++ Fm.cMid CH).getD 17 0`. Rewrite using `[e0, e17]`. Conclude with `hm`. Establish `e1 : thD C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max ((cDiag C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose ((cDiag C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose_spec.choose)` using `dif_pos hm'`. Establish `hs` using `((cDiag C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose_spec.choose_spec`.

Rewrite `h1`, `h2` using `[e1]`. Establish `hC' : 1 ≤ sC' Fm` using `le_trans (by norm_num) (le_trans (le_max_left _ _) h1)`. Establish `hCl : 2 < sCl Fm` using `lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) h2)`. Establish `hK2` using `Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'`. Introduce `u`.

Establish `hH5` using `Formalism.MainNotions.count_hypotheses_diagonal_words _ _ _ _ _ _ _ _ _ _ 1 hH.1 hH.2.1 hH.2.2 hCl hC' le_rfl u`. Establish `hA` using `hAbs _ c.X c.Y u u c.tie`. Establish `hG : (Fm.L x i).CGam = (Fm.cOut ++ Fm.cMid CH).getD 17 0` using `by rw [e17]; exact Fm.CGam_eq x i`. Establish `hd` using `hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1)) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u hH5 hK2.2 c.tie hA hG`. Unfold `Formalism.L2.SG.RowsOther.DiagRow Formalism.L2.SG.RowsConc.ddC at hd`.

Rewrite `hd` using `[c.tie.2.2.1 u, c.tie.2.2.2.1, (Fm.D x i).GamP_eq u]`. Rewrite using `[hsNormSq_diag c.hI (hExp _ c.X c.Y u u c.tie) hA (Formalism.L2.SG.Pf.SatGram.idDegenerate_tO c.Y u u)]`. Unfold `AdmissibleBoundsFromSource.Gam AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.Dst`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hypOwn_diag (hC : DiagCW) (hExp : KExpTied) (hAbs : Formalism.L2.SG.RowsConc.AbsConvTied)
    {𝒞 : FamClass} (sel : CSel 𝒞) :
    Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClDiag D := by
  refine closed_of_th (thmD C0 hC) (thD C0 hC) fun Fm CH hc hm h1 h2 => ⟨max (sel Fm hc).1 (Fm.x1 + 1), fun x hx i hH => ?_⟩
  have hx1 : Fm.x1 < x := by have := le_trans (le_max_right _ _) hx; linarith
  have c := (sel Fm hc).2 x hx1 (le_trans (le_max_left _ _) hx) i
  have e0 : (Fm.cOut ++ Fm.cMid CH).take 16 = Fm.cOut := rfl
  have e17 : (Fm.cOut ++ Fm.cMid CH).getD 17 0 = Fm.CGam := rfl
  have hm' : thmD C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16) ≤ (Fm.cOut ++ Fm.cMid CH).getD 17 0 := by
    rw [e0, e17]; exact hm
  have e1 : thD C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3
      (max ((cDiag C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose
        ((cDiag C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose_spec.choose) :=
    dif_pos hm'
  have hs := ((cDiag C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose_spec.choose_spec
  rw [e1] at h1 h2
  have hC' : 1 ≤ sC' Fm := le_trans (by norm_num) (le_trans (le_max_left _ _) h1)
  have hCl : 2 < sCl Fm := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) h2)
  have hK2 := Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'
  intro u
  have hH5 := Formalism.MainNotions.count_hypotheses_diagonal_words _ _ _ _ _ _ _ _ _ _ 1 hH.1 hH.2.1 hH.2.2 hCl hC' le_rfl u
  have hA := hAbs _ c.X c.Y u u c.tie
  have hG : (Fm.L x i).CGam = (Fm.cOut ++ Fm.cMid CH).getD 17 0 := by rw [e17]; exact Fm.CGam_eq x i
  have hd := hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1))
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u hH5 hK2.2 c.tie hA hG
  unfold Formalism.L2.SG.RowsOther.DiagRow Formalism.L2.SG.RowsConc.ddC at hd
  rw [c.tie.2.2.1 u, c.tie.2.2.2.1, (Fm.D x i).GamP_eq u] at hd
  rw [hsNormSq_diag c.hI (hExp _ c.X c.Y u u c.tie) hA (Formalism.L2.SG.Pf.SatGram.idDegenerate_tO c.Y u u)]
  unfold AdmissibleBoundsFromSource.Gam AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.Dst
  calc _ ≤ _ := hd
    _ = _ := by ring

/- English proof (translation)
Use `closed_with hO (fun _ => 0) (closedThreshold C0 hC) fun Fm CH hc hO' _ h1 h2 => ?_` and prove the remaining obligations. Take `⟨x0, H⟩` from `hO' hc`. Use `⟨max x0 (max (sel Fm hc).1 (Fm.x1 + 1)), fun x hx i hH => ?_⟩` and prove the remaining obligations. Establish `hx'` using `le_trans (le_max_right _ _) hx`. Establish `hx1 : Fm.x1 < x` using `by have := le_trans (le_max_right _ _) hx'; linarith`.

Establish `h0 : (sel Fm hc).1 ≤ x` using `le_trans (le_max_left _ _) hx'`. Set `c` to `(sel Fm hc).2 x hx1 h0 i`. Establish `hs` using `(hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose_spec`. Establish `e : closedThreshold C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose)` using `rfl`. Rewrite `h1`, `h2` using `[e]`.

Establish `hC' : 1 ≤ sC' Fm` using `le_trans (by norm_num) (le_trans (le_max_left _ _) h1)`. Establish `hK2` using `Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'`. Introduce `u u' hne`. Establish `hZ` using `hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1)) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u u' hK2 c.tie hne`. Establish `hb : 0 ≤ (Fm.L x i).sc.b` using `le_trans zero_le_two (Formalism.MainNotions.S.two_le_scb _)`.

Rewrite using `[hsNormSq_off c.hI (hExp _ c.X c.Y u u' c.tie) (hAbs _ c.X c.Y u u' c.tie) (Formalism.L2.SG.Pf.SatGram.idDegenerate_tO c.Y u u') hZ]`. Establish `hK` using `H x (le_trans (le_max_left _ _) hx) i hH hx1 h0 u u' hne`. Unfold `AdmissibleBoundsFromSource.eta0 AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.Dst`. Rewrite using `[Formalism.L2.SG.PackageTie.rpow_neg_six hb]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hypOwn_off (hC : Formalism.L2.SG.RowsConc.KppOffC) (hExp : KExpTied) (hAbs : Formalism.L2.SG.RowsConc.AbsConvTied)
    {𝒞 : FamClass} (sel : CSel 𝒞)
    (hO : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, TheoremSDifferentWords Fm C0 (sel Fm hc)) :
    Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D L => ClOff D L := by
  refine closed_with hO (fun _ => 0) (closedThreshold C0 hC) fun Fm CH hc hO' _ h1 h2 => ?_
  obtain ⟨x0, H⟩ := hO' hc
  refine ⟨max x0 (max (sel Fm hc).1 (Fm.x1 + 1)), fun x hx i hH => ?_⟩
  have hx' := le_trans (le_max_right _ _) hx
  have hx1 : Fm.x1 < x := by have := le_trans (le_max_right _ _) hx'; linarith
  have h0 : (sel Fm hc).1 ≤ x := le_trans (le_max_left _ _) hx'
  let c := (sel Fm hc).2 x hx1 h0 i
  have hs := (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose_spec
  have e : closedThreshold C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose
      (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose) := rfl
  rw [e] at h1 h2
  have hC' : 1 ≤ sC' Fm := le_trans (by norm_num) (le_trans (le_max_left _ _) h1)
  have hK2 := Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'
  intro u u' hne
  have hZ := hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1))
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u u' hK2 c.tie hne
  have hb : 0 ≤ (Fm.L x i).sc.b := le_trans zero_le_two (Formalism.MainNotions.S.two_le_scb _)
  rw [hsNormSq_off c.hI (hExp _ c.X c.Y u u' c.tie) (hAbs _ c.X c.Y u u' c.tie)
    (Formalism.L2.SG.Pf.SatGram.idDegenerate_tO c.Y u u') hZ]
  have hK := H x (le_trans (le_max_left _ _) hx) i hH hx1 h0 u u' hne
  unfold AdmissibleBoundsFromSource.eta0 AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.Dst
  rw [Formalism.L2.SG.PackageTie.rpow_neg_six hb]
  calc _ ≤ _ := hK
    _ = _ := by ring

/- English proof (translation)
The claim follows from `linkS_concrete 𝒞 C0 c30 h1 hc30 hRes hRows (hypOwn_kppOff C0 hK2a sel) (hypOwn_kppDiag C0 hK2b hAbs sel) (hypOwn_off C0 hK2a hExp hAbs sel hO) (hypOwn_diag C0 hDg hExp hAbs sel) S30 A30`.
-/
theorem linkS_conc (𝒞 : FamClass) (sel : CSel 𝒞) (c30 : List ℝ → CountingConstants)
    (h1 : 1 ≤ C0)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm)
    (hRows : Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut, PlaceDegreeData.RowsTie (Fm.D x i) X)
    (hK2a : Formalism.L2.SG.RowsConc.KppOffC) (hK2b : Formalism.L2.SG.RowsConc.KppDiagC) (hDg : DiagCW)
    (hExp : KExpTied) (hAbs : Formalism.L2.SG.RowsConc.AbsConvTied)
    (hO : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, TheoremSDifferentWords Fm C0 (sel Fm hc))
    (S30 : Closed 𝒞 fun Fm _ => PlaceDegreeData.KudlaFamilyStatement Fm (c30 Fm.cOut).Cres (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).Cb
      (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (A30 : Closed 𝒞 fun Fm _ => PlaceDegreeData.AdmF Fm (c30 Fm.cOut).Cres) :
    Closed 𝒞 fun Fm _ => TuSize Fm → Formalism.MainNotions.LinkS Fm C0 :=
  linkS_concrete 𝒞 C0 c30 h1 hc30 hRes hRows (hypOwn_kppOff C0 hK2a sel) (hypOwn_kppDiag C0 hK2b hAbs sel)
    (hypOwn_off C0 hK2a hExp hAbs sel hO) (hypOwn_diag C0 hDg hExp hAbs sel) S30 A30

end Family2

section ClosedE

/- English proof (translation)
The claim follows from `closed_of_large (linkThresholds (fun _ => caZero) c30) (hRes.and (hRows.and (hK1.and (hK2.and (hK3.and (hK4.and (S30.and A30))))))) fun Fm CH hL h a0 => by obtain ⟨-, g2, g3, g4⟩ := link_thresholds_spec Fm CH (fun _ => caZero) c30 hL obtain ⟨a1, a2, k1, k2, k3, k4, a6, a7⟩ := h e …`.
-/
theorem linkS_concreteE (𝒞 : FamClass) (C0 : ℝ) (c30 : List ℝ → CountingConstants) (h1 : 1 ≤ C0)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm)
    (hRows : Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut,
      CountE.RowsTieP CountE.PLev (Fm.D x i) X)
    (hK1 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppOff D)
    (hK2 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppDiag D)
    (hK3 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D L => ClOff D L)
    (hK4 : Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClDiag D)
    (S30 : Closed 𝒞 fun Fm _ => CountE.ShareFamilyAtConstant CountE.PLev Fm (c30 Fm.cOut).Cres (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).Cb (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (A30 : Closed 𝒞 fun Fm _ => PlaceDegreeData.AdmF Fm (c30 Fm.cOut).Cres) :
    Closed 𝒞 fun Fm _ => TuSize Fm → Formalism.MainNotions.LinkS Fm C0 :=
  closed_of_large (linkThresholds (fun _ => caZero) c30)
    (hRes.and (hRows.and (hK1.and (hK2.and (hK3.and (hK4.and (S30.and A30)))))))
    fun Fm CH hL h a0 => by
      obtain ⟨-, g2, g3, g4⟩ := link_thresholds_spec Fm CH (fun _ => caZero) c30 hL
      obtain ⟨a1, a2, k1, k2, k3, k4, a6, a7⟩ := h
      exact CountE.linkS_of_thmSP CountE.PLev Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 _ _ _ _ _ _ _ h1
        (hc30 Fm).1 (hc30 Fm).2 g2 g3 (standing_hypotheses_hold_family Fm C0 h1 ⟨g4, a0, a1⟩) a2 (thmSOwn_of_clauses k1 k2 k3 k4) a6 a7

end ClosedE

section FamilyE

variable (C0 : ℝ)

/- English proof (translation)
The claim follows from `linkS_concreteE 𝒞 C0 c30 h1 hc30 hRes hRows (hypOwn_kppOff C0 hK2a sel) (hypOwn_kppDiag C0 hK2b hAbs sel) (hypOwn_off C0 hK2a hExp hAbs sel hO) (hypOwn_diag C0 hDg hExp hAbs sel) S30 A30`.
-/
theorem linkS_concE (𝒞 : FamClass) (sel : CSel 𝒞) (c30 : List ℝ → CountingConstants) (h1 : 1 ≤ C0)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm)
    (hRows : Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut,
      CountE.RowsTieP CountE.PLev (Fm.D x i) X)
    (hK2a : Formalism.L2.SG.RowsConc.KppOffC) (hK2b : Formalism.L2.SG.RowsConc.KppDiagC) (hDg : DiagCW)
    (hExp : KExpTied) (hAbs : Formalism.L2.SG.RowsConc.AbsConvTied)
    (hO : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, TheoremSDifferentWords Fm C0 (sel Fm hc))
    (S30 : Closed 𝒞 fun Fm _ => CountE.ShareFamilyAtConstant CountE.PLev Fm (c30 Fm.cOut).Cres (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).Cb (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (A30 : Closed 𝒞 fun Fm _ => PlaceDegreeData.AdmF Fm (c30 Fm.cOut).Cres) :
    Closed 𝒞 fun Fm _ => TuSize Fm → Formalism.MainNotions.LinkS Fm C0 :=
  linkS_concreteE 𝒞 C0 c30 h1 hc30 hRes hRows (hypOwn_kppOff C0 hK2a sel) (hypOwn_kppDiag C0 hK2b hAbs sel)
    (hypOwn_off C0 hK2a hExp hAbs sel hO) (hypOwn_diag C0 hDg hExp hAbs sel) S30 A30

end FamilyE

section Sel

def SSelF {eps : ℝ} (Fm : FamP eps) :=
  Σ' x0 : ℝ, ∀ x (_ : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, Formalism.L2.SG.SpectralTiesReal.STies (Fm.D x i)

def SSel (𝒞 : FamClass) := ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → SSelF Fm

def STiesOK {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) : Prop :=
  FinX T.Y ∧ T.X.LevelSubgroupNormalized ∧ (∀ u, Formalism.L2.SG.PoincareInHH.Cut.NeatKu T.X u T.Y.hK) ∧ Formalism.L2.SG.WuDecay.WuDecay T.X ∧
    Integrable T.X.ph (Formalism.L2.SG.ProjRows.muInf T.X.B.I) ∧ Formalism.L2.SG.Pf.LocCP.LocTied D ∧ Formalism.L2.SG.RowsConc.TFrameAt D

def concKOf {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) (h : STiesOK T) : ConcK D :=
  ⟨T.X, T.Y, h.1, T.hI h.1, T.concTie h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩

def cselOf {𝒞 : FamClass} (sel : SSel 𝒞)
    (hOK : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      STiesOK ((sel Fm hc).2 x hx h0 i)) : CSel 𝒞 :=
  fun Fm hc => ⟨(sel Fm hc).1, fun x hx h0 i => concKOf ((sel Fm hc).2 x hx h0 i) (hOK Fm hc x hx h0 i)⟩

def TheoremSSelected {eps : ℝ} (Fm : FamP eps) (C0 : ℝ) (s : SSelF Fm) : Prop :=
  OwnEv Fm fun C' Cl x i =>
    AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
    ∀ (hx : Fm.x1 < x) (h0 : s.1 ≤ x) (u u' : (Fm.D x i).what₂.Word), u ≠ u' →
      ‖((s.2 x hx h0 i).Y.tO u u').K0‖ ^ 2 ≤ (1 + ((Fm.L x i).sc.b ^ 6)⁻¹) *
        (((Fm.D x i).duS u : ℝ) * ((Fm.D x i).duS u') / (Fm.D x i).what₂.Dstar)

/- English proof (translation)
The claim follows from `h`.
-/
theorem theoremS_different_of_selected {𝒞 : FamClass} (sel : SSel 𝒞)
    (hOK : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      STiesOK ((sel Fm hc).2 x hx h0 i)) {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) (C0 : ℝ)
    (h : TheoremSSelected Fm C0 (sel Fm hc)) : TheoremSDifferentWords Fm C0 (cselOf sel hOK Fm hc) := h

variable (C0 : ℝ)

/- English proof (translation)
The claim follows from `linkS_concE C0 𝒞 (cselOf sel hOK) c30 h1 hc30 hRes hRows hK2a hK2b hDg hExp hAbs (hO.imp fun Fm _ _ h hc => theoremS_different_of_selected sel hOK Fm hc C0 (h hc)) S30 A30`.
-/
theorem linkS_sel (𝒞 : FamClass) (sel : SSel 𝒞)
    (hOK : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      STiesOK ((sel Fm hc).2 x hx h0 i))
    (c30 : List ℝ → CountingConstants) (h1 : 1 ≤ C0)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm)
    (hRows : Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut,
      CountE.RowsTieP CountE.PLev (Fm.D x i) X)
    (hK2a : Formalism.L2.SG.RowsConc.KppOffC) (hK2b : Formalism.L2.SG.RowsConc.KppDiagC) (hDg : DiagCW)
    (hExp : KExpTied) (hAbs : Formalism.L2.SG.RowsConc.AbsConvTied)
    (hO : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, TheoremSSelected Fm C0 (sel Fm hc))
    (S30 : Closed 𝒞 fun Fm _ => CountE.ShareFamilyAtConstant CountE.PLev Fm (c30 Fm.cOut).Cres (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).Cb (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (A30 : Closed 𝒞 fun Fm _ => PlaceDegreeData.AdmF Fm (c30 Fm.cOut).Cres) :
    Closed 𝒞 fun Fm _ => TuSize Fm → Formalism.MainNotions.LinkS Fm C0 :=
  linkS_concE C0 𝒞 (cselOf sel hOK) c30 h1 hc30 hRes hRows hK2a hK2b hDg hExp hAbs
    (hO.imp fun Fm _ _ h hc => theoremS_different_of_selected sel hOK Fm hc C0 (h hc)) S30 A30

end Sel

/- English proof (translation)
Take `⟨-, hk, hmf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap, -, -, -, -⟩` from `h`. Establish `hL : 1 < large₂.sc.L` using `Formalism.MainNotions.S.one_lt_scL large₂`. Establish `hm2 : 2 ≤ D.R.m` using `D.R.two_le_m`. Establish `hm : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm2`. Establish `hf16 : 16 ≤ D.R.f` using `le_trans (by`.

Combine the equalities or inequalities in the displayed calculation. Establish `hf : (16 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf16`. Establish `hkn : D.R.k ≤ D.R.r` using `by have := D.R.two_le_m; unfold Formalism.BasicNotions.Ranks.r; omega`. Establish `hm5 : (32 : ℝ) ≤ (D.R.m : ℝ) ^ 5`. Combine the equalities or inequalities in the displayed calculation.

Establish `hkR : (1801 : ℝ) ≤ D.R.k`. Establish `h1 : (29 : ℝ) * 32 * 16 * 1 ≤ C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk1801 : 1801 ≤ D.R.k` using `by exact_mod_cast hkR`. Use `⟨le_trans hk1801 hkn, fun τ j hj => ?_⟩` and prove the remaining obligations.

Establish `g` using `hgap τ (j.1 + 1) (by omega) (by omega)`. Rewrite `g` using `[Formalism.MainNotions.S.bOne_succ τ (j.1 + 1) hj, Formalism.MainNotions.S.bOne_succ τ j.1 j.2]`. Establish `hn0 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19` using `by positivity`. Establish `hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5` using `one_le_pow₀ (by linarith)`. Establish `h16 : 16 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L`.

Establish `a1 : 16 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19` using `by nlinarith`. Establish `a2 : Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * large₂.sc.L)` using `le_mul_of_one_le_right (by positivity) (by nlinarith)`. Combine the linear relations using `[show Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) = Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L by ring]`. Establish `hR : ((16 * (D.R.r : ℚ) ^ 19 : ℚ) : ℝ) ≤ (((D.hc τ).b ⟨j.1 + 1, hj⟩ - (D.hc τ).b j : ℚ) : ℝ)`. Use `push_cast`.

Establish `e : ((D.hc τ).b ⟨j.1, j.2⟩ : ℝ) = ((D.hc τ).b j : ℝ)` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hR` after adjusting the coercions.
-/
theorem gap_hypothesis_of_hypotheses {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ}
    (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCl : 16 ≤ Cl) (hC' : 29 ≤ C') : Formalism.L2.SG.ConcreteSettingExists.GapHyp D := by
  obtain ⟨-, hk, hmf, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap, -, -, -, -⟩ := h
  have hL : 1 < large₂.sc.L := Formalism.MainNotions.S.one_lt_scL large₂
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hf16 : 16 ≤ D.R.f := le_trans (by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4) hmf
  have hf : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf16
  have hkn : D.R.k ≤ D.R.r := by have := D.R.two_le_m; unfold Formalism.BasicNotions.Ranks.r; omega
  have hm5 : (32 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := by
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hm 5
  have hkR : (1801 : ℝ) ≤ D.R.k := by
    have h1 : (29 : ℝ) * 32 * 16 * 1 ≤ C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      gcongr
    linarith
  have hk1801 : 1801 ≤ D.R.k := by exact_mod_cast hkR
  refine ⟨le_trans hk1801 hkn, fun τ j hj => ?_⟩
  have g := hgap τ (j.1 + 1) (by omega) (by omega)
  rw [Formalism.MainNotions.S.bOne_succ τ (j.1 + 1) hj, Formalism.MainNotions.S.bOne_succ τ j.1 j.2] at g
  have hn0 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ (by linarith)
  have h16 : 16 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have a1 : 16 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := by nlinarith
    have a2 : Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) :=
      le_mul_of_one_le_right (by positivity) (by nlinarith)
    linarith [show Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) =
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L by ring]
  have hR : ((16 * (D.R.r : ℚ) ^ 19 : ℚ) : ℝ) ≤ (((D.hc τ).b ⟨j.1 + 1, hj⟩ - (D.hc τ).b j : ℚ) : ℝ) := by
    push_cast
    have e : ((D.hc τ).b ⟨j.1, j.2⟩ : ℝ) = ((D.hc τ).b j : ℝ) := rfl
    linarith
  exact_mod_cast hR

/- English proof (translation)
Take `⟨-, hk, hmf, hfk, -, -, -, -, -, -, -, hg1, -, hg2, -, hbj, -, -, -, -, -, -, -, -, -⟩` from `h`. Establish `hL : 1 < large₂.sc.L` using `Formalism.MainNotions.S.one_lt_scL large₂`. Establish `hlogb : Real.log large₂.sc.b = large₂.sc.L` using `Formalism.MainNotions.S.log_scb large₂`. Establish `hb2 : 2 ≤ large₂.sc.b` using `Formalism.MainNotions.S.two_le_scb large₂`. Establish `hm2 : 2 ≤ D.R.m` using `D.R.two_le_m`.

Establish `hm : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm2`. Establish `hf16 : 16 ≤ D.R.f` using `le_trans (by`. Combine the equalities or inequalities in the displayed calculation. Establish `hf : (16 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf16`. Establish `hm4 : (16 : ℝ) ≤ (D.R.m : ℝ) ^ 4`.

Combine the equalities or inequalities in the displayed calculation. Establish `hm5 : 16 * (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 5`. Establish `e : (D.R.m : ℝ) ^ 5 = (D.R.m : ℝ) * (D.R.m : ℝ) ^ 4` using `by ring`. Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hX : 256 * (D.R.m : ℝ) * large₂.sc.L ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L`. Establish `: 256 * (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hX0 : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L` using `by positivity`. Establish `hkX : 70 * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) ≤ D.R.k`.

Establish `: 70 * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)` using `mul_le_mul_of_nonneg_right hC' hX0`. Establish `e : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L = C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkR : (35840 : ℝ) ≤ D.R.k` using `by nlinarith`. Establish `hkm : 2 * (D.R.m : ℝ) + 8 ≤ D.R.k` using `by nlinarith`.

Establish `hkm' : 2 * D.R.m + 8 ≤ D.R.k` using `by exact_mod_cast hkm`. Establish `hm2r : 2 * D.R.rS + 2 = D.R.m`. Unfold `Formalism.BasicNotions.Ranks.rS`. Take `⟨j, hj⟩` from `D.R.m_even`. Use linear arithmetic over natural numbers and integers.

Establish `hcard : 0 < Fintype.card D.what₂.Tau`. Rewrite using `[← Formalism.MainNotions.BesselShellMomentBounds.card_places D, Formalism.MainNotions.LatticeGluingRadicals.d_card D]`. Use linear arithmetic over natural numbers and integers. Take `⟨τ⟩` from `Fintype.card_pos_iff.1 hcard`. Establish `hb1` using `hbj τ 1 le_rfl (by omega)`.

Establish `hkb : (D.R.k : ℝ) ≤ large₂.sc.b ^ 2`. Establish `h1 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ Cl` using `Real.self_le_rpow_of_one_le (by linarith) (by linarith)`. Establish `h2` using `le_trans (le_max_left _ _) hb1.1`. Establish `h3` using `hb1.2`. Rewrite `h3` using `[Real.rpow_two]`.

Conclude with `le_trans h1 (le_trans h2 h3)`. Use `⟨by nlinarith, by exact_mod_cast (show (32 : ℝ) ≤ D.R.k by linarith), hfk, by omega, hg1, hg2, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hlogb]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlk : (1 : ℝ) ≤ Real.log D.R.k`.

Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hm2r, hlogb]`.

Establish `: 8 * (Cn * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) = (8 * Cn) * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)` using `by ring`. Rewrite using `[this]`. Establish `h1 : (8 * Cn) * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)` using `mul_le_mul_of_nonneg_right hCn hX0`. Establish `e : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L = C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem size_numbers_of_hypotheses {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT Cn : ℝ}
    (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCl : 16 ≤ Cl) (hC' : 70 ≤ C') (hCn : 8 * Cn ≤ C') :
    Formalism.FourierDecayAlt.PB.SizeNumbers D.R.k D.R.rS D.R.f large₂.sc.b (D.host.g 0) (D.host.g 1) (1 / 3) Cn := by
  obtain ⟨-, hk, hmf, hfk, -, -, -, -, -, -, -, hg1, -, hg2, -, hbj, -, -, -, -, -, -, -, -, -⟩ := h
  have hL : 1 < large₂.sc.L := Formalism.MainNotions.S.one_lt_scL large₂
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := Formalism.MainNotions.S.log_scb large₂
  have hb2 : 2 ≤ large₂.sc.b := Formalism.MainNotions.S.two_le_scb large₂
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hf16 : 16 ≤ D.R.f := le_trans (by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4) hmf
  have hf : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf16
  have hm4 : (16 : ℝ) ≤ (D.R.m : ℝ) ^ 4 := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hm 4
  have hm5 : 16 * (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 5 := by
    have e : (D.R.m : ℝ) ^ 5 = (D.R.m : ℝ) * (D.R.m : ℝ) ^ 4 := by ring
    rw [e]; nlinarith
  have hX : 256 * (D.R.m : ℝ) * large₂.sc.L ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
    have : 256 * (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f := by nlinarith
    nlinarith
  have hX0 : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
  have hkX : 70 * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) ≤ D.R.k := by
    have : 70 * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) :=
      mul_le_mul_of_nonneg_right hC' hX0
    have e : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L = C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by ring
    linarith
  have hkR : (35840 : ℝ) ≤ D.R.k := by nlinarith
  have hkm : 2 * (D.R.m : ℝ) + 8 ≤ D.R.k := by nlinarith
  have hkm' : 2 * D.R.m + 8 ≤ D.R.k := by exact_mod_cast hkm
  have hm2r : 2 * D.R.rS + 2 = D.R.m := by
    unfold Formalism.BasicNotions.Ranks.rS; obtain ⟨j, hj⟩ := D.R.m_even; omega
  have hcard : 0 < Fintype.card D.what₂.Tau := by
    rw [← Formalism.MainNotions.BesselShellMomentBounds.card_places D, Formalism.MainNotions.LatticeGluingRadicals.d_card D]; omega
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hcard
  have hb1 := hbj τ 1 le_rfl (by omega)
  have hkb : (D.R.k : ℝ) ≤ large₂.sc.b ^ 2 := by
    have h1 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ Cl := Real.self_le_rpow_of_one_le (by linarith) (by linarith)
    have h2 := le_trans (le_max_left _ _) hb1.1
    have h3 := hb1.2
    rw [Real.rpow_two] at h3
    exact le_trans h1 (le_trans h2 h3)
  refine ⟨by nlinarith, by exact_mod_cast (show (32 : ℝ) ≤ D.R.k by linarith), hfk, by omega, hg1, hg2, ?_, ?_, ?_⟩
  · rw [hlogb]; nlinarith
  · have hlk : (1 : ℝ) ≤ Real.log D.R.k := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    nlinarith
  · rw [hm2r, hlogb]
    have : 8 * (Cn * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) = (8 * Cn) * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by ring
    rw [this]
    have h1 : (8 * Cn) * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) :=
      mul_le_mul_of_nonneg_right hCn hX0
    have e : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L = C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by ring
    linarith

section SelH

variable (C0 : ℝ)

def SelOK {eps : ℝ} (Fm : FamP eps) (s : SSelF Fm) : Prop :=
  OwnEv Fm fun C' Cl x i =>
    AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
    ∀ (hx : Fm.x1 < x) (h0 : s.1 ≤ x), STiesOK (s.2 x hx h0 i)

def ConcEv {eps : ℝ} (Fm : FamP eps) : Prop :=
  OwnEv Fm fun C' Cl x i =>
    AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu → Nonempty (ConcK (Fm.D x i))

/- English proof (translation)
Take `⟨x0, H⟩` from `h`. Use `⟨max x0 (max s.1 (Fm.x1 + 1)), fun x hx i hH => ?_⟩` and prove the remaining obligations. Establish `hx'` using `le_trans (le_max_right _ _) hx`. Establish `hx1 : Fm.x1 < x` using `by have := le_trans (le_max_right _ _) hx'; linarith`. Establish `h0 : s.1 ≤ x` using `le_trans (le_max_left _ _) hx'`.

Conclude with `⟨concKOf (s.2 x hx1 h0 i) (H x (le_trans (le_max_left _ _) hx) i hH hx1 h0)⟩`.
-/
theorem concEv_of_sel {eps : ℝ} {Fm : FamP eps} {s : SSelF Fm} (h : SelOK C0 Fm s) : ConcEv C0 Fm := by
  obtain ⟨x0, H⟩ := h
  refine ⟨max x0 (max s.1 (Fm.x1 + 1)), fun x hx i hH => ?_⟩
  have hx' := le_trans (le_max_right _ _) hx
  have hx1 : Fm.x1 < x := by have := le_trans (le_max_right _ _) hx'; linarith
  have h0 : s.1 ≤ x := le_trans (le_max_left _ _) hx'
  exact ⟨concKOf (s.2 x hx1 h0 i) (H x (le_trans (le_max_left _ _) hx) i hH hx1 h0)⟩

/- English proof (translation)
Use `closed_with hE (fun _ => 0) (closedThreshold C0 hC) fun Fm CH _ hE' _ h1 h2 => ?_` and prove the remaining obligations. Take `⟨x0, H⟩` from `hE'`. Use `⟨x0, fun x hx i hH => ?_⟩` and prove the remaining obligations. Take `⟨c⟩` from `H x hx i hH`. Establish `hs` using `(hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose_spec`.

Establish `e : closedThreshold C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose)` using `rfl`. Rewrite `h1`, `h2` using `[e]`. Establish `hC' : 1 ≤ sC' Fm` using `le_trans (by norm_num) (le_trans (le_max_left _ _) h1)`. Establish `hK2` using `Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'`. Introduce `u u' hne`.

Conclude with `kpp_zero c.hI (hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1)) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u u' hK2 c.tie hne)`.
-/
theorem hypOwnE_kppOff (hC : Formalism.L2.SG.RowsConc.KppOffC) {𝒞 : FamClass}
    (hE : Closed 𝒞 fun Fm _ => ConcEv C0 Fm) :
    Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppOff D := by
  refine closed_with hE (fun _ => 0) (closedThreshold C0 hC) fun Fm CH _ hE' _ h1 h2 => ?_
  obtain ⟨x0, H⟩ := hE'
  refine ⟨x0, fun x hx i hH => ?_⟩
  obtain ⟨c⟩ := H x hx i hH
  have hs := (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose_spec
  have e : closedThreshold C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose
      (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose) := rfl
  rw [e] at h1 h2
  have hC' : 1 ≤ sC' Fm := le_trans (by norm_num) (le_trans (le_max_left _ _) h1)
  have hK2 := Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'
  intro u u' hne
  exact kpp_zero c.hI (hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1))
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u u' hK2 c.tie hne)

/- English proof (translation)
Use `closed_with hE (fun _ => 0) (quadratic_base_change_GL3 C0 hC) fun Fm CH _ hE' _ h1 h2 => ?_` and prove the remaining obligations. Take `⟨x0, H⟩` from `hE'`. Use `⟨x0, fun x hx i hH => ?_⟩` and prove the remaining obligations. Take `⟨c⟩` from `H x hx i hH`. Establish `hs` using `(hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose_spec`.

Establish `e : quadratic_base_change_GL3 C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose)` using `rfl`. Rewrite `h1`, `h2` using `[e]`. Establish `hC' : 1 ≤ sC' Fm` using `le_trans (by norm_num) (le_trans (le_max_left _ _) h1)`. Establish `hK2` using `Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'`. Introduce `u`.

Establish `hA` using `hAbs _ c.X c.Y u u c.tie`. Establish `hd` using `(hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1)) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u hK2 c.tie hA).2`. Unfold `Formalism.L2.SG.RowsOther.KppDiag at hd`. Rewrite `hd` using `[c.tie.2.2.1 u]`. Rewrite using `[hsNormSq_Kpp c.hI hA]`.

Unfold `AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.xK`. Conclude with `hd`.
-/
theorem hypOwnE_kppDiag (hC : Formalism.L2.SG.RowsConc.KppDiagC) (hAbs : Formalism.L2.SG.RowsConc.AbsConvTied) {𝒞 : FamClass}
    (hE : Closed 𝒞 fun Fm _ => ConcEv C0 Fm) :
    Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClKppDiag D := by
  refine closed_with hE (fun _ => 0) (quadratic_base_change_GL3 C0 hC) fun Fm CH _ hE' _ h1 h2 => ?_
  obtain ⟨x0, H⟩ := hE'
  refine ⟨x0, fun x hx i hH => ?_⟩
  obtain ⟨c⟩ := H x hx i hH
  have hs := (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose_spec
  have e : quadratic_base_change_GL3 C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose
      (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose) := rfl
  rw [e] at h1 h2
  have hC' : 1 ≤ sC' Fm := le_trans (by norm_num) (le_trans (le_max_left _ _) h1)
  have hK2 := Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'
  intro u
  have hA := hAbs _ c.X c.Y u u c.tie
  have hd := (hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1))
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u hK2 c.tie hA).2
  unfold Formalism.L2.SG.RowsOther.KppDiag at hd
  rw [c.tie.2.2.1 u] at hd
  rw [hsNormSq_Kpp c.hI hA]
  unfold AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.xK
  exact hd

/- English proof (translation)
Use `closed_with hE (thmD C0 hC) (thD C0 hC) fun Fm CH _ hE' hm h1 h2 => ?_` and prove the remaining obligations. Take `⟨x0, H⟩` from `hE'`. Use `⟨x0, fun x hx i hH => ?_⟩` and prove the remaining obligations. Take `⟨c⟩` from `H x hx i hH`. Establish `e0 : (Fm.cOut ++ Fm.cMid CH).take 16 = Fm.cOut` using `rfl`.

Establish `e17 : (Fm.cOut ++ Fm.cMid CH).getD 17 0 = Fm.CGam` using `rfl`. Establish `hm' : thmD C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16) ≤ (Fm.cOut ++ Fm.cMid CH).getD 17 0`. Rewrite using `[e0, e17]`. Conclude with `hm`. Establish `e1 : thD C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max ((cDiag C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose ((cDiag C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose_spec.choose)` using `dif_pos hm'`.

Establish `hs` using `((cDiag C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose_spec.choose_spec`. Rewrite `h1`, `h2` using `[e1]`. Establish `hC' : 1 ≤ sC' Fm` using `le_trans (by norm_num) (le_trans (le_max_left _ _) h1)`. Establish `hCl : 2 < sCl Fm` using `lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) h2)`. Establish `hK2` using `Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'`.

Introduce `u`. Establish `hH5` using `Formalism.MainNotions.count_hypotheses_diagonal_words _ _ _ _ _ _ _ _ _ _ 1 hH.1 hH.2.1 hH.2.2 hCl hC' le_rfl u`. Establish `hA` using `hAbs _ c.X c.Y u u c.tie`. Establish `hG : (Fm.L x i).CGam = (Fm.cOut ++ Fm.cMid CH).getD 17 0` using `by rw [e17]; exact Fm.CGam_eq x i`. Establish `hd` using `hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1)) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u hH5 hK2.2 c.tie hA hG`.

Unfold `Formalism.L2.SG.RowsOther.DiagRow Formalism.L2.SG.RowsConc.ddC at hd`. Rewrite `hd` using `[c.tie.2.2.1 u, c.tie.2.2.2.1, (Fm.D x i).GamP_eq u]`. Rewrite using `[hsNormSq_diag c.hI (hExp _ c.X c.Y u u c.tie) hA (Formalism.L2.SG.Pf.SatGram.idDegenerate_tO c.Y u u)]`. Unfold `AdmissibleBoundsFromSource.Gam AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.Dst`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hypOwnE_diag (hC : DiagCW) (hExp : KExpTied) (hAbs : Formalism.L2.SG.RowsConc.AbsConvTied) {𝒞 : FamClass}
    (hE : Closed 𝒞 fun Fm _ => ConcEv C0 Fm) :
    Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D _ => ClDiag D := by
  refine closed_with hE (thmD C0 hC) (thD C0 hC) fun Fm CH _ hE' hm h1 h2 => ?_
  obtain ⟨x0, H⟩ := hE'
  refine ⟨x0, fun x hx i hH => ?_⟩
  obtain ⟨c⟩ := H x hx i hH
  have e0 : (Fm.cOut ++ Fm.cMid CH).take 16 = Fm.cOut := rfl
  have e17 : (Fm.cOut ++ Fm.cMid CH).getD 17 0 = Fm.CGam := rfl
  have hm' : thmD C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16) ≤ (Fm.cOut ++ Fm.cMid CH).getD 17 0 := by
    rw [e0, e17]; exact hm
  have e1 : thD C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3
      (max ((cDiag C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose
        ((cDiag C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose_spec.choose) :=
    dif_pos hm'
  have hs := ((cDiag C0 hC ((Fm.cOut ++ Fm.cMid CH).take 16)).choose_spec.choose_spec.2.2 _ hm').choose_spec.choose_spec
  rw [e1] at h1 h2
  have hC' : 1 ≤ sC' Fm := le_trans (by norm_num) (le_trans (le_max_left _ _) h1)
  have hCl : 2 < sCl Fm := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) h2)
  have hK2 := Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'
  intro u
  have hH5 := Formalism.MainNotions.count_hypotheses_diagonal_words _ _ _ _ _ _ _ _ _ _ 1 hH.1 hH.2.1 hH.2.2 hCl hC' le_rfl u
  have hA := hAbs _ c.X c.Y u u c.tie
  have hG : (Fm.L x i).CGam = (Fm.cOut ++ Fm.cMid CH).getD 17 0 := by rw [e17]; exact Fm.CGam_eq x i
  have hd := hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1))
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u hH5 hK2.2 c.tie hA hG
  unfold Formalism.L2.SG.RowsOther.DiagRow Formalism.L2.SG.RowsConc.ddC at hd
  rw [c.tie.2.2.1 u, c.tie.2.2.2.1, (Fm.D x i).GamP_eq u] at hd
  rw [hsNormSq_diag c.hI (hExp _ c.X c.Y u u c.tie) hA (Formalism.L2.SG.Pf.SatGram.idDegenerate_tO c.Y u u)]
  unfold AdmissibleBoundsFromSource.Gam AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.Dst
  calc _ ≤ _ := hd
    _ = _ := by ring

/- English proof (translation)
Use `closed_with (hOK.and hO) (fun _ => 0) (closedThreshold C0 hC) fun Fm CH hc hQ _ h1 h2 => ?_` and prove the remaining obligations. Take `⟨x2, H2⟩` from `hQ.1 hc`. Take `⟨x0, H⟩` from `hQ.2 hc`. Use `⟨max x0 (max x2 (max (sel Fm hc).1 (Fm.x1 + 1))), fun x hx i hH => ?_⟩` and prove the remaining obligations. Establish `hxa` using `le_trans (le_max_right _ _) hx`.

Establish `hx'` using `le_trans (le_max_right _ _) hxa`. Establish `hx1 : Fm.x1 < x` using `by have := le_trans (le_max_right _ _) hx'; linarith`. Establish `h0 : (sel Fm hc).1 ≤ x` using `le_trans (le_max_left _ _) hx'`. Set `c` to `concKOf ((sel Fm hc).2 x hx1 h0 i) (H2 x (le_trans (le_max_left _ _) hxa) i hH hx1 h0)`. Establish `hs` using `(hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose_spec`.

Establish `e : closedThreshold C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose)` using `rfl`. Rewrite `h1`, `h2` using `[e]`. Establish `hC' : 1 ≤ sC' Fm` using `le_trans (by norm_num) (le_trans (le_max_left _ _) h1)`. Establish `hK2` using `Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'`. Introduce `u u' hne`.

Establish `hZ` using `hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1)) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u u' hK2 c.tie hne`. Establish `hb : 0 ≤ (Fm.L x i).sc.b` using `le_trans zero_le_two (Formalism.MainNotions.S.two_le_scb _)`. Rewrite using `[hsNormSq_off c.hI (hExp _ c.X c.Y u u' c.tie) (hAbs _ c.X c.Y u u' c.tie) (Formalism.L2.SG.Pf.SatGram.idDegenerate_tO c.Y u u') hZ]`. Establish `hK` using `H x (le_trans (le_max_left _ _) hx) i hH hx1 h0 u u' hne`. Unfold `AdmissibleBoundsFromSource.eta0 AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.Dst`.

Rewrite using `[Formalism.L2.SG.PackageTie.rpow_neg_six hb]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hypOwnS_off (hC : Formalism.L2.SG.RowsConc.KppOffC) (hExp : KExpTied) (hAbs : Formalism.L2.SG.RowsConc.AbsConvTied)
    {𝒞 : FamClass} (sel : SSel 𝒞)
    (hOK : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, SelOK C0 Fm (sel Fm hc))
    (hO : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, TheoremSSelected Fm C0 (sel Fm hc)) :
    Closed 𝒞 fun Fm _ => HypOwn Fm C0 fun D L => ClOff D L := by
  refine closed_with (hOK.and hO) (fun _ => 0) (closedThreshold C0 hC) fun Fm CH hc hQ _ h1 h2 => ?_
  obtain ⟨x2, H2⟩ := hQ.1 hc
  obtain ⟨x0, H⟩ := hQ.2 hc
  refine ⟨max x0 (max x2 (max (sel Fm hc).1 (Fm.x1 + 1))), fun x hx i hH => ?_⟩
  have hxa := le_trans (le_max_right _ _) hx
  have hx' := le_trans (le_max_right _ _) hxa
  have hx1 : Fm.x1 < x := by have := le_trans (le_max_right _ _) hx'; linarith
  have h0 : (sel Fm hc).1 ≤ x := le_trans (le_max_left _ _) hx'
  let c := concKOf ((sel Fm hc).2 x hx1 h0 i) (H2 x (le_trans (le_max_left _ _) hxa) i hH hx1 h0)
  have hs := (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose_spec
  have e : closedThreshold C0 hC (Fm.cOut ++ Fm.cMid CH) = max 3 (max (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose
      (hC (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0).choose_spec.choose) := rfl
  rw [e] at h1 h2
  have hC' : 1 ≤ sC' Fm := le_trans (by norm_num) (le_trans (le_max_left _ _) h1)
  have hK2 := Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 hC'
  intro u u' hne
  have hZ := hs _ _ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h1))
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)) _ _ c.X c.Y u u' hK2 c.tie hne
  have hb : 0 ≤ (Fm.L x i).sc.b := le_trans zero_le_two (Formalism.MainNotions.S.two_le_scb _)
  rw [hsNormSq_off c.hI (hExp _ c.X c.Y u u' c.tie) (hAbs _ c.X c.Y u u' c.tie)
    (Formalism.L2.SG.Pf.SatGram.idDegenerate_tO c.Y u u') hZ]
  have hK := H x (le_trans (le_max_left _ _) hx) i hH hx1 h0 u u' hne
  unfold AdmissibleBoundsFromSource.eta0 AdmissibleBoundsFromSource.du AdmissibleBoundsFromSource.Dst
  rw [Formalism.L2.SG.PackageTie.rpow_neg_six hb]
  calc _ ≤ _ := hK
    _ = _ := by ring

/- English proof (translation)
The claim follows from `have hE : Closed 𝒞 fun Fm _ => ConcEv C0 Fm := closed_with hOK (fun _ => 0) (fun _ => 0) fun Fm _ hc h _ _ _ => concEv_of_sel C0 (h hc) linkS_concreteE 𝒞 C0 c30 h1 hc30 hRes hRows (hypOwnE_kppOff C0 hK2a hE) (hypOwnE_kppDiag C0 hK2b hAbs hE) (hypOwnS_off C0 hK2a hExp hAbs sel hOK …`.
-/
theorem linkS_selH (𝒞 : FamClass) (sel : SSel 𝒞)
    (hOK : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, SelOK C0 Fm (sel Fm hc))
    (c30 : List ℝ → CountingConstants) (h1 : 1 ≤ C0)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (hRes : Closed 𝒞 fun Fm _ => ResidEv Fm)
    (hRows : Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut,
      CountE.RowsTieP CountE.PLev (Fm.D x i) X)
    (hK2a : Formalism.L2.SG.RowsConc.KppOffC) (hK2b : Formalism.L2.SG.RowsConc.KppDiagC) (hDg : DiagCW)
    (hExp : KExpTied) (hAbs : Formalism.L2.SG.RowsConc.AbsConvTied)
    (hO : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, TheoremSSelected Fm C0 (sel Fm hc))
    (S30 : Closed 𝒞 fun Fm _ => CountE.ShareFamilyAtConstant CountE.PLev Fm (c30 Fm.cOut).Cres (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).Cb (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (A30 : Closed 𝒞 fun Fm _ => PlaceDegreeData.AdmF Fm (c30 Fm.cOut).Cres) :
    Closed 𝒞 fun Fm _ => TuSize Fm → Formalism.MainNotions.LinkS Fm C0 :=
  have hE : Closed 𝒞 fun Fm _ => ConcEv C0 Fm :=
    closed_with hOK (fun _ => 0) (fun _ => 0) fun Fm _ hc h _ _ _ => concEv_of_sel C0 (h hc)
  linkS_concreteE 𝒞 C0 c30 h1 hc30 hRes hRows (hypOwnE_kppOff C0 hK2a hE) (hypOwnE_kppDiag C0 hK2b hAbs hE)
    (hypOwnS_off C0 hK2a hExp hAbs sel hOK hO) (hypOwnE_diag C0 hDg hExp hAbs hE) S30 A30

/- English proof (translation)
Establish `hK` using `Formalism.L2.SG.Closed.level_subgroup_properties T.X`. Conclude with `⟨hFX D T hG, hK, fun u => Formalism.L2.SG.Pf.RegroupPf.neatKu_K2Level D T.X T.Y u hK, (hWu D hG T.X).1, (hWu D hG T.X).2, hL, hTF⟩`.
-/
theorem sTiesOK_of (hFX : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC) (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) {D : D7}
    (T : Formalism.L2.SG.SpectralTiesReal.STies D) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (hL : Formalism.L2.SG.Pf.LocCP.LocTied D)
    (hTF : Formalism.L2.SG.RowsConc.TFrameAt D) : STiesOK T := by
  have hK := Formalism.L2.SG.Closed.level_subgroup_properties T.X
  exact ⟨hFX D T hG, hK, fun u => Formalism.L2.SG.Pf.RegroupPf.neatKu_K2Level D T.X T.Y u hK, (hWu D hG T.X).1,
    (hWu D hG T.X).2, hL, hTF⟩

/- English proof (translation)
Use `closed_with hTF (fun _ => 0) (fun _ => 29) fun Fm _ _ hT _ h1 h2 hc => ?_` and prove the remaining obligations. Take `⟨x0, H⟩` from `hT`. Use `⟨x0, fun x hx' i hH hx h0 => ?_⟩` and prove the remaining obligations. Establish `h1' : (29 : ℝ) ≤ sC' Fm` using `h1`. Establish `h2' : (29 : ℝ) ≤ sCl Fm` using `h2`.

Conclude with `sTiesOK_of hFX hWu _ (gap_hypothesis_of_hypotheses hH.2.1 (by linarith) h1') (hLoc Fm hc x hx h0 i) (H x hx' i ⟨hH.2.1, hH.1, hH.2.2⟩)`.
-/
theorem selOK_of (hFX : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC) (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) {𝒞 : FamClass} (sel : SSel 𝒞)
    (hLoc : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒞 Fm) x (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.SG.Pf.LocCP.LocTied (Fm.D x i))
    (hTF : Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0) :
    Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, SelOK C0 Fm (sel Fm hc) := by
  refine closed_with hTF (fun _ => 0) (fun _ => 29) fun Fm _ _ hT _ h1 h2 hc => ?_
  obtain ⟨x0, H⟩ := hT
  refine ⟨x0, fun x hx' i hH hx h0 => ?_⟩
  have h1' : (29 : ℝ) ≤ sC' Fm := h1
  have h2' : (29 : ℝ) ≤ sCl Fm := h2
  exact sTiesOK_of hFX hWu _ (gap_hypothesis_of_hypotheses hH.2.1 (by linarith) h1') (hLoc Fm hc x hx h0 i)
    (H x hx' i ⟨hH.2.1, hH.1, hH.2.2⟩)

end SelH

section OffLeaves

open Formalism.L2.SG.RowsConc

def TheoremSAtDataAlt (CA C0 CG CDel cT Cb Cn : ℝ) (k0 : ℕ) (C' Cl Cg cb Cw cTf CT C0f : ℝ) : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word), u ≠ u' → 0 ≤ L.sc.b →
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.SizesAt CA C0 CG CDel cT Cb Cn k0 D L T u u' →
    Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f → Formalism.MainNotions.S.Cnt.Stand D u u' →
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D L C' Cl Cg cb Cw cTf CT C0f →
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → TFrameAt D →
    (T.Y.tO u u').RowBig (epsL D) (ddC T.X T.Y u u') → (T.Y.tO u u').RowNotScalar (epsL D) (ddC T.X T.Y u u') →
    ‖(T.Y.tO u u').K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * ((D.duS u : ℝ) * (D.duS u') / D.what₂.Dstar)

def TheoremSSingle : Prop :=
  ∀ Cthr : ℝ, ∃ C₄ CA C : ℝ, 1 ≤ C₄ ∧ Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      TheoremSAtDataAlt CA C0 CG CDel cT Cb Cn k0 C' Cl Cg cb Cw cTf CT C0f

def TheoremSClosedHypotheses : Prop :=
  ∀ Cthr : ℝ, ∃ C₄ CA C : ℝ, 1 ≤ C₄ ∧ Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word), u ≠ u' → 0 ≤ L.sc.b →
      Formalism.L2.SG.PoincareAmplitudeLowerBounds.SizesAt CA C0 CG CDel cT Cb Cn k0 D L T u u' →
      Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f → Formalism.MainNotions.S.Cnt.Stand D u u' →
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D L C' Cl Cg cb Cw cTf CT C0f →
      Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → TFrameAt D →
      (T.Y.tO u u').RowBig (epsL D) (ddC T.X T.Y u u') → (T.Y.tO u u').RowNotScalar (epsL D) (ddC T.X T.Y u u') →
      ‖(T.Y.tO u u').K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * ((D.duS u : ℝ) * (D.duS u') / D.what₂.Dstar) ∧
      L.hsSq u u' ≤ (1 + L.sc.b ^ (-(6 : ℝ))) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar

/- English proof (translation)
Introduce `Cthr`. Take `⟨C₄, CA, C, a1, a2, a3, a4, a5, hrest⟩` from `h Cthr`. Use `⟨C₄, CA, C, a1, a2, a3, a4, a5, fun C0 CG CDel cT Cb b1 b2 b3 b4 b5 b6 => ?_⟩` and prove the remaining obligations. Take `⟨k0, hk⟩` from `hrest C0 CG CDel cT Cb b1 b2 b3 b4 b5 b6`. Use `⟨k0, fun Cg cb Cw cTf CT C0f => ?_⟩` and prove the remaining obligations.

Take `⟨Cn, C'₀, Cl₀, hn, hh⟩` from `hk Cg cb Cw cTf CT C0f`. Conclude with `⟨Cn, C'₀, Cl₀, hn, fun C' Cl c1 c2 D L T u u' hne hb hS hH0 hSt hK hG hL hT hR1 hR2 => (hh C' Cl c1 c2 D L T u u' hne hb hS hH0 hSt hK hG hL hT hR1 hR2).1⟩`.
-/
theorem theoremS_single_of_closed (h : TheoremSClosedHypotheses) : TheoremSSingle := by
  intro Cthr
  obtain ⟨C₄, CA, C, a1, a2, a3, a4, a5, hrest⟩ := h Cthr
  refine ⟨C₄, CA, C, a1, a2, a3, a4, a5, fun C0 CG CDel cT Cb b1 b2 b3 b4 b5 b6 => ?_⟩
  obtain ⟨k0, hk⟩ := hrest C0 CG CDel cT Cb b1 b2 b3 b4 b5 b6
  refine ⟨k0, fun Cg cb Cw cTf CT C0f => ?_⟩
  obtain ⟨Cn, C'₀, Cl₀, hn, hh⟩ := hk Cg cb Cw cTf CT C0f
  exact ⟨Cn, C'₀, Cl₀, hn, fun C' Cl c1 c2 D L T u u' hne hb hS hH0 hSt hK hG hL hT hR1 hR2 =>
    (hh C' Cl c1 c2 D L T u u' hne hb hS hH0 hSt hK hG hL hT hR1 hR2).1⟩

variable (C0 : ℝ)

def SizesRowS (𝒞 : FamClass) (sel : SSel 𝒞) : Prop :=
  ∀ CA : ℝ, 1 ≤ CA → ∀ (k0 : List ℝ → ℕ) (cn : List ℝ → ℝ), Closed 𝒞 fun Fm CH => ∀ hc : 𝒞 Fm,
    OwnEv Fm fun C' Cl x i => AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
      ∀ (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (u u' : (Fm.D x i).what₂.Word), u ≠ u' →
        Formalism.L2.SG.PoincareAmplitudeLowerBounds.SizesAt CA C0 Fm.CGam 5 (1 / 2) 3 (cn (Fm.cOut ++ Fm.cMid CH))
          (k0 (Fm.cOut ++ Fm.cMid CH)) (Fm.D x i) (Fm.L x i) ((sel Fm hc).2 x hx h0 i) u u'

def LoopRowS (𝒞 : FamClass) (sel : SSel 𝒞) : Prop :=
  ∀ aF : List ℝ → ℝ, Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, OwnEv Fm fun C' Cl x i =>
    ∀ (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (u u' : (Fm.D x i).what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (aF Fm.cOut) →
      ConcTie ((sel Fm hc).2 x hx h0 i).X ((sel Fm hc).2 x hx h0 i).Y →
      (((sel Fm hc).2 x hx h0 i).Y.tO u u').AbsConv →
      (((sel Fm hc).2 x hx h0 i).Y.tO u u').RowBig (epsL (Fm.D x i))
          (ddC ((sel Fm hc).2 x hx h0 i).X ((sel Fm hc).2 x hx h0 i).Y u u') ∧
        (((sel Fm hc).2 x hx h0 i).Y.tO u u').RowNotScalar (epsL (Fm.D x i))
          (ddC ((sel Fm hc).2 x hx h0 i).X ((sel Fm hc).2 x hx h0 i).Y u u')

/- English proof (translation)
Take `⟨-, CA, -, -, -, hCA, -, -, hrest⟩` from `hT 1`. Establish `H : ∀ l : List ℝ, ∃ k0 : ℕ, 0 ≤ l.getD 17 0 → ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl → TheoremSAtDataAlt CA C0 (l.getD 17 0) 5 (1 / 2) 3 Cn k0 C' Cl (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0`. Introduce `l`. Distinguish the cases in `h : 0 ≤ l.getD 17 0`. Take `⟨k0, hk⟩` from `hrest C0 (l.getD 17 0) 5 (1 / 2) 3 h1 h (by norm_num) (by norm_num) (by norm_num) (by norm_num)`.

Conclude with `⟨k0, fun _ => hk _ _ _ _ _ _⟩`. Conclude with `⟨0, fun h' => absurd h' h⟩`. Use `choose k0f hk0 using H`. Establish `G : ∀ l : List ℝ, ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ l.getD 17 0 → 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl → TheoremSAtDataAlt CA C0 (l.getD 17 0) 5 (1 / 2) 3 Cn (k0f l) C' Cl (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0`. Introduce `l`.

Distinguish the cases in `h : 0 ≤ l.getD 17 0`. Take `⟨Cn, a, b, hn, hh⟩` from `hk0 l h`. Conclude with `⟨Cn, a, b, fun _ => ⟨hn, hh⟩⟩`. Conclude with `⟨0, 0, 0, fun h' => absurd h' h⟩`. Use `choose cnf c'f clf hG using G`.

Use `closed_with (hOK.and ((hSz CA hCA k0f cnf).and ((hLp aF).and hA))) (fun _ => 0) (fun l => max (max (c'f l) (clf l)) 29) fun Fm CH _ hQ _ ht1 ht2 hc => ?_` and prove the remaining obligations. Take `⟨hQ1, hQ2, hQ3, hA1, hQ4⟩` from `hQ`. Take `⟨xa, Ha⟩` from `hQ1 hc`. Take `⟨xb, Hb⟩` from `hQ2 hc`. Take `⟨xc, Hc⟩` from `hQ3 hc`.

Take `⟨xd, Hd⟩` from `hQ4`. Use `⟨max (max xa xb) (max xc xd), fun x hx i hH hx1 h0 u u' hne => ?_⟩` and prove the remaining obligations. Establish `hxa : xa ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `hxb : xb ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `hxc : xc ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`.

Establish `hxd : xd ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx`. Establish `e17 : (Fm.cOut ++ Fm.cMid CH).getD 17 0 = Fm.CGam` using `rfl`. Establish `hCG : 0 ≤ (Fm.cOut ++ Fm.cMid CH).getD 17 0`. Rewrite using `[e17, ← Fm.CGam_eq x i]`. Conclude with `(Fm.L x i).CGam_pos.le`.

Take `⟨-, hrow⟩` from `hG (Fm.cOut ++ Fm.cMid CH) hCG`. Establish `hC'a : c'f (Fm.cOut ++ Fm.cMid CH) ≤ sC' Fm` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht1`. Establish `hCla : clf (Fm.cOut ++ Fm.cMid CH) ≤ sCl Fm` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht2`. Establish `hC'29 : (29 : ℝ) ≤ sC' Fm` using `le_trans (le_max_right _ _) ht1`. Establish `hCl29 : (29 : ℝ) ≤ sCl Fm` using `le_trans (le_max_right _ _) ht2`.

Establish `ok` using `Ha x hxa i hH hx1 h0`. Establish `tie : ConcTie ((sel Fm hc).2 x hx1 h0 i).X ((sel Fm hc).2 x hx1 h0 i).Y` using `(concKOf ((sel Fm hc).2 x hx1 h0 i) ok).tie`. Establish `hCnt` using `Formalism.MainNotions.count_hypotheses_of_sizes (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 (aF Fm.cOut) hH.1 hH.2.1 hH.2.2 (by linarith) (by linarith) hA1 (Hd x hxd i hH) u u'`. Establish `hAC` using `hAbs _ _ _ u u' tie`. Take `⟨hRB, hRNS⟩` from `Hc x hxc i hx1 h0 u u' hCnt tie hAC`.

Establish `hb0 : 0 ≤ (Fm.L x i).sc.b` using `le_trans zero_le_two (Formalism.MainNotions.S.two_le_scb _)`. Conclude with `hrow (sC' Fm) (sCl Fm) hC'a hCla (Fm.D x i) (Fm.L x i) ((sel Fm hc).2 x hx1 h0 i) u u' hne hb0 (Hb x hxb i hH hx1 h0 u u' hne) ⟨hH.2.1, hH.1, hH.2.2⟩ (Formalism.MainNotions.Stand_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 (by linarith) u u') (Formalism.MainNotions.NonGenericAndKTwoTheore …`.
-/
theorem theoremS_selected_of_loops (hT : TheoremSSingle) (h1 : 1 ≤ C0) {𝒞 : FamClass} (sel : SSel 𝒞)
    (hOK : Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, SelOK C0 Fm (sel Fm hc))
    (hSz : SizesRowS C0 𝒞 sel) (aF : List ℝ → ℝ)
    (hA : Closed 𝒞 fun Fm _ => 1 ≤ aF Fm.cOut ∧ OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu → Formalism.MainNotions.Sizes3b (Fm.D x i) (aF Fm.cOut))
    (hLp : LoopRowS C0 𝒞 sel) (hAbs : AbsConvTied) :
    Closed 𝒞 fun Fm _ => ∀ hc : 𝒞 Fm, TheoremSSelected Fm C0 (sel Fm hc) := by
  obtain ⟨-, CA, -, -, -, hCA, -, -, hrest⟩ := hT 1
  have H : ∀ l : List ℝ, ∃ k0 : ℕ, 0 ≤ l.getD 17 0 → ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      TheoremSAtDataAlt CA C0 (l.getD 17 0) 5 (1 / 2) 3 Cn k0 C' Cl (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0 := by
    intro l
    by_cases h : 0 ≤ l.getD 17 0
    · obtain ⟨k0, hk⟩ := hrest C0 (l.getD 17 0) 5 (1 / 2) 3 h1 h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact ⟨k0, fun _ => hk _ _ _ _ _ _⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose k0f hk0 using H
  have G : ∀ l : List ℝ, ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ l.getD 17 0 → 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      TheoremSAtDataAlt CA C0 (l.getD 17 0) 5 (1 / 2) 3 Cn (k0f l) C' Cl (l.getD 6 0 + 1) (1 / 4) 3 (1 / 2) (l.getD 13 0) C0 := by
    intro l
    by_cases h : 0 ≤ l.getD 17 0
    · obtain ⟨Cn, a, b, hn, hh⟩ := hk0 l h
      exact ⟨Cn, a, b, fun _ => ⟨hn, hh⟩⟩
    · exact ⟨0, 0, 0, fun h' => absurd h' h⟩
  choose cnf c'f clf hG using G
  refine closed_with (hOK.and ((hSz CA hCA k0f cnf).and ((hLp aF).and hA))) (fun _ => 0)
    (fun l => max (max (c'f l) (clf l)) 29) fun Fm CH _ hQ _ ht1 ht2 hc => ?_
  obtain ⟨hQ1, hQ2, hQ3, hA1, hQ4⟩ := hQ
  obtain ⟨xa, Ha⟩ := hQ1 hc
  obtain ⟨xb, Hb⟩ := hQ2 hc
  obtain ⟨xc, Hc⟩ := hQ3 hc
  obtain ⟨xd, Hd⟩ := hQ4
  refine ⟨max (max xa xb) (max xc xd), fun x hx i hH hx1 h0 u u' hne => ?_⟩
  have hxa : xa ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : xb ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxc : xc ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxd : xd ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have e17 : (Fm.cOut ++ Fm.cMid CH).getD 17 0 = Fm.CGam := rfl
  have hCG : 0 ≤ (Fm.cOut ++ Fm.cMid CH).getD 17 0 := by
    rw [e17, ← Fm.CGam_eq x i]; exact (Fm.L x i).CGam_pos.le
  obtain ⟨-, hrow⟩ := hG (Fm.cOut ++ Fm.cMid CH) hCG
  have hC'a : c'f (Fm.cOut ++ Fm.cMid CH) ≤ sC' Fm := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht1
  have hCla : clf (Fm.cOut ++ Fm.cMid CH) ≤ sCl Fm := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht2
  have hC'29 : (29 : ℝ) ≤ sC' Fm := le_trans (le_max_right _ _) ht1
  have hCl29 : (29 : ℝ) ≤ sCl Fm := le_trans (le_max_right _ _) ht2
  have ok := Ha x hxa i hH hx1 h0
  have tie : ConcTie ((sel Fm hc).2 x hx1 h0 i).X ((sel Fm hc).2 x hx1 h0 i).Y :=
    (concKOf ((sel Fm hc).2 x hx1 h0 i) ok).tie
  have hCnt := Formalism.MainNotions.count_hypotheses_of_sizes (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0
    (aF Fm.cOut) hH.1 hH.2.1 hH.2.2 (by linarith) (by linarith) hA1 (Hd x hxd i hH) u u'
  have hAC := hAbs _ _ _ u u' tie
  obtain ⟨hRB, hRNS⟩ := Hc x hxc i hx1 h0 u u' hCnt tie hAC
  have hb0 : 0 ≤ (Fm.L x i).sc.b := le_trans zero_le_two (Formalism.MainNotions.S.two_le_scb _)
  exact hrow (sC' Fm) (sCl Fm) hC'a hCla (Fm.D x i) (Fm.L x i) ((sel Fm hc).2 x hx1 h0 i) u u' hne hb0
    (Hb x hxb i hH hx1 h0 u u' hne) ⟨hH.2.1, hH.1, hH.2.2⟩
    (Formalism.MainNotions.Stand_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 (by linarith) u u')
    (Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of _ _ _ _ _ _ _ _ _ _ hH.1 hH.2.1 hH.2.2 (by linarith))
    (gap_hypothesis_of_hypotheses hH.2.1 (by linarith) hC'29) ok.2.2.2.2.2.1 ok.2.2.2.2.2.2 hRB hRNS

end OffLeaves

section RowsTieSel

/- English proof (translation)
Introduce `P hP hpP`. Set `ψ : 𝓞 E ≃+* 𝓞 E'` to `RingOfIntegers.mapRingEquiv φ`. Establish `hP' : (P.map ψ).IsMaximal` using `by haveI := hP; exact Ideal.map_isMaximal_of_equiv ψ`. Establish `hp' : (p : 𝓞 E') ∈ P.map ψ`. Use `Ideal.mem_map_of_mem ψ hpP` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Take `⟨h1, h2⟩` from `h _ hP' hp'`. Use `⟨?_, fun hc => h2 ?_⟩` and prove the remaining obligations. Rewrite using `[← h1, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `Nat.card_congr (Ideal.quotientEquiv P (P.map ψ) ψ rfl).toEquiv`.

Use `Ideal.mem_map_of_mem ψ hc` as an intermediate fact. Rewrite `this` using `[map_natCast, Ideal.map_pow]`. Then use the resulting hypothesis.
-/
theorem splitsCompl_of_equiv {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (φ : E ≃+* E')
    {p : ℕ} (h : Formalism.MainNotions.S.SplitsCompl E' p) : Formalism.MainNotions.S.SplitsCompl E p := by
  intro P hP hpP
  let ψ : 𝓞 E ≃+* 𝓞 E' := RingOfIntegers.mapRingEquiv φ
  have hP' : (P.map ψ).IsMaximal := by haveI := hP; exact Ideal.map_isMaximal_of_equiv ψ
  have hp' : (p : 𝓞 E') ∈ P.map ψ := by
    have := Ideal.mem_map_of_mem ψ hpP
    rwa [map_natCast] at this
  obtain ⟨h1, h2⟩ := h _ hP' hp'
  refine ⟨?_, fun hc => h2 ?_⟩
  · rw [← h1, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv P (P.map ψ) ψ rfl).toEquiv
  · have := Ideal.mem_map_of_mem ψ hc
    rwa [map_natCast, Ideal.map_pow] at this

/- English proof (translation)
Establish `hK` using `Formalism.L2.SG.Closed.level_subgroup_is_group T.X`. Establish `hKL` using `Formalism.L2.SG.Closed.level_subgroup_properties T.X`. Establish `hcl` using `Formalism.L2.SG.PoincareInHH.Cut.level_subgroup_isClopen T.X hK hKL`. Use `⟨(Formalism.MainNotions.S.Inh.aut_rowsTie_iff D T.X.B).2 ⟨⟨T.X.pl, T.autTie⟩, fun h => ?_⟩, Formalism.L2.SG.Count.levelSubgroupOfCharacter T.X hK, T.X.chi2, hcl.isOpen, (PI.WAU.Cpt.isCompact_Kset T.X.B.I).of_isClosed_subset hcl.isClosed hKL.2.1, hKL.2.1, ?_, fun k hk k' hk' => hK …` and prove the remaining obligations. Rewrite using `[T.X.g0_eq]`.

Conclude with `splitsCompl_of_equiv T.X.ιE h`. Establish `hg0` using `(D.host.g_prime 0).pos`. Establish `hg1` using `(D.host.g_prime 1).pos`. Establish `hn : 2 * D.R.rS + D.R.k + 1 ≤ T.X.B.I.n`. Rewrite using `[T.X.n_eq, Formalism.MainNotions.BridgeLemma.sza_r_eq]`.

Use linear arithmetic over natural numbers and integers. Use `Formalism.L2.SG.Pf.BunEx.unipotence_mod_g T.X.B.I T.X.B.g T.X.B.g₀ T.X.e0 T.X.f0 T.X.z0 T.X.bw T.X.bwd T.X.ew (by rw [T.X.g_eq]; exact Nat.mul_pos hg0 hg1) (by rw [T.X.g_eq, T.X.g0_eq]; exact dvd_mul_right _ _) hn T.X.vectorsInLattice T.X.gramIntegral T.X.formsAtZero T.X.weightVe …` and prove the remaining obligations. Rewrite using `[T.X.e_eq x] split_ifs with h1 h2 h2`. Rewrite using `[inv_eq_of_mul_eq_one_right (Formalism.L2.SG.Pf.BunA.unit_mul_star (hK.2.2.2.2 x h1))]`. Both sides reduce to the same expression.

Conclude with `absurd h1 h2`. Conclude with `absurd h2 h1`. Both sides reduce to the same expression.
-/
theorem rowsTieP_of {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) : CountE.RowsTieP CountE.PLev D T.X.B := by
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group T.X
  have hKL := Formalism.L2.SG.Closed.level_subgroup_properties T.X
  have hcl := Formalism.L2.SG.PoincareInHH.Cut.level_subgroup_isClopen T.X hK hKL
  refine ⟨(Formalism.MainNotions.S.Inh.aut_rowsTie_iff D T.X.B).2 ⟨⟨T.X.pl, T.autTie⟩, fun h => ?_⟩,
    Formalism.L2.SG.Count.levelSubgroupOfCharacter T.X hK, T.X.chi2, hcl.isOpen,
    (PI.WAU.Cpt.isCompact_Kset T.X.B.I).of_isClosed_subset hcl.isClosed hKL.2.1, hKL.2.1, ?_,
    fun k hk k' hk' => hK.2.2.2.1 k hk k' hk', fun k hk => hK.2.2.2.2 k hk, fun x => ?_⟩
  · rw [T.X.g0_eq]; exact splitsCompl_of_equiv T.X.ιE h
  · have hg0 := (D.host.g_prime 0).pos
    have hg1 := (D.host.g_prime 1).pos
    have hn : 2 * D.R.rS + D.R.k + 1 ≤ T.X.B.I.n := by
      rw [T.X.n_eq, Formalism.MainNotions.BridgeLemma.sza_r_eq]; omega
    refine Formalism.L2.SG.Pf.BunEx.unipotence_mod_g T.X.B.I T.X.B.g T.X.B.g₀ T.X.e0 T.X.f0 T.X.z0 T.X.bw T.X.bwd T.X.ew
      (by rw [T.X.g_eq]; exact Nat.mul_pos hg0 hg1) (by rw [T.X.g_eq, T.X.g0_eq]; exact dvd_mul_right _ _) hn
      T.X.vectorsInLattice T.X.gramIntegral T.X.formsAtZero T.X.weightVectorsIntegral T.X.ew_idem T.X.ew_orth T.X.ew_int T.X.bw_w T.X.bwd_w T.X.bw_dual
      T.X.latticeSpan
  · rw [T.X.e_eq x]
    split_ifs with h1 h2 h2
    · rw [inv_eq_of_mul_eq_one_right (Formalism.L2.SG.Pf.BunA.unit_mul_star (hK.2.2.2.2 x h1))]
      rfl
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rfl

end RowsTieSel

end Formalism.L2.SG.ThmSOwn
