import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DtTiedTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryUnramifiedUnit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfDiagMulFinPartI
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelCharactersEqReference
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DeterminantCharacterUnitaryApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem

noncomputable section

namespace GlobalTheory.Pdv.UnStd

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.KerJ
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

/- English proof (translation)
Use `letI := D.host.cmStar`. Establish `hcm : IsCMField D.host.E` using `D.host.isCMField_hostE`. Introduce `i hi`. Establish `hun : (C.mu0 ⟨i, hi⟩ * ξ).IsUnitary` using `fun x => by`. Establish `e : (C.mu0 ⟨i, hi⟩ * ξ).1 x = (C.mu0 ⟨i, hi⟩).1 x * ξ.1 x` using `rfl`.

Rewrite using `[e, Units.val_mul, norm_mul, (C.isMu0 ⟨i, hi⟩).unitary x, CharModel.isUnitary_of_orderDvd hn hord x, one_mul]`. Use `⟨fun k hk => ?_, ?_⟩` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `(Dt.UO_eq k).1 hk`. Take `⟨m, hm, hu⟩` from `GlobalTheory.UnUnitCmp.Val.finUnit_pow _ hun`. Use `⟨m, hm, Units.ext ?_⟩` and prove the remaining obligations.

Rewrite using `[← CharModel.eDt_finPart Dt a, h ⟨i, hi⟩ _ (CharModel.isFin_finPart a), Units.val_pow_eq_pow_val]`. Conclude with `hu _ (CharModel.isFin_finPart a) ha`. Use `choose e he using fun τ => (D.hcW u τ).e_int ⟨i, hi⟩`. Use `⟨e, fun τ => (he τ).symm, fun z => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `GlobalTheory.Mem.Col2.exists_eq_div_conj D.host z`.

Take `⟨m, hm, hinf⟩` from `(C.isMu0 ⟨i, hi⟩).inf`. Rewrite using `[← Dt.rat k z hk, ← CharModel.eDt_finPart Dt, h ⟨i, hi⟩ _ (CharModel.isFin_finPart _), GlobalTheory.Mem.Chr.DetGroupModel.fin_diag, HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one _ hn hord, mul_one, Units.val_inv_eq_inv_val, hinf k, ← Finset.prod_inv_distrib, ← D.eTau.prod_com …`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `hme : m (D.eTau τ) = 2 * -e τ`. Establish `h1` using `hm (D.eTau τ)`.

Establish `h2 : eExp D ⟨i, hi⟩ (D.eTau τ) = e τ`. Rewrite using `[← he τ, D.hcW_e]`. Simplify using `[eExp]`. Simplify using `only [h2] at h1`. Conclude with `h1` after adjusting the coercions.

Establish `h1` using `congrArg (embPsi D.host (D.eTau τ)) hk`. Rewrite `h1` using `[map_mul, GlobalTheory.Mem.Chr.DetGroupModel.emb_conj]`. Establish `h0 : embPsi D.host (D.eTau τ) (k : D.host.E) ≠ 0` using `by simp`. Use `show _ = embPsi D.host (D.eTau τ) z.1 ^ e τ`. Generalize the expression as in `embPsi D.host (D.eTau τ) (k : D.host.E) = a at *`.

Generalize the expression as in `embPsi D.host (D.eTau τ) z.1 = b at *`. Establish `hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0` using `by simpa using h0`. Establish `h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b`. Rewrite using `[zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]`. Take the linear combination `(-a) * h1`. Rewrite using `[hme, zpow_mul, h3, zpow_neg, inv_inv]`.
-/
theorem mtType_of_frame_mul {D : D7} {C : CharFrame D} (Dt : DtTied D C) (ξ : HChar D.host.E) {n : ℕ} (hn : 0 < n)
    (hord : ξ.OrderDvd n) (mt : ℕ → D.Dt →* ℂˣ)
    (h : ∀ (j : Fin D.R.m) a, IsFinIdele a → mt (j.1 + 1) (Dt.eDt a) = (C.mu0 j * ξ).1 a) (u : D.what₂.Word) :
    MtType u mt := by
  letI := D.host.cmStar
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  intro i hi
  have hun : (C.mu0 ⟨i, hi⟩ * ξ).IsUnitary := fun x => by
    have e : (C.mu0 ⟨i, hi⟩ * ξ).1 x = (C.mu0 ⟨i, hi⟩).1 x * ξ.1 x := rfl
    rw [e, Units.val_mul, norm_mul, (C.isMu0 ⟨i, hi⟩).unitary x, CharModel.isUnitary_of_orderDvd hn hord x, one_mul]
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (Dt.UO_eq k).1 hk
    obtain ⟨m, hm, hu⟩ := GlobalTheory.UnUnitCmp.Val.finUnit_pow _ hun
    refine ⟨m, hm, Units.ext ?_⟩
    rw [← CharModel.eDt_finPart Dt a, h ⟨i, hi⟩ _ (CharModel.isFin_finPart a), Units.val_pow_eq_pow_val]
    exact hu _ (CharModel.isFin_finPart a) ha
  · choose e he using fun τ => (D.hcW u τ).e_int ⟨i, hi⟩
    refine ⟨e, fun τ => (he τ).symm, fun z => ?_⟩
    obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host z
    obtain ⟨m, hm, hinf⟩ := (C.isMu0 ⟨i, hi⟩).inf
    rw [← Dt.rat k z hk, ← CharModel.eDt_finPart Dt, h ⟨i, hi⟩ _ (CharModel.isFin_finPart _), GlobalTheory.Mem.Chr.DetGroupModel.fin_diag,
      HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one _ hn hord, mul_one, Units.val_inv_eq_inv_val, hinf k,
      ← Finset.prod_inv_distrib, ← D.eTau.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : m (D.eTau τ) = 2 * -e τ := by
      have h1 := hm (D.eTau τ)
      have h2 : eExp D ⟨i, hi⟩ (D.eTau τ) = e τ := by
        rw [← he τ, D.hcW_e]; simp [eExp]
      simp only [h2] at h1
      exact_mod_cast h1
    have h1 := congrArg (embPsi D.host (D.eTau τ)) hk
    rw [map_mul, GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    have h0 : embPsi D.host (D.eTau τ) (k : D.host.E) ≠ 0 := by simp
    show _ = embPsi D.host (D.eTau τ) z.1 ^ e τ
    generalize embPsi D.host (D.eTau τ) (k : D.host.E) = a at *
    generalize embPsi D.host (D.eTau τ) z.1 = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]

end GlobalTheory.Pdv.UnStd

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Pdv.UnStd

open Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.KerJ

/- English proof (translation)
Take `⟨T, hT⟩` from `TC.dtTied_true I hok hp l Z`. Establish `ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K)` using `(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2`. Take `⟨n, hn, hpow⟩` from `isOfFinOrder_iff_pow_eq_one.1 ht`. Establish `hk : KDq B.host I.SQ ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker` using `(KDq_anti B.host (I.Q_subset_SQ a)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).2.2 a).1`. Use `mtType_of_frame_mul T (I.xi a) hn ((hok.xi_reads a).orderDvd hpow) _ (fun j x hx => ?_) u` and prove the remaining obligations.

Establish `hm : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ B.R.m` using `⟨by omega, j.2⟩`. Establish `e1 : (O u a).mt (j.1 + 1) = (I.rec7 l Z).muTil (j.1 + 1) * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a))`. Rewrite using `[hO.mt u a]`. Conclude with `if_pos hm`. Rewrite using `[e1, MonoidHom.mul_apply, T.muTil_eq j x hx, hT x]`.

Establish `e2 : (tildeQ B.host I.SQ (I.xi a)) (QuotientGroup.mk x) = (I.xi a).1 x` using `(tildeQ_mk B.host I.SQ hk x).trans (congrArg _ (finPartI_eq_self hx))`. Conclude with `congrArg _ e2`.
-/
theorem mtType_stdO {B : Base} {X : PreX B.toPre} (I : TC B X) (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ} {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)}
    (hO : I.StdO l Z Qp O) (u : (I.rec7 l Z).what₂.Word) (a : (I.rec7 l Z).what₂.Tup) : MtType u (O u a).mt := by
  obtain ⟨T, hT⟩ := TC.dtTied_true I hok hp l Z
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  have hk : KDq B.host I.SQ ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).2.2 a).1
  refine mtType_of_frame_mul T (I.xi a) hn ((hok.xi_reads a).orderDvd hpow) _ (fun j x hx => ?_) u
  have hm : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ B.R.m := ⟨by omega, j.2⟩
  have e1 : (O u a).mt (j.1 + 1) = (I.rec7 l Z).muTil (j.1 + 1) * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) := by
    rw [hO.mt u a]
    exact if_pos hm
  rw [e1, MonoidHom.mul_apply, T.muTil_eq j x hx, hT x]
  have e2 : (tildeQ B.host I.SQ (I.xi a)) (QuotientGroup.mk x) = (I.xi a).1 x :=
    (tildeQ_mk B.host I.SQ hk x).trans (congrArg _ (finPartI_eq_self hx))
  exact congrArg _ e2

end GlobalTheory.Pdv.UnStd

open GlobalTheory.Pdv.UnStd in

/- English proof (translation)
Introduce `B X I hok hp l Z L hT Gi Gl K Y cX ex t hs`. Conclude with `GlobalTheory.KerJ.unUnit_of_mtType _ L hT Gi Gl K Y cX ex t (fun u μ => mtType_stdO I hok hp l Z hs.O u μ)`.
-/
theorem GlobalTheory.Pdv.unUnit_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → t.ent.UnUnit := by
  intro B X I hok hp l Z L hT Gi Gl K Y cX ex t hs
  exact GlobalTheory.KerJ.unUnit_of_mtType _ L hT Gi Gl K Y cX ex t (fun u μ => mtType_stdO I hok hp l Z hs.O u μ)

end
