import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopTermLem

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.Pf.JointAmplitudePoints

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pt

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)

def gamP (w : Point D.host.E (D.R.rS + 1)) (τ : D.what₂.Tau) : MatKR D.R.k D.R.rS :=
  Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ))

def ptP (w : Point D.host.E (D.R.rS + 1)) (τ : D.what₂.Tau) : Point ℂ (D.R.rS + 1) :=
  if h : ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamP C u u' w τ) p ∧
      Formalism.MainNotions.S.Pv.Frames.turnPt p = ptLoc D τ w then h.choose else Formalism.L2.SG.Pf.LTL.pt0 D

def nu1P (w : Point D.host.E (D.R.rS + 1)) (τ : D.what₂.Tau) : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :=
  if h : ∃ ν, RMeas D (locW C u u' τ) (gamP C u u' w τ) 1 ν then h.choose else 0

variable {C} (hB : WuBessel C)

def localAmplitudeProduct (w : Point D.host.E (D.R.rS + 1)) : ℝ :=
  ∏ τ, hsNormSq ((locS hB u u' τ).J (nu1P C u u' w τ) (gamP C u u' w τ))

def thetaP (J2 : ℝ) (w : Point D.host.E (D.R.rS + 1)) : ℝ :=
  if 0 < J2 ∧ 0 < localAmplitudeProduct u u' hB w then
    (localAmplitudeProduct u u' hB w / J2) ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau))
  else 1

end Pt

section Stmts

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
  {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

def RelPtExP : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → ∀ τ,
      ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamP C u u' w τ) p ∧
        Formalism.MainNotions.S.Pv.Frames.turnPt p = ptLoc D τ w

def RMeasExP : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → ∀ τ, ∃ ν₁, RMeas D (locW C u u' τ) (gamP C u u' w τ) 1 ν₁

def LocalAmplitudesPositive : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    0 < J2of Y u u' ν (toPts w) → 0 < localAmplitudeProduct u u' hB w

def ThetaWinP (large₂ : SizeData₂ D) (C1 : ℝ) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    0 < J2of Y u u' ν (toPts w) → normWin D large₂ C1 (thetaP u u' hB (J2of Y u u' ν (toPts w)) w)

end Stmts

section Proof

variable {D : D7} {X : HidaSetting D}

/- English proof (translation)
Use `first`. Consider the case `(haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩; exact Fintype.card_pos)`. Consider the case `(haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, one_mem _⟩⟩; exact Fintype.card_pos)`.
-/
theorem card_pos' (D : D7) : 0 < Fintype.card D.what₂.Tau := by
  first
  | (haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩; exact Fintype.card_pos)
  | (haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, one_mem _⟩⟩; exact Fintype.card_pos)

def ofPts {K : Type} {i : ℕ} (s : Σ c : Composition (i + 1), (Fin c.length → K)) : List (K × ℕ) :=
  List.ofFn fun a => (s.2 a, s.1.blocksFun a)

/- English proof (translation)
Use `first`. Consider the case `(apply List.ext_getElem <;> simp [ofPts, toPts, Composition.blocksFun, Composition.length])`. Consider the case `(apply List.ext_get <;> simp [ofPts, toPts, Composition.blocksFun, Composition.length])`.
-/
theorem ofPts_toPts {K : Type} [Zero K] {i : ℕ} (p : Point K (i + 1)) : ofPts (toPts p) = p.1 := by
  first
  | (apply List.ext_getElem <;> simp [ofPts, toPts, Composition.blocksFun, Composition.length])
  | (apply List.ext_get <;> simp [ofPts, toPts, Composition.blocksFun, Composition.length])

/- English proof (translation)
Introduce `p q h`. Establish `h'` using `congrArg ofPts h`. Rewrite `h'` using `[ofPts_toPts, ofPts_toPts]`. Conclude with `Subtype.ext h'`.
-/
theorem toPts_injective {K : Type} [Zero K] {i : ℕ} :
    Function.Injective (toPts : Point K (i + 1) → Σ c : Composition (i + 1), (Fin c.length → K)) := by
  intro p q h
  have h' := congrArg ofPts h
  rw [ofPts_toPts, ofPts_toPts] at h'
  exact Subtype.ext h'

/- English proof (translation)
Unfold `J2of at h`. Use `split_ifs at h with hc`. Conclude with `hc`. Conclude with `absurd h (lt_irrefl 0)`.
-/
theorem isPtRep_of_J2of {Y : Full X} {u u' : D.what₂.Word} {ν : X.B.I.Ginf → Measure X.B.I.Ginf}
    {w : Point D.host.E (D.R.rS + 1)} (h : 0 < J2of Y u u' ν (toPts w)) :
    ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = toPts w ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g := by
  unfold J2of at h
  split_ifs at h with hc
  · exact hc
  · exact absurd h (lt_irrefl 0)

/- English proof (translation)
Introduce `γ w _ hw hb hJ`. Substitute `hw` using the available equality. Establish `hJ' : 0 < J2of Y u u' ν (toPts w)` using `hJ`. Take `⟨w', hw', g0, hg0⟩` from `isPtRep_of_J2of hJ'`. Establish `hw'w : w' = w` using `hinj _ _ hw'`.

Substitute `hw'w` using the available equality. Establish `hrep : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g` using `⟨g0, hg0⟩`. Establish `hP1` using `hP w' hb hJ'`. Use `set J2 := J2of Y u u' ν (toPts w') with hJ2`. Use `set th := thetaP u u' hB J2 w' with hth`.

Establish `hthv : th = (localAmplitudeProduct u u' hB w' / J2) ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau))`. Rewrite using `[hth]`. Unfold `thetaP`. Rewrite using `[if_pos ⟨hJ', hP1⟩]`. Establish `hth0 : 0 < th` using `by rw [hthv]; exact Real.rpow_pos_of_pos (div_pos hP1 hJ') _`.

Establish `hfc : (0 : ℝ) < 2 * Fintype.card D.what₂.Tau`. Use `card_pos' D` as an intermediate fact. Check the signs of the components of the expression. Establish `hpow : th ^ (2 * Fintype.card D.what₂.Tau) = localAmplitudeProduct u u' hB w' / J2`. Rewrite using `[hthv, ← Real.rpow_natCast, ← Real.rpow_mul (div_pos hP1 hJ').le]`.

Use `push_cast`. Rewrite using `[one_div_mul_cancel hfc.ne', Real.rpow_one]`. Use `⟨gamP C u u' w', ptP C u u' w', fun _ => th, fun τ => (ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ, fun τ => ?_, ?_⟩` and prove the remaining obligations. Establish `hpt : ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamP C u u' w' τ) p ∧ Formalism.MainNotions.S.Pv.Frames.turnPt p = ptLoc D τ w'` using `hR w' hb hrep τ`. Establish `hnu : ∃ ν₁, RMeas D (locW C u u' τ) (gamP C u u' w' τ) 1 ν₁` using `hM w' hb hrep τ`.

Establish `hp` using `hpt.choose_spec`. Establish `hptP : ptP C u u' w' τ = hpt.choose` using `by unfold ptP; rw [dif_pos hpt]`. Establish `hnuP : nu1P C u u' w' τ = hnu.choose` using `by unfold nu1P; rw [dif_pos hnu]`. Use `⟨?_, hT w' hb hJ', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hptP]`.

Conclude with `hp.1`. Take `⟨p, μR, hR1, hQ⟩` from `hnu.choose_spec`. Use `⟨p, μR, hR1, ?_⟩` and prove the remaining obligations. Use `show IsQuotMeas _ (ENNReal.ofReal th • μR) ((ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ)`. Rewrite using `[hnuP]`.

Establish `hQ' : IsQuotMeas (Formalism.L2.SG.Pf.BDat.WX C u u' τ).μG μR hnu.choose`. Simplify `hQ` using `[ENNReal.ofReal_one, one_smul]`. Conclude with `Formalism.L2.SG.Pf.LTL.isQuotMeas_smul hQ' (by simpa using hth0) ENNReal.ofReal_ne_top`. Rewrite using `[hptP]`. Conclude with `hp.2`.

Establish `hloc : ∀ τ, hsNormSq ((Formalism.L2.SG.Pf.BDat.AX hB u u' τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ) (gamP C u u' w' τ)) = (th ^ 2)⁻¹ * hsNormSq ((locS hB u u' τ).J (nu1P C u u' w' τ) (gamP C u u' w' τ))`. Introduce `τ`. Rewrite using `[Formalism.L2.SG.Pf.LTL.locJ_smul, Formalism.L2.SG.Pf.LTL.hsNormSq_smul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hth0.le, Complex.normSq_ofReal]`. Use `congr 1`. Rewrite using `[sq, mul_inv]`.

Establish `hprod : ∏ τ, hsNormSq ((Formalism.L2.SG.Pf.BDat.AX hB u u' τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ) (gamP C u u' w' τ)) = J2`. Rewrite using `[Finset.prod_congr rfl fun τ _ => hloc τ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`. Express the relevant statement in the definitionally equal form `((th ^ 2)⁻¹) ^ Fintype.card D.what₂.Tau * localAmplitudeProduct u u' hB w' = J2`. Rewrite using `[inv_pow, ← pow_mul, hpow]`. Clear the denominators using the available nonvanishing facts.

Establish `hnn : ∀ τ, 0 ≤ hsNormSq ((Formalism.L2.SG.Pf.BDat.AX hB u u' τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ) (gamP C u u' w' τ))` using `fun τ => Formalism.L2.SG.Pf.LTL.hsNormSq_nonneg _`. Rewrite using `[ENNReal.ofReal_one, one_mul, ← ENNReal.ofReal_prod_of_nonneg (fun τ _ => hnn τ), hprod]`. Conclude with `le_rfl`.
-/
theorem jointAmplitudeFactorization_of_inj (Y : Full X) (u u' : D.what₂.Word) (large₂ : SizeData₂ D) (C1 : ℝ) {θ : ℝ} (C : Choice X θ)
    (hB : WuBessel C) (ν νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ)
    (hinj : ∀ w w' : Point D.host.E (D.R.rS + 1), toPts w = toPts w' → w = w')
    (hR : RelPtExP u u' C) (hM : RMeasExP u u' C) (hP : LocalAmplitudesPositive Y u u' ν C hB) (hT : ThetaWinP Y u u' ν C hB large₂ C1) :
    Formalism.L2.SG.Pf.BDat.JointAmplitudeFactorization (Y.tO u u') (NOf2 Y u u' νL ν ng) large₂ C1 (Formalism.L2.SG.Pf.BDat.WX C u u')
      (Formalism.L2.SG.Pf.BDat.AX hB u u') (D.mem u).A.T (D.mem u').A.T 1 := by
  intro γ w _ hw hb hJ
  subst hw
  have hJ' : 0 < J2of Y u u' ν (toPts w) := hJ
  obtain ⟨w', hw', g0, hg0⟩ := isPtRep_of_J2of hJ'
  have hw'w : w' = w := hinj _ _ hw'
  subst hw'w
  have hrep : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g := ⟨g0, hg0⟩
  have hP1 := hP w' hb hJ'
  set J2 := J2of Y u u' ν (toPts w') with hJ2
  set th := thetaP u u' hB J2 w' with hth
  have hthv : th = (localAmplitudeProduct u u' hB w' / J2) ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)) := by
    rw [hth]; unfold thetaP; rw [if_pos ⟨hJ', hP1⟩]
  have hth0 : 0 < th := by rw [hthv]; exact Real.rpow_pos_of_pos (div_pos hP1 hJ') _
  have hfc : (0 : ℝ) < 2 * Fintype.card D.what₂.Tau := by
    have := card_pos' D; positivity
  have hpow : th ^ (2 * Fintype.card D.what₂.Tau) = localAmplitudeProduct u u' hB w' / J2 := by
    rw [hthv, ← Real.rpow_natCast, ← Real.rpow_mul (div_pos hP1 hJ').le]
    push_cast
    rw [one_div_mul_cancel hfc.ne', Real.rpow_one]
  refine ⟨gamP C u u' w', ptP C u u' w', fun _ => th,
    fun τ => (ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ, fun τ => ?_, ?_⟩
  · have hpt : ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamP C u u' w' τ) p ∧
        Formalism.MainNotions.S.Pv.Frames.turnPt p = ptLoc D τ w' := hR w' hb hrep τ
    have hnu : ∃ ν₁, RMeas D (locW C u u' τ) (gamP C u u' w' τ) 1 ν₁ := hM w' hb hrep τ
    have hp := hpt.choose_spec
    have hptP : ptP C u u' w' τ = hpt.choose := by unfold ptP; rw [dif_pos hpt]
    have hnuP : nu1P C u u' w' τ = hnu.choose := by unfold nu1P; rw [dif_pos hnu]
    refine ⟨?_, hT w' hb hJ', ?_, ?_⟩
    · rw [hptP]; exact hp.1
    · obtain ⟨p, μR, hR1, hQ⟩ := hnu.choose_spec
      refine ⟨p, μR, hR1, ?_⟩
      show IsQuotMeas _ (ENNReal.ofReal th • μR) ((ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ)
      rw [hnuP]
      have hQ' : IsQuotMeas (Formalism.L2.SG.Pf.BDat.WX C u u' τ).μG μR hnu.choose := by
        simpa [ENNReal.ofReal_one, one_smul] using hQ
      exact Formalism.L2.SG.Pf.LTL.isQuotMeas_smul hQ' (by simpa using hth0) ENNReal.ofReal_ne_top
    · rw [hptP]; exact hp.2
  ·
    have hloc : ∀ τ, hsNormSq ((Formalism.L2.SG.Pf.BDat.AX hB u u' τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ)
        (gamP C u u' w' τ)) = (th ^ 2)⁻¹ *
          hsNormSq ((locS hB u u' τ).J (nu1P C u u' w' τ) (gamP C u u' w' τ)) := by
      intro τ
      rw [Formalism.L2.SG.Pf.LTL.locJ_smul, Formalism.L2.SG.Pf.LTL.hsNormSq_smul, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal hth0.le, Complex.normSq_ofReal]
      congr 1
      rw [sq, mul_inv]
    have hprod : ∏ τ, hsNormSq ((Formalism.L2.SG.Pf.BDat.AX hB u u' τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ)
        (gamP C u u' w' τ)) = J2 := by
      rw [Finset.prod_congr rfl fun τ _ => hloc τ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      change ((th ^ 2)⁻¹) ^ Fintype.card D.what₂.Tau * localAmplitudeProduct u u' hB w' = J2
      rw [inv_pow, ← pow_mul, hpow]
      field_simp
    have hnn : ∀ τ, 0 ≤ hsNormSq ((Formalism.L2.SG.Pf.BDat.AX hB u u' τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ)
        (gamP C u u' w' τ)) := fun τ => Formalism.L2.SG.Pf.LTL.hsNormSq_nonneg _
    rw [ENNReal.ofReal_one, one_mul, ← ENNReal.ofReal_prod_of_nonneg (fun τ _ => hnn τ), hprod]
    exact le_rfl

/- English proof (translation)
The claim follows from `jointAmplitudeFactorization_of_inj Y u u' large₂ C1 C hB ν νL ng (fun w w' h => toPts_injective h) hR hM hP hT`.
-/
theorem jointAmplitudeFactorization_of (Y : Full X) (u u' : D.what₂.Word) (large₂ : SizeData₂ D) (C1 : ℝ) {θ : ℝ} (C : Choice X θ)
    (hB : WuBessel C) (ν νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ)
    (hR : RelPtExP u u' C) (hM : RMeasExP u u' C) (hP : LocalAmplitudesPositive Y u u' ν C hB) (hT : ThetaWinP Y u u' ν C hB large₂ C1) :
    Formalism.L2.SG.Pf.BDat.JointAmplitudeFactorization (Y.tO u u') (NOf2 Y u u' νL ν ng) large₂ C1 (Formalism.L2.SG.Pf.BDat.WX C u u')
      (Formalism.L2.SG.Pf.BDat.AX hB u u') (D.mem u).A.T (D.mem u').A.T 1 :=
  jointAmplitudeFactorization_of_inj Y u u' large₂ C1 C hB ν νL ng (fun w w' h => toPts_injective h) hR hM hP hT

/- English proof (translation)
Unfold `Formalism.L2.SG.Pf.BDat.RowBData`. Conclude with `⟨hIre, θ, C, hB, hθ0, hθw, hloc, 1, zero_le_one, fun νL ng => jointAmplitudeFactorization_of Y u u' large₂ C1 C hB ν νL ng hR hM hP hT, fun sec hsec => by simpa using hN sec hsec⟩`.
-/
theorem rowBData_of (large₂ : SizeData₂ D) (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (C1 Cn Ire : ℝ) (hIre : 0 ≤ Ire) {θ : ℝ} (C : Choice X θ) (hB : WuBessel C) (hθ0 : 0 < θ)
    (hθw : normWin D large₂ C1 θ)
    (hloc : ∀ τ, ColsTypeTr C u τ ∧ ColsTypeTr C u' τ ∧ ZTr C u τ ∧ ZTr C u' τ ∧ HaarTr C τ ∧ GoodSRest hB u u' τ)
    (hR : RelPtExP u u' C) (hM : RMeasExP u u' C) (hP : LocalAmplitudesPositive Y u u' ν C hB) (hT : ThetaWinP Y u u' ν C hB large₂ C1)
    (hN : ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
        (∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (Formalism.L2.SG.Pf.BDat.WX C u u' τ).z (Formalism.L2.SG.Pf.BDat.WX C u u' τ).z'
          (sec τ)) →
        ∏ τ, MMv D u u' (Formalism.L2.SG.Pf.BDat.AX hB u u' τ) (sec τ) ≤
          ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)) :
    Formalism.L2.SG.Pf.BDat.RowBData large₂ Y u u' ν C1 Cn Ire := by
  unfold Formalism.L2.SG.Pf.BDat.RowBData
  exact ⟨hIre, θ, C, hB, hθ0, hθw, hloc, 1, zero_le_one,
    fun νL ng => jointAmplitudeFactorization_of Y u u' large₂ C1 C hB ν νL ng hR hM hP hT,
    fun sec hsec => by simpa using hN sec hsec⟩

end Proof

end Formalism.L2.SG.Pf.JointAmplitudePoints
