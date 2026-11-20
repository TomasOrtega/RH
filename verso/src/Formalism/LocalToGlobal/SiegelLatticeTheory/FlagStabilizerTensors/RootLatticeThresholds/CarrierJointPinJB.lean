import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DetUpMatSub
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActL
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPfLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DistinctWordsDistinctParameters
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeviTens

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointPinJB

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPf
  Formalism.L2.SG.Pf.Carrier.JointQuot Formalism.L2.SG.Pf.Carrier.JointPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def HlocU (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  {s | ∀ x ∈ Set.range X.eR ∪ Set.range X.fR ∪ {X.zR u},
    uMat s *ᵥ Formalism.L2.SG.HidaSetting.rv X.B.I v x = Formalism.L2.SG.HidaSetting.rv X.B.I v x}

def WlocEqv (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Prop :=
  ∀ (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (s : Formalism.REAL.UJ (X.B.I.ε v)), s ∈ HlocU X u v →
    ∀ x, X.Wloc u v (s * x) = X.piLoc u v (matQ (X.B.I.ε v) (X.wfr u v) (uMat s)) (X.Wloc u v x)

def JvConj (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Prop :=
  ∀ (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (h h' : Formalism.REAL.UJ (X.B.I.ε v)), h ∈ HlocU X u v →
    h' ∈ HlocU X u' v → ∀ (ν : Measure (Formalism.REAL.UJ (X.B.I.ε v))) (γ : Formalism.REAL.UJ (X.B.I.ε v)) (y : X.Vloc u' v),
      X.piLoc u v (matQ (X.B.I.ε v) (X.wfr u v) (uMat h⁻¹))
        ((haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Jv ν (X.Wloc u v) (X.Wloc u' v) γ)
          (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h')) y)) =
      (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
        Jv (ν.map (fun x => h⁻¹ * x)) (X.Wloc u v) (X.Wloc u' v) (h⁻¹ * γ * h')) y

def ZhatConj (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Prop :=
  ∀ (u u' : D.what₂.Word) (sc : ℝ) (v : InfinitePlace X.B.I.F) (h h' γ : Formalism.REAL.UJ (X.B.I.ε v)), h ∈ HlocU X u v →
    h' ∈ HlocU X u' v →
    Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat (h⁻¹ * γ * h')) =
      Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat γ)

def GPosScale (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Prop :=
  ∀ (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (γ : Formalism.REAL.UJ (X.B.I.ε v)),
    0 < Gv (Tw (D := D) u) (Tw (D := D) u')
      (Zhat (X.B.I.ε v) (frm X u D.host.rdE v) (frm X u' D.host.rdE v) (uMat γ)) →
    0 < Gv (Tw (D := D) u) (Tw (D := D) u') (Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat γ))

def MonoPt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Prop :=
  ∀ (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)), OkPt X u u' w → ∀ v : InfinitePlace X.B.I.F,
    Formalism.FourierDecayAlt.C2.IsMonomial (Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat ((gamW X u u' w) v)))

def RelTr {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word} (P : Parts X u u') (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  0 < sc → StRel X u u' → P.FromX → P.Base i0 i0' → (∀ j x, P.S.emb j (X.ιE x) = X.B.I.φ (P.τ j) x) →
  ∀ w, OkPt X u u' w → ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' → ∀ v : InfinitePlace X.B.I.F,
    Formalism.FourierDecayAlt.C6.IsRelevant (P.T (P.τ.symm v)).base
      (trG (P.Q v) (P.Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v))

def MeasConj (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Prop :=
  ∀ (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (h h' γ : Formalism.REAL.UJ (X.B.I.ε v)), h ∈ HlocU X u v →
    h' ∈ HlocU X u' v → ∀ μR ν : Measure (Formalism.REAL.UJ (X.B.I.ε v)),
    IsHaarLoc (StSet (NV X u v) (NV X u' v) γ) μR → IsQuotLoc μR ν →
    IsHaarLoc (StSet (NV X u v) (NV X u' v) (h⁻¹ * γ * h')) (μR.map (fun s => h⁻¹ * s * h)) ∧
      IsQuotLoc (μR.map (fun s => h⁻¹ * s * h)) (ν.map (fun x => h⁻¹ * x))

def OrbVecAt {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word} (P : Parts X u u') (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  0 < sc → P.FromX → P.Base i0 i0' → (∀ j x, P.S.emb j (X.ιE x) = X.B.I.φ (P.τ j) x) → P.Built →
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → OkPt X u u' w →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' → ∀ (v : InfinitePlace X.B.I.F)
      (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v))), IsHaarLoc (StV X u u' (gamW X u u' w) v) μRv →
      μRv.map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w →
    ∀ F : Formalism.FourierDecayAlt.B.Mat P.S.G.k P.S.G.r → (P.Wq (P.S.pl (P.τ.symm v)) →L[ℂ] P.Wp (P.S.pl (P.τ.symm v))),
      Formalism.FourierDecayAlt.D.orbJ (P.T (P.τ.symm v)).base (trG (P.Q v) (P.Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v))
                (trMeas P v (μRv.map (fun s => (h v)⁻¹ * s * h v))) F =
        (((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (P.S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
            (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
          Formalism.FourierDecayAlt.D.vecV (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v)) F
            (Formalism.FourierDecayAlt.D.toStd P.S.G.r P.S.g 1 (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))

variable {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

/- English proof (translation)
Introduce `x hx` and use `hh v x hx`.
-/
theorem hlocU_of_mem {h : X.B.I.Ginf} (hh : h ∈ HsetU X u) (v : InfinitePlace X.B.I.F) : h v ∈ HlocU X u v :=
  fun x hx => hh v x hx

/- English proof (translation)
Unfold `frm famSc`. Rewrite using `[mulVec_smul]`. Use `congr 1`. Unfold `fam`. Proceed by induction on `a using Fin.lastCases with`.

Consider the case `last => simp only [Fin.snoc_last]`. Conclude with `hs _ (Or.inr rfl)`. Consider the case `cast i => simp only [Fin.snoc_castSucc]`. Conclude with `hs _ (Or.inl (Or.inl ⟨i, rfl⟩))`.
-/
theorem hloc_fix_frm (sc : ℝ) (v : InfinitePlace X.B.I.F) (s : Formalism.REAL.UJ (X.B.I.ε v)) (hs : s ∈ HlocU X u v)
    (a : Fin (D.R.rS + 1)) : uMat s *ᵥ frm X u sc v a = frm X u sc v a := by
  unfold frm famSc
  rw [mulVec_smul]
  congr 1
  unfold fam
  induction a using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; exact hs _ (Or.inr rfl)
  | cast i => simp only [Fin.snoc_castSucc]; exact hs _ (Or.inl (Or.inl ⟨i, rfl⟩))

/- English proof (translation)
Introduce `u u' sc v h h' γ hh hh'`. Establish `hm : uMat (h⁻¹ * γ * h') = uMat h⁻¹ * uMat γ * uMat h'` using `by simp [uMat]`. Use function extensionality and compare the values at `a b`. Unfold `Formalism.L2.SG.RealObj.Zhat`. Rewrite using `[hm, ← mulVec_mulVec, ← mulVec_mulVec, hloc_fix_frm sc v h' hh' b, Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj h⁻¹ (frm X u sc v a), inv_inv, hloc_fix_frm sc v h hh a]`.
-/
theorem zhatConj_holds : ZhatConj X := by
  intro u u' sc v h h' γ hh hh'
  have hm : uMat (h⁻¹ * γ * h') = uMat h⁻¹ * uMat γ * uMat h' := by simp [uMat]
  funext a b
  unfold Formalism.L2.SG.RealObj.Zhat
  rw [hm, ← mulVec_mulVec, ← mulVec_mulVec, hloc_fix_frm sc v h' hh' b,
    Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj h⁻¹ (frm X u sc v a), inv_inv, hloc_fix_frm sc v h hh a]

def dsc (r : ℕ) (sc : ℝ) : Fin (r + 1) → ℂ := fun a => (((sc ^ (r - a.1))⁻¹ : ℝ) : ℂ)

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.mul_diagonal, Matrix.diagonal_mul]`. Unfold `Formalism.L2.SG.RealObj.Zhat famSc Formalism.L2.SG.HidaSetting.hJ dsc`. Simplify using `only [mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, RCLike.star_def, map_inv₀, map_pow, Complex.conj_ofReal]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem zhat_famSc {n r : ℕ} (ε : Fin n → Bool) (sc : ℝ) (e e' : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    Zhat ε (famSc sc e z) (famSc sc e' z') g =
      Matrix.diagonal (dsc r sc) * Zhat ε (famSc 1 e z) (famSc 1 e' z') g * Matrix.diagonal (dsc r sc) := by
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold Formalism.L2.SG.RealObj.Zhat famSc Formalism.L2.SG.HidaSetting.hJ dsc
  simp only [mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    RCLike.star_def, map_inv₀, map_pow, Complex.conj_ofReal]
  push_cast
  ring

/- English proof (translation)
Unfold `Formalism.L2.SG.RealObj.Dl`. Rewrite using `[dif_pos hl, dif_pos hl]`. Establish `hs : (Matrix.diagonal d * Z * Matrix.diagonal d).submatrix (Fin.castLE hl) (Fin.castLE hl) = Matrix.diagonal (fun i => d (Fin.castLE hl i)) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) * Matrix.diagonal (fun i => d (Fin.castLE hl i))`. Use extensionality with `i j`. Simplify using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Rewrite using `[hs, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dl_dzd {r : ℕ} (d : Fin (r + 1) → ℂ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (l : ℕ) (hl : l ≤ r + 1) :
    Dl (Matrix.diagonal d * Z * Matrix.diagonal d) l = (∏ i : Fin l, d (Fin.castLE hl i)) ^ 2 * Dl Z l := by
  unfold Formalism.L2.SG.RealObj.Dl
  rw [dif_pos hl, dif_pos hl]
  have hs : (Matrix.diagonal d * Z * Matrix.diagonal d).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i => d (Fin.castLE hl i)) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun i => d (Fin.castLE hl i)) := by
    ext i j
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [hs, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  ring

/- English proof (translation)
Unfold `Gv`. Rewrite using `[dl_dzd d Z (r + 1) le_rfl, dl_dzd d Z r (Nat.le_succ r)]`. Establish `e1 : (∏ i : Fin (r + 1), d (Fin.castLE (le_refl (r + 1)) i)) = ∏ i : Fin r, d (Fin.castSucc i)`. Rewrite using `[Fin.prod_univ_castSucc]`. Establish `: Fin.castLE (le_refl (r + 1)) (Fin.last r) = Fin.last r` using `Fin.ext rfl`.

Rewrite using `[this, hd, mul_one]`. Both sides reduce to the same expression. Establish `e2 : (∏ i : Fin r, d (Fin.castLE (Nat.le_succ r) i)) = ∏ i : Fin r, d (Fin.castSucc i)` using `rfl`. Rewrite using `[e1, e2]`. Simplify using `only [norm_mul, norm_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gv_dzd {r : ℕ} (T T' : ℝ) (d : Fin (r + 1) → ℂ) (hd : d (Fin.last r) = 1)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Gv T T' (Matrix.diagonal d * Z * Matrix.diagonal d) =
      ‖∏ i : Fin r, d (Fin.castSucc i)‖ ^ 4 * Gv T T' Z := by
  unfold Gv
  rw [dl_dzd d Z (r + 1) le_rfl, dl_dzd d Z r (Nat.le_succ r)]
  have e1 : (∏ i : Fin (r + 1), d (Fin.castLE (le_refl (r + 1)) i)) = ∏ i : Fin r, d (Fin.castSucc i) := by
    rw [Fin.prod_univ_castSucc]
    have : Fin.castLE (le_refl (r + 1)) (Fin.last r) = Fin.last r := Fin.ext rfl
    rw [this, hd, mul_one]
    rfl
  have e2 : (∏ i : Fin r, d (Fin.castLE (Nat.le_succ r) i)) = ∏ i : Fin r, d (Fin.castSucc i) := rfl
  rw [e1, e2]
  simp only [norm_mul, norm_pow]
  ring

/- English proof (translation)
Introduce `u u' v γ hG`. Establish `hd : dsc D.R.rS D.host.rdE (Fin.last D.R.rS) = 1` using `by simp [dsc]`. Unfold `frm at hG ⊢`. Rewrite `hG` using `[zhat_famSc, gv_dzd _ _ _ hd]`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Establish `h4 : 0 ≤ ‖∏ i : Fin D.R.rS, dsc D.R.rS D.host.rdE (Fin.castSucc i)‖ ^ 4` using `by positivity`. Use polynomial arithmetic with `[mul_nonpos_of_nonneg_of_nonpos h4 hc]`.
-/
theorem gPosScale_holds : GPosScale X := by
  intro u u' v γ hG
  have hd : dsc D.R.rS D.host.rdE (Fin.last D.R.rS) = 1 := by simp [dsc]
  unfold frm at hG ⊢
  rw [zhat_famSc, gv_dzd _ _ _ hd] at hG
  by_contra hc
  push Not at hc
  have h4 : 0 ≤ ‖∏ i : Fin D.R.rS, dsc D.R.rS D.host.rdE (Fin.castSucc i)‖ ^ 4 := by positivity
  nlinarith [mul_nonpos_of_nonneg_of_nonpos h4 hc]

/- English proof (translation)
Introduce `u u' w hok v`. Establish `hrep : IsPtRep X u u' w (gamW X u u' w)`. Unfold `gamW`. Rewrite using `[dif_pos hok.1]`. Conclude with `hok.1.choose_spec`.

Establish `hZ` using `hrep v`. Establish `hinv : Function.Involutive (Formalism.L2.SG.PtCell.pinv w)` using `Formalism.L2.SG.PtCell.pinv_pinv w`. Use `⟨hinv.toPerm _, fun a => (-1 : ℂ) ^ (D.R.rS - a.val) * X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PtCell.pval w.1 (Formalism.L2.SG.PtCell.pinv w a).val)), fun a => mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_, ?_⟩` and prove the remaining obligations. Use `(map_ne_zero _).2 ((map_ne_zero _).2 ?_)` and prove the remaining obligations. Conclude with `Formalism.L2.SG.PtCell.pval_ne w.1 (fun b hb => (w.2.1 b hb).1) _ (by rw [w.2.2]; exact (Formalism.L2.SG.PtCell.pinv w a).isLt)`.

Use extensionality with `i a`. Establish `hia : Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat ((gamW X u u' w) v)) i a = (-1 : ℂ) ^ (D.R.rS - a.val) * Formalism.L2.SG.RealObj.ZhatO (ZX X u u' 1 (gamW X u u' w) v) i a`. Unfold `Formalism.L2.SG.RealObj.ZhatO ZX`. Rewrite using `[← mul_assoc, ← mul_pow]`. Evaluate the numerical expressions.

Rewrite using `[hia, hZ]`. Unfold `ptC`. Rewrite using `[Matrix.map_apply, Formalism.L2.SG.PtCell.ptMat_eq_mono]`. Simplify using `only [Formalism.L2.SG.PtCell.mono, Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply, Function.Involutive.coe_toPerm]`. Distinguish the cases in `h : a = Formalism.L2.SG.PtCell.pinv w i`.

Establish `h2 : i = Formalism.L2.SG.PtCell.pinv w a` using `by rw [h, hinv]`. Rewrite using `[if_pos h]`. Simplify using `only [h2, if_true]`. Establish `h2 : ¬ i = Formalism.L2.SG.PtCell.pinv w a` using `fun e => h (by rw [e, hinv])`. Rewrite using `[if_neg h]`.

Simplify using `only [h2, if_false, map_zero, mul_zero]`.
-/
theorem monoPt_holds : MonoPt X := by
  intro u u' w hok v
  have hrep : IsPtRep X u u' w (gamW X u u' w) := by
    unfold gamW; rw [dif_pos hok.1]; exact hok.1.choose_spec
  have hZ := hrep v
  have hinv : Function.Involutive (Formalism.L2.SG.PtCell.pinv w) := Formalism.L2.SG.PtCell.pinv_pinv w
  refine ⟨hinv.toPerm _, fun a => (-1 : ℂ) ^ (D.R.rS - a.val) *
      X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PtCell.pval w.1 (Formalism.L2.SG.PtCell.pinv w a).val)),
    fun a => mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_, ?_⟩
  · refine (map_ne_zero _).2 ((map_ne_zero _).2 ?_)
    exact Formalism.L2.SG.PtCell.pval_ne w.1 (fun b hb => (w.2.1 b hb).1) _
      (by rw [w.2.2]; exact (Formalism.L2.SG.PtCell.pinv w a).isLt)
  · ext i a
    have hia : Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat ((gamW X u u' w) v)) i a =
        (-1 : ℂ) ^ (D.R.rS - a.val) * Formalism.L2.SG.RealObj.ZhatO (ZX X u u' 1 (gamW X u u' w) v) i a := by
      unfold Formalism.L2.SG.RealObj.ZhatO ZX
      rw [← mul_assoc, ← mul_pow]
      norm_num
    rw [hia, hZ]
    unfold ptC
    rw [Matrix.map_apply, Formalism.L2.SG.PtCell.ptMat_eq_mono]
    simp only [Formalism.L2.SG.PtCell.mono, Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply, Function.Involutive.coe_toPerm]
    by_cases h : a = Formalism.L2.SG.PtCell.pinv w i
    · have h2 : i = Formalism.L2.SG.PtCell.pinv w a := by rw [h, hinv]
      rw [if_pos h]
      simp only [h2, if_true]
    · have h2 : ¬ i = Formalism.L2.SG.PtCell.pinv w a := fun e => h (by rw [e, hinv])
      rw [if_neg h]
      simp only [h2, if_false, map_zero, mul_zero]

/- English proof (translation)
Introduce `x hx`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mulVec_mulVec, Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul', one_mulVec]`.
-/
theorem hlocU_inv {v : InfinitePlace X.B.I.F} {h : Formalism.REAL.UJ (X.B.I.ε v)} (hh : h ∈ HlocU X u v) :
    h⁻¹ ∈ HlocU X u v := by
  intro x hx
  calc uMat h⁻¹ *ᵥ Formalism.L2.SG.HidaSetting.rv X.B.I v x
      = uMat h⁻¹ *ᵥ (uMat h *ᵥ Formalism.L2.SG.HidaSetting.rv X.B.I v x) := by rw [hh x hx]
    _ = Formalism.L2.SG.HidaSetting.rv X.B.I v x := by
      rw [mulVec_mulVec, Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul', one_mulVec]

/- English proof (translation)
Unfold `Formalism.L2.SG.HidaSetting.spanLt at hx ⊢`. Establish `hle : Submodule.span ℂ (e '' {b | b.1 < a}) ≤ (Submodule.span ℂ (e '' {b | b.1 < a})).comap (Matrix.mulVecLin M)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨b, hb, rfl⟩` from `hy`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, hM b]`. Conclude with `Submodule.subset_span ⟨b, hb, rfl⟩`. Conclude with `hle hx`.
-/
theorem spanLt_fix {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (e : Fin r → Fin n → ℂ) (hM : ∀ b, M *ᵥ e b = e b)
    (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ Formalism.L2.SG.HidaSetting.spanLt e a) : M *ᵥ x ∈ Formalism.L2.SG.HidaSetting.spanLt e a := by
  unfold Formalism.L2.SG.HidaSetting.spanLt at hx ⊢
  have hle : Submodule.span ℂ (e '' {b | b.1 < a}) ≤
      (Submodule.span ℂ (e '' {b | b.1 < a})).comap (Matrix.mulVecLin M) := by
    refine Submodule.span_le.2 ?_
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, hM b]
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  exact hle hx

/- English proof (translation)
Establish `hhi` using `hlocU_inv hh`. Establish `hfe : ∀ a, uMat h *ᵥ Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a) = Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)` using `fun a => hh _ (Or.inl (Or.inl ⟨a, rfl⟩))`. Establish `hfz : uMat h *ᵥ Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u) = Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)` using `hh _ (Or.inr rfl)`. Establish `hie : ∀ a, uMat h⁻¹ *ᵥ Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a) = Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)` using `fun a => hhi _ (Or.inl (Or.inl ⟨a, rfl⟩))`. Establish `hm : uMat (h⁻¹ * s * h) = uMat h⁻¹ * uMat s * uMat h` using `by simp [uMat]`.

Establish `hI : uMat h⁻¹ * uMat h = 1` using `Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' h`. Establish `key : ∀ x, (uMat (h⁻¹ * s * h) - 1) *ᵥ x = uMat h⁻¹ *ᵥ ((uMat s - 1) *ᵥ (uMat h *ᵥ x))`. Introduce `x`. Rewrite using `[hm]`. Simplify using `only [mulVec_mulVec, ← Matrix.mul_assoc]`.

Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hI, sub_mulVec, one_mulVec]`. Take `⟨⟨he, hz⟩, hy⟩` from `hs`. Use `⟨⟨fun a => ?_, ?_⟩, fun y hy0 => ?_⟩` and prove the remaining obligations. Rewrite using `[key, hfe a]`. Conclude with `spanLt_fix _ _ hie _ (he a)`.

Rewrite using `[key, hfz]`. Conclude with `spanLt_fix _ _ hie _ hz`. Rewrite using `[key]`. Use `spanLt_fix _ _ hie _ (hy _ fun a => ?_)` and prove the remaining obligations. Rewrite using `[Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj h, hie a]`.

Conclude with `hy0 a`.
-/
theorem nv_conj {v : InfinitePlace X.B.I.F} {h s : Formalism.REAL.UJ (X.B.I.ε v)} (hh : h ∈ HlocU X u v)
    (hs : s ∈ NV X u v) : h⁻¹ * s * h ∈ NV X u v := by
  have hhi := hlocU_inv hh
  have hfe : ∀ a, uMat h *ᵥ Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a) = Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a) :=
    fun a => hh _ (Or.inl (Or.inl ⟨a, rfl⟩))
  have hfz : uMat h *ᵥ Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u) = Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u) :=
    hh _ (Or.inr rfl)
  have hie : ∀ a, uMat h⁻¹ *ᵥ Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a) = Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a) :=
    fun a => hhi _ (Or.inl (Or.inl ⟨a, rfl⟩))
  have hm : uMat (h⁻¹ * s * h) = uMat h⁻¹ * uMat s * uMat h := by simp [uMat]
  have hI : uMat h⁻¹ * uMat h = 1 := Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' h
  have key : ∀ x, (uMat (h⁻¹ * s * h) - 1) *ᵥ x = uMat h⁻¹ *ᵥ ((uMat s - 1) *ᵥ (uMat h *ᵥ x)) := by
    intro x
    rw [hm]
    simp only [mulVec_mulVec, ← Matrix.mul_assoc]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hI, sub_mulVec, one_mulVec]
  obtain ⟨⟨he, hz⟩, hy⟩ := hs
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy0 => ?_⟩
  · rw [key, hfe a]
    exact spanLt_fix _ _ hie _ (he a)
  · rw [key, hfz]
    exact spanLt_fix _ _ hie _ hz
  · rw [key]
    refine spanLt_fix _ _ hie _ (hy _ fun a => ?_)
    rw [Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj h, hie a]
    exact hy0 a

/- English proof (translation)
Establish `e1 : (h⁻¹ * γ * h')⁻¹ * (h⁻¹ * s * h) * (h⁻¹ * γ * h') = h'⁻¹ * (γ⁻¹ * s * γ) * h'` using `by group`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `nv_conj (hlocU_inv hh) h1` as an intermediate fact.

Simplify `this` using `[mul_assoc]`. Rewrite `h2` using `[e1]`. Use `nv_conj (hlocU_inv hh') h2` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨nv_conj hh h1, ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `nv_conj hh' h2`.
-/
theorem stSet_conj {v : InfinitePlace X.B.I.F} {h h' γ : Formalism.REAL.UJ (X.B.I.ε v)} (hh : h ∈ HlocU X u v)
    (hh' : h' ∈ HlocU X u' v) (s : Formalism.REAL.UJ (X.B.I.ε v)) :
    h⁻¹ * s * h ∈ StSet (NV X u v) (NV X u' v) (h⁻¹ * γ * h') ↔ s ∈ StSet (NV X u v) (NV X u' v) γ := by
  have e1 : (h⁻¹ * γ * h')⁻¹ * (h⁻¹ * s * h) * (h⁻¹ * γ * h') = h'⁻¹ * (γ⁻¹ * s * γ) * h' := by group
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := nv_conj (hlocU_inv hh) h1
      simpa [mul_assoc] using this
    · rw [e1] at h2
      have := nv_conj (hlocU_inv hh') h2
      simpa [mul_assoc] using this
  · rintro ⟨h1, h2⟩
    refine ⟨nv_conj hh h1, ?_⟩
    rw [e1]
    exact nv_conj hh' h2

/- English proof (translation)
Introduce `u u' v h h' γ hh hh' μR ν hH hQ`. Take `⟨hsf, hne, hc, hinv⟩` from `hH`. Set `c : Formalism.REAL.UJ (X.B.I.ε v) ≃ᵐ Formalism.REAL.UJ (X.B.I.ε v)` to `(MeasurableEquiv.mulLeft h⁻¹).trans (MeasurableEquiv.mulRight h)`. Establish `hcc : (fun s => h⁻¹ * s * h) = ⇑c` using `rfl`. Set `L : Formalism.REAL.UJ (X.B.I.ε v) ≃ᵐ Formalism.REAL.UJ (X.B.I.ε v)` to `MeasurableEquiv.mulLeft h⁻¹`.

Establish `hLL : (fun x => h⁻¹ * x) = ⇑L` using `rfl`. Establish `hpre : c ⁻¹' (StSet (NV X u v) (NV X u' v) (h⁻¹ * γ * h')) = StSet (NV X u v) (NV X u' v) γ`. Use extensionality with `s`. Conclude with `stSet_conj hh hh' s`. Rewrite using `[hcc, hLL]`.

Use `⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `c.sigmaFinite_map`. Conclude with `(Measure.map_ne_zero_iff c.measurable.aemeasurable).2 hne`. Rewrite using `[c.map_apply, Set.preimage_compl, hpre]`. Conclude with `hc`.

Introduce `s hs`. Establish `ht : h * s * h⁻¹ ∈ StSet (NV X u v) (NV X u' v) γ`. Rewrite using `[← stSet_conj hh hh']`. Simplify `hs` using `[mul_assoc]`. Establish `e2 : (fun x => s * x) ∘ ⇑c = ⇑c ∘ (fun x => (h * s * h⁻¹) * x)`.

Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp, hcc.symm]`. Use `group`. Rewrite using `[Measure.map_map (measurable_const_mul s) c.measurable, e2, ← Measure.map_map c.measurable (measurable_const_mul _), hinv _ ht]`. Introduce `f hf`.

Rewrite using `[lintegral_map_equiv]`. Repeatedly rewrite using `[lintegral_map_equiv]`. Establish `e3 : ∀ x s, f (c s * L x) = (fun y => f (h⁻¹ * y)) (s * x)`. Introduce `x s`. Use `show f (h⁻¹ * s * h * (h⁻¹ * x)) = f (h⁻¹ * (s * x))`.

Use `congr 1`. Use `group`. Repeatedly rewrite using `[e3]`. Establish `hQ'` using `hQ (fun y => f (h⁻¹ * y)) (hf.comp (measurable_const_mul _))`. Rewrite using `[← hQ']`.

Conclude with `(lintegral_mul_left_eq_self f h⁻¹).symm`.
-/
theorem measConj_holds : MeasConj X := by
  intro u u' v h h' γ hh hh' μR ν hH hQ
  obtain ⟨hsf, hne, hc, hinv⟩ := hH
  let c : Formalism.REAL.UJ (X.B.I.ε v) ≃ᵐ Formalism.REAL.UJ (X.B.I.ε v) :=
    (MeasurableEquiv.mulLeft h⁻¹).trans (MeasurableEquiv.mulRight h)
  have hcc : (fun s => h⁻¹ * s * h) = ⇑c := rfl
  let L : Formalism.REAL.UJ (X.B.I.ε v) ≃ᵐ Formalism.REAL.UJ (X.B.I.ε v) := MeasurableEquiv.mulLeft h⁻¹
  have hLL : (fun x => h⁻¹ * x) = ⇑L := rfl
  have hpre : c ⁻¹' (StSet (NV X u v) (NV X u' v) (h⁻¹ * γ * h')) = StSet (NV X u v) (NV X u' v) γ := by
    ext s; exact stSet_conj hh hh' s
  rw [hcc, hLL]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact c.sigmaFinite_map
  · exact (Measure.map_ne_zero_iff c.measurable.aemeasurable).2 hne
  · rw [c.map_apply, Set.preimage_compl, hpre]
    exact hc
  · intro s hs
    have ht : h * s * h⁻¹ ∈ StSet (NV X u v) (NV X u' v) γ := by
      rw [← stSet_conj hh hh']
      simpa [mul_assoc] using hs
    have e2 : (fun x => s * x) ∘ ⇑c = ⇑c ∘ (fun x => (h * s * h⁻¹) * x) := by
      funext x; simp only [Function.comp, hcc.symm]; group
    rw [Measure.map_map (measurable_const_mul s) c.measurable, e2,
      ← Measure.map_map c.measurable (measurable_const_mul _), hinv _ ht]
  · intro f hf
    rw [lintegral_map_equiv]
    simp_rw [lintegral_map_equiv]
    have e3 : ∀ x s, f (c s * L x) = (fun y => f (h⁻¹ * y)) (s * x) := by
      intro x s; show f (h⁻¹ * s * h * (h⁻¹ * x)) = f (h⁻¹ * (s * x)); congr 1; group
    simp_rw [e3]
    have hQ' := hQ (fun y => f (h⁻¹ * y)) (hf.comp (measurable_const_mul _))
    rw [← hQ']
    exact (lintegral_mul_left_eq_self f h⁻¹).symm

open Classical in

/- English proof (translation)
Establish `key : ∀ p q : ∀ w, X.Vloc w0 w, (∀ w, w ≠ v → p w = a w) → (∀ w, w ≠ v → q w = a w) → inner ℂ (X.tensU w0 p) (X.tensU w0 q) = inner ℂ (p v) (q v) * ∏ w ∈ Finset.univ.erase v, inner ℂ (a w) (a w)`. Introduce `p q hp hq`. Rewrite using `[X.tensU_inner, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]`. Use `congr 1`. Use `Finset.prod_congr rfl fun w hw => ?_` and prove the remaining obligations.

Rewrite using `[hp w (Finset.ne_of_mem_erase hw), hq w (Finset.ne_of_mem_erase hw)]`. Establish `hb : ∀ w, w ≠ v → b w = a w` using `fun w hw => (hab w hw).symm`. Establish `ha : ∀ w, w ≠ v → a w = a w` using `fun _ _ => rfl`. Establish `e1` using `key a a ha ha`. Establish `e2` using `key a b ha hb`.

Establish `e3` using `key b a hb ha`. Establish `e4` using `key b b hb hb`. Rewrite `e1`, `e2`, `e3` using `[h]`. Establish `f1 : inner ℂ (a v) (a v) = inner ℂ (b v) (b v)` using `mul_right_cancel₀ hK (e1.symm.trans e4)`. Establish `f2 : inner ℂ (a v) (b v) = inner ℂ (b v) (b v)` using `mul_right_cancel₀ hK (e2.symm.trans e4)`.

Establish `f3 : inner ℂ (b v) (a v) = inner ℂ (b v) (b v)` using `mul_right_cancel₀ hK (e3.symm.trans e4)`. Establish `hz : inner ℂ (a v - b v) (a v - b v) = (0 : ℂ)`. Rewrite using `[inner_sub_left, inner_sub_right, inner_sub_right, f1, f2, f3]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `sub_eq_zero.1 (inner_self_eq_zero.1 hz)`.
-/
theorem tens_cancel (w0 : D.what₂.Word) (v : InfinitePlace X.B.I.F) (a b : ∀ w, X.Vloc w0 w)
    (hab : ∀ w, w ≠ v → a w = b w) (hK : (∏ w ∈ Finset.univ.erase v, inner ℂ (a w) (a w)) ≠ 0)
    (h : X.tensU w0 a = X.tensU w0 b) : a v = b v := by
  have key : ∀ p q : ∀ w, X.Vloc w0 w, (∀ w, w ≠ v → p w = a w) → (∀ w, w ≠ v → q w = a w) →
      inner ℂ (X.tensU w0 p) (X.tensU w0 q) =
        inner ℂ (p v) (q v) * ∏ w ∈ Finset.univ.erase v, inner ℂ (a w) (a w) := by
    intro p q hp hq
    rw [X.tensU_inner, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
    congr 1
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [hp w (Finset.ne_of_mem_erase hw), hq w (Finset.ne_of_mem_erase hw)]
  have hb : ∀ w, w ≠ v → b w = a w := fun w hw => (hab w hw).symm
  have ha : ∀ w, w ≠ v → a w = a w := fun _ _ => rfl
  have e1 := key a a ha ha
  have e2 := key a b ha hb
  have e3 := key b a hb ha
  have e4 := key b b hb hb
  rw [h] at e1 e2 e3
  have f1 : inner ℂ (a v) (a v) = inner ℂ (b v) (b v) := mul_right_cancel₀ hK (e1.symm.trans e4)
  have f2 : inner ℂ (a v) (b v) = inner ℂ (b v) (b v) := mul_right_cancel₀ hK (e2.symm.trans e4)
  have f3 : inner ℂ (b v) (a v) = inner ℂ (b v) (b v) := mul_right_cancel₀ hK (e3.symm.trans e4)
  have hz : inner ℂ (a v - b v) (a v - b v) = (0 : ℂ) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, f1, f2, f3]
    ring
  exact sub_eq_zero.1 (inner_self_eq_zero.1 hz)

open Classical in

/- English proof (translation)
Introduce `w0 v s hs x`. Take `⟨x0, hx0⟩` from `Formalism.L2.SG.Pf.Carrier.EnergyPfLoc.wu_ne X w0`. Use `set S : X.B.I.Ginf := Function.update 1 v s with hSdef`. Establish `hSw : ∀ w, ∀ y ∈ Set.range X.eR ∪ Set.range X.fR ∪ {X.zR w0}, uMat (S w) *ᵥ Formalism.L2.SG.HidaSetting.rv X.B.I w y = Formalism.L2.SG.HidaSetting.rv X.B.I w y`. Introduce `w y hy`.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Simplify `hs y hy` using `[S]`. Simplify using `[S, Function.update_of_ne hw, uMat]`. Establish `hSH : S ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.Hinf X w0` using `hSw`.

Establish `hmul : S * Function.update x0 v x = Function.update x0 v (s * x)`. Use function extensionality and compare the values at `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Simplify using `[S]`.

Simplify using `[S, Function.update_of_ne hw]`. Use `set a : ∀ w, X.Vloc w0 w := fun w => X.Wloc w0 w (Function.update x0 v (s * x) w) with ha`. Use `set b : ∀ w, X.Vloc w0 w := fun w => X.piLoc w0 w (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr w0 w) w S) (X.Wloc w0 w (Function.update x0 v x w)) with hb`. Establish `hT : X.tensU w0 a = X.tensU w0 b`. Rewrite using `[ha, hb, ← X.Wu_tens, ← hmul, Formalism.L2.SG.Pf.SatGramActL.wu_left X w0 hSH, X.Wu_tens]`.

Conclude with `X.tensU_equiv w0 S hSw _`. Establish `hone : ∀ w, w ≠ v → Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr w0 w) w S = 1`. Introduce `w hw`. Use extensionality with `i j`. Simplify using `[Formalism.L2.SG.HidaSetting.matW, S, Function.update_of_ne hw, uMat, X.wfr_on, Matrix.one_apply]`.

Establish `hab : ∀ w, w ≠ v → a w = b w`. Introduce `w hw`. Simplify using `only [ha, hb]`. Rewrite using `[hone w hw, (X.piLoc_type w0 w).2.2.1.1.1, Function.update_of_ne hw, Function.update_of_ne hw]`. Both sides reduce to the same expression.

Establish `hK : (∏ w ∈ Finset.univ.erase v, inner ℂ (a w) (a w)) ≠ 0`. Establish `hne : inner ℂ (X.Wu w0 x0) (X.Wu w0 x0) ≠ (0 : ℂ)` using `inner_self_ne_zero.2 hx0`. Rewrite `hne` using `[X.Wu_tens, X.tensU_inner, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]`. Establish `h2` using `right_ne_zero_of_mul hne`. Rewrite using `[Finset.prod_congr rfl fun w hw => by` and apply the resulting hypothesis.

Simplify using `only [ha]`. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hw)]]`. Use `tens_cancel w0 v a b hab hK hT` as an intermediate fact. Simplify using `only [ha, hb, Function.update_self] at this`. Establish `hv : Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr w0 v) v S = matQ (X.B.I.ε v) (X.wfr w0 v) (uMat s)`.

Use extensionality with `i j`. Simplify using `[Formalism.L2.SG.HidaSetting.matW, matQ, S]`. Rewrite `this` using `[hv]`. Conclude with `this`.
-/
theorem wlocEqv_holds : WlocEqv X := by
  intro w0 v s hs x
  obtain ⟨x0, hx0⟩ := Formalism.L2.SG.Pf.Carrier.EnergyPfLoc.wu_ne X w0
  set S : X.B.I.Ginf := Function.update 1 v s with hSdef
  have hSw : ∀ w, ∀ y ∈ Set.range X.eR ∪ Set.range X.fR ∪ {X.zR w0},
      uMat (S w) *ᵥ Formalism.L2.SG.HidaSetting.rv X.B.I w y = Formalism.L2.SG.HidaSetting.rv X.B.I w y := by
    intro w y hy
    by_cases hw : w = v
    · subst hw; simpa [S] using hs y hy
    · simp [S, Function.update_of_ne hw, uMat]
  have hSH : S ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.Hinf X w0 := hSw
  have hmul : S * Function.update x0 v x = Function.update x0 v (s * x) := by
    funext w
    by_cases hw : w = v
    · subst hw; simp [S]
    · simp [S, Function.update_of_ne hw]
  set a : ∀ w, X.Vloc w0 w := fun w => X.Wloc w0 w (Function.update x0 v (s * x) w) with ha
  set b : ∀ w, X.Vloc w0 w := fun w => X.piLoc w0 w (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr w0 w) w S)
    (X.Wloc w0 w (Function.update x0 v x w)) with hb
  have hT : X.tensU w0 a = X.tensU w0 b := by
    rw [ha, hb, ← X.Wu_tens, ← hmul, Formalism.L2.SG.Pf.SatGramActL.wu_left X w0 hSH, X.Wu_tens]
    exact X.tensU_equiv w0 S hSw _
  have hone : ∀ w, w ≠ v → Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr w0 w) w S = 1 := by
    intro w hw
    ext i j
    simp [Formalism.L2.SG.HidaSetting.matW, S, Function.update_of_ne hw, uMat, X.wfr_on, Matrix.one_apply]
  have hab : ∀ w, w ≠ v → a w = b w := by
    intro w hw
    simp only [ha, hb]
    rw [hone w hw, (X.piLoc_type w0 w).2.2.1.1.1, Function.update_of_ne hw, Function.update_of_ne hw]
    rfl
  have hK : (∏ w ∈ Finset.univ.erase v, inner ℂ (a w) (a w)) ≠ 0 := by
    have hne : inner ℂ (X.Wu w0 x0) (X.Wu w0 x0) ≠ (0 : ℂ) := inner_self_ne_zero.2 hx0
    rw [X.Wu_tens, X.tensU_inner, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)] at hne
    have h2 := right_ne_zero_of_mul hne
    rwa [Finset.prod_congr rfl fun w hw => by
      simp only [ha]; rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]]
  have := tens_cancel w0 v a b hab hK hT
  simp only [ha, hb, Function.update_self] at this
  have hv : Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr w0 v) v S = matQ (X.B.I.ε v) (X.wfr w0 v) (uMat s) := by
    ext i j
    simp [Formalism.L2.SG.HidaSetting.matW, matQ, S]
  rw [hv] at this
  exact this

/- English proof (translation)
Unfold `Formalism.L2.SG.HidaSetting.hJ`. Simplify using `only [star_sum, star_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul]`.
-/
theorem hJ_sum_left {n : ℕ} (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (c : ι → ℂ) (x : ι → Fin n → ℂ)
    (y : Fin n → ℂ) :
    Formalism.L2.SG.HidaSetting.hJ ε (∑ i, c i • x i) y = ∑ i, star (c i) * Formalism.L2.SG.HidaSetting.hJ ε (x i) y := by
  unfold Formalism.L2.SG.HidaSetting.hJ
  simp only [star_sum, star_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Unfold `Formalism.L2.SG.HidaSetting.hJ`. Simplify using `only [mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]`.
-/
theorem hJ_sum_right {n : ℕ} (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (c : ι → ℂ) (x : Fin n → ℂ)
    (y : ι → Fin n → ℂ) :
    Formalism.L2.SG.HidaSetting.hJ ε x (∑ i, c i • y i) = ∑ i, c i * Formalism.L2.SG.HidaSetting.hJ ε x (y i) := by
  unfold Formalism.L2.SG.HidaSetting.hJ
  simp only [mulVec_sum, mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Establish `hgi` using `hlocU_inv hg`. Simplify using `only [Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj g]`. Use `⟨fun a => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hgi _ (Or.inl (Or.inl ⟨a, rfl⟩))]`. Conclude with `((X.wfr_perp w0 v b).1 a).1`.

Rewrite using `[hgi _ (Or.inl (Or.inr ⟨a, rfl⟩))]`. Conclude with `((X.wfr_perp w0 v b).1 a).2`. Rewrite using `[hgi _ (Or.inr rfl)]`. Conclude with `(X.wfr_perp w0 v b).2`.
-/
theorem hloc_perp {w0 : D.what₂.Word} {v : InfinitePlace X.B.I.F} {g : Formalism.REAL.UJ (X.B.I.ε v)}
    (hg : g ∈ HlocU X w0 v) (b : Fin D.R.k) :
    (∀ a, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)) (uMat g *ᵥ X.wfr w0 v b) = 0 ∧
      Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR a)) (uMat g *ᵥ X.wfr w0 v b) = 0) ∧
    Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR w0)) (uMat g *ᵥ X.wfr w0 v b) = 0 := by
  have hgi := hlocU_inv hg
  simp only [Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj g]
  refine ⟨fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [hgi _ (Or.inl (Or.inl ⟨a, rfl⟩))]; exact ((X.wfr_perp w0 v b).1 a).1
  · rw [hgi _ (Or.inl (Or.inr ⟨a, rfl⟩))]; exact ((X.wfr_perp w0 v b).1 a).2
  · rw [hgi _ (Or.inr rfl)]; exact (X.wfr_perp w0 v b).2

/- English proof (translation)
The claim follows from `PI.SchurPlaces.wfrSpan D X w0 v _ (hloc_perp hg b).1 (hloc_perp hg b).2`.
-/
theorem hloc_span {w0 : D.what₂.Word} {v : InfinitePlace X.B.I.F} {g : Formalism.REAL.UJ (X.B.I.ε v)}
    (hg : g ∈ HlocU X w0 v) (b : Fin D.R.k) :
    uMat g *ᵥ X.wfr w0 v b =
      ∑ c, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (X.wfr w0 v c) (uMat g *ᵥ X.wfr w0 v b) • X.wfr w0 v c :=
  PI.SchurPlaces.wfrSpan D X w0 v _ (hloc_perp hg b).1 (hloc_perp hg b).2

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, matQ, Matrix.one_apply]`. Establish `h1 : Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (uMat g *ᵥ X.wfr w0 v a) (uMat g *ᵥ X.wfr w0 v b) = ∑ c, star (Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (X.wfr w0 v c) (uMat g *ᵥ X.wfr w0 v a)) * Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (X.wfr w0 v c) (uMat g *ᵥ X.wfr w0 v b)` using `by conv_lhs => rw [hloc_span hg a]`. Rewrite using `[hJ_sum_left]`. Establish `h2 : Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (uMat g *ᵥ X.wfr w0 v a) (uMat g *ᵥ X.wfr w0 v b) = Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (X.wfr w0 v a) (X.wfr w0 v b)`.

Rewrite using `[Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj g, mulVec_mulVec, Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul', one_mulVec]`. Rewrite using `[← h1, h2, X.wfr_on]`.
-/
theorem matQ_unitary {w0 : D.what₂.Word} {v : InfinitePlace X.B.I.F} {g : Formalism.REAL.UJ (X.B.I.ε v)}
    (hg : g ∈ HlocU X w0 v) :
    (matQ (X.B.I.ε v) (X.wfr w0 v) (uMat g))ᴴ * matQ (X.B.I.ε v) (X.wfr w0 v) (uMat g) = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, matQ, Matrix.one_apply]
  have h1 : Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (uMat g *ᵥ X.wfr w0 v a) (uMat g *ᵥ X.wfr w0 v b) =
      ∑ c, star (Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (X.wfr w0 v c) (uMat g *ᵥ X.wfr w0 v a)) *
        Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (X.wfr w0 v c) (uMat g *ᵥ X.wfr w0 v b) := by
    conv_lhs => rw [hloc_span hg a]
    rw [hJ_sum_left]
  have h2 : Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (uMat g *ᵥ X.wfr w0 v a) (uMat g *ᵥ X.wfr w0 v b) =
      Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (X.wfr w0 v a) (X.wfr w0 v b) := by
    rw [Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj g, mulVec_mulVec, Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul',
      one_mulVec]
  rw [← h1, h2, X.wfr_on]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [matQ, Matrix.mul_apply]`. Establish `e : uMat (g * h) = uMat g * uMat h` using `by simp [uMat]`. Rewrite using `[e, ← mulVec_mulVec]`. Use `conv_lhs => rw [hloc_span hh b]`.

Rewrite using `[mulVec_sum]`. Simplify using `only [mulVec_smul]`. Rewrite using `[hJ_sum_right]`. Conclude with `Finset.sum_congr rfl fun c _ => mul_comm _ _`.
-/
theorem matQ_mul {w0 : D.what₂.Word} {v : InfinitePlace X.B.I.F} {h : Formalism.REAL.UJ (X.B.I.ε v)}
    (hh : h ∈ HlocU X w0 v) (g : Formalism.REAL.UJ (X.B.I.ε v)) :
    matQ (X.B.I.ε v) (X.wfr w0 v) (uMat (g * h)) =
      matQ (X.B.I.ε v) (X.wfr w0 v) (uMat g) * matQ (X.B.I.ε v) (X.wfr w0 v) (uMat h) := by
  ext a b
  simp only [matQ, Matrix.mul_apply]
  have e : uMat (g * h) = uMat g * uMat h := by simp [uMat]
  rw [e, ← mulVec_mulVec]
  conv_lhs => rw [hloc_span hh b]
  rw [mulVec_sum]
  simp only [mulVec_smul]
  rw [hJ_sum_right]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[matQ, uMat, X.wfr_on, Matrix.one_apply]`.
-/
theorem matQ_one (w0 : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    matQ (X.B.I.ε v) (X.wfr w0 v) (uMat (1 : Formalism.REAL.UJ (X.B.I.ε v))) = 1 := by
  ext a b
  simp [matQ, uMat, X.wfr_on, Matrix.one_apply]

/- English proof (translation)
Establish `hU` using `(X.piLoc_type w0 v).2.2.1`. Rewrite using `[← hU.1.2 _ (Formalism.L2.SG.Pf.IdBlocks2.Geo.uj_of_unitary (matQ_unitary (hlocU_inv hg))) _ (Formalism.L2.SG.Pf.IdBlocks2.Geo.uj_of_unitary (matQ_unitary hg)), ← matQ_mul hg g⁻¹, inv_mul_cancel, matQ_one, hU.1.1]`.
-/
theorem piLoc_inv_comp {w0 : D.what₂.Word} {v : InfinitePlace X.B.I.F} {g : Formalism.REAL.UJ (X.B.I.ε v)}
    (hg : g ∈ HlocU X w0 v) :
    (X.piLoc w0 v (matQ (X.B.I.ε v) (X.wfr w0 v) (uMat g⁻¹))).comp
      (X.piLoc w0 v (matQ (X.B.I.ε v) (X.wfr w0 v) (uMat g))) = 1 := by
  have hU := (X.piLoc_type w0 v).2.2.1
  rw [← hU.1.2 _ (Formalism.L2.SG.Pf.IdBlocks2.Geo.uj_of_unitary (matQ_unitary (hlocU_inv hg))) _
    (Formalism.L2.SG.Pf.IdBlocks2.Geo.uj_of_unitary (matQ_unitary hg)), ← matQ_mul hg g⁻¹, inv_mul_cancel,
    matQ_one, hU.1.1]

/- English proof (translation)
Establish `hU` using `(X.piLoc_type w0 v).2.2.1`. Rewrite using `[← hU.1.2 _ (Formalism.L2.SG.Pf.IdBlocks2.Geo.uj_of_unitary (matQ_unitary hg)) _ (Formalism.L2.SG.Pf.IdBlocks2.Geo.uj_of_unitary (matQ_unitary (hlocU_inv hg))), ← matQ_mul (hlocU_inv hg) g, mul_inv_cancel, matQ_one, hU.1.1]`.
-/
theorem piLoc_comp_inv {w0 : D.what₂.Word} {v : InfinitePlace X.B.I.F} {g : Formalism.REAL.UJ (X.B.I.ε v)}
    (hg : g ∈ HlocU X w0 v) :
    (X.piLoc w0 v (matQ (X.B.I.ε v) (X.wfr w0 v) (uMat g))).comp
      (X.piLoc w0 v (matQ (X.B.I.ε v) (X.wfr w0 v) (uMat g⁻¹))) = 1 := by
  have hU := (X.piLoc_type w0 v).2.2.1
  rw [← hU.1.2 _ (Formalism.L2.SG.Pf.IdBlocks2.Geo.uj_of_unitary (matQ_unitary hg)) _
    (Formalism.L2.SG.Pf.IdBlocks2.Geo.uj_of_unitary (matQ_unitary (hlocU_inv hg))), ← matQ_mul (hlocU_inv hg) g,
    mul_inv_cancel, matQ_one, hU.1.1]

/- English proof (translation)
Introduce `u u' v h h' hh hh' ν γ y`. Use `FiniteDimensional.complete ℂ (X.Vloc u v)` as an intermediate fact. Use `FiniteDimensional.complete ℂ (X.Vloc u' v)` as an intermediate fact. Establish `hU'` using `(X.piLoc_type u' v).2.2.1`. Set `Ae : X.Vloc u v ≃L[ℂ] X.Vloc u v` to `ContinuousLinearEquiv.equivOfInverse (X.piLoc u v (matQ (X.B.I.ε v) (X.wfr u v) (uMat h⁻¹))) (X.piLoc u v (matQ (X.B.I.ε v) (X.wfr u v) (uMat h))) (fun x => by`.

Use `congrArg (fun T : X.Vloc u v →L[ℂ] X.Vloc u v => T x) (piLoc_comp_inv hh)` as an intermediate fact. Simplify using `using this)`. Use the proof step `(fun x => by`. Use `congrArg (fun T : X.Vloc u v →L[ℂ] X.Vloc u v => T x) (piLoc_inv_comp hh)` as an intermediate fact. Simplify using `using this)`.

Set `Be : X.Vloc u' v ≃L[ℂ] X.Vloc u' v` to `ContinuousLinearEquiv.equivOfInverse (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'))) (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'⁻¹))) (fun x => by`. Use `congrArg (fun T : X.Vloc u' v →L[ℂ] X.Vloc u' v => T x) (piLoc_inv_comp hh')` as an intermediate fact. Simplify using `using this)`. Use the proof step `(fun x => by`. Use `congrArg (fun T : X.Vloc u' v →L[ℂ] X.Vloc u' v => T x) (piLoc_comp_inv hh')` as an intermediate fact.

Simplify using `using this)`. Set `L : (X.Vloc u' v →L[ℂ] X.Vloc u v) ≃L[ℂ] (X.Vloc u' v →L[ℂ] X.Vloc u v)` to `Be.symm.arrowCongr Ae`. Establish `hL : ∀ T, L T = (X.piLoc u v (matQ (X.B.I.ε v) (X.wfr u v) (uMat h⁻¹))).comp (T.comp (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'))))` using `fun T => by`. Use extensionality with `ξ`. Both sides reduce to the same expression.

Establish `hn : ∀ ξ, ‖X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h')) ξ‖ = ‖ξ‖` using `hU'.2.1 _ (Formalism.L2.SG.Pf.IdBlocks2.Geo.uj_of_unitary (matQ_unitary hh'))`. Set `Bi : X.Vloc u' v →ₗᵢ[ℂ] X.Vloc u' v` to `⟨(X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'))).toLinearMap, hn⟩`. Establish `hadj : ∀ b ξ, inner ℂ b (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h')) ξ) = inner ℂ (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'⁻¹)) b) ξ`. Introduce `b ξ`. Establish `e : X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h')) (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'⁻¹)) b) = b`.

Use `congrArg (fun T : X.Vloc u' v →L[ℂ] X.Vloc u' v => T b) (piLoc_comp_inv hh')` as an intermediate fact. Simplify using `using this`. Establish `e2 : inner ℂ (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h')) (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'⁻¹)) b)) (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h')) ξ) = inner ℂ (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'⁻¹)) b) ξ` using `Bi.inner_map_map _ _`. Rewrite using `[← e2, e]`. Establish `hpt : ∀ x, L (Formalism.L2.SG.TermOp.rk1 (X.Wloc u v x) (X.Wloc u' v (γ⁻¹ * x))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (h⁻¹ * x)) (X.Wloc u' v ((h⁻¹ * γ * h')⁻¹ * (h⁻¹ * x)))`.

Introduce `x`. Rewrite using `[hL]`. Use extensionality with `ξ`. Establish `e1 : (h⁻¹ * γ * h')⁻¹ * (h⁻¹ * x) = h'⁻¹ * (γ⁻¹ * x)` using `by group`. Simplify using `only [ContinuousLinearMap.comp_apply, Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, map_smul, hadj]`.

Rewrite using `[e1, wlocEqv_holds u v h⁻¹ (hlocU_inv hh) x, wlocEqv_holds u' v h'⁻¹ (hlocU_inv hh') (γ⁻¹ * x)]`. Establish `hA : X.piLoc u v (matQ (X.B.I.ε v) (X.wfr u v) (uMat h⁻¹)) ((Jv ν (X.Wloc u v) (X.Wloc u' v) γ) (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h')) y)) = (L (Jv ν (X.Wloc u v) (X.Wloc u' v) γ)) y`. Rewrite using `[hL]`. Both sides reduce to the same expression. Rewrite using `[hA]`.

Use `congr 1`. Unfold `Jv Formalism.L2.SG.TermOp.OO`. Rewrite using `[Measure.restrict_univ, Measure.restrict_univ, ← ContinuousLinearEquiv.integral_comp_comm]`. Repeatedly rewrite using `[hpt]`. Rewrite using `[show (fun x => h⁻¹ * x) = ⇑(MeasurableEquiv.mulLeft h⁻¹) from rfl, integral_map_equiv]`.

Both sides reduce to the same expression.
-/
theorem jvConj_holds : JvConj X := by
  intro u u' v h h' hh hh' ν γ y
  have := FiniteDimensional.complete ℂ (X.Vloc u v)
  have := FiniteDimensional.complete ℂ (X.Vloc u' v)
  have hU' := (X.piLoc_type u' v).2.2.1
  let Ae : X.Vloc u v ≃L[ℂ] X.Vloc u v :=
    ContinuousLinearEquiv.equivOfInverse (X.piLoc u v (matQ (X.B.I.ε v) (X.wfr u v) (uMat h⁻¹)))
      (X.piLoc u v (matQ (X.B.I.ε v) (X.wfr u v) (uMat h)))
      (fun x => by
        have := congrArg (fun T : X.Vloc u v →L[ℂ] X.Vloc u v => T x) (piLoc_comp_inv hh)
        simpa using this)
      (fun x => by
        have := congrArg (fun T : X.Vloc u v →L[ℂ] X.Vloc u v => T x) (piLoc_inv_comp hh)
        simpa using this)
  let Be : X.Vloc u' v ≃L[ℂ] X.Vloc u' v :=
    ContinuousLinearEquiv.equivOfInverse (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h')))
      (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'⁻¹)))
      (fun x => by
        have := congrArg (fun T : X.Vloc u' v →L[ℂ] X.Vloc u' v => T x) (piLoc_inv_comp hh')
        simpa using this)
      (fun x => by
        have := congrArg (fun T : X.Vloc u' v →L[ℂ] X.Vloc u' v => T x) (piLoc_comp_inv hh')
        simpa using this)
  let L : (X.Vloc u' v →L[ℂ] X.Vloc u v) ≃L[ℂ] (X.Vloc u' v →L[ℂ] X.Vloc u v) := Be.symm.arrowCongr Ae
  have hL : ∀ T, L T = (X.piLoc u v (matQ (X.B.I.ε v) (X.wfr u v) (uMat h⁻¹))).comp
      (T.comp (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h')))) := fun T => by
    ext ξ; rfl
  have hn : ∀ ξ, ‖X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h')) ξ‖ = ‖ξ‖ :=
    hU'.2.1 _ (Formalism.L2.SG.Pf.IdBlocks2.Geo.uj_of_unitary (matQ_unitary hh'))
  let Bi : X.Vloc u' v →ₗᵢ[ℂ] X.Vloc u' v :=
    ⟨(X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'))).toLinearMap, hn⟩
  have hadj : ∀ b ξ, inner ℂ b (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h')) ξ) =
      inner ℂ (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'⁻¹)) b) ξ := by
    intro b ξ
    have e : X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'))
        (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'⁻¹)) b) = b := by
      have := congrArg (fun T : X.Vloc u' v →L[ℂ] X.Vloc u' v => T b) (piLoc_comp_inv hh')
      simpa using this
    have e2 : inner ℂ (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'))
          (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'⁻¹)) b))
          (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h')) ξ) =
        inner ℂ (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h'⁻¹)) b) ξ := Bi.inner_map_map _ _
    rw [← e2, e]
  have hpt : ∀ x, L (Formalism.L2.SG.TermOp.rk1 (X.Wloc u v x) (X.Wloc u' v (γ⁻¹ * x))) =
      Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (h⁻¹ * x)) (X.Wloc u' v ((h⁻¹ * γ * h')⁻¹ * (h⁻¹ * x))) := by
    intro x
    rw [hL]
    ext ξ
    have e1 : (h⁻¹ * γ * h')⁻¹ * (h⁻¹ * x) = h'⁻¹ * (γ⁻¹ * x) := by group
    simp only [ContinuousLinearMap.comp_apply, Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, map_smul, hadj]
    rw [e1, wlocEqv_holds u v h⁻¹ (hlocU_inv hh) x, wlocEqv_holds u' v h'⁻¹ (hlocU_inv hh') (γ⁻¹ * x)]
  have hA : X.piLoc u v (matQ (X.B.I.ε v) (X.wfr u v) (uMat h⁻¹))
      ((Jv ν (X.Wloc u v) (X.Wloc u' v) γ) (X.piLoc u' v (matQ (X.B.I.ε v) (X.wfr u' v) (uMat h')) y)) =
      (L (Jv ν (X.Wloc u v) (X.Wloc u' v) γ)) y := by
    rw [hL]; rfl
  rw [hA]
  congr 1
  unfold Jv Formalism.L2.SG.TermOp.OO
  rw [Measure.restrict_univ, Measure.restrict_univ, ← ContinuousLinearEquiv.integral_comp_comm]
  simp_rw [hpt]
  rw [show (fun x => h⁻¹ * x) = ⇑(MeasurableEquiv.mulLeft h⁻¹) from rfl, integral_map_equiv]
  rfl

/- English proof (translation)
Introduce `hsc hR hFX hBase hEmb hBuilt νl hνl p w hp hw hG h h' hf v`. Establish `hok : OkPt X u u' w` using `⟨hw, hG⟩`. Take `⟨μRv, hHaar, hQ, hmap⟩` from `hνl w hok v`. Establish `hv : h v ∈ HlocU X u v` using `hlocU_of_mem hf.1 v`. Establish `hv' : h' v ∈ HlocU X u' v` using `hlocU_of_mem hf.2.1 v`.

Take `⟨hH2, hQ2⟩` from `hMC u u' v (h v) (h' v) ((gamW X u u' w) v) hv hv' μRv (νl w v) hHaar hQ`. Use `⟨(h v)⁻¹ * (gamW X u u' w) v * h' v, μRv.map (fun s => (h v)⁻¹ * s * h v), (νl w v).map (fun x => (h v)⁻¹ * x), ⟨?_, ?_, hRT hsc hR hFX hBase hEmb w hok h h' hf v, hH2, hQ2⟩, ?_, hOV hsc hFX hBase hEmb hBuilt p w hp hok h h' hf v μRv hHaar hmap _⟩` and prove the remaining obligations. Rewrite using `[hZC u u' 1 v (h v) (h' v) _ hv hv']`. Conclude with `hGS u u' v _ (hG v)`. Rewrite using `[hZC u u' 1 v (h v) (h' v) _ hv hv']`.

Conclude with `hMP u u' w hok v`. Introduce `y`. Conclude with `hJC u u' v (h v) (h' v) hv hv' (νl w v) ((gamW X u u' w) v) y`.
-/
theorem jointBridge_of_steps (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (hJC : JvConj X) (hZC : ZhatConj X) (hGS : GPosScale X) (hMP : MonoPt X) (hRT : RelTr P sc i0 i0')
    (hMC : MeasConj X) (hOV : OrbVecAt P sc i0 i0') : JointBridge P sc i0 i0' := by
  intro hsc hR hFX hBase hEmb hBuilt νl hνl p w hp hw hG h h' hf v
  have hok : OkPt X u u' w := ⟨hw, hG⟩
  obtain ⟨μRv, hHaar, hQ, hmap⟩ := hνl w hok v
  have hv : h v ∈ HlocU X u v := hlocU_of_mem hf.1 v
  have hv' : h' v ∈ HlocU X u' v := hlocU_of_mem hf.2.1 v
  obtain ⟨hH2, hQ2⟩ := hMC u u' v (h v) (h' v) ((gamW X u u' w) v) hv hv' μRv (νl w v) hHaar hQ
  refine ⟨(h v)⁻¹ * (gamW X u u' w) v * h' v, μRv.map (fun s => (h v)⁻¹ * s * h v),
    (νl w v).map (fun x => (h v)⁻¹ * x), ⟨?_, ?_, hRT hsc hR hFX hBase hEmb w hok h h' hf v, hH2, hQ2⟩, ?_,
    hOV hsc hFX hBase hEmb hBuilt p w hp hok h h' hf v μRv hHaar hmap _⟩
  · rw [hZC u u' 1 v (h v) (h' v) _ hv hv']
    exact hGS u u' v _ (hG v)
  · rw [hZC u u' 1 v (h v) (h' v) _ hv hv']
    exact hMP u u' w hok v
  · intro y
    exact hJC u u' v (h v) (h' v) hv hv' (νl w v) ((gamW X u u' w) v) y

/- English proof (translation)
The claim follows from `jointBridge_of_steps P sc i0 i0' jvConj_holds zhatConj_holds gPosScale_holds monoPt_holds hRT measConj_holds hOV`.
-/
theorem jointBridge_of_open (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (hRT : RelTr P sc i0 i0') (hOV : OrbVecAt P sc i0 i0') : JointBridge P sc i0 i0' :=
  jointBridge_of_steps P sc i0 i0' jvConj_holds zhatConj_holds gPosScale_holds monoPt_holds hRT measConj_holds hOV

end Formalism.L2.SG.Pf.Carrier.JointPinJB
