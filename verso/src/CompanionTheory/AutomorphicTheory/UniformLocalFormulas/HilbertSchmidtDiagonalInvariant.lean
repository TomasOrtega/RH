import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinGlob
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEqMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RelPtR
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HsNormSqEqHilbertSchmidtSq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyNF
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyCV
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyKM
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPfLocSec
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyConst
import Formalism.HermitianCurvature.StatementPN
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian

noncomputable section

open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
  Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocJEq Formalism.L2.SG.Pf.Carrier

namespace Formalism.MainStatements.RowRest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

/- English proof (translation)
Take `⟨h1, -, -⟩` from `y_facts C τ`. Use `set y' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) := ujOf' _ h1 with hy'`. Establish `hr : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant` using `⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩`. Establish `hm : Measurable fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => (Matrix.of.symm (trG (C.Q τ) (C.Qi τ) z) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)` using `(AmpWinLoc.eT_emb C τ (vOf X τ)).measurable`. Establish `e : Smap C τ γ = (fun z => (Matrix.of.symm (trG (C.Q τ) (C.Qi τ) z) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) ∘ (fun z => z * y') ∘ fun z => γ⁻¹ * z`.

Use function extensionality and compare the values at `z`. Use `show Matrix.of.symm (C.Qi τ * umat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) = Matrix.of.symm (C.Qi τ * (umat (γ⁻¹ * z) * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ)) * C.Q τ)`. Use `congr 1`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[(C.isT τ).1, Matrix.mul_one]`.

Rewrite using `[e, ← Measure.map_map hm ((measurable_mul_const y').comp (measurable_const_mul γ⁻¹)), ← Measure.map_map (measurable_mul_const y') (measurable_const_mul γ⁻¹), map_mul_left_eq_self, map_mul_right_eq_self]`. Both sides reduce to the same expression.
-/
theorem muG_smap (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (Smap C τ γ) = muGB X (C.Q τ) (C.Qi τ) τ := by
  obtain ⟨h1, -, -⟩ := y_facts C τ
  set y' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) := ujOf' _ h1 with hy'
  have hr : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  have hm : Measurable fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (trG (C.Q τ) (C.Qi τ) z) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) := (AmpWinLoc.eT_emb C τ (vOf X τ)).measurable
  have e : Smap C τ γ = (fun z => (Matrix.of.symm (trG (C.Q τ) (C.Qi τ) z) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) ∘
      (fun z => z * y') ∘ fun z => γ⁻¹ * z := by
    funext z
    show Matrix.of.symm (C.Qi τ * umat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹) =
      Matrix.of.symm (C.Qi τ * (umat (γ⁻¹ * z) * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ)) * C.Q τ)
    congr 1
    simp only [Matrix.mul_assoc]
    rw [(C.isT τ).1, Matrix.mul_one]
  rw [e, ← Measure.map_map hm ((measurable_mul_const y').comp (measurable_const_mul γ⁻¹)),
    ← Measure.map_map (measurable_mul_const y') (measurable_const_mul γ⁻¹), map_mul_left_eq_self, map_mul_right_eq_self]
  rfl

/- English proof (translation)
Rewrite using `[← muG_smap C τ γ, locJ_map_eq C hB u u' τ γ _ (integrand_aesm C hB u u' τ γ _), ← OOCoreHilbertSchmidt.hsNormSq_eq_hilbertSchmidt_sq]`. Conclude with `LTL.hsNormSq_smul _ _`.
-/
theorem hs_J (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    hsNormSq ((locS hB u u' τ).J (muGB X (C.Q τ) (C.Qi τ) τ) (trG (C.Q τ) (C.Qi τ) γ)) =
      AmpWin.kap u u' C hB τ * hs2 (JvX X u u' (vOf X τ) γ) := by
  rw [← muG_smap C τ γ, locJ_map_eq C hB u u' τ γ _ (integrand_aesm C hB u u' τ γ _),
    ← OOCoreHilbertSchmidt.hsNormSq_eq_hilbertSchmidt_sq]
  exact LTL.hsNormSq_smul _ _

/- English proof (translation)
Take `⟨_, hQQi, hH, _⟩` from `C.isT τ`. Establish `hA : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (trG (C.Q τ) (C.Qi τ) γ) a b = hJ (X.B.I.ε (vOf X τ)) (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a) (uMat γ *ᵥ (C.Q τ *ᵥ Formalism.QuantumDeterminants. …`. Unfold `Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm trG hJ`. Rewrite using `[← hH, ← LTL.star_dot_conjT]`. Use `congr 1`.

Simplify using `only [Matrix.mulVec_mulVec]`. Use `congr 1`. Rewrite using `[show (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ * (C.Qi τ * uMat γ * C.Q τ) = (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) * uMat γ * C.Q τ by`. Simplify using `only [Matrix.mul_assoc], hQQi]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`.

Rewrite using `[hA, LTL.Q_fvec C u τ a, LTL.Q_fvec C u' τ b, Matrix.mulVec_smul, LTL.hJ_smul_real, RelPtR.rv_crd_fvec, RelPtR.rv_crd_fvec]`. Both sides reduce to the same expression.
-/
theorem zhat_tr (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (a b : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (trG (C.Q τ) (C.Qi τ) γ) a b =
      ((rhoF D a * rhoF D b : ℝ) : ℂ) *
        Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ) a b := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  have hA : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (trG (C.Q τ) (C.Qi τ) γ) a b =
      hJ (X.B.I.ε (vOf X τ)) (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a)
        (uMat γ *ᵥ (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u' τ) b)) := by
    unfold Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm trG hJ
    rw [← hH, ← LTL.star_dot_conjT]
    congr 1
    simp only [Matrix.mulVec_mulVec]
    congr 1
    rw [show (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ * (C.Qi τ * uMat γ * C.Q τ) =
      (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) * uMat γ * C.Q τ by
        simp only [Matrix.mul_assoc], hQQi]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hA, LTL.Q_fvec C u τ a, LTL.Q_fvec C u' τ b, Matrix.mulVec_smul, LTL.hJ_smul_real, RelPtR.rv_crd_fvec,
    RelPtR.rv_crd_fvec]
  rfl

/- English proof (translation)
Establish `hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0` using `fun a b => by`. Rewrite using `[show X.eR a = X.crd (X.eX a) from rfl, show X.eR b = X.crd (X.eX b) from rfl, InfCut.UnitaryIsometries.hJ_rvX, X.ee, map_zero]`. Establish `hez : ∀ (w : D.what₂.Word) a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) = 0` using `fun w a => by`. Rewrite using `[show X.eR a = X.crd (X.eX a) from rfl, show X.zR w = X.crd (X.zu w) from rfl, InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth w a).1, map_zero]`. Take `⟨s, s', hs, hs', heq⟩` from `InfCut.UnitaryIsometries.diagDC_pair (X.B.I.ε v) 1 _ _ _ (Tw u) (Tw u') hee (hez u) (hez u') (InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v u) (InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v u') cv hc.1 hc.2 g g' hg hg'`.

Rewrite using `[heq]`. Conclude with `EnergyPfLoc.hilbertSchmidt_double_coset_invariant X u u' v _ s s' hs hs'`.
-/
theorem hilbert_schmidt_diagonal_invariant (X : HidaSetting D) (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) {cv : Fin (D.R.rS + 1) → ℂ}
    (hc : cv ∈ GoodV (D := D) u u') {g g' : Formalism.REAL.UJ (X.B.I.ε v)}
    (hg : Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g) = Matrix.diagonal cv)
    (hg' : Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g') = Matrix.diagonal cv) :
    hs2 (JvX X u u' v g') = hs2 (JvX X u u' v g) := by
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    rw [show X.eR a = X.crd (X.eX a) from rfl, show X.eR b = X.crd (X.eX b) from rfl,
      InfCut.UnitaryIsometries.hJ_rvX, X.ee, map_zero]
  have hez : ∀ (w : D.what₂.Word) a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) = 0 :=
    fun w a => by
      rw [show X.eR a = X.crd (X.eX a) from rfl, show X.zR w = X.crd (X.zu w) from rfl,
        InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth w a).1, map_zero]
  obtain ⟨s, s', hs, hs', heq⟩ := InfCut.UnitaryIsometries.diagDC_pair (X.B.I.ε v) 1 _ _ _ (Tw u) (Tw u')
    hee (hez u) (hez u') (InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v u) (InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v u') cv hc.1 hc.2 g g' hg hg'
  rw [heq]
  exact EnergyPfLoc.hilbertSchmidt_double_coset_invariant X u u' v _ s s' hs hs'

def lamB (D : D7) (a : Fin D.R.rS) : ℝ := (D.host.rdE ^ (2 * (D.R.rS - a.val)))⁻¹

/- English proof (translation)
The claim follows from `EnergyConst.rdE_pos'`.
-/
theorem rd_pos (D : D7) : 0 < D.host.rdE := EnergyConst.rdE_pos'

/- English proof (translation)
The claim follows from `inv_pos.2 (pow_pos (rd_pos D) _)`.
-/
theorem lamB_pos (D : D7) (a : Fin D.R.rS) : 0 < lamB D a := inv_pos.2 (pow_pos (rd_pos D) _)

/- English proof (translation)
Unfold `rhoF lamB`. Rewrite using `[← Real.rpow_add (rd_pos D), ← Real.rpow_natCast, ← Real.rpow_neg (rd_pos D).le]`. Use `congr 1`. Move the coercions through the operations in `[Nat.cast_sub h.le]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rho_sq (D : D7) (a : Fin (D.R.rS + 1)) (h : a.val < D.R.rS) : rhoF D a * rhoF D a = lamB D ⟨a.val, h⟩ := by
  unfold rhoF lamB
  rw [← Real.rpow_add (rd_pos D), ← Real.rpow_natCast, ← Real.rpow_neg (rd_pos D).le]
  congr 1
  push_cast [Nat.cast_sub h.le]
  ring

/- English proof (translation)
The claim follows from `Real.rpow_pos_of_pos (rd_pos D) _`.
-/
theorem rho_pos (D : D7) (a : Fin (D.R.rS + 1)) : 0 < rhoF D a := Real.rpow_pos_of_pos (rd_pos D) _

/- English proof (translation)
Take `⟨hz, hT⟩` from `zTr C u τ`. Take `⟨hz', hT'⟩` from `zTr C u' τ`. Establish `hζ : Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) * Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u' τ) < Complex.normSq (cv ⟨D.R.rS, by omega⟩)`. Establish `h` using `hc.2`. Rewrite `h` using `[EnergyCV.gv_diag]`.

Establish `h2` using `(pos_iff_pos_of_mul_pos h).1 (lt_of_le_of_ne (sq_nonneg _) fun h0 => by rw [← h0, zero_mul] at h; exact lt_irrefl _ h)`. Rewrite using `[hT, hT', Complex.normSq_eq_norm_sq]`. Conclude with `sub_pos.1 h2`. Take `⟨hμ, hh⟩` from `hsec.2 _ hζ`. Use `set q : Fin D.R.rS → ℂ := fun a => ((lamB D a : ℝ) : ℂ) * cv ⟨a.val, by have := a.2; omega⟩ with hq`.

Establish `hq0 : ∀ a, q a ≠ 0` using `fun a => mul_ne_zero (Complex.ofReal_ne_zero.2 (lamB_pos D a).ne') (hc.1 _)`. Use `set m := Formalism.QuantumDeterminants.bigCell D.R.k D.R.rS q (sec (cv ⟨D.R.rS, by omega⟩)) with hm`. Establish `hmU : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)` using `Formalism.QuantumDeterminants.bigCellMem _ _ q _ hq0 hμ`. Use `set g' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) := ujOf' _ (transp_mem C τ hmU) with hg'`. Establish `htr : trG (C.Q τ) (C.Qi τ) g' = m` using `by show C.Qi τ * (C.Q τ * m * C.Qi τ) * C.Q τ = m`.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, (C.isT τ).1, Matrix.one_mul, Matrix.mul_assoc, (C.isT τ).1, Matrix.mul_one]`. Establish `hZ : Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat g') = Matrix.diagonal cv`. Use extensionality with `a b`. Establish `h1` using `zhat_tr C u u' τ g' a b`. Rewrite `h1` using `[htr, hm, Formalism.QuantumDeterminants.bigCellZhat _ _ _ _ _ _ hz hz']`.

Establish `hρ : ((rhoF D a * rhoF D b : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (mul_pos (rho_pos D a) (rho_pos D b)).ne'`. Use `mul_left_cancel₀ hρ ?_` and prove the remaining obligations. Rewrite using `[← h1]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Rewrite using `[Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]`. Use `split_ifs with ha`. Rewrite using `[rho_sq D a ha]`. Establish `hal : a = Fin.last D.R.rS` using `Fin.ext (by have := a.isLt; simp only [Fin.val_last]; omega)`. Substitute `hal` using the available equality.

Rewrite using `[Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ hz hz', hh, LTL.rhoF_last]`. Simplify using `only [mul_one, Complex.ofReal_one, one_mul]`. Both sides reduce to the same expression. Rewrite using `[Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab, mul_zero]`. Rewrite using `[← htr, hs_J C hB u u' τ g', hilbert_schmidt_diagonal_invariant X u u' _ hc hg hZ]`.
-/
theorem place_pt (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    {sec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hsec : Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) sec)
    {cv : Fin (D.R.rS + 1) → ℂ} (hc : cv ∈ GoodV (D := D) u u') {g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))}
    (hg : Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat g) = Matrix.diagonal cv) :
    hsNormSq ((locS hB u u' τ).J (muGB X (C.Q τ) (C.Qi τ) τ) (Formalism.QuantumDeterminants.bigCell D.R.k D.R.rS
      (fun a => ((lamB D a : ℝ) : ℂ) * cv ⟨a.val, by have := a.2; omega⟩) (sec (cv ⟨D.R.rS, by omega⟩)))) =
      AmpWin.kap u u' C hB τ * hs2 (JvX X u u' (vOf X τ) g) := by
  obtain ⟨hz, hT⟩ := zTr C u τ
  obtain ⟨hz', hT'⟩ := zTr C u' τ
  have hζ : Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) * Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u' τ) <
      Complex.normSq (cv ⟨D.R.rS, by omega⟩) := by
    have h := hc.2
    rw [EnergyCV.gv_diag] at h
    have h2 := (pos_iff_pos_of_mul_pos h).1 (lt_of_le_of_ne (sq_nonneg _) fun h0 => by rw [← h0, zero_mul] at h; exact lt_irrefl _ h)
    rw [hT, hT', Complex.normSq_eq_norm_sq]
    exact sub_pos.1 h2
  obtain ⟨hμ, hh⟩ := hsec.2 _ hζ
  set q : Fin D.R.rS → ℂ := fun a => ((lamB D a : ℝ) : ℂ) * cv ⟨a.val, by have := a.2; omega⟩ with hq
  have hq0 : ∀ a, q a ≠ 0 := fun a => mul_ne_zero (Complex.ofReal_ne_zero.2 (lamB_pos D a).ne') (hc.1 _)
  set m := Formalism.QuantumDeterminants.bigCell D.R.k D.R.rS q (sec (cv ⟨D.R.rS, by omega⟩)) with hm
  have hmU : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := Formalism.QuantumDeterminants.bigCellMem _ _ q _ hq0 hμ
  set g' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) := ujOf' _ (transp_mem C τ hmU) with hg'
  have htr : trG (C.Q τ) (C.Qi τ) g' = m := by
    show C.Qi τ * (C.Q τ * m * C.Qi τ) * C.Q τ = m
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, (C.isT τ).1, Matrix.one_mul, Matrix.mul_assoc, (C.isT τ).1, Matrix.mul_one]
  have hZ : Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat g') = Matrix.diagonal cv := by
    ext a b
    have h1 := zhat_tr C u u' τ g' a b
    rw [htr, hm, Formalism.QuantumDeterminants.bigCellZhat _ _ _ _ _ _ hz hz'] at h1
    have hρ : ((rhoF D a * rhoF D b : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (mul_pos (rho_pos D a) (rho_pos D b)).ne'
    refine mul_left_cancel₀ hρ ?_
    rw [← h1]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      split_ifs with ha
      · rw [rho_sq D a ha]
      · have hal : a = Fin.last D.R.rS := Fin.ext (by have := a.isLt; simp only [Fin.val_last]; omega)
        subst hal
        rw [Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ hz hz', hh, LTL.rhoF_last]
        simp only [mul_one, Complex.ofReal_one, one_mul]
        rfl
    · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab, mul_zero]
  rw [← htr, hs_J C hB u u' τ g', hilbert_schmidt_diagonal_invariant X u u' _ hc hg hZ]

def Kpl (D : D7) : ℝ := 2 ^ (D.R.rS + 1) * ∏ a : Fin D.R.rS, (lamB D a ^ (2 * (Formalism.QuantumDeterminants.Mdim D.R.k D.R.rS a - 1)))⁻¹

/- English proof (translation)
Use `choose h hm hs using EnergyPfLoc.stepSecX_holds D X u u'`. Establish `hL : EnergyPf.LocRep X u u' fun v cv => hs2 (JvX X u u' v (h v cv))`. Use `⟨fun v => ⟨(EnergyPfLoc.jvX_meas X u u' v).comp (hm v), fun cv => EnergyPfLoc.hilbertSchmidt_sq_nonneg _⟩, fun c hc v => ?_⟩` and prove the remaining obligations. Establish `hex : ∃ γ, HasDiag X u u' 1 c γ` using `⟨fun w => h w (c w), fun w => hs w (c w) (hc w)⟩`. Establish `hh : HasDiag X u u' 1 c (hOf X u u' 1 c)`.

Unfold `hOf`. Rewrite using `[dif_pos hex]`. Conclude with `hex.choose_spec`. Conclude with `hilbert_schmidt_diagonal_invariant X u u' v (hc v) (hs v (c v) (hc v)) (hh v)`. Establish `hk0 : ∀ τ, 0 ≤ AmpWin.kap u u' C hB τ` using `fun τ => Complex.normSq_nonneg _`.

Establish `hpl : ∀ τ, ENNReal.ofReal (AmpWin.kap u u' C hB τ) * ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * hs2 (JvX X u u' (vOf X τ) (h (vOf X τ) cv))) ∂(dcV (D` using `D)) = ENNReal.ofReal (Kpl D) * MMv D u u' (locS hB u u' τ) (sec τ) := by`. Introduce `τ`. Establish `h1` using `EnergyCV.cv_inst u u' D.R.rS rfl (lamB D) (lamB_pos D) fun q => hsNormSq ((locS hB u u' τ).J (muGB X (C.Q τ) (C.Qi τ) τ) (Formalism.QuantumDeterminants.bigCell D.R.k D.R.rS q.1 (sec τ q.2)))`. Use `Eq.trans ?_ h1` and prove the remaining obligations. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`.

Use `setLIntegral_congr_fun (goodV_meas u u') fun cv hcv => ?_` and prove the remaining obligations. Simplify using `only []`. Rewrite using `[place_pt C hB u u' τ (hsec τ) hcv (hs _ cv hcv), ← ENNReal.ofReal_mul (hk0 τ)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[EnergyNF.intCe_eq_prodE _ hL, ENNReal.ofReal_prod_of_nonneg fun τ _ => hk0 τ, ← Fintype.prod_equiv X.pl.symm (fun τ => ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * hs2 (JvX X u u' (vOf X τ) (h (vOf X τ) cv))) ∂(dcV (D := D))) _ (fun τ => rfl), ← Finset.prod_mul_distrib, Fi …`.
-/
theorem energy_prod (hB : WuBessel C) (u u' : D.what₂.Word)
    {sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hsec : ∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (sec τ)) :
    ENNReal.ofReal (∏ τ, AmpWin.kap u u' C hB τ) * intCe X u u' 1 =
      ENNReal.ofReal (Kpl D) ^ D.R.f * ∏ τ, MMv D u u' (locS hB u u' τ) (sec τ) := by
  choose h hm hs using EnergyPfLoc.stepSecX_holds D X u u'
  have hL : EnergyPf.LocRep X u u' fun v cv => hs2 (JvX X u u' v (h v cv)) := by
    refine ⟨fun v => ⟨(EnergyPfLoc.jvX_meas X u u' v).comp (hm v), fun cv => EnergyPfLoc.hilbertSchmidt_sq_nonneg _⟩, fun c hc v => ?_⟩
    have hex : ∃ γ, HasDiag X u u' 1 c γ := ⟨fun w => h w (c w), fun w => hs w (c w) (hc w)⟩
    have hh : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
      unfold hOf; rw [dif_pos hex]; exact hex.choose_spec
    exact hilbert_schmidt_diagonal_invariant X u u' v (hc v) (hs v (c v) (hc v)) (hh v)
  have hk0 : ∀ τ, 0 ≤ AmpWin.kap u u' C hB τ := fun τ => Complex.normSq_nonneg _
  have hpl : ∀ τ, ENNReal.ofReal (AmpWin.kap u u' C hB τ) *
      ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * hs2 (JvX X u u' (vOf X τ) (h (vOf X τ) cv))) ∂(dcV (D := D)) =
      ENNReal.ofReal (Kpl D) * MMv D u u' (locS hB u u' τ) (sec τ) := by
    intro τ
    have h1 := EnergyCV.cv_inst u u' D.R.rS rfl (lamB D) (lamB_pos D) fun q =>
      hsNormSq ((locS hB u u' τ).J (muGB X (C.Q τ) (C.Qi τ) τ) (Formalism.QuantumDeterminants.bigCell D.R.k D.R.rS q.1 (sec τ q.2)))
    refine Eq.trans ?_ h1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun (goodV_meas u u') fun cv hcv => ?_
    simp only []
    rw [place_pt C hB u u' τ (hsec τ) hcv (hs _ cv hcv), ← ENNReal.ofReal_mul (hk0 τ)]
    congr 1
    ring
  rw [EnergyNF.intCe_eq_prodE _ hL, ENNReal.ofReal_prod_of_nonneg fun τ _ => hk0 τ,
    ← Fintype.prod_equiv X.pl.symm (fun τ => ∫⁻ cv in GoodV u u',
      ENNReal.ofReal (wtV u u' cv * hs2 (JvX X u u' (vOf X τ) (h (vOf X τ) cv))) ∂(dcV (D := D))) _ (fun τ => rfl),
    ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun τ _ => hpl τ, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, D.what₂.card_Tau]

/- English proof (translation)
Establish `hk : 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `hrd` using `rd_pos D`. Use `set r := D.R.rS`. Use `set S : ℕ := ∑ j ∈ Finset.range r, 4 * (j + 1) * (2 * (j + 1) + D.R.k) with hS`. Establish `h1 : ∏ a : Fin r, (lamB D a ^ (2 * (Formalism.QuantumDeterminants.Mdim D.R.k r a - 1)))⁻¹ = D.host.rdE ^ S`.

Establish `e : ∀ a : Fin r, (lamB D a ^ (2 * (Formalism.QuantumDeterminants.Mdim D.R.k r a - 1)))⁻¹ = D.host.rdE ^ (4 * (r - 1 - a.val + 1) * (2 * (r - 1 - a.val + 1) + D.R.k))` using `fun a => by`. Establish `ha : r - 1 - a.val + 1 = r - a.val` using `by have := a.2; omega`. Unfold `lamB Formalism.QuantumDeterminants.Mdim`. Rewrite using `[inv_pow, inv_inv, ← pow_mul, ha, Nat.add_sub_cancel]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.prod_congr rfl fun a _ => e a, Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun a => 4 * (r - 1 - a + 1) * (2 * (r - 1 - a + 1) + D.R.k)) r, Finset.sum_range_reflect (fun j => 4 * (j + 1) * (2 * (j + 1) + D.R.k)) r]`. Establish `h3 : (3 : ℝ) * S = 4 * r * (r + 1) * (2 * r + 1) + 6 * D.R.k * r * (r + 1)`. Conclude with `EnergyKM.sum_closed r D.R.k` after adjusting the coercions. Unfold `Kpl Formalism.FourierDecayAlt.PN.abelian₂`.

Rewrite using `[h1, mul_pow, ← pow_mul, ← pow_mul, mul_comm (r + 1) D.R.f]`. Use `congr 1`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hrd]`. Use `congr 1`. Move the coercions through the operations in `[Nat.cast_sub hk]`.

Take the linear combination `((D.R.f : ℝ) / 3) * h3`.
-/
theorem kpl_pow (D : D7) : Kpl D ^ D.R.f = 2 ^ (D.R.f * (D.R.rS + 1)) *
    (Formalism.FourierDecayAlt.PN.abelian₂ D.host.rdE D.R.rS D.R.k D.R.f *
      D.host.rdE ^ (((D.R.f * D.R.rS * (D.R.rS + 1) * (8 * D.R.rS + 10) : ℕ) : ℝ) / 3)) := by
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hrd := rd_pos D
  set r := D.R.rS
  set S : ℕ := ∑ j ∈ Finset.range r, 4 * (j + 1) * (2 * (j + 1) + D.R.k) with hS
  have h1 : ∏ a : Fin r, (lamB D a ^ (2 * (Formalism.QuantumDeterminants.Mdim D.R.k r a - 1)))⁻¹ = D.host.rdE ^ S := by
    have e : ∀ a : Fin r, (lamB D a ^ (2 * (Formalism.QuantumDeterminants.Mdim D.R.k r a - 1)))⁻¹ =
        D.host.rdE ^ (4 * (r - 1 - a.val + 1) * (2 * (r - 1 - a.val + 1) + D.R.k)) := fun a => by
      have ha : r - 1 - a.val + 1 = r - a.val := by have := a.2; omega
      unfold lamB Formalism.QuantumDeterminants.Mdim
      rw [inv_pow, inv_inv, ← pow_mul, ha, Nat.add_sub_cancel]
      congr 1
      ring
    rw [Finset.prod_congr rfl fun a _ => e a, Finset.prod_pow_eq_pow_sum,
      Fin.sum_univ_eq_sum_range (fun a => 4 * (r - 1 - a + 1) * (2 * (r - 1 - a + 1) + D.R.k)) r,
      Finset.sum_range_reflect (fun j => 4 * (j + 1) * (2 * (j + 1) + D.R.k)) r]
  have h3 : (3 : ℝ) * S = 4 * r * (r + 1) * (2 * r + 1) + 6 * D.R.k * r * (r + 1) := by
    exact_mod_cast EnergyKM.sum_closed r D.R.k
  unfold Kpl Formalism.FourierDecayAlt.PN.abelian₂
  rw [h1, mul_pow, ← pow_mul, ← pow_mul, mul_comm (r + 1) D.R.f]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hrd]
  congr 1
  push_cast [Nat.cast_sub hk]
  linear_combination ((D.R.f : ℝ) / 3) * h3

/- English proof (translation)
The claim follows from `mul_pos (by positivity) (Finset.prod_pos fun a _ => inv_pos.2 (pow_pos (lamB_pos D a) _))`.
-/
theorem kpl_pos (D : D7) : 0 < Kpl D :=
  mul_pos (by positivity) (Finset.prod_pos fun a _ => inv_pos.2 (pow_pos (lamB_pos D a) _))

end Formalism.MainStatements.RowRest
