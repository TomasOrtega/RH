import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointTermAndLiftSameRealDoubleCoset
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLoUniMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpUniMul
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RelPtLift

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.LowerUnipotentMul.main`. Consider the case `exact _root_.GlobalTheory.LowerUnipotentMul.main`. Consider the case `(apply _root_.GlobalTheory.LowerUnipotentMul.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.LowerUnipotentMul.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.LowerUnipotentMul.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.LowerUnipotentMul.main ..)`.
-/
theorem loUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsLoUni l) (h' : IsLoUni l') : IsLoUni (l * l') := by
  first
  | exact @_root_.GlobalTheory.LowerUnipotentMul.main
  | exact _root_.GlobalTheory.LowerUnipotentMul.main
  | (apply _root_.GlobalTheory.LowerUnipotentMul.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LowerUnipotentMul.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LowerUnipotentMul.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LowerUnipotentMul.main ..)

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul`. Consider the case `exact _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul`. Consider the case `(apply _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul ..)`.
-/
theorem upUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsUpUni l) (h' : IsUpUni l') : IsUpUni (l * l') := by
  first
  | exact @_root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul
  | exact _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul
  | (apply _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul ..)

end Uni

variable {k r : ℕ}

def sgn (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.val)

/- English proof (translation)
Rewrite using `[sgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem sgn_sq : sgn r * sgn r = 1 := by
  rw [sgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow]
  simp

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[sgn, Matrix.mul_diagonal, mul_comm]`. Both sides reduce to the same expression.
-/
theorem zhatO_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ZhatO k r z z' g = Formalism.QuantumDeterminants.Zhat k r z z' g * sgn r := by
  ext a b
  rw [sgn, Matrix.mul_diagonal, mul_comm]
  rfl

/- English proof (translation)
Introduce `a b`. Rewrite using `[sgn, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Use `⟨fun hab => by rw [hU0 a b hab]; ring, fun hab => ?_⟩` and prove the remaining obligations. Substitute `hab` using the available equality. Rewrite using `[hU1, mul_one, ← mul_pow]`.

Simplify using the standard rewrite rules.
-/
theorem upUni_sgn_conj {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hU0 : ∀ c b, b < c → U c b = 0)
    (hU1 : ∀ c, U c c = 1) : IsUpUni (sgn r * U * sgn r) := by
  intro a b
  rw [sgn, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun hab => by rw [hU0 a b hab]; ring, fun hab => ?_⟩
  subst hab
  rw [hU1, mul_one, ← mul_pow]
  simp

/- English proof (translation)
Introduce `a b`. Use `⟨fun hab => by rw [conjTranspose_apply, hU0 b a hab, star_zero], fun hab => ?_⟩` and prove the remaining obligations. Substitute `hab` using the available equality. Rewrite using `[conjTranspose_apply, hU1, star_one]`.
-/
theorem loUni_conjT {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hU0 : ∀ c b, b < c → U c b = 0)
    (hU1 : ∀ c, U c c = 1) : IsLoUni Uᴴ := by
  intro a b
  refine ⟨fun hab => by rw [conjTranspose_apply, hU0 b a hab, star_zero], fun hab => ?_⟩
  subst hab
  rw [conjTranspose_apply, hU1, star_one]

/- English proof (translation)
The claim follows from `Matrix.isUnit_det_of_right_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1`.
-/
theorem det_Hpk : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1

/- English proof (translation)
The claim follows from `Formalism.QuantumDeterminants.Sset_UH ha`.
-/
theorem mem_UH_of_Sset {z : Fin (2 * r + k + 1) → ℂ} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.Sset k r z) : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
  Formalism.QuantumDeterminants.Sset_UH ha

/- English proof (translation)
Take `⟨-, -, hinv⟩` from `Formalism.QuantumDeterminants.sGroup k r z hz`. Take `⟨-, -, hinv'⟩` from `Formalism.QuantumDeterminants.sGroup k r z' hz'`. Take `⟨U, hU0, hU1, hF⟩` from `Formalism.QuantumDeterminants.S_F hz (hinv a ha)`. Take `⟨U', hU0', hU1', hF'⟩` from `Formalism.QuantumDeterminants.S_F hz' (hinv' a' ha')`. Establish `hdet : IsUnit a.det` using `((Formalism.QuantumDeterminants.uHGroup _ _ det_Hpk).2.2 a (mem_UH_of_Sset ha)).1`.

Establish `hai : (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * a⁻¹ = Formalism.QuantumDeterminants.Hpk k r` using `Formalism.QuantumDeterminants.Sset_UH (hinv a ha)`. Establish `hHa : Formalism.QuantumDeterminants.Hpk k r * a = (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]`. Use `⟨U, U', hU0, hU1, hU0', hU1', ?_⟩` and prove the remaining obligations.

Rewrite using `[Formalism.QuantumDeterminants.Zhat_eq, Formalism.QuantumDeterminants.Zhat_eq]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (Formalism.QuantumDeterminants.Fm k r z)ᴴ * ((a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r) * g * (Formalism.QuantumDeterminants.Fm k r z' * U') := by`. Rewrite using `[hHa, hF']`.

Use `_ = (a⁻¹ * Formalism.QuantumDeterminants.Fm k r z)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g * Formalism.QuantumDeterminants.Fm k r z' * U' := by`. Rewrite using `[conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Uᴴ * ((Formalism.QuantumDeterminants.Fm k r z)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g * Formalism.QuantumDeterminants.Fm k r z') * U' := by`. Rewrite using `[hF, conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`.
-/
theorem zhat_dcoset {z z' : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) (hz' : Formalism.QuantumDeterminants.inWb k r z')
    {a a' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.Sset k r z)
    (ha' : a' ∈ Formalism.QuantumDeterminants.Sset k r z') (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ∃ U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, (∀ c b, b < c → U c b = 0) ∧ (∀ c, U c c = 1) ∧
      (∀ c b, b < c → U' c b = 0) ∧ (∀ c, U' c c = 1) ∧
      Formalism.QuantumDeterminants.Zhat k r z z' (a * g * a'⁻¹) = Uᴴ * Formalism.QuantumDeterminants.Zhat k r z z' g * U' := by
  obtain ⟨-, -, hinv⟩ := Formalism.QuantumDeterminants.sGroup k r z hz
  obtain ⟨-, -, hinv'⟩ := Formalism.QuantumDeterminants.sGroup k r z' hz'
  obtain ⟨U, hU0, hU1, hF⟩ := Formalism.QuantumDeterminants.S_F hz (hinv a ha)
  obtain ⟨U', hU0', hU1', hF'⟩ := Formalism.QuantumDeterminants.S_F hz' (hinv' a' ha')
  have hdet : IsUnit a.det := ((Formalism.QuantumDeterminants.uHGroup _ _ det_Hpk).2.2 a (mem_UH_of_Sset ha)).1
  have hai : (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * a⁻¹ = Formalism.QuantumDeterminants.Hpk k r := Formalism.QuantumDeterminants.Sset_UH (hinv a ha)
  have hHa : Formalism.QuantumDeterminants.Hpk k r * a = (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r := by
    calc Formalism.QuantumDeterminants.Hpk k r * a = (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * a⁻¹ * a := by rw [hai]
      _ = (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r := by
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  refine ⟨U, U', hU0, hU1, hU0', hU1', ?_⟩
  rw [Formalism.QuantumDeterminants.Zhat_eq, Formalism.QuantumDeterminants.Zhat_eq]
  calc (Formalism.QuantumDeterminants.Fm k r z)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * g * a'⁻¹) * Formalism.QuantumDeterminants.Fm k r z'
      = (Formalism.QuantumDeterminants.Fm k r z)ᴴ * (Formalism.QuantumDeterminants.Hpk k r * a) * g * (a'⁻¹ * Formalism.QuantumDeterminants.Fm k r z') := by
        simp only [Matrix.mul_assoc]
    _ = (Formalism.QuantumDeterminants.Fm k r z)ᴴ * ((a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r) * g * (Formalism.QuantumDeterminants.Fm k r z' * U') := by
        rw [hHa, hF']
    _ = (a⁻¹ * Formalism.QuantumDeterminants.Fm k r z)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g * Formalism.QuantumDeterminants.Fm k r z' * U' := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Uᴴ * ((Formalism.QuantumDeterminants.Fm k r z)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g * Formalism.QuantumDeterminants.Fm k r z') * U' := by
        rw [hF, conjTranspose_mul]; simp only [Matrix.mul_assoc]

/- English proof (translation)
Take `⟨hUH, ⟨L, V, hL, hV, hZ⟩, hGf⟩` from `h`. Take `⟨-, -, hinv'⟩` from `Formalism.QuantumDeterminants.sGroup _ _ z' hz'`. Establish `hG` using `Formalism.QuantumDeterminants.uHGroup _ _ (det_Hpk (k := D.R.k) (r := D.R.rS))`. Use `⟨hG.2.1 _ (hG.2.1 _ (mem_UH_of_Sset ha) _ hUH) _ (mem_UH_of_Sset (hinv' a' ha')), ?_, ?_⟩` and prove the remaining obligations. Take `⟨U, U', hU0, hU1, hU0', hU1', he⟩` from `zhat_dcoset hz hz' ha ha' γ`.

Establish `hZ' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' γ = L * ptMat p * V * sgn D.R.rS`. Rewrite using `[← hZ, zhatO_eq, Matrix.mul_assoc, sgn_sq, Matrix.mul_one]`. Use `⟨Uᴴ * L, V * (sgn D.R.rS * U' * sgn D.R.rS), loUni_mul (loUni_conjT hU0 hU1) hL, upUni_mul hV (upUni_sgn_conj hU0' hU1'), ?_⟩` and prove the remaining obligations. Rewrite using `[zhatO_eq, he, hZ']`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[Formalism.QuantumDeterminants.gInv _ _ z z' hz hz' a ha a'⁻¹ (hinv' a' ha') γ]`. Conclude with `hGf`.
-/
theorem relPt_dcoset (D : D7) {z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z)
    (hz' : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z') {a a' γ : MatKR D.R.k D.R.rS} (ha : a ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z)
    (ha' : a' ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z') {p : Point ℂ (D.R.rS + 1)} (h : RelPt D z z' γ p) :
    RelPt D z z' (a * γ * a'⁻¹) p := by
  obtain ⟨hUH, ⟨L, V, hL, hV, hZ⟩, hGf⟩ := h
  obtain ⟨-, -, hinv'⟩ := Formalism.QuantumDeterminants.sGroup _ _ z' hz'
  have hG := Formalism.QuantumDeterminants.uHGroup _ _ (det_Hpk (k := D.R.k) (r := D.R.rS))
  refine ⟨hG.2.1 _ (hG.2.1 _ (mem_UH_of_Sset ha) _ hUH) _ (mem_UH_of_Sset (hinv' a' ha')), ?_, ?_⟩
  · obtain ⟨U, U', hU0, hU1, hU0', hU1', he⟩ := zhat_dcoset hz hz' ha ha' γ
    have hZ' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' γ = L * ptMat p * V * sgn D.R.rS := by
      rw [← hZ, zhatO_eq, Matrix.mul_assoc, sgn_sq, Matrix.mul_one]
    refine ⟨Uᴴ * L, V * (sgn D.R.rS * U' * sgn D.R.rS), loUni_mul (loUni_conjT hU0 hU1) hL,
      upUni_mul hV (upUni_sgn_conj hU0' hU1'), ?_⟩
    rw [zhatO_eq, he, hZ']
    simp only [Matrix.mul_assoc]
  · rw [Formalism.QuantumDeterminants.gInv _ _ z z' hz hz' a ha a'⁻¹ (hinv' a' ha') γ]
    exact hGf

end GlobalTheory.RelPtLift

/- English proof (translation)
Introduce `D X Y hF hI θ C u u' t s hs hG hr τ`. Take `⟨p, hp⟩` from `relPtEx_holds hI C u u' t hG hr τ`. Take `⟨a, ha, a', ha', heq⟩` from `GlobalTheory.TermCoset.dcoset D X Y hF hI θ C u u' t s hs τ`. Use `⟨p, ?_⟩` and prove the remaining obligations. Rewrite using `[heq]`.

Conclude with `GlobalTheory.RelPtLift.relPt_dcoset D (Formalism.L2.SG.Pf.zTr C u τ).1 (Formalism.L2.SG.Pf.zTr C u' τ).1 ha ha' hp`.
-/
theorem GlobalTheory.RelPtLift.relPt_lift : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ, ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) p := by
  intro D X Y hF hI θ C u u' t s hs hG hr τ
  obtain ⟨p, hp⟩ := relPtEx_holds hI C u u' t hG hr τ
  obtain ⟨a, ha, a', ha', heq⟩ := GlobalTheory.TermCoset.dcoset D X Y hF hI θ C u u' t s hs τ
  refine ⟨p, ?_⟩
  rw [heq]
  exact GlobalTheory.RelPtLift.relPt_dcoset D (Formalism.L2.SG.Pf.zTr C u τ).1 (Formalism.L2.SG.Pf.zTr C u' τ).1 ha ha' hp
