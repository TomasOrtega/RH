import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.UMatMulInv

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (v : InfinitePlace X.B.I.F)

/- English proof (translation)
Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`. Rewrite using `[frm_last, hfz_v, if_neg (Fin.castSucc_ne_last a).symm]`. Consider the case `cast b`. Rewrite using `[frm_castSucc, hJs_r, hfe_v]`.

Distinguish the cases in `h : b = a`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg (fun e => h (Fin.castSucc_injective _ e)), mul_zero]`.
-/
theorem hfF (w' : D.what₂.Word) (a : Fin D.R.rS) (b : Fin (D.R.rS + 1)) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (frm X w' D.host.rdE v b) =
      if b = a.castSucc then ((D.host.rdE : ℂ) ^ (D.R.rS - a.1))⁻¹ else 0 := by
  induction b using Fin.lastCases with
  | last =>
    rw [frm_last, hfz_v, if_neg (Fin.castSucc_ne_last a).symm]
  | cast b =>
    rw [frm_castSucc, hJs_r, hfe_v]
    by_cases h : b = a
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_injective _ e)), mul_zero]

/- English proof (translation)
Unfold `stCoordV`. Use `set a' : Fin D.R.rS := ⟨p.1.1.1, by have := p.2.1; omega⟩ with ha'`. Establish `hcs : a'.castSucc = p.1.1` using `Fin.ext rfl`. Establish `hT : uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) *ᵥ frm X u' D.host.rdE v p.1.2 = frm X u' D.host.rdE v p.1.2 + ∑ b', (Cw w c - 1) b' p.1.2 • frm X u' D.host.rdE v b'`. Establish `h1` using `T_sub X u u' w v hw c (frm X u' D.host.rdE v p.1.2)`.

Rewrite `h1` using `[sub_one_mulVec, ← G_eq, TG_comb X u u' w v hw c]`. Rewrite using `[← h1]`. Normalize the expressions using the abelian group laws. Rewrite using `[hT, hJ_add_r', hJ_sum_r', hfF, if_neg (fun e => (ne_of_lt p.2.1) (by rw [← hcs, e]))]`. Rewrite using `[Finset.sum_eq_single a'.castSucc]`.

Rewrite using `[hfF, if_pos rfl, zero_add, hcs, Matrix.sub_apply, Matrix.one_apply, if_neg (ne_of_lt p.2.1), sub_zero, Cw_apply_free]`. Establish `hrd : (D.host.rdE : ℂ) ^ (D.R.rS - a'.1) ≠ 0` using `pow_ne_zero _ (Complex.ofReal_ne_zero.2 (rdE_pos_c (D := D)).ne')`. Rewrite using `[show p.1.1.1 = a'.1 from rfl]`. Clear the denominators using the available nonvanishing facts. Introduce `b _ hb`.

Rewrite using `[hfF, if_neg hb, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem coord_eq (hw : OkPt X u u' w) (c : FreeE w → ℂ) (p : FreeE w) :
    stCoordV X u' w (gamW X u u' w) v (yU X u u' w v c hw) p = c p := by
  unfold stCoordV
  set a' : Fin D.R.rS := ⟨p.1.1.1, by have := p.2.1; omega⟩ with ha'
  have hcs : a'.castSucc = p.1.1 := Fin.ext rfl
  have hT : uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) *ᵥ frm X u' D.host.rdE v p.1.2 =
      frm X u' D.host.rdE v p.1.2 + ∑ b', (Cw w c - 1) b' p.1.2 • frm X u' D.host.rdE v b' := by
    have h1 := T_sub X u u' w v hw c (frm X u' D.host.rdE v p.1.2)
    rw [sub_one_mulVec, ← G_eq, TG_comb X u u' w v hw c] at h1
    rw [← h1]; abel
  rw [hT, hJ_add_r', hJ_sum_r', hfF, if_neg (fun e => (ne_of_lt p.2.1) (by rw [← hcs, e]))]
  rw [Finset.sum_eq_single a'.castSucc]
  · rw [hfF, if_pos rfl, zero_add, hcs, Matrix.sub_apply, Matrix.one_apply, if_neg (ne_of_lt p.2.1), sub_zero,
      Cw_apply_free]
    have hrd : (D.host.rdE : ℂ) ^ (D.R.rS - a'.1) ≠ 0 :=
      pow_ne_zero _ (Complex.ofReal_ne_zero.2 (rdE_pos_c (D := D)).ne')
    rw [show p.1.1.1 = a'.1 from rfl]
    field_simp
  · intro b _ hb
    rw [hfF, if_neg hb, mul_zero]
  · simp

/- English proof (translation)
Establish `hC : Continuous fun c : FreeE w → ℂ => Cw w c`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [Cw, Matrix.of_apply]`. Use `split_ifs`. Conclude with `continuous_const`.

Conclude with `continuous_apply _`. Conclude with `continuous_const`. Establish `hdet : ∀ c : FreeE w → ℂ, (Cw w c).det = 1`. Introduce `c`. Rewrite using `[Matrix.det_of_upperTriangular]`.

Simplify using `[Cw]`. Introduce `i j hij`. Simplify using `only [Cw, Matrix.of_apply]`. Establish `hji : j < i` using `hij`. Rewrite using `[if_neg (ne_of_gt hji), dif_neg (fun h => absurd h.1 (lt_asymm hji))]`.

Establish `hinv : Continuous fun c : FreeE w → ℂ => (Cw w c)⁻¹`. Establish `h : (fun c : FreeE w → ℂ => (Cw w c)⁻¹) = fun c => (Cw w c).adjugate`. Use function extensionality and compare the values at `c`. Rewrite using `[Matrix.inv_def, hdet c, Ring.inverse_one, one_smul]`. Rewrite using `[h]`.

Conclude with `hC.matrix_adjugate`. Unfold `Yc Ymat Mm Am`. Conclude with `continuous_const.add ((((continuous_const.matrix_mul (Continuous.matrix_fromBlocks (((continuous_const.matrix_mul hinv).matrix_mul continuous_const).matrix_conjTranspose.sub continuous_const) continuous_const continuous_const (hC.sub continuous_const))).matrix_mul continuous_cons …`.
-/
theorem continuous_yM (hw : OkPt X u u' w) :
    Continuous fun c : FreeE w → ℂ => Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) := by

  have hC : Continuous fun c : FreeE w → ℂ => Cw w c := by
    refine continuous_matrix fun i j => ?_
    simp only [Cw, Matrix.of_apply]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
    · exact continuous_const

  have hdet : ∀ c : FreeE w → ℂ, (Cw w c).det = 1 := by
    intro c
    rw [Matrix.det_of_upperTriangular]
    · simp [Cw]
    · intro i j hij
      simp only [Cw, Matrix.of_apply]
      have hji : j < i := hij
      rw [if_neg (ne_of_gt hji), dif_neg (fun h => absurd h.1 (lt_asymm hji))]

  have hinv : Continuous fun c : FreeE w → ℂ => (Cw w c)⁻¹ := by
    have h : (fun c : FreeE w → ℂ => (Cw w c)⁻¹) = fun c => (Cw w c).adjugate := by
      funext c
      rw [Matrix.inv_def, hdet c, Ring.inverse_one, one_smul]
    rw [h]
    exact hC.matrix_adjugate
  unfold Yc Ymat Mm Am
  exact continuous_const.add ((((continuous_const.matrix_mul (Continuous.matrix_fromBlocks
    (((continuous_const.matrix_mul hinv).matrix_mul continuous_const).matrix_conjTranspose.sub continuous_const)
    continuous_const continuous_const (hC.sub continuous_const))).matrix_mul continuous_const).matrix_mul
    continuous_const).matrix_mul continuous_const)

/- English proof (translation)
Introduce `w hw v`. Use `⟨fun c => yU X u u' w v c hw, ?_, fun c => ⟨inN_u X u u' w v hw c, inN_u' X u u' w v hw c⟩, fun c => funext fun p => coord_eq X u u' w v hw c p⟩` and prove the remaining obligations. Establish `hY` using `continuous_yM X u u' w v hw`. Unfold `yU mkUJ`. Use `Continuous.subtype_mk (Units.continuous_iff.2 ⟨hY, ?_⟩) _` and prove the remaining obligations.

Conclude with `(continuous_const.matrix_mul hY.matrix_conjTranspose).matrix_mul continuous_const`.
-/
theorem stVSec_holds : StVSec X u u' := by
  intro w hw v
  refine ⟨fun c => yU X u u' w v c hw, ?_, fun c => ⟨inN_u X u u' w v hw c, inN_u' X u u' w v hw c⟩,
    fun c => funext fun p => coord_eq X u u' w v hw c p⟩
  have hY := continuous_yM X u u' w v hw
  unfold yU mkUJ
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨hY, ?_⟩) _
  exact (continuous_const.matrix_mul hY.matrix_conjTranspose).matrix_mul continuous_const

/- English proof (translation)
The claim follows from `ooQuot_geo X u u' νq hN (stRel_holds X u u') (stVGeo_of_sec X u u' (stVSec_holds X u u'))`.
-/
theorem ooQuot_of_nuQPin (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq) :
    ∃ νl, (∀ w, OkPt X u u' w → LocPin X u u' w νl) ∧ Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' νq νl :=
  ooQuot_geo X u u' νq hN (stRel_holds X u u') (stVGeo_of_sec X u u' (stVSec_holds X u u'))

end Formalism.L2.S.L6.UnitaryStandardVectors
