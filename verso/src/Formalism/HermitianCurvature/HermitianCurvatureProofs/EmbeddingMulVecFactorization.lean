import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomCut

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open PI.UnitaryGroupMassFormula.GsFr PI.UnitaryGroupMassFormula.DLm.Gram
open Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S5

variable {k r : ℕ}

/- English proof (translation)
Establish `hc1 : Continuous fun v : Fin (2 * r + k + 1) → ℂ => herm (Hpk k r) v z`. Unfold `herm`. Use `fun_prop`. Establish `hc2 : Continuous fun v : Fin (2 * r + k + 1) → ℂ => (herm (Hpk k r) v v).re`. Unfold `herm`.

Use `fun_prop`. Establish `hWb : IsClosed {v : Fin (2 * r + k + 1) → ℂ | inWb k r v}`. Simplify using `only [inWb, Set.ofPred_forall]`. Conclude with `isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const`. Use `set K : Set (Fin (2 * r + k + 1) → ℂ) := Metric.sphere 0 1 ∩ ({v | inWb k r v} ∩ {v | herm (Hpk k r) v z = 0}) with hK`.

Establish `hKc : IsCompact K` using `(isCompact_sphere 0 1).inter_right (hWb.inter (isClosed_eq hc1 continuous_const))`. Establish `hpos : ∀ v ∈ K, 0 < (herm (Hpk k r) v v).re`. Introduce and unpack `v ⟨hv1, hv2, hv3⟩`. Use `posV hz hv2 hv3 ?_` and prove the remaining obligations. Introduce and unpack `rfl`.

Simplify using `at hv1`. Take `⟨C, hC⟩` from `hKc.exists_bound_of_continuousOn (f := fun v => ((herm (Hpk k r) v v).re)⁻¹) (hc2.continuousOn.inv₀ fun v hv => (hpos v hv).ne')`. Use `⟨max C 0, le_max_right _ _, fun v hv hvz => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : v = 0`. Substitute `h0` using the available equality.

Simplify using `[herm]`. Establish `hn : 0 < ‖v‖` using `norm_pos_iff.2 h0`. Use `set c : ℂ := ((‖v‖⁻¹ : ℝ) : ℂ) with hc`. Establish `hwK : c • v ∈ K`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']`. Introduce `i hi`. Simplify using `[hv i hi]`. Use `show herm (Hpk k r) (c • v) z = 0`. Rewrite using `[hm_smul_l, hvz, mul_zero]`.

Establish `hf : (herm (Hpk k r) (c • v) (c • v)).re = ‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re`. Rewrite using `[hm_smul_l, hm_smul_r, hc, Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hb` using `hC (c • v) hwK`. Establish `hp` using `hpos _ hwK`.

Rewrite `hp`, `hb` using `[hf]`. Establish `ht : 0 < (herm (Hpk k r) v v).re`. Establish `: 0 < ‖v‖⁻¹ ^ 2` using `by positivity`. Conclude with `pos_of_mul_pos_right hp this.le`. Rewrite `hb` using `[Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp)]`.

Establish `hb2 : 1 ≤ C * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re)`. Rewrite `hb` using `[inv_le_iff_one_le_mul₀ hp]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : ‖v‖ ^ 2 * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re) = (herm (Hpk k r) v v).re`. Clear the denominators using the available nonvanishing facts.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma W_bound {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin (2 * r + k + 1) → ℂ, inWb k r v → herm (Hpk k r) v z = 0 →
      ‖v‖ ^ 2 ≤ C * (herm (Hpk k r) v v).re := by
  have hc1 : Continuous fun v : Fin (2 * r + k + 1) → ℂ => herm (Hpk k r) v z := by
    unfold herm; fun_prop
  have hc2 : Continuous fun v : Fin (2 * r + k + 1) → ℂ => (herm (Hpk k r) v v).re := by
    unfold herm; fun_prop
  have hWb : IsClosed {v : Fin (2 * r + k + 1) → ℂ | inWb k r v} := by
    simp only [inWb, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const
  set K : Set (Fin (2 * r + k + 1) → ℂ) :=
    Metric.sphere 0 1 ∩ ({v | inWb k r v} ∩ {v | herm (Hpk k r) v z = 0}) with hK
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_right (hWb.inter (isClosed_eq hc1 continuous_const))
  have hpos : ∀ v ∈ K, 0 < (herm (Hpk k r) v v).re := by
    rintro v ⟨hv1, hv2, hv3⟩
    refine posV hz hv2 hv3 ?_
    rintro rfl
    simp at hv1
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (f := fun v => ((herm (Hpk k r) v v).re)⁻¹)
    (hc2.continuousOn.inv₀ fun v hv => (hpos v hv).ne')
  refine ⟨max C 0, le_max_right _ _, fun v hv hvz => ?_⟩
  by_cases h0 : v = 0
  · subst h0; simp [herm]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 h0
  set c : ℂ := ((‖v‖⁻¹ : ℝ) : ℂ) with hc
  have hwK : c • v ∈ K := by
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, hc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']
    · intro i hi; simp [hv i hi]
    · show herm (Hpk k r) (c • v) z = 0
      rw [hm_smul_l, hvz, mul_zero]
  have hf : (herm (Hpk k r) (c • v) (c • v)).re = ‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re := by
    rw [hm_smul_l, hm_smul_r, hc, Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.re_ofReal_mul]
    ring
  have hb := hC (c • v) hwK
  have hp := hpos _ hwK
  rw [hf] at hp hb
  have ht : 0 < (herm (Hpk k r) v v).re := by
    have : 0 < ‖v‖⁻¹ ^ 2 := by positivity
    exact pos_of_mul_pos_right hp this.le
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp)] at hb
  have hb2 : 1 ≤ C * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re) := by
    rw [inv_le_iff_one_le_mul₀ hp] at hb; linarith
  have e : ‖v‖ ^ 2 * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re) = (herm (Hpk k r) v v).re := by
    field_simp
  calc ‖v‖ ^ 2 = ‖v‖ ^ 2 * 1 := by ring
    _ ≤ ‖v‖ ^ 2 * (C * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re)) :=
        mul_le_mul_of_nonneg_left hb2 (by positivity)
    _ = C * (‖v‖ ^ 2 * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re)) := by ring
    _ = C * (herm (Hpk k r) v v).re := by rw [e]
    _ ≤ max C 0 * (herm (Hpk k r) v v).re := mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le

/- English proof (translation)
Use `show star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (c • x)) = c * (star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x))`. Rewrite using `[Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
private theorem herm_Hpk_smul_left (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (c • x) y = c * Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x y := by
  show star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (c • x)) = c * (star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x))
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Use `show star (c • y) ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x) = star c * (star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x))`. Rewrite using `[star_smul, smul_dotProduct, smul_eq_mul]`.
-/
private theorem herm_Hpk_smul_right_eq_star_mul (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x (c • y) = star c * Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x y := by
  show star (c • y) ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x) = star c * (star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x))
  rw [star_smul, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Take `⟨hw, ho⟩` from `hv`. Use `set s : ℝ := (Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re)⁻¹ with hs`. Establish `hU : unitH k r v = (s : ℂ) • v` using `rfl`. Rewrite using `[hU]`. Use `⟨⟨fun i hi => by rw [Pi.smul_apply, hw i hi, smul_zero], ?_⟩, ?_⟩` and prove the remaining obligations.

Use `show Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) ((s : ℂ) • v) z = 0`. Rewrite using `[herm_Hpk_smul_left, ho, mul_zero]`. Use `show (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) ((s : ℂ) • v) ((s : ℂ) • v)).re ≤ 1`. Rewrite using `[herm_Hpk_smul_left, herm_Hpk_smul_right_eq_star_mul, Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]`. Distinguish the cases in `hpos : 0 < (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re`.

Conclude with `le_of_eq (by rw [hs, ← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne'])`. Rewrite using `[hs, Real.sqrt_eq_zero'.2 (not_lt.1 hpos)]`. Simplify using the standard rewrite rules.
-/
lemma unitH_facts {z v : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hv : v ∈ Wsp k r z) :
    unitH k r v ∈ Wsp k r z ∧ (herm (Hpk k r) (unitH k r v) (unitH k r v)).re ≤ 1 := by
  obtain ⟨hw, ho⟩ := hv
  set s : ℝ := (Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re)⁻¹ with hs
  have hU : unitH k r v = (s : ℂ) • v := rfl
  rw [hU]
  refine ⟨⟨fun i hi => by rw [Pi.smul_apply, hw i hi, smul_zero], ?_⟩, ?_⟩
  · show Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) ((s : ℂ) • v) z = 0
    rw [herm_Hpk_smul_left, ho, mul_zero]
  · show (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) ((s : ℂ) • v) ((s : ℂ) • v)).re ≤ 1
    rw [herm_Hpk_smul_left, herm_Hpk_smul_right_eq_star_mul, Complex.star_def, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    by_cases hpos : 0 < (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re
    · exact le_of_eq (by rw [hs, ← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne'])
    · rw [hs, Real.sqrt_eq_zero'.2 (not_lt.1 hpos)]
      simp

/- English proof (translation)
Establish `e : ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * herm (Hpk k r) (y *ᵥ u) (fvec k r z a) = 0`. Establish `h1 : ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * herm (Hpk k r) (y *ᵥ u) (fvec k r z a) = herm (Hpk k r) (y *ᵥ u) (xcofL k r z z' y)`. Unfold `xcofL`. Rewrite using `[hm_sum_r]`. Simplify using `only [star_star]`.

Rewrite using `[h1, ← ginv_cancel hy (xcofL k r z z' y), Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, ← herm_prW_r huW]`. Conclude with `huo`. Establish `hlast : gam k r z z' y u (Fin.last r) = 0`. Simplify using `only [gam, wv, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct]`. Rewrite using `[e, mul_zero]`.

Establish `hS : Lm k r z z' y *ᵥ u - u = ∑ c, gam k r z z' y u c • fvec k r z' c` using `by rw [Lm_mulVec]; abel`. Rewrite using `[hS]`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : c = Fin.last r`. Rewrite using `[hc, hlast, zero_smul]`.

Conclude with `Submodule.zero_mem _`. Conclude with `Submodule.smul_mem _ _ (fv_X z' c hc)`.
-/
lemma lift_X' {z z' : Fin (2 * r + k + 1) → ℂ} {y : B.Mat k r} (hy : y ∈ B.GV k r)
    {u : Fin (2 * r + k + 1) → ℂ} (huW : u ∈ Wsp k r z') (huo : herm (Hpk k r) u (omW' k r z z' y) = 0) :
    Lm k r z z' y *ᵥ u - u ∈ Xsp k r := by
  have e : ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * herm (Hpk k r) (y *ᵥ u) (fvec k r z a) = 0 := by
    have h1 : ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * herm (Hpk k r) (y *ᵥ u) (fvec k r z a) =
        herm (Hpk k r) (y *ᵥ u) (xcofL k r z z' y) := by
      unfold xcofL; rw [hm_sum_r]; simp only [star_star]
    rw [h1, ← ginv_cancel hy (xcofL k r z z' y), Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, ← herm_prW_r huW]
    exact huo
  have hlast : gam k r z z' y u (Fin.last r) = 0 := by
    simp only [gam, wv, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct]
    rw [e, mul_zero]
  have hS : Lm k r z z' y *ᵥ u - u = ∑ c, gam k r z z' y u c • fvec k r z' c := by rw [Lm_mulVec]; abel
  rw [hS]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : c = Fin.last r
  · rw [hc, hlast, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (fv_X z' c hc)

/- English proof (translation)
Rewrite using `[Phi_mulVec]`. Establish `hx` using `sub_prW_X hz (lift_orth hd u)`. Establish `hP` using `prW_mem hz (y *ᵥ (Lm k r z z' y *ᵥ u))`. Establish `hL` using `lift_X' hy huW huo`. Rewrite using `[← herm_add_X hP.1 hP.1 hx hx, aps, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, ← herm_add_X huW.1 huW.1 hL hL, aps]`.
-/
lemma phi_iso' {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {y : B.Mat k r} (hy : y ∈ B.GV k r)
    (hd : (Zhat k r z z' y).det ≠ 0) {u : Fin (2 * r + k + 1) → ℂ} (huW : u ∈ Wsp k r z')
    (huo : herm (Hpk k r) u (omW' k r z z' y) = 0) :
    herm (Hpk k r) (Phi k r z z' y *ᵥ u) (Phi k r z z' y *ᵥ u) = herm (Hpk k r) u u := by
  rw [Phi_mulVec]
  have hx := sub_prW_X hz (lift_orth hd u)
  have hP := prW_mem hz (y *ᵥ (Lm k r z z' y *ᵥ u))
  have hL := lift_X' hy huW huo
  rw [← herm_add_X hP.1 hP.1 hx hx, aps, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, ← herm_add_X huW.1 huW.1 hL hL, aps]

/- English proof (translation)
Establish `hH : (Hpk k r)ᴴ = Hpk k r` using `(Formalism.QuantumDeterminants.hpkFacts k r).1`. Establish `hPe : PpG z z' g *ᵥ v = PI.UnitaryGroupMassFormula.GsFr.prW k r z' v - herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v) (nuG' z z' g) • nuG' z z' g`. Unfold `PpG`. Rewrite using `[sub_mulVec, ← mulVec_mulVec, Pm_mulVec, Rk_mulVec]`. Use `set p := PI.UnitaryGroupMassFormula.GsFr.prW k r z' v with hp`.

Use `set om := omW' k r z z' g with hom`. Establish `hpW : p ∈ Wsp k r z'` using `prW_mem hz' v`. Establish `homW : om ∈ Wsp k r z'` using `prW_mem hz' _`. Establish `hνW : nuG' z z' g ∈ Wsp k r z'` using `Wsp_smul _ homW`. Rewrite using `[hPe]`.

Use `⟨Wsp_sub hpW (Wsp_smul _ hνW), ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : om = 0`. Establish `hν0 : nuG' z z' g = 0` using `by show unitH k r om = 0`. Rewrite using `[h0]`. Simplify using `[unitH]`.

Rewrite using `[hν0, h0]`. Simplify using `[herm]`. Establish `ht` using `posV hz' homW.1 homW.2 h0`. Establish `hνν : herm (Hpk k r) (nuG' z z' g) (nuG' z z' g) = 1` using `nz_unit ht`. Use `set c := herm (Hpk k r) p (nuG' z z' g) with hcdef`.

Use `set u := p - c • nuG' z z' g with hu`. Establish `huν : herm (Hpk k r) u (nuG' z z' g) = 0`. Rewrite using `[hu, hm_sub_l, hm_smul_l, hνν, mul_one, sub_self]`. Establish `hνu : herm (Hpk k r) (nuG' z z' g) u = 0`. Rewrite using `[hm_symm _ hH, huν, star_zero]`.

Use `⟨(nz_orth ht u).1 huν, ?_⟩` and prove the remaining obligations. Establish `hpu : p = u + c • nuG' z z' g` using `by rw [hu, sub_add_cancel]`. Establish `e : herm (Hpk k r) p p = herm (Hpk k r) u u + c * star c` using `by conv_lhs => rw [hpu]`. Rewrite using `[hm_add_l, hm_add_r, hm_add_r, hm_smul_l, hm_smul_l, hm_smul_r, hm_smul_r, huν, hνu, hνν]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, Complex.add_re]`. Establish `: 0 ≤ (c * star c).re`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.ofReal_re]`. Conclude with `Complex.normSq_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma Pp_facts {z z' : Fin (2 * r + k + 1) → ℂ} (hz' : C2.StdZ k r z') (g : B.Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) :
    PpG z z' g *ᵥ v ∈ Wsp k r z' ∧ herm (Hpk k r) (PpG z z' g *ᵥ v) (omW' k r z z' g) = 0 ∧
      (herm (Hpk k r) (PpG z z' g *ᵥ v) (PpG z z' g *ᵥ v)).re ≤
        (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v)).re := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (Formalism.QuantumDeterminants.hpkFacts k r).1
  have hPe : PpG z z' g *ᵥ v = PI.UnitaryGroupMassFormula.GsFr.prW k r z' v -
      herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v) (nuG' z z' g) • nuG' z z' g := by
    unfold PpG
    rw [sub_mulVec, ← mulVec_mulVec, Pm_mulVec, Rk_mulVec]
  set p := PI.UnitaryGroupMassFormula.GsFr.prW k r z' v with hp
  set om := omW' k r z z' g with hom
  have hpW : p ∈ Wsp k r z' := prW_mem hz' v
  have homW : om ∈ Wsp k r z' := prW_mem hz' _
  have hνW : nuG' z z' g ∈ Wsp k r z' := Wsp_smul _ homW
  rw [hPe]
  refine ⟨Wsp_sub hpW (Wsp_smul _ hνW), ?_⟩
  by_cases h0 : om = 0
  · have hν0 : nuG' z z' g = 0 := by
      show unitH k r om = 0
      rw [h0]; simp [unitH]
    rw [hν0, h0]
    simp [herm]
  have ht := posV hz' homW.1 homW.2 h0
  have hνν : herm (Hpk k r) (nuG' z z' g) (nuG' z z' g) = 1 := nz_unit ht
  set c := herm (Hpk k r) p (nuG' z z' g) with hcdef
  set u := p - c • nuG' z z' g with hu
  have huν : herm (Hpk k r) u (nuG' z z' g) = 0 := by
    rw [hu, hm_sub_l, hm_smul_l, hνν, mul_one, sub_self]
  have hνu : herm (Hpk k r) (nuG' z z' g) u = 0 := by
    rw [hm_symm _ hH, huν, star_zero]
  refine ⟨(nz_orth ht u).1 huν, ?_⟩
  have hpu : p = u + c • nuG' z z' g := by rw [hu, sub_add_cancel]
  have e : herm (Hpk k r) p p = herm (Hpk k r) u u + c * star c := by
    conv_lhs => rw [hpu]
    rw [hm_add_l, hm_add_r, hm_add_r, hm_smul_l, hm_smul_l, hm_smul_r, hm_smul_r, huν, hνu, hνν]
    ring
  rw [e, Complex.add_re]
  have : 0 ≤ (c * star c).re := by
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]; exact Complex.normSq_nonneg _
  linarith

/- English proof (translation)
Use `show (PI.UnitaryGroupMassFormula.GsFr.Phi k r z z' g * PpG z z' g) *ᵥ v = _`. Rewrite using `[← Matrix.mulVec_mulVec]`.
-/
lemma embedding_mul_vec_factorization (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    ioG z z' g *ᵥ v = Phi k r z z' g *ᵥ (PpG z z' g *ᵥ v) := by
  show (PI.UnitaryGroupMassFormula.GsFr.Phi k r z z' g * PpG z z' g) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]

/- English proof (translation)
Use polynomial arithmetic with `[sq_nonneg (x - 1)]`.
-/
lemma sq_bound {x C : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) (h : x ^ 2 ≤ C) : x ≤ C + 1 := by
  nlinarith [sq_nonneg (x - 1)]

end S5

open S5 in
/- English proof (translation)
Introduce `k r z z' hk hz hz'`. Take `⟨C1, hC1, hW⟩` from `W_bound hz`. Take `⟨C2, hC2, hW'⟩` from `W_bound hz'`. Use `set M := ∑ j : Fin (2 * r + k + 1), |(herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1)) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re| with hM`. Establish `hM0 : 0 ≤ M` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`.

Establish `hν : ∀ g, ‖nuG z z' g‖ ≤ C1 + 1`. Introduce `g`. Establish `hu` using `unitH_facts hz (prW_mem hz (xcof k r z z' g))`. Establish `h1` using `hW _ hu.1.1 hu.1.2`. Use `sq_bound (norm_nonneg _) hC1 (h1.trans ?_)` and prove the remaining obligations.

Use `mul_le_mul_of_nonneg_left hu.2 hC1` as an intermediate fact. Simplify `this` using `[nuG, omW]`. Establish `hν' : ∀ g, ‖nuG' z z' g‖ ≤ C2 + 1`. Introduce `g`. Establish `hu` using `unitH_facts hz' (prW_mem hz' (g⁻¹ *ᵥ xcofL k r z z' g))`.

Establish `h1` using `hW' _ hu.1.1 hu.1.2`. Use `sq_bound (norm_nonneg _) hC2 (h1.trans ?_)` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left hu.2 hC2` as an intermediate fact. Simplify `this` using `[nuG', omW']`. Use `⟨(C1 + 1) + (C2 + 1) + (C1 * M + 1), fun g hg => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations.

Use `hν g` as an intermediate fact. Use `mul_nonneg hC1 hM0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `hν' g` as an intermediate fact. Use `mul_nonneg hC1 hM0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hCM` using `mul_nonneg hC1 hM0`. Establish `hC : 0 ≤ (C1 + 1) + (C2 + 1) + (C1 * M + 1)` using `by linarith`. Rewrite using `[Matrix.norm_le_iff hC]`. Introduce `i j`.

Establish `hd` using `det_ne_of_G hz hz' hg.2`. Take `⟨huW, huo, hle⟩` from `Pp_facts (z := z) hz' g (Pi.single j 1)`. Establish `hiso` using `phi_iso' hz hg.1 hd huW huo`. Use `set q := Phi k r z z' g *ᵥ (PpG z z' g *ᵥ Pi.single j 1) with hq`. Establish `hqW : q ∈ Wsp k r z` using `by rw [hq, Phi_mulVec]; exact prW_mem hz _`.

Establish `h1` using `hW q hqW.1 hqW.2`. Rewrite `h1` using `[hiso]`. Establish `hpM : (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1)) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re ≤ M` using `(le_abs_self _).trans (Finset.single_le_sum (f := fun j : Fin (2 * r + k + 1) => |(herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1)) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))`. Establish `h2 : ‖q‖ ^ 2 ≤ C1 * M` using `h1.trans (mul_le_mul_of_nonneg_left (hle.trans hpM) hC1)`. Establish `h3` using `sq_bound (norm_nonneg q) hCM h2`.

Establish `e : ioG z z' g i j = q i`. Rewrite using `[hq, ← embedding_mul_vec_factorization]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Use `norm_le_pi_norm q i` as an intermediate fact.

Use `hν g` as an intermediate fact. Use `hν' g` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem geometry_boundedness_at_zero : GeomBd0 := by
  intro k r z z' hk hz hz'
  obtain ⟨C1, hC1, hW⟩ := W_bound hz
  obtain ⟨C2, hC2, hW'⟩ := W_bound hz'
  set M := ∑ j : Fin (2 * r + k + 1),
    |(herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1)) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re|
    with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hν : ∀ g, ‖nuG z z' g‖ ≤ C1 + 1 := by
    intro g
    have hu := unitH_facts hz (prW_mem hz (xcof k r z z' g))
    have h1 := hW _ hu.1.1 hu.1.2
    refine sq_bound (norm_nonneg _) hC1 (h1.trans ?_)
    have := mul_le_mul_of_nonneg_left hu.2 hC1
    simpa [nuG, omW] using this
  have hν' : ∀ g, ‖nuG' z z' g‖ ≤ C2 + 1 := by
    intro g
    have hu := unitH_facts hz' (prW_mem hz' (g⁻¹ *ᵥ xcofL k r z z' g))
    have h1 := hW' _ hu.1.1 hu.1.2
    refine sq_bound (norm_nonneg _) hC2 (h1.trans ?_)
    have := mul_le_mul_of_nonneg_left hu.2 hC2
    simpa [nuG', omW'] using this
  refine ⟨(C1 + 1) + (C2 + 1) + (C1 * M + 1), fun g hg => ⟨?_, ?_, ?_⟩⟩
  · have := hν g; have := mul_nonneg hC1 hM0; linarith
  · have := hν' g; have := mul_nonneg hC1 hM0; linarith
  · have hCM := mul_nonneg hC1 hM0
    have hC : 0 ≤ (C1 + 1) + (C2 + 1) + (C1 * M + 1) := by linarith
    rw [Matrix.norm_le_iff hC]
    intro i j
    have hd := det_ne_of_G hz hz' hg.2
    obtain ⟨huW, huo, hle⟩ := Pp_facts (z := z) hz' g (Pi.single j 1)
    have hiso := phi_iso' hz hg.1 hd huW huo
    set q := Phi k r z z' g *ᵥ (PpG z z' g *ᵥ Pi.single j 1) with hq
    have hqW : q ∈ Wsp k r z := by rw [hq, Phi_mulVec]; exact prW_mem hz _
    have h1 := hW q hqW.1 hqW.2
    rw [hiso] at h1
    have hpM : (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))
        (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re ≤ M :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun j : Fin (2 * r + k + 1) =>
        |(herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))
          (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
    have h2 : ‖q‖ ^ 2 ≤ C1 * M := h1.trans (mul_le_mul_of_nonneg_left (hle.trans hpM) hC1)
    have h3 := sq_bound (norm_nonneg q) hCM h2
    have e : ioG z z' g i j = q i := by
      rw [hq, ← embedding_mul_vec_factorization]
      simp
    rw [e]
    have := norm_le_pi_norm q i
    have := hν g
    have := hν' g
    linarith

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
