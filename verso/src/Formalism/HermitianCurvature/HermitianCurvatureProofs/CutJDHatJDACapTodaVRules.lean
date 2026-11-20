import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrpCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx3 Formalism.FourierDecayAlt.P.WeylCellAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section diff

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `hv : ∀ w : ℂ, fderiv ℝ F₁ c (Pi.single l w) = fderiv ℝ F₂ c (Pi.single l w)` using `fun w => fderiv_line h₁ h₂ fun t => h _ fun a ha => by simp [ha]`. Simplify using `only [pbOp, wirtBar, hv]`.
-/
theorem pbOp_line {F₁ F₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (l : Fin r) (h₁ : DifferentiableAt ℝ F₁ c)
    (h₂ : DifferentiableAt ℝ F₂ c) (h : ∀ c' : Fin r → ℂ, (∀ a, a ≠ l → c' a = c a) → F₁ c' = F₂ c') :
    pbOp l F₁ c = pbOp l F₂ c := by
  have hv : ∀ w : ℂ, fderiv ℝ F₁ c (Pi.single l w) = fderiv ℝ F₂ c (Pi.single l w) := fun w =>
    fderiv_line h₁ h₂ fun t => h _ fun a ha => by simp [ha]
  simp only [pbOp, wirtBar, hv]

end diff

/- English proof (translation)
Introduce `E _ _ k r z' D f hz' hD hS hR g hg a b hab`. Establish `ha` using `a.isLt`. Establish `hc : Continuous fun x : Mx k r => g * x` using `cont_lmul g`. Establish `hD' : IsOpen {x : Mx k r | g * x ∈ D}` using `hD.preimage hc`. Establish `hS' : SmoothLev k r b.castSucc {x | g * x ∈ D} (fun x => f (g * x))` using `smooth_left g (fun x hx => glev0 hg.1 hx) hS`.

Establish `hR' : RightEq k r z' b.castSucc {x | g * x ∈ D} (fun x => f (g * x))`. Introduce `x hx n hn`. Use `hR (g * x) ⟨glev0 hg.1 hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)` as an intermediate fact. Simplify `this` using `[Matrix.mul_assoc]`. Establish `h1 : (1 : Mx k r) ∈ Glev k r b.castSucc ∩ {x | g * x ∈ D}` using `⟨glev_one _, by simpa using hg.2⟩`.

Establish `hrule` using `(Formalism.FourierDecayAlt.P.right_action_rule E k r z' b {x | g * x ∈ D} (fun x => f (g * x)) hz' hD' hS' hR' 1 h1).2.1`. Establish `hjlt : 2 * r + k - a.val - b.val - 1 < mdim k r b.succ` using `by simp [mdim]; omega`. Establish `hpos : posL k r b.succ ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ = esI k r a`. Simplify using `[posL, esI, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.

Establish `h` using `hrule ⟨2 * r + k - a.val - b.val - 1, hjlt⟩`. Rewrite `h` using `[hpos, eH_left, Matrix.mul_one]`. Rewrite using `[h]`. Use `congr 1`. Simplify using `only [xbv, fvec, hpos, Fin.val_succ]`.

Rewrite using `[dif_pos (show b.val + 1 < r by omega)]`. Rewrite using `[Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI]`. Distinguish the cases in `hh : a.val = b.val + 1`. Simplify using `[hh, bvec, esI]`. Rewrite using `[if_neg hh]`.

Simplify using `only [bvec, Pi.single_apply, esI, Fin.ext_iff]`. Rewrite using `[if_neg (by omega)]`.
-/
theorem mirror_right_rule_holds : RightRuleEv := by
  intro E _ _ k r z' D f hz' hD hS hR g hg a b hab
  have ha := a.isLt
  have hc : Continuous fun x : Mx k r => g * x := cont_lmul g
  have hD' : IsOpen {x : Mx k r | g * x ∈ D} := hD.preimage hc
  have hS' : SmoothLev k r b.castSucc {x | g * x ∈ D} (fun x => f (g * x)) :=
    smooth_left g (fun x hx => glev0 hg.1 hx) hS
  have hR' : RightEq k r z' b.castSucc {x | g * x ∈ D} (fun x => f (g * x)) := by
    intro x hx n hn
    have := hR (g * x) ⟨glev0 hg.1 hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
    simpa [Matrix.mul_assoc] using this
  have h1 : (1 : Mx k r) ∈ Glev k r b.castSucc ∩ {x | g * x ∈ D} :=
    ⟨glev_one _, by simpa using hg.2⟩
  have hrule := (Formalism.FourierDecayAlt.P.right_action_rule E k r z' b {x | g * x ∈ D} (fun x => f (g * x)) hz' hD' hS' hR'
    1 h1).2.1
  have hjlt : 2 * r + k - a.val - b.val - 1 < mdim k r b.succ := by simp [mdim]; omega
  have hpos : posL k r b.succ ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ = esI k r a := by
    simp [posL, esI, Fin.ext_iff]; omega
  have h := hrule ⟨2 * r + k - a.val - b.val - 1, hjlt⟩
  rw [hpos, eH_left, Matrix.mul_one] at h
  rw [h]
  congr 1
  simp only [xbv, fvec, hpos, Fin.val_succ]
  rw [dif_pos (show b.val + 1 < r by omega)]
  rw [Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI]
  by_cases hh : a.val = b.val + 1
  · simp [hh, bvec, esI]
  · rw [if_neg hh]
    simp only [bvec, Pi.single_apply, esI, Fin.ext_iff]
    rw [if_neg (by omega)]

/- English proof (translation)
Introduce `E _ _ k r D f hD hS c hc g hg hWD l`. Establish `hcne : ∀ a, c a ≠ 0` using `hc`. Establish `hl` using `l.isLt`. Take `⟨hW0, -⟩` from `head_comm (k := k) c hcne l.val l.castSucc (by simp)`. Take `⟨T, hT, hTG, -, -, hTc⟩` from `tail (k := k) c hcne l (r - l.val - 1) (Fin.last r) (by simp; omega)`.

Establish `hg₁ : T * g ∈ Glev k r l.succ` using `glev_mul hTG (glev_mono (Fin.le_last _) hg)`. Establish `hsplit : wCell k r (Fin.last r) c * g = wCell k r l.castSucc c * (w1 k r l (c l) * (T * g))`. Simplify using `only [hT, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, Matrix.mul_assoc]`. Establish `hWx : ∀ x ∈ Glev k r l.castSucc, wCell k r l.castSucc c * x ∈ Glev k r 0` using `fun x hx => glev0 hW0 hx`. Establish `hS'` using `smooth_left (E := E) (f := f) (D := D) (wCell k r l.castSucc c) hWx hS`.

Establish `hD' : IsOpen {x : Mx k r | wCell k r l.castSucc c * x ∈ D}` using `hD.preimage (cont_lmul _)`. Establish `hpt : w1 k r l (c l) * (T * g) ∈ {x | wCell k r l.castSucc c * x ∈ D}` using `by show _ ∈ D`. Rewrite using `[← hsplit]`. Conclude with `hWD`. Establish `hrule` using `(Formalism.FourierDecayAlt.P.torus_action_rule E k r l {x | wCell k r l.castSucc c * x ∈ D} (fun x => f (wCell k r l.castSucc c * x)) hD' hS' c hc (T * g) hg₁ hpt).2`.

Rewrite `hrule` using `[eH_left, ← hsplit]`. Rewrite using `[hrule]`. Establish `hG : ∀ c' ∈ OmX r, wCell k r (Fin.last r) c' ∈ Glev k r 0` using `fun c' hc' => (head_comm (k := k) c' hc' r (Fin.last r) (by simp)).1`. Establish `hd₂ : DifferentiableAt ℝ (fun c' => f (wCell k r (Fin.last r) c' * g)) c`. Use `diff_comp hS (φ := fun c' => wCell k r (Fin.last r) c' * g) (Formalism.FourierDecayAlt.P.Qx6.cd_matmul (cd_wCell r (Fin.last r) (by simp)) contDiffOn_const) (fun c' hc' => glev_mul (hG c' hc') (glev_mono (zero_le' _) hg)) hc hWD` and prove the remaining obligations.

Establish `hd₁ : DifferentiableAt ℝ (fun c' => f (wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g)))) c`. Use `diff_comp hS (φ := fun c' => wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g))) (Formalism.FourierDecayAlt.P.Qx6.cd_matmul contDiffOn_const (Formalism.FourierDecayAlt.P.Qx6.cd_matmul (Formalism.FourierDecayAlt.P.Qx6.contDiffOn_weyl_cell l) contDiffOn_const)) (fun c' hc' => ?_) …` and prove the remaining obligations. Use `glev_mul hW0 (glev_mul (glev_mono (zero_le' _) (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r l (c' l) (hc' l)).1) (glev_mono (zero_le' _) hg₁))` and prove the remaining obligations. Rewrite using `[← hsplit]`. Conclude with `hWD`.

Use `congr 1`. Use `pbOp_line l hd₁ hd₂ fun c' hc' => ?_` and prove the remaining obligations. Establish `hlow : wCell k r l.castSucc c' = wCell k r l.castSucc c` using `Formalism.FourierDecayAlt.P.Qx6.wCell_congr fun a ha => hc' a (fun h => by subst h; simp at ha)`. Establish `hup` using `hTc c' fun a ha => hc' a (fun h => by subst h; omega)`. Use `show f (wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g))) = f (wCell k r (Fin.last r) c' * g)`.

Rewrite using `[hup, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hlow, Matrix.mul_assoc, Matrix.mul_assoc]`.
-/
theorem mirror_torus_cell_holds : TorusCellv := by
  intro E _ _ k r D f hD hS c hc g hg hWD l
  have hcne : ∀ a, c a ≠ 0 := hc
  have hl := l.isLt
  obtain ⟨hW0, -⟩ := head_comm (k := k) c hcne l.val l.castSucc (by simp)
  obtain ⟨T, hT, hTG, -, -, hTc⟩ := tail (k := k) c hcne l (r - l.val - 1) (Fin.last r) (by simp; omega)
  have hg₁ : T * g ∈ Glev k r l.succ := glev_mul hTG (glev_mono (Fin.le_last _) hg)
  have hsplit : wCell k r (Fin.last r) c * g = wCell k r l.castSucc c * (w1 k r l (c l) * (T * g)) := by
    simp only [hT, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, Matrix.mul_assoc]
  have hWx : ∀ x ∈ Glev k r l.castSucc, wCell k r l.castSucc c * x ∈ Glev k r 0 := fun x hx => glev0 hW0 hx
  have hS' := smooth_left (E := E) (f := f) (D := D) (wCell k r l.castSucc c) hWx hS
  have hD' : IsOpen {x : Mx k r | wCell k r l.castSucc c * x ∈ D} := hD.preimage (cont_lmul _)
  have hpt : w1 k r l (c l) * (T * g) ∈ {x | wCell k r l.castSucc c * x ∈ D} := by
    show _ ∈ D
    rw [← hsplit]; exact hWD
  have hrule := (Formalism.FourierDecayAlt.P.torus_action_rule E k r l {x | wCell k r l.castSucc c * x ∈ D}
    (fun x => f (wCell k r l.castSucc c * x)) hD' hS' c hc (T * g) hg₁ hpt).2
  rw [eH_left, ← hsplit] at hrule
  rw [hrule]
  have hG : ∀ c' ∈ OmX r, wCell k r (Fin.last r) c' ∈ Glev k r 0 := fun c' hc' =>
    (head_comm (k := k) c' hc' r (Fin.last r) (by simp)).1
  have hd₂ : DifferentiableAt ℝ (fun c' => f (wCell k r (Fin.last r) c' * g)) c := by
    refine diff_comp hS (φ := fun c' => wCell k r (Fin.last r) c' * g)
      (Formalism.FourierDecayAlt.P.Qx6.cd_matmul (cd_wCell r (Fin.last r) (by simp)) contDiffOn_const)
      (fun c' hc' => glev_mul (hG c' hc') (glev_mono (zero_le' _) hg)) hc hWD
  have hd₁ : DifferentiableAt ℝ (fun c' => f (wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g)))) c := by
    refine diff_comp hS (φ := fun c' => wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g)))
      (Formalism.FourierDecayAlt.P.Qx6.cd_matmul contDiffOn_const
        (Formalism.FourierDecayAlt.P.Qx6.cd_matmul (Formalism.FourierDecayAlt.P.Qx6.contDiffOn_weyl_cell l) contDiffOn_const)) (fun c' hc' => ?_) hc ?_
    · refine glev_mul hW0 (glev_mul (glev_mono (zero_le' _) (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r l (c' l) (hc' l)).1)
        (glev_mono (zero_le' _) hg₁))
    · rw [← hsplit]; exact hWD
  congr 1
  refine pbOp_line l hd₁ hd₂ fun c' hc' => ?_
  have hlow : wCell k r l.castSucc c' = wCell k r l.castSucc c :=
    Formalism.FourierDecayAlt.P.Qx6.wCell_congr fun a ha => hc' a (fun h => by subst h; simp at ha)
  have hup := hTc c' fun a ha => hc' a (fun h => by subst h; omega)
  show f (wCell k r l.castSucc c * (w1 k r l (c' l) * (T * g))) = f (wCell k r (Fin.last r) c' * g)
  rw [hup, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hlow, Matrix.mul_assoc, Matrix.mul_assoc]

/- English proof (translation)
Unfold `herm`. Rewrite using `[star_smul, smul_dotProduct, smul_eq_mul]`.
-/
theorem herm_smul_right' {k r : ℕ} (v w : Fin (2 * r + k + 1) → ℂ) (s : ℂ) :
    herm (Hpk k r) v (s • w) = star s * herm (Hpk k r) v w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Introduce `E _ _ k r z D f hz hD hDN hS hL c hc g hg hWD a b hba`. Establish `ha` using `a.isLt`. Establish `hcne : ∀ l, c l ≠ 0` using `hc`. Take `⟨hW0, hWcomm⟩` from `head_comm (k := k) c hcne b.val b.castSucc (by simp)`. Take `⟨T, hT, hTG, hTe, -, -⟩` from `tail (k := k) c hcne b (r - b.val - 1) (Fin.last r) (by simp; omega)`.

Establish `hg₁ : T * g ∈ Glev k r b.succ` using `glev_mul hTG (glev_mono (Fin.le_last _) hg)`. Establish `hsplit : wCell k r (Fin.last r) c * g = wCell k r b.castSucc c * (w1 k r b (c b) * (T * g))`. Simplify using `only [hT, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, Matrix.mul_assoc]`. Establish `hWx : ∀ x ∈ Glev k r b.castSucc, wCell k r b.castSucc c * x ∈ Glev k r 0` using `fun x hx => glev0 hW0 hx`. Establish `hS'` using `smooth_left (E := E) (f := f) (D := D) (wCell k r b.castSucc c) hWx hS`.

Establish `hcont : Continuous fun x : Mx k r => wCell k r b.castSucc c * x` using `cont_lmul _`. Establish `hD' : IsOpen {x : Mx k r | wCell k r b.castSucc c * x ∈ D}` using `hD.preimage hcont`. Establish `hN' : ∀ x ∈ Glev k r b.castSucc ∩ {x | wCell k r b.castSucc c * x ∈ D}, ∀ n ∈ Nlev k r b.castSucc, n * x ∈ {x | wCell k r b.castSucc c * x ∈ D}`. Introduce `x hx n hn`. Use `show wCell k r b.castSucc c * (n * x) ∈ D`.

Rewrite using `[← Matrix.mul_assoc, hWcomm b.castSucc le_rfl n hn.2, Matrix.mul_assoc]`. Conclude with `hDN _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)`. Establish `hL' : LeftEq k r z b.castSucc {x | wCell k r b.castSucc c * x ∈ D} (fun x => f (wCell k r b.castSucc c * x))`. Introduce `x hx n hn`. Use `show f (wCell k r b.castSucc c * (n * x)) = _ • f (wCell k r b.castSucc c * x)`.

Rewrite using `[← Matrix.mul_assoc, hWcomm b.castSucc le_rfl n hn.2, Matrix.mul_assoc]`. Conclude with `hL _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)`. Establish `hpt : w1 k r b (c b) * (T * g) ∈ {x | wCell k r b.castSucc c * x ∈ D}` using `by show _ ∈ D`. Rewrite using `[← hsplit]`. Conclude with `hWD`.

Establish `hrule` using `(Formalism.FourierDecayAlt.P.left_action_rule E k r z b {x | wCell k r b.castSucc c * x ∈ D} (fun x => f (wCell k r b.castSucc c * x)) hz hD' hS' hN' hL' (c b) (hcne b) (T * g) hg₁ hpt).2.1`. Establish `hjlt : 2 * r + k - a.val - b.val - 1 < mdim k r b.succ` using `by simp [mdim]; omega`. Establish `hpos : posL k r b.succ ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ = esI k r a`. Simplify using `[posL, esI, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.

Establish `h` using `hrule ⟨2 * r + k - a.val - b.val - 1, hjlt⟩`. Rewrite `h` using `[hpos, eH_left, ← hsplit]`. Rewrite using `[h]`. Use `congr 1`. Establish `hb1 : (b.succ : Fin (r + 1)).val < r` using `by simp; omega`.

Establish `hga : g *ᵥ bvec (eI k r a) = bvec (eI k r a)` using `(hg.2 a (by simp)).1`. Establish `hTa` using `hTe a hba`. Rewrite `hTa` using `[if_pos (by simp)]`. Establish `hU : T * g ∈ UH (Hpk k r)` using `hg₁.1`. Establish `key : ((T * g)⁻¹ *ᵥ bvec (eI k r ⟨b.val + 1, by omega⟩)) (esI k r a) = if a.val = b.val + 1 then star (c a) else 0`.

Rewrite using `[← Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI ((T * g)⁻¹ *ᵥ bvec (eI k r ⟨b.val + 1, by omega⟩)) a, ← Formalism.FourierDecayAlt.P.Qx2.herm_uh hU, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hU), Matrix.o …`. Distinguish the cases in `hh : a.val = b.val + 1`. Rewrite using `[if_pos hh]`. Establish `: (bvec (esI k r a) : Fin (2 * r + k + 1) → ℂ) (esI k r ⟨b.val + 1, by omega⟩) = 1`. Simplify using `[bvec, esI, hh]`.

Rewrite using `[this, star_one, mul_one]`. Rewrite using `[if_neg hh]`. Establish `: (bvec (esI k r a) : Fin (2 * r + k + 1) → ℂ) (esI k r ⟨b.val + 1, by omega⟩) = 0`. Simplify using `only [bvec, Pi.single_apply, esI, Fin.ext_iff]`. Rewrite using `[if_neg (by omega)]`.

Rewrite using `[this, star_zero, mul_zero]`. Establish `hy : yv k r z b.succ (T * g) ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ = if a.val = b.val + 1 then star (c a) else 0`. Simplify using `only [yv, hpos, fvec, dif_pos hb1]`. Conclude with `key`. Rewrite using `[hy]`.

Distinguish the cases in `hh : a.val = b.val + 1`. Rewrite using `[if_pos hh, if_pos hh, div_eq_inv_mul]`. Rewrite using `[if_neg hh, if_neg hh, mul_zero]`.
-/
theorem mirror_left_rule_cell_holds : LeftRuleCellv := by
  intro E _ _ k r z D f hz hD hDN hS hL c hc g hg hWD a b hba
  have ha := a.isLt
  have hcne : ∀ l, c l ≠ 0 := hc
  obtain ⟨hW0, hWcomm⟩ := head_comm (k := k) c hcne b.val b.castSucc (by simp)
  obtain ⟨T, hT, hTG, hTe, -, -⟩ := tail (k := k) c hcne b (r - b.val - 1) (Fin.last r) (by simp; omega)
  have hg₁ : T * g ∈ Glev k r b.succ := glev_mul hTG (glev_mono (Fin.le_last _) hg)
  have hsplit : wCell k r (Fin.last r) c * g = wCell k r b.castSucc c * (w1 k r b (c b) * (T * g)) := by
    simp only [hT, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, Matrix.mul_assoc]
  have hWx : ∀ x ∈ Glev k r b.castSucc, wCell k r b.castSucc c * x ∈ Glev k r 0 := fun x hx => glev0 hW0 hx
  have hS' := smooth_left (E := E) (f := f) (D := D) (wCell k r b.castSucc c) hWx hS
  have hcont : Continuous fun x : Mx k r => wCell k r b.castSucc c * x := cont_lmul _
  have hD' : IsOpen {x : Mx k r | wCell k r b.castSucc c * x ∈ D} := hD.preimage hcont
  have hN' : ∀ x ∈ Glev k r b.castSucc ∩ {x | wCell k r b.castSucc c * x ∈ D}, ∀ n ∈ Nlev k r b.castSucc,
      n * x ∈ {x | wCell k r b.castSucc c * x ∈ D} := by
    intro x hx n hn
    show wCell k r b.castSucc c * (n * x) ∈ D
    rw [← Matrix.mul_assoc, hWcomm b.castSucc le_rfl n hn.2, Matrix.mul_assoc]
    exact hDN _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
  have hL' : LeftEq k r z b.castSucc {x | wCell k r b.castSucc c * x ∈ D} (fun x => f (wCell k r b.castSucc c * x)) := by
    intro x hx n hn
    show f (wCell k r b.castSucc c * (n * x)) = _ • f (wCell k r b.castSucc c * x)
    rw [← Matrix.mul_assoc, hWcomm b.castSucc le_rfl n hn.2, Matrix.mul_assoc]
    exact hL _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
  have hpt : w1 k r b (c b) * (T * g) ∈ {x | wCell k r b.castSucc c * x ∈ D} := by
    show _ ∈ D
    rw [← hsplit]; exact hWD
  have hrule := (Formalism.FourierDecayAlt.P.left_action_rule E k r z b {x | wCell k r b.castSucc c * x ∈ D}
    (fun x => f (wCell k r b.castSucc c * x)) hz hD' hS' hN' hL' (c b) (hcne b) (T * g) hg₁ hpt).2.1
  have hjlt : 2 * r + k - a.val - b.val - 1 < mdim k r b.succ := by simp [mdim]; omega
  have hpos : posL k r b.succ ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ = esI k r a := by
    simp [posL, esI, Fin.ext_iff]; omega
  have h := hrule ⟨2 * r + k - a.val - b.val - 1, hjlt⟩
  rw [hpos, eH_left, ← hsplit] at h
  rw [h]
  congr 1
  have hb1 : (b.succ : Fin (r + 1)).val < r := by simp; omega
  have hga : g *ᵥ bvec (eI k r a) = bvec (eI k r a) := (hg.2 a (by simp)).1
  have hTa := hTe a hba
  rw [if_pos (by simp)] at hTa
  have hU : T * g ∈ UH (Hpk k r) := hg₁.1
  have key : ((T * g)⁻¹ *ᵥ bvec (eI k r ⟨b.val + 1, by omega⟩)) (esI k r a) =
      if a.val = b.val + 1 then star (c a) else 0 := by
    rw [← Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI ((T * g)⁻¹ *ᵥ bvec (eI k r ⟨b.val + 1, by omega⟩)) a,
      ← Formalism.FourierDecayAlt.P.Qx2.herm_uh hU, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hU), Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hga, hTa,
      herm_smul_right', ← Formalism.FourierDecayAlt.P.Qx2.herm_star, Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI]
    by_cases hh : a.val = b.val + 1
    · rw [if_pos hh]
      have : (bvec (esI k r a) : Fin (2 * r + k + 1) → ℂ) (esI k r ⟨b.val + 1, by omega⟩) = 1 := by
        simp [bvec, esI, hh]
      rw [this, star_one, mul_one]
    · rw [if_neg hh]
      have : (bvec (esI k r a) : Fin (2 * r + k + 1) → ℂ) (esI k r ⟨b.val + 1, by omega⟩) = 0 := by
        simp only [bvec, Pi.single_apply, esI, Fin.ext_iff]
        rw [if_neg (by omega)]
      rw [this, star_zero, mul_zero]
  have hy : yv k r z b.succ (T * g) ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ =
      if a.val = b.val + 1 then star (c a) else 0 := by
    simp only [yv, hpos, fvec, dif_pos hb1]
    exact key
  rw [hy]
  by_cases hh : a.val = b.val + 1
  · rw [if_pos hh, if_pos hh, div_eq_inv_mul]
  · rw [if_neg hh, if_neg hh, mul_zero]

end Formalism.FourierDecayAlt.P.CutMP.TVG
