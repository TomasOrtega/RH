import Formalism.HermitianCurvature.ActualZetaSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelLevelMultiplier

section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.NFx4

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section MulZ

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Use function extensionality and compare the values at `c g`. Simplify using `only [mulZ]`. Distinguish the cases in `hx : (c, g) ∈ DomR k r z z'`. Rewrite using `[Set.indicator_of_mem hx]`. Rewrite using `[Set.indicator_of_notMem hx, hΦ.1 (c, g) hx, smul_zero]`.
-/
theorem mulZ_eq (f : ℂ → ℂ) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    mulZ k r z z' f Φ = fun c g => f (zetaL k r z z' (Fin.last r) g) • Φ c g := by
  funext c g
  simp only [mulZ]
  by_cases hx : (c, g) ∈ DomR k r z z'
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hΦ.1 (c, g) hx, smul_zero]

/- English proof (translation)
Rewrite using `[mulZ_eq f hΦ]`. Use `Qx5.smul_mem (a := fun x => f (zetaL k r z z' (Fin.last r) x.2)) ?_ (fun x _ h hh h' hh' => by simp only [Qx5.zeta_inv hh hh']) hΦ` and prove the remaining obligations. Use `hf.comp ((Qx5.zetaL_contDiff k r z z' (Fin.last r)).comp contDiff_snd).contDiffOn ?_` and prove the remaining obligations. Introduce `x hx`. Establish `h2 : 0 < GGl k r z z' x.2` using `hx.2`.

Unfold `GGl at h2`. Use `show Tz k r z * Tz k r z' < Complex.normSq (zetaL k r z z' (Fin.last r) x.2)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mulZ_mem {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ})
    {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') : mulZ k r z z' f Φ ∈ RadSp k r z z' π π' := by
  rw [mulZ_eq f hΦ]
  refine Qx5.smul_mem (a := fun x => f (zetaL k r z z' (Fin.last r) x.2)) ?_
    (fun x _ h hh h' hh' => by simp only [Qx5.zeta_inv hh hh']) hΦ
  refine hf.comp ((Qx5.zetaL_contDiff k r z z' (Fin.last r)).comp contDiff_snd).contDiffOn ?_
  intro x hx
  have h2 : 0 < GGl k r z z' x.2 := hx.2
  unfold GGl at h2
  show Tz k r z * Tz k r z' < Complex.normSq (zetaL k r z z' (Fin.last r) x.2)
  linarith

/- English proof (translation)
Use function extensionality and compare the values at `c g`. Simplify using `only [mulZ, Pi.add_apply, Pi.smul_apply]`. Distinguish the cases in `hx : (c, g) ∈ DomR k r z z'`. Simplify using `only [Set.indicator_of_mem hx, Pi.add_apply, Pi.smul_apply, smul_add]`. Rewrite using `[smul_comm]`.

Simplify using `[Set.indicator_of_notMem hx]`.
-/
theorem mulZ_lin (f : ℂ → ℂ) (Φ Ψ : Fn k r (Wq →L[ℂ] Wp)) (s : ℂ) :
    mulZ k r z z' f (Φ + s • Ψ) = mulZ k r z z' f Φ + s • mulZ k r z z' f Ψ := by
  funext c g
  simp only [mulZ, Pi.add_apply, Pi.smul_apply]
  by_cases hx : (c, g) ∈ DomR k r z z'
  · simp only [Set.indicator_of_mem hx, Pi.add_apply, Pi.smul_apply, smul_add]
    rw [smul_comm]
  · simp [Set.indicator_of_notMem hx]

def mulZEnd {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ}) :
    Module.End ℂ (RadSp k r z z' π π') :=
  Qx5.mkEnd _ (mulZ k r z z' f) (fun _ h => mulZ_mem hf h) (fun x _ y _ s => mulZ_lin f x y s)

/- English proof (translation)
Introduce `_` and use `rfl`.
-/
theorem isMulZ_mulZEnd {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ}) :
    IsMulZ (mulZEnd (π := π) (π' := π') hf) f := fun _ => rfl

end MulZ

/- English proof (translation)
Take `⟨-, -, -, h1, h2, -, -⟩` from `h`. Rewrite using `[h1, h2]`. Both sides reduce to the same expression.
-/
theorem TT_eq {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
    {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} (h : IsPlace P z z' π π') : Tz P.k P.r z * Tz P.k P.r z' = P.TT := by
  obtain ⟨-, -, -, h1, h2, -, -⟩ := h
  rw [h1, h2]
  rfl

section Wirt

variable {U : Set ℂ}

/- English proof (translation)
Introduce `w hw`. Establish `e : fderiv ℝ f w = fderiv ℝ g w` using `Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hw) h)`. Simplify using `only [dZ, e]`.
-/
theorem dZ_congr {f g : ℂ → ℂ} (hU : IsOpen U) (h : Set.EqOn f g U) : Set.EqOn (dZ f) (dZ g) U := by
  intro w hw
  have e : fderiv ℝ f w = fderiv ℝ g w :=
    Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hw) h)
  simp only [dZ, e]

/- English proof (translation)
Introduce `w hw`. Establish `e : fderiv ℝ f w = fderiv ℝ g w` using `Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hw) h)`. Simplify using `only [dZb, e]`.
-/
theorem dZb_congr {f g : ℂ → ℂ} (hU : IsOpen U) (h : Set.EqOn f g U) : Set.EqOn (dZb f) (dZb g) U := by
  intro w hw
  have e : fderiv ℝ f w = fderiv ℝ g w :=
    Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hw) h)
  simp only [dZb, e]

/- English proof (translation)
Conclude with `le_top` after adjusting the coercions.
-/
theorem inf_ge (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

/- English proof (translation)
The claim follows from `(hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const`.
-/
theorem contDiffOn_fderiv_apply {f : ℂ → ℂ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (v : ℂ) :
    ContDiffOn ℝ ∞ (fun w => fderiv ℝ f w v) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

/- English proof (translation)
Unfold `dZ`. Conclude with `contDiffOn_const.mul ((contDiffOn_fderiv_apply hU hf 1).sub (contDiffOn_const.mul (contDiffOn_fderiv_apply hU hf Complex.I)))`.
-/
theorem contDiffOn_dZ {f : ℂ → ℂ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (dZ f) U := by
  unfold dZ
  exact contDiffOn_const.mul ((contDiffOn_fderiv_apply hU hf 1).sub
    (contDiffOn_const.mul (contDiffOn_fderiv_apply hU hf Complex.I)))

/- English proof (translation)
Unfold `dZb`. Conclude with `contDiffOn_const.mul ((contDiffOn_fderiv_apply hU hf 1).add (contDiffOn_const.mul (contDiffOn_fderiv_apply hU hf Complex.I)))`.
-/
theorem contDiffOn_dZb {f : ℂ → ℂ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (dZb f) U := by
  unfold dZb
  exact contDiffOn_const.mul ((contDiffOn_fderiv_apply hU hf 1).add
    (contDiffOn_const.mul (contDiffOn_fderiv_apply hU hf Complex.I)))

/- English proof (translation)
Establish `hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Establish `hs : star v = (v.re : ℂ) - (v.im : ℂ) * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Establish `hv2 : v = (v.re : ℂ) + (v.im : ℂ) * Complex.I`.

Apply the tactic sequence `apply Complex.ext <;> simp`. Establish `e : dZ f w * v + dZb f w * star v = dZ f w * ((v.re : ℂ) + (v.im : ℂ) * Complex.I) + dZb f w * ((v.re : ℂ) - (v.im : ℂ) * Complex.I)`. Rewrite using `[← hv2, ← hs]`. Rewrite using `[e]`. Use `conv_lhs => rw [hv]`.

Rewrite using `[map_add, map_smul, map_smul]`. Simplify using `only [dZ, dZb, Complex.real_smul]`. Establish `hI : Complex.I * Complex.I = -1` using `Complex.I_mul_I`. Take the linear combination `((v.im : ℂ) * fderiv ℝ f w Complex.I) * hI`.
-/
theorem fderiv_wirt (f : ℂ → ℂ) (w v : ℂ) :
    fderiv ℝ f w v = dZ f w * v + dZb f w * star v := by
  have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have hs : star v = (v.re : ℂ) - (v.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hv2 : v = (v.re : ℂ) + (v.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have e : dZ f w * v + dZb f w * star v =
      dZ f w * ((v.re : ℂ) + (v.im : ℂ) * Complex.I) + dZb f w * ((v.re : ℂ) - (v.im : ℂ) * Complex.I) := by
    rw [← hv2, ← hs]
  rw [e]
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]
  simp only [dZ, dZb, Complex.real_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination ((v.im : ℂ) * fderiv ℝ f w Complex.I) * hI

/- English proof (translation)
Establish `hfa : ContDiffAt ℝ ∞ f w` using `hf.contDiffAt (hU.mem_nhds hw)`. Establish `hsymm : IsSymmSndFDerivAt ℝ f w` using `hfa.isSymmSndFDerivAt (by simpa using inf_ge 2)`. Establish `hdf : DifferentiableAt ℝ (fderiv ℝ f) w` using `((hf.fderiv_of_isOpen (m := ∞) hU (by simp)).contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp)`. Use `set D2 := fderiv ℝ (fderiv ℝ f) w with hD2`. Establish `key : ∀ v : ℂ, HasFDerivAt (fun x => fderiv ℝ f x v) ((ContinuousLinearMap.apply ℝ ℂ v).comp D2) w` using `fun v => (ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt.comp w hdf.hasFDerivAt`.

Establish `hb : HasFDerivAt (dZb f) ((1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ 1).comp D2 + Complex.I • (ContinuousLinearMap.apply ℝ ℂ Complex.I).comp D2)) w` using `((key 1).add ((key Complex.I).const_mul Complex.I)).const_mul (1 / 2 : ℂ)`. Establish `ha : HasFDerivAt (dZ f) ((1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ 1).comp D2 - Complex.I • (ContinuousLinearMap.apply ℝ ℂ Complex.I).comp D2)) w` using `((key 1).sub ((key Complex.I).const_mul Complex.I)).const_mul (1 / 2 : ℂ)`. Establish `hs : D2 1 Complex.I = D2 Complex.I 1` using `hsymm 1 Complex.I`. Simplify using `only [dZ, dZb, hb.fderiv, ha.fderiv, _root_.smul_apply, _root_.add_apply, _root_.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]`. Rewrite using `[hs]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dZ_dZb_comm {f : ℂ → ℂ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {w : ℂ} (hw : w ∈ U) :
    dZ (dZb f) w = dZb (dZ f) w := by
  have hfa : ContDiffAt ℝ ∞ f w := hf.contDiffAt (hU.mem_nhds hw)
  have hsymm : IsSymmSndFDerivAt ℝ f w := hfa.isSymmSndFDerivAt (by simpa using inf_ge 2)
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) w :=
    ((hf.fderiv_of_isOpen (m := ∞) hU (by simp)).contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp)
  set D2 := fderiv ℝ (fderiv ℝ f) w with hD2
  have key : ∀ v : ℂ, HasFDerivAt (fun x => fderiv ℝ f x v) ((ContinuousLinearMap.apply ℝ ℂ v).comp D2) w :=
    fun v => (ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt.comp w hdf.hasFDerivAt
  have hb : HasFDerivAt (dZb f) ((1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ 1).comp D2 +
      Complex.I • (ContinuousLinearMap.apply ℝ ℂ Complex.I).comp D2)) w :=
    ((key 1).add ((key Complex.I).const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have ha : HasFDerivAt (dZ f) ((1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ 1).comp D2 -
      Complex.I • (ContinuousLinearMap.apply ℝ ℂ Complex.I).comp D2)) w :=
    ((key 1).sub ((key Complex.I).const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hs : D2 1 Complex.I = D2 Complex.I 1 := hsymm 1 Complex.I
  simp only [dZ, dZb, hb.fderiv, ha.fderiv, _root_.smul_apply, _root_.add_apply, _root_.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
  rw [hs]
  ring

def wd : List Bool → (ℂ → ℂ) → ℂ → ℂ
  | [], f => f
  | b :: w, f => if b then dZb (wd w f) else dZ (wd w f)

/- English proof (translation)
Proceed by induction on `v with`. Consider the case `nil => rfl`. Consider the case `cons b v ih => simp only [List.cons_append, wd, ih]`.
-/
theorem wd_append (v w : List Bool) (f : ℂ → ℂ) : wd (v ++ w) f = wd v (wd w f) := by
  induction v with
  | nil => rfl
  | cons b v ih => simp only [List.cons_append, wd, ih]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact hf`. Consider the case `cons b w ih`. Consider the cases of `b`. Conclude with `contDiffOn_dZ hU ih`.

Conclude with `contDiffOn_dZb hU ih`.
-/
theorem contDiffOn_wd (hU : IsOpen U) {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f U) (w : List Bool) :
    ContDiffOn ℝ ∞ (wd w f) U := by
  induction w with
  | nil => exact hf
  | cons b w ih =>
    cases b
    · exact contDiffOn_dZ hU ih
    · exact contDiffOn_dZb hU ih

def wn (j l : ℕ) (f : ℂ → ℂ) : ℂ → ℂ := dZ^[j] (dZb^[l] f)

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => exact hf`. Consider the case `succ j ih => rw [Function.iterate_succ_apply']`. Conclude with `contDiffOn_dZ hU ih`.
-/
theorem contDiffOn_iter_dZ (hU : IsOpen U) {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f U) (j : ℕ) :
    ContDiffOn ℝ ∞ (dZ^[j] f) U := by
  induction j with
  | zero => exact hf
  | succ j ih => rw [Function.iterate_succ_apply']; exact contDiffOn_dZ hU ih

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => exact hf`. Consider the case `succ j ih => rw [Function.iterate_succ_apply']`. Conclude with `contDiffOn_dZb hU ih`.
-/
theorem contDiffOn_iter_dZb (hU : IsOpen U) {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f U) (j : ℕ) :
    ContDiffOn ℝ ∞ (dZb^[j] f) U := by
  induction j with
  | zero => exact hf
  | succ j ih => rw [Function.iterate_succ_apply']; exact contDiffOn_dZb hU ih

/- English proof (translation)
The claim follows from `contDiffOn_iter_dZ hU (contDiffOn_iter_dZb hU hf l) j`.
-/
theorem contDiffOn_wn (hU : IsOpen U) {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f U) (j l : ℕ) :
    ContDiffOn ℝ ∞ (wn j l f) U :=
  contDiffOn_iter_dZ hU (contDiffOn_iter_dZb hU hf l) j

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Introduce `w _`. Simplify using `only [wn, Function.iterate_zero, id_eq, Function.iterate_succ_apply']`. Consider the case `succ j ih`.

Introduce `w hw`. Establish `e1 : wn (j + 1) l f = dZ (wn j l f)`. Simplify using `only [wn, Function.iterate_succ_apply']`. Establish `e2 : wn (j + 1) (l + 1) f = dZ (wn j (l + 1) f)`. Simplify using `only [wn, Function.iterate_succ_apply']`.

Rewrite using `[e1, e2, ← dZ_dZb_comm hU (contDiffOn_wn hU hf j l) hw]`. Conclude with `dZ_congr hU ih hw`.
-/
theorem dZb_wn (hU : IsOpen U) {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f U) (j l : ℕ) :
    Set.EqOn (dZb (wn j l f)) (wn j (l + 1) f) U := by
  induction j with
  | zero =>
    intro w _
    simp only [wn, Function.iterate_zero, id_eq, Function.iterate_succ_apply']
  | succ j ih =>
    intro w hw
    have e1 : wn (j + 1) l f = dZ (wn j l f) := by
      simp only [wn, Function.iterate_succ_apply']
    have e2 : wn (j + 1) (l + 1) f = dZ (wn j (l + 1) f) := by
      simp only [wn, Function.iterate_succ_apply']
    rw [e1, e2, ← dZ_dZb_comm hU (contDiffOn_wn hU hf j l) hw]
    exact dZ_congr hU ih hw

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => intro x _`. Both sides reduce to the same expression. Consider the case `cons b w ih`. Consider the cases of `b`.

Introduce `x hx`. Establish `e : wn ((false :: w).count false) ((false :: w).count true) f = dZ (wn (w.count false) (w.count true) f)`. Simplify using `only [List.count_cons_self, List.count_cons, wn, Function.iterate_succ_apply']`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Conclude with `dZ_congr hU ih hx`. Introduce `x hx`. Establish `e : wn ((true :: w).count false) ((true :: w).count true) f = wn (w.count false) (w.count true + 1) f`. Simplify using `only [List.count_cons]`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `(dZb_congr hU ih hx).trans (dZb_wn hU hf _ _ hx)`.
-/
theorem wd_eq (hU : IsOpen U) {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f U) (w : List Bool) :
    Set.EqOn (wd w f) (wn (w.count false) (w.count true) f) U := by
  induction w with
  | nil => intro x _; rfl
  | cons b w ih =>
    cases b
    · intro x hx
      have e : wn ((false :: w).count false) ((false :: w).count true) f = dZ (wn (w.count false) (w.count true) f) := by
        simp only [List.count_cons_self, List.count_cons, wn, Function.iterate_succ_apply']
        simp
      rw [e]
      exact dZ_congr hU ih hx
    · intro x hx
      have e : wn ((true :: w).count false) ((true :: w).count true) f = wn (w.count false) (w.count true + 1) f := by
        simp only [List.count_cons]
        simp
      rw [e]
      exact (dZb_congr hU ih hx).trans (dZb_wn hU hf _ _ hx)

end Wirt

end Formalism.FourierDecayAlt.P.NFx4

end
end

section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.NFx4

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF

section Jet

variable {U : Set ℂ}

/- English proof (translation)
Establish `h1` using `h 1`. Establish `hI` using `h Complex.I`. Simplify using `only [star_one, mul_one, Complex.star_def, Complex.conj_I] at h1 hI`. Establish `hII : Complex.I * Complex.I = -1` using `Complex.I_mul_I`. Prove the components needed by the constructor for the conclusion.

Simplify using `only [dZ, h1, hI]`. Take the linear combination `(-(1 / 2 : ℂ) * α + (1 / 2 : ℂ) * β) * hII`. Simplify using `only [dZb, h1, hI]`. Take the linear combination `((1 / 2 : ℂ) * α - (1 / 2 : ℂ) * β) * hII`.
-/
theorem dZ_dZb_of {F : ℂ → ℂ} {w α β : ℂ} (h : ∀ v, fderiv ℝ F w v = α * v + β * star v) :
    dZ F w = α ∧ dZb F w = β := by
  have h1 := h 1
  have hI := h Complex.I
  simp only [star_one, mul_one, Complex.star_def, Complex.conj_I] at h1 hI
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  constructor
  · simp only [dZ, h1, hI]
    linear_combination (-(1 / 2 : ℂ) * α + (1 / 2 : ℂ) * β) * hII
  · simp only [dZb, h1, hI]
    linear_combination ((1 / 2 : ℂ) * α - (1 / 2 : ℂ) * β) * hII

def mono (ζ0 : ℂ) (j l : ℕ) (w : ℂ) : ℂ := (w - ζ0) ^ j * (star w - star ζ0) ^ l

/- English proof (translation)
Establish `hp : HasDerivAt (fun x : ℂ => (x - ζ0) ^ j) ((j : ℂ) * (w - ζ0) ^ (j - 1) * 1) w` using `((hasDerivAt_id w).sub_const ζ0).pow j`. Establish `hpl : HasDerivAt (fun x : ℂ => (x - ζ0) ^ l) ((l : ℂ) * (w - ζ0) ^ (l - 1) * 1) w` using `((hasDerivAt_id w).sub_const ζ0).pow l`. Establish `hp'` using `hp.hasFDerivAt.restrictScalars ℝ`. Establish `hq'` using `(hpl.hasFDerivAt.restrictScalars ℝ).star`. Establish `e : (fun x => c * mono ζ0 j l x) = fun x => c * ((x - ζ0) ^ j * star ((x - ζ0) ^ l))`.

Use function extensionality and compare the values at `x`. Simplify using `[mono, star_pow, star_sub]`. Establish `H : HasFDerivAt (fun x => c * ((x - ζ0) ^ j * star ((x - ζ0) ^ l))) _ w` using `(hp'.mul hq').const_mul c`. Rewrite using `[e, H.fderiv]`. Simplify using `[mono, star_pow, star_sub, star_mul', smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fderiv_cmono (ζ0 c : ℂ) (j l : ℕ) (w v : ℂ) :
    fderiv ℝ (fun x => c * mono ζ0 j l x) w v =
      (c * j * mono ζ0 (j - 1) l w) * v + (c * l * mono ζ0 j (l - 1) w) * star v := by
  have hp : HasDerivAt (fun x : ℂ => (x - ζ0) ^ j) ((j : ℂ) * (w - ζ0) ^ (j - 1) * 1) w :=
    ((hasDerivAt_id w).sub_const ζ0).pow j
  have hpl : HasDerivAt (fun x : ℂ => (x - ζ0) ^ l) ((l : ℂ) * (w - ζ0) ^ (l - 1) * 1) w :=
    ((hasDerivAt_id w).sub_const ζ0).pow l
  have hp' := hp.hasFDerivAt.restrictScalars ℝ
  have hq' := (hpl.hasFDerivAt.restrictScalars ℝ).star
  have e : (fun x => c * mono ζ0 j l x) = fun x => c * ((x - ζ0) ^ j * star ((x - ζ0) ^ l)) := by
    funext x
    simp [mono, star_pow, star_sub]
  have H : HasFDerivAt (fun x => c * ((x - ζ0) ^ j * star ((x - ζ0) ^ l))) _ w := (hp'.mul hq').const_mul c
  rw [e, H.fderiv]
  simp [mono, star_pow, star_sub, star_mul', smul_eq_mul]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `w`. Rewrite using `[(dZ_dZb_of (fderiv_cmono ζ0 c j l w)).1]`.
-/
theorem dZ_cmono (ζ0 c : ℂ) (j l : ℕ) :
    dZ (fun x => c * mono ζ0 j l x) = fun w => (c * j) * mono ζ0 (j - 1) l w := by
  funext w
  rw [(dZ_dZb_of (fderiv_cmono ζ0 c j l w)).1]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Rewrite using `[(dZ_dZb_of (fderiv_cmono ζ0 c j l w)).2]`.
-/
theorem dZb_cmono (ζ0 c : ℂ) (j l : ℕ) :
    dZb (fun x => c * mono ζ0 j l x) = fun w => (c * l) * mono ζ0 j (l - 1) w := by
  funext w
  rw [(dZ_dZb_of (fderiv_cmono ζ0 c j l w)).2]

/- English proof (translation)
Proceed by induction on `b with`. Consider the case `zero => funext w`. Simplify using the standard rewrite rules. Consider the case `succ b ih`. Rewrite using `[Function.iterate_succ_apply', ih, dZb_cmono]`.

Use function extensionality and compare the values at `w`. Rewrite using `[Nat.descFactorial_succ, Nat.sub_sub]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iter_dZb_cmono (ζ0 c : ℂ) (j l b : ℕ) :
    dZb^[b] (fun x => c * mono ζ0 j l x) = fun w => (c * (l.descFactorial b : ℂ)) * mono ζ0 j (l - b) w := by
  induction b with
  | zero => funext w; simp
  | succ b ih =>
    rw [Function.iterate_succ_apply', ih, dZb_cmono]
    funext w
    rw [Nat.descFactorial_succ, Nat.sub_sub]
    push_cast
    ring

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => funext w`. Simplify using the standard rewrite rules. Consider the case `succ a ih`. Rewrite using `[Function.iterate_succ_apply', ih, dZ_cmono]`.

Use function extensionality and compare the values at `w`. Rewrite using `[Nat.descFactorial_succ, Nat.sub_sub]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iter_dZ_cmono (ζ0 c : ℂ) (j l a : ℕ) :
    dZ^[a] (fun x => c * mono ζ0 j l x) = fun w => (c * (j.descFactorial a : ℂ)) * mono ζ0 (j - a) l w := by
  induction a with
  | zero => funext w; simp
  | succ a ih =>
    rw [Function.iterate_succ_apply', ih, dZ_cmono]
    funext w
    rw [Nat.descFactorial_succ, Nat.sub_sub]
    push_cast
    ring

/- English proof (translation)
Simplify using `only [mono, sub_self]`. Apply the tactic sequence `by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn, zero_pow]`.
-/
theorem mono_self (ζ0 : ℂ) (m n : ℕ) : mono ζ0 m n ζ0 = if m = 0 ∧ n = 0 then 1 else 0 := by
  simp only [mono, sub_self]
  by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn, zero_pow]

/- English proof (translation)
Establish `e : mono ζ0 j l = fun x => 1 * mono ζ0 j l x` using `by funext x; ring`. Rewrite using `[wn, e, iter_dZb_cmono, iter_dZ_cmono]`. Use `beta_reduce`. Rewrite using `[mono_self]`. Distinguish the cases in `hab : (a, b) = (j, l)`.

Simplify using `only [Prod.mk.injEq] at hab`. Take `⟨rfl, rfl⟩` from `hab`. Simplify using `[Nat.descFactorial_self, mul_comm]`. Rewrite using `[if_neg hab]`. Simplify using `only [Prod.mk.injEq, not_and_or] at hab`.

Establish `h : (l.descFactorial b : ℂ) * (j.descFactorial a : ℂ) * (if j - a = 0 ∧ l - b = 0 then 1 else 0) = 0`. Break down `hab with ha | hb` into its components or cases. Break down `Nat.lt_or_gt_of_ne ha with ha | ha` into its components or cases. Rewrite using `[if_neg (by omega)]; ring`. Rewrite using `[Nat.descFactorial_eq_zero_iff_lt.mpr ha]`.

Simplify using the standard rewrite rules. Break down `Nat.lt_or_gt_of_ne hb with hb | hb` into its components or cases. Rewrite using `[if_neg (by omega)]; ring`. Rewrite using `[Nat.descFactorial_eq_zero_iff_lt.mpr hb]`. Simplify using the standard rewrite rules.

Simplify `h` using `[mul_comm, mul_left_comm, mul_assoc]`.
-/
theorem wn_mono (ζ0 : ℂ) (j l a b : ℕ) :
    wn a b (mono ζ0 j l) ζ0 = if (a, b) = (j, l) then ((j.factorial * l.factorial : ℕ) : ℂ) else 0 := by
  have e : mono ζ0 j l = fun x => 1 * mono ζ0 j l x := by funext x; ring
  rw [wn, e, iter_dZb_cmono, iter_dZ_cmono]
  beta_reduce
  rw [mono_self]
  by_cases hab : (a, b) = (j, l)
  · simp only [Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    simp [Nat.descFactorial_self, mul_comm]
  · rw [if_neg hab]
    simp only [Prod.mk.injEq, not_and_or] at hab
    have h : (l.descFactorial b : ℂ) * (j.descFactorial a : ℂ) * (if j - a = 0 ∧ l - b = 0 then 1 else 0) = 0 := by
      rcases hab with ha | hb
      · rcases Nat.lt_or_gt_of_ne ha with ha | ha
        · rw [if_neg (by omega)]; ring
        · rw [Nat.descFactorial_eq_zero_iff_lt.mpr ha]; simp
      · rcases Nat.lt_or_gt_of_ne hb with hb | hb
        · rw [if_neg (by omega)]; ring
        · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hb]; simp
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

/- English proof (translation)
Establish `hs : ContDiff ℝ ∞ (fun x : ℂ => star x)` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff`. Unfold `mono`. Conclude with `((contDiff_id.sub contDiff_const).pow j).mul ((hs.sub contDiff_const).pow l)`.
-/
theorem contDiff_mono (ζ0 : ℂ) (j l : ℕ) : ContDiff ℝ ∞ (mono ζ0 j l) := by
  have hs : ContDiff ℝ ∞ (fun x : ℂ => star x) := (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff
  unfold mono
  exact ((contDiff_id.sub contDiff_const).pow j).mul ((hs.sub contDiff_const).pow l)

def JetT {E : Type*} [AddCommGroup E] [Module ℂ E] (U : Set ℂ) (ζ0 : ℂ) (Λ : (ℂ → ℂ) → E) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (w : ι → List Bool) (e : ι → E),
    ∀ f, ContDiffOn ℝ ∞ f U → Λ f = ∑ i, wd (w i) f ζ0 • e i

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ζ0 : ℂ}

/- English proof (translation)
Take `⟨ι, _, w, e, h⟩` from `hΛ`. Set `cnt : ι → ℕ × ℕ` to `fun i => ((w i).count false, (w i).count true)`. Establish `hS : ∀ c : ℕ × ℕ, ∑ i ∈ univ.filter (fun i => cnt i = c), e i = 0`. Introduce `c`. Establish `hc` using `h (mono ζ0 c.1 c.2) (contDiff_mono ζ0 c.1 c.2).contDiffOn`.

Rewrite `hc` using `[hP]`. Establish `e1 : ∀ i, wd (w i) (mono ζ0 c.1 c.2) ζ0 • e i = if cnt i = c then ((c.1.factorial * c.2.factorial : ℕ) : ℂ) • e i else 0`. Introduce `i`. Rewrite using `[wd_eq hU (contDiff_mono ζ0 c.1 c.2).contDiffOn (w i) h0, wn_mono]`. Distinguish the cases in `hi : cnt i = c`.

Rewrite using `[if_pos hi, if_pos (by rw [← hi])]`. Rewrite using `[if_neg hi, if_neg (by intro h'; exact hi (by rw [h'])), zero_smul]`. Rewrite `hc` using `[Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.sum_filter, ← Finset.smul_sum]`. Establish `hne : ((c.1.factorial * c.2.factorial : ℕ) : ℂ) ≠ 0`. Conclude with `(Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'` after adjusting the coercions.

Conclude with `(smul_eq_zero.mp hc.symm).resolve_left hne`. Introduce `f hf`. Rewrite using `[h f hf, Finset.sum_congr rfl (fun i _ => by rw [wd_eq hU hf (w i) h0]), ← Finset.sum_fiberwise_of_maps_to (g := cnt) (t := univ.image cnt) (fun i _ => Finset.mem_image_of_mem cnt (Finset.mem_univ i))]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Establish `e2 : ∀ i ∈ univ.filter (fun i => cnt i = c), wn ((w i).count false) ((w i).count true) f ζ0 • e i = wn c.1 c.2 f ζ0 • e i`.

Introduce `i hi`. Establish `hi' : cnt i = c` using `(Finset.mem_filter.1 hi).2`. Rewrite using `[← hi']`. Rewrite using `[Finset.sum_congr rfl e2, ← Finset.smul_sum, hS c, smul_zero]`.
-/
theorem jet_zero (hU : IsOpen U) (h0 : ζ0 ∈ U) {Λ : (ℂ → ℂ) → E} (hΛ : JetT U ζ0 Λ)
    (hP : ∀ j l, Λ (mono ζ0 j l) = 0) : ∀ f, ContDiffOn ℝ ∞ f U → Λ f = 0 := by
  classical
  obtain ⟨ι, _, w, e, h⟩ := hΛ
  let cnt : ι → ℕ × ℕ := fun i => ((w i).count false, (w i).count true)
  have hS : ∀ c : ℕ × ℕ, ∑ i ∈ univ.filter (fun i => cnt i = c), e i = 0 := by
    intro c
    have hc := h (mono ζ0 c.1 c.2) (contDiff_mono ζ0 c.1 c.2).contDiffOn
    rw [hP] at hc
    have e1 : ∀ i, wd (w i) (mono ζ0 c.1 c.2) ζ0 • e i =
        if cnt i = c then ((c.1.factorial * c.2.factorial : ℕ) : ℂ) • e i else 0 := by
      intro i
      rw [wd_eq hU (contDiff_mono ζ0 c.1 c.2).contDiffOn (w i) h0, wn_mono]
      by_cases hi : cnt i = c
      · rw [if_pos hi, if_pos (by rw [← hi])]
      · rw [if_neg hi, if_neg (by intro h'; exact hi (by rw [h'])), zero_smul]
    rw [Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.sum_filter, ← Finset.smul_sum] at hc
    have hne : ((c.1.factorial * c.2.factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
    exact (smul_eq_zero.mp hc.symm).resolve_left hne
  intro f hf
  rw [h f hf, Finset.sum_congr rfl (fun i _ => by rw [wd_eq hU hf (w i) h0]),
    ← Finset.sum_fiberwise_of_maps_to (g := cnt) (t := univ.image cnt)
      (fun i _ => Finset.mem_image_of_mem cnt (Finset.mem_univ i))]
  refine Finset.sum_eq_zero fun c _ => ?_
  have e2 : ∀ i ∈ univ.filter (fun i => cnt i = c),
      wn ((w i).count false) ((w i).count true) f ζ0 • e i = wn c.1 c.2 f ζ0 • e i := by
    intro i hi
    have hi' : cnt i = c := (Finset.mem_filter.1 hi).2
    rw [← hi']
  rw [Finset.sum_congr rfl e2, ← Finset.smul_sum, hS c, smul_zero]

/- English proof (translation)
Take `⟨ι, _, w, e, h⟩` from `h`. Take `⟨ι', _, w', e', h'⟩` from `h'`. Use `⟨ι ⊕ ι', inferInstance, Sum.elim w w', Sum.elim e e', fun f hf => ?_⟩` and prove the remaining obligations. Use `show Λ f + Λ' f = _`. Rewrite using `[Fintype.sum_sum_type, h f hf, h' f hf]`.

Both sides reduce to the same expression.
-/
theorem jet_add {Λ Λ' : (ℂ → ℂ) → E} (h : JetT U ζ0 Λ) (h' : JetT U ζ0 Λ') : JetT U ζ0 (fun f => Λ f + Λ' f) := by
  obtain ⟨ι, _, w, e, h⟩ := h
  obtain ⟨ι', _, w', e', h'⟩ := h'
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim w w', Sum.elim e e', fun f hf => ?_⟩
  show Λ f + Λ' f = _
  rw [Fintype.sum_sum_type, h f hf, h' f hf]
  rfl

/- English proof (translation)
Take `⟨ι, _, w, e, h⟩` from `h`. Use `⟨ι, inferInstance, w, fun i => c • e i, fun f hf => ?_⟩` and prove the remaining obligations. Use `show c • Λ f = _`. Rewrite using `[h f hf, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_comm]`.
-/
theorem jet_smul {Λ : (ℂ → ℂ) → E} (h : JetT U ζ0 Λ) (c : ℂ) : JetT U ζ0 (fun f => c • Λ f) := by
  obtain ⟨ι, _, w, e, h⟩ := h
  refine ⟨ι, inferInstance, w, fun i => c • e i, fun f hf => ?_⟩
  show c • Λ f = _
  rw [h f hf, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Empty, inferInstance, Empty.elim, Empty.elim, fun _ _ => by simp⟩`.
-/
theorem jet_zero' : JetT (E := E) U ζ0 (fun _ => 0) :=
  ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun _ _ => by simp⟩

/- English proof (translation)
Use `jet_smul h (-1)` as an intermediate fact. Simplify using `using this`.
-/
theorem jet_neg {Λ : (ℂ → ℂ) → E} (h : JetT U ζ0 Λ) : JetT U ζ0 (fun f => -Λ f) := by
  have := jet_smul h (-1)
  simpa using this

/- English proof (translation)
Simplify `jet_add h (jet_neg h')` using `[sub_eq_add_neg]`.
-/
theorem jet_sub {Λ Λ' : (ℂ → ℂ) → E} (h : JetT U ζ0 Λ) (h' : JetT U ζ0 Λ') : JetT U ζ0 (fun f => Λ f - Λ' f) := by
  simpa [sub_eq_add_neg] using jet_add h (jet_neg h')

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (jet_zero' (U := U) (ζ0 := ζ0) (E := E))`. Consider the case `insert j s hj ih`. Use `jet_add (h j (by simp)) (ih fun l hl => h l (by simp [hl]))` as an intermediate fact. Simplify `this` using `only [Finset.sum_insert hj]`.
-/
theorem jet_sum {κ : Type*} (s : Finset κ) {Λ : κ → (ℂ → ℂ) → E} (h : ∀ j ∈ s, JetT U ζ0 (Λ j)) :
    JetT U ζ0 (fun f => ∑ j ∈ s, Λ j f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (jet_zero' (U := U) (ζ0 := ζ0) (E := E))
  | insert j s hj ih =>
    have := jet_add (h j (by simp)) (ih fun l hl => h l (by simp [hl]))
    simpa only [Finset.sum_insert hj] using this

/- English proof (translation)
Distinguish the cases in `hp : p`. Simplify `h` using `only [if_pos hp]`. Simplify `(jet_zero' (U := U) (ζ0 := ζ0) (E := E))` using `only [if_neg hp]`.
-/
theorem jet_ite {Λ : (ℂ → ℂ) → E} (h : JetT U ζ0 Λ) (p : Prop) [Decidable p] :
    JetT U ζ0 (fun f => if p then Λ f else 0) := by
  by_cases hp : p
  · simpa only [if_pos hp] using h
  · simpa only [if_neg hp] using (jet_zero' (U := U) (ζ0 := ζ0) (E := E))

/- English proof (translation)
Assemble the required witnesses or components as `⟨Unit, inferInstance, fun _ => [], fun _ => A, fun f _ => by simp [wd]⟩`.
-/
theorem jet_val (A : E) : JetT U ζ0 (fun f => f ζ0 • A) :=
  ⟨Unit, inferInstance, fun _ => [], fun _ => A, fun f _ => by simp [wd]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨Unit, inferInstance, fun _ => [false], fun _ => A, fun f _ => by simp [wd]⟩`.
-/
theorem jet_dZ (A : E) : JetT U ζ0 (fun f => dZ f ζ0 • A) :=
  ⟨Unit, inferInstance, fun _ => [false], fun _ => A, fun f _ => by simp [wd]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨Unit, inferInstance, fun _ => [true], fun _ => A, fun f _ => by simp [wd]⟩`.
-/
theorem jet_dZb (A : E) : JetT U ζ0 (fun f => dZb f ζ0 • A) :=
  ⟨Unit, inferInstance, fun _ => [true], fun _ => A, fun f _ => by simp [wd]⟩

end Jet

end Formalism.FourierDecayAlt.P.NFx4

end
end

section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.NFx4

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.Qx5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Op

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
  {U : Set ℂ} (z z' : Fin (2 * r + k + 1) → ℂ)

/- English proof (translation)
Introduce `_ hg0` and use `⟨D, fun g => f (zetaL k r z z' i g), hD, hg0.2, hf.comp (zetaL_contDiff k r z z' i).contDiffOn (fun g hg => hDU g hg), fun _ _ _ => rfl⟩`.
-/
theorem smooth_comp (hD : IsOpen D) (hDU : ∀ g ∈ D, zetaL k r z z' i g ∈ U) {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f U) :
    SmoothLev k r i D (fun g => f (zetaL k r z z' i g)) := fun _ hg0 =>
  ⟨D, fun g => f (zetaL k r z z' i g), hD, hg0.2,
    hf.comp (zetaL_contDiff k r z z' i).contDiffOn (fun g hg => hDU g hg), fun _ _ _ => rfl⟩

open Classical in

def MF (hD : IsOpen D) (f : ℂ → ℂ) : Module.End ℂ (VS k r i D E) :=
  if h : SmoothLev k r i D (fun g => f (zetaL k r z z' i g)) then Mh hD _ h else 0

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem MF_eq (hD : IsOpen D) {f : ℂ → ℂ} (h : SmoothLev k r i D (fun g => f (zetaL k r z z' i g))) :
    MF (E := E) z z' hD f = Mh hD _ h := dif_pos h

/- English proof (translation)
Rewrite using `[MF_eq z z' hD h]`. Conclude with `ev_M hD h v hg`.
-/
theorem ev_MF (hD : IsOpen D) {f : ℂ → ℂ} (h : SmoothLev k r i D (fun g => f (zetaL k r z z' i g)))
    (v : VS k r i D E) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    (MF z z' hD f v : Mx k r → E) g = f (zetaL k r z z' i g) • (v : Mx k r → E) g := by
  rw [MF_eq z z' hD h]
  exact ev_M hD h v hg

/- English proof (translation)
Establish `h1` using `rd_hasDeriv (sm_zeta (D := D) z z') hg hX`. Establish `hfd : HasFDerivAt f (fderiv ℝ f (zetaL k r z z' i g)) (zetaL k r z z' i g)` using `((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hDU g hg.2))).hasFDerivAt`. Establish `h2` using `hfd.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by rw [B5.curve_zero])`. Conclude with `h2.deriv`.
-/
theorem rd_comp (hU : IsOpen U) (hDU : ∀ g ∈ D, zetaL k r z z' i g ∈ U) {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    {g X : Mx k r} (hg : g ∈ Glev k r i ∩ D) (hX : inLieLev k r i X) :
    RdV X (fun y => f (zetaL k r z z' i y)) g = fderiv ℝ f (zetaL k r z z' i g) (RdV X (zetaL k r z z' i) g) := by
  have h1 := rd_hasDeriv (sm_zeta (D := D) z z') hg hX
  have hfd : HasFDerivAt f (fderiv ℝ f (zetaL k r z z' i g)) (zetaL k r z z' i g) :=
    ((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hDU g hg.2))).hasFDerivAt
  have h2 := hfd.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by rw [B5.curve_zero])
  exact h2.deriv

/- English proof (translation)
Establish `h1` using `rd_hasDeriv (sm_zeta (D := D) z z') hg hX`. Establish `h2` using `((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1`. Conclude with `h2.deriv`.
-/
theorem rd_star {g X : Mx k r} (hg : g ∈ Glev k r i ∩ D) (hX : inLieLev k r i X) :
    RdV X (fun y => star (zetaL k r z z' i y)) g = star (RdV X (zetaL k r z z' i) g) := by
  have h1 := rd_hasDeriv (sm_zeta (D := D) z z') hg hX
  have h2 := ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  exact h2.deriv

/- English proof (translation)
Establish `hz : EH k r (posL k r i a) (posL k r i b) (zbF k r z z' i) g = EH k r (posL k r i a) (posL k r i b) (fun y => star (zetaL k r z z' i y)) g` using `(good_eh (E := ℂ) hD a b).loc _ _ (fun x hx => (zb_eq z z' hx.1).symm) g hg`. Rewrite using `[hz]`. Use `show RdV _ _ g + Complex.I • RdV _ _ g = dZ f (zetaL k r z z' i g) * (RdV _ _ g + Complex.I • RdV _ _ g) + dZb f (zetaL k r z z' i g) * (RdV _ _ g + Complex.I • RdV _ _ g)`. Rewrite using `[rd_comp z z' hU hDU hf hg (hpart_lev i a b).1, rd_comp z z' hU hDU hf hg (hpart_lev i a b).2, rd_star z z' hg (hpart_lev i a b).1, rd_star z z' hg (hpart_lev i a b).2, fderiv_wirt, fderiv_wirt]`. Simplify using `only [smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eh_comp (hD : IsOpen D) (hU : IsOpen U) (hDU : ∀ g ∈ D, zetaL k r z z' i g ∈ U) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) (a b : Fin (mdim k r i)) :
    EH k r (posL k r i a) (posL k r i b) (fun y => f (zetaL k r z z' i y)) g =
      dZ f (zetaL k r z z' i g) * EH k r (posL k r i a) (posL k r i b) (zetaL k r z z' i) g +
        dZb f (zetaL k r z z' i g) * EH k r (posL k r i a) (posL k r i b) (zbF k r z z' i) g := by
  have hz : EH k r (posL k r i a) (posL k r i b) (zbF k r z z' i) g =
      EH k r (posL k r i a) (posL k r i b) (fun y => star (zetaL k r z z' i y)) g :=
    (good_eh (E := ℂ) hD a b).loc _ _ (fun x hx => (zb_eq z z' hx.1).symm) g hg
  rw [hz]
  show RdV _ _ g + Complex.I • RdV _ _ g =
    dZ f (zetaL k r z z' i g) * (RdV _ _ g + Complex.I • RdV _ _ g) +
      dZb f (zetaL k r z z' i g) * (RdV _ _ g + Complex.I • RdV _ _ g)
  rw [rd_comp z z' hU hDU hf hg (hpart_lev i a b).1, rd_comp z z' hU hDU hf hg (hpart_lev i a b).2,
    rd_star z z' hg (hpart_lev i a b).1, rd_star z z' hg (hpart_lev i a b).2, fderiv_wirt, fderiv_wirt]
  simp only [smul_eq_mul]
  ring

/- English proof (translation)
Establish `h0` using `smooth_comp z z' hD hDU hf`. Establish `h1` using `smooth_comp z z' hD hDU (contDiffOn_dZ hU hf)`. Establish `h2` using `smooth_comp z z' hD hDU (contDiffOn_dZb hU hf)`. Rewrite using `[MF_eq z z' hD h0, MF_eq z z' hD h1, MF_eq z z' hD h2]`. Use `end_ext fun v g hg => ?_` and prove the remaining obligations.

Rewrite using `[comm_EM hD a b h0 v hg, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, Module.End.mul_apply, Module.End.mul_apply, ev_M hD h1 _ hg, ev_M hD h2 _ hg, comm_EM hD a b (sm_zeta z z') v hg, comm_EM hD a b (sm_zb z z') v hg, eh_comp z z' hD hU hDU hf hg a b]`. Simplify using `only [add_smul, mul_smul]`.
-/
theorem comm_EMF (hD : IsOpen D) (hU : IsOpen U) (hDU : ∀ g ∈ D, zetaL k r z z' i g ∈ U) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (a b : Fin (mdim k r i)) :
    Eh (E := E) hD a b * MF z z' hD f - MF z z' hD f * Eh hD a b =
      MF z z' hD (dZ f) * (Eh hD a b * Mh hD _ (sm_zeta z z') - Mh hD _ (sm_zeta z z') * Eh hD a b) +
        MF z z' hD (dZb f) * (Eh hD a b * Mh hD _ (sm_zb z z') - Mh hD _ (sm_zb z z') * Eh hD a b) := by
  have h0 := smooth_comp z z' hD hDU hf
  have h1 := smooth_comp z z' hD hDU (contDiffOn_dZ hU hf)
  have h2 := smooth_comp z z' hD hDU (contDiffOn_dZb hU hf)
  rw [MF_eq z z' hD h0, MF_eq z z' hD h1, MF_eq z z' hD h2]
  refine end_ext fun v g hg => ?_
  rw [comm_EM hD a b h0 v hg, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, Module.End.mul_apply,
    Module.End.mul_apply, ev_M hD h1 _ hg, ev_M hD h2 _ hg, comm_EM hD a b (sm_zeta z z') v hg,
    comm_EM hD a b (sm_zb z z') v hg, eh_comp z z' hD hU hDU hf hg a b]
  simp only [add_smul, mul_smul]

def Exp (hD : IsOpen D) (U : Set ℂ) (T : Module.End ℂ (VS k r i D E)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (w : ι → List Bool) (Tw : ι → Module.End ℂ (VS k r i D E)),
    ∀ f, ContDiffOn ℝ ∞ f U → T * MF z z' hD f = ∑ j, MF z z' hD (wd (w j) f) * Tw j

/- English proof (translation)
Assemble the required witnesses or components as `⟨Unit, inferInstance, fun _ => [], fun _ => algebraMap ℂ _ c, fun f _ => by simp only [Finset.univ_unique, Finset.sum_singleton, wd] exact Algebra.commutes c _⟩`.
-/
theorem exp_alg (hD : IsOpen D) (c : ℂ) : Exp (E := E) (i := i) z z' hD U (algebraMap ℂ _ c) :=
  ⟨Unit, inferInstance, fun _ => [], fun _ => algebraMap ℂ _ c, fun f _ => by
    simp only [Finset.univ_unique, Finset.sum_singleton, wd]
    exact Algebra.commutes c _⟩

/- English proof (translation)
Take `⟨ι, _, w, Tw, h⟩` from `hT`. Take `⟨ι', _, w', Sw, h'⟩` from `hS`. Use `⟨ι ⊕ ι', inferInstance, Sum.elim w w', Sum.elim Tw Sw, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[add_mul, h f hf, h' f hf, Fintype.sum_sum_type]`. Both sides reduce to the same expression.
-/
theorem exp_add (hD : IsOpen D) {T S : Module.End ℂ (VS k r i D E)} (hT : Exp z z' hD U T) (hS : Exp z z' hD U S) :
    Exp z z' hD U (T + S) := by
  obtain ⟨ι, _, w, Tw, h⟩ := hT
  obtain ⟨ι', _, w', Sw, h'⟩ := hS
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim w w', Sum.elim Tw Sw, fun f hf => ?_⟩
  rw [add_mul, h f hf, h' f hf, Fintype.sum_sum_type]
  rfl

/- English proof (translation)
Take `⟨ι, _, w, Tw, h⟩` from `hT`. Take `⟨ι', _, w', Sw, h'⟩` from `hS`. Use `⟨ι × ι', inferInstance, fun p => w p.1 ++ w' p.2, fun p => Tw p.1 * Sw p.2, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, h' f hf, Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_assoc, h _ (contDiffOn_wd hU hf _), Finset.sum_mul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[wd_append, mul_assoc]`.
-/
theorem exp_mul (hD : IsOpen D) (hU : IsOpen U) {T S : Module.End ℂ (VS k r i D E)} (hT : Exp z z' hD U T)
    (hS : Exp z z' hD U S) : Exp z z' hD U (T * S) := by
  obtain ⟨ι, _, w, Tw, h⟩ := hT
  obtain ⟨ι', _, w', Sw, h'⟩ := hS
  refine ⟨ι × ι', inferInstance, fun p => w p.1 ++ w' p.2, fun p => Tw p.1 * Sw p.2, fun f hf => ?_⟩
  rw [mul_assoc, h' f hf, Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, h _ (contDiffOn_wd hU hf _), Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [wd_append, mul_assoc]

/- English proof (translation)
Use `⟨Fin 3, inferInstance, ![[], [false], [true]], ![Eh hD a b, Eh hD a b * Mh hD _ (sm_zeta z z') - Mh hD _ (sm_zeta z z') * Eh hD a b, Eh hD a b * Mh hD _ (sm_zb z z') - Mh hD _ (sm_zb z z') * Eh hD a b], fun f hf => ?_⟩` and prove the remaining obligations. Establish `h` using `comm_EMF (E := E) z z' hD hU hDU hf a b`. Rewrite using `[Fin.sum_univ_three]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, wd, Bool.false_eq_true, if_false, if_true]`. Rewrite using `[add_assoc, ← h]`.

Normalize the expressions using the abelian group laws.
-/
theorem exp_Eh (hD : IsOpen D) (hU : IsOpen U) (hDU : ∀ g ∈ D, zetaL k r z z' i g ∈ U) (a b : Fin (mdim k r i)) :
    Exp (E := E) z z' hD U (Eh hD a b) := by
  refine ⟨Fin 3, inferInstance, ![[], [false], [true]],
    ![Eh hD a b, Eh hD a b * Mh hD _ (sm_zeta z z') - Mh hD _ (sm_zeta z z') * Eh hD a b,
      Eh hD a b * Mh hD _ (sm_zb z z') - Mh hD _ (sm_zb z z') * Eh hD a b], fun f hf => ?_⟩
  have h := comm_EMF (E := E) z z' hD hU hDU hf a b
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, wd, Bool.false_eq_true, if_false, if_true]
  rw [add_assoc, ← h]
  abel

/- English proof (translation)
Proceed by induction on `hT using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨p, rfl⟩` from `hx`. Conclude with `exp_Eh z z' hD hU hDU p.1 p.2`. Consider the case `algebraMap c => exact exp_alg z z' hD c`.

Consider the case `add x y _ _ hx hy => exact exp_add z z' hD hx hy`. Consider the case `mul x y _ _ hx hy => exact exp_mul z z' hD hU hx hy`.
-/
theorem exp_adjoin (hD : IsOpen D) (hU : IsOpen U) (hDU : ∀ g ∈ D, zetaL k r z z' i g ∈ U)
    {T : Module.End ℂ (VS k r i D E)}
    (hT : T ∈ Algebra.adjoin ℂ (Set.range fun p : Fin (mdim k r i) × Fin (mdim k r i) => Eh (E := E) hD p.1 p.2)) :
    Exp z z' hD U T := by
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact exp_Eh z z' hD hU hDU p.1 p.2
  | algebraMap c => exact exp_alg z z' hD c
  | add x y _ _ hx hy => exact exp_add z z' hD hx hy
  | mul x y _ _ hx hy => exact exp_mul z z' hD hU hx hy

/- English proof (translation)
Unfold `qminor`. Use `Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (intCast_mem _ _) (Subalgebra.list_prod_mem _ ?_)` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[List.mem_ofFn]`. Take `⟨l, rfl⟩` from `hx`.

Unfold `Tm`. Use `Subalgebra.add_mem _ ?_ (Algebra.subset_adjoin ⟨(a (σ l), b l), rfl⟩)` and prove the remaining obligations. Use `split_ifs`. Conclude with `Subalgebra.algebraMap_mem _ _`. Conclude with `Subalgebra.zero_mem _`.
-/
theorem qminor_mem (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    qminor (Eh (E := E) hD) a b u ∈
      Algebra.adjoin ℂ (Set.range fun p : Fin (mdim k r i) × Fin (mdim k r i) => Eh (E := E) hD p.1 p.2) := by
  unfold qminor
  refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (intCast_mem _ _) (Subalgebra.list_prod_mem _ ?_)
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨l, rfl⟩ := hx
  unfold Tm
  refine Subalgebra.add_mem _ ?_ (Algebra.subset_adjoin ⟨(a (σ l), b l), rfl⟩)
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

/- English proof (translation)
Take `⟨ι, _, w, Tw, hE⟩` from `exp_adjoin z z' hD hU hDU (qminor_mem (E := E) hD a b u)`. Set `v : VS k r i D E` to `⟨cut k r i D h, cut_mem hD hh⟩`. Use `⟨ι, inferInstance, w, fun j => (Tw j v : Mx k r → E) g, fun f hf => ?_⟩` and prove the remaining obligations. Establish `hf0` using `smooth_comp z z' hD hDU hf`. Establish `e1 : qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u (fun y => f (zetaL k r z z' i y) • h y) g = (qminor (Eh (E` using `E) hD) a b u (MF z z' hD f v) : Mx k r → E) g := by`.

Rewrite using `[rep_qminor hD a b u _ g hg]`. Use `(good_qminor hD a b u).loc _ _ (fun x hx => ?_) g hg` and prove the remaining obligations. Rewrite using `[ev_MF z z' hD hf0 v hx]`. Use `show f (zetaL k r z z' i x) • h x = f (zetaL k r z z' i x) • cut k r i D h x`. Rewrite using `[cut_of_mem h hx]`.

Use `show qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u (fun y => f (zetaL k r z z' i y) • h y) g = _`. Rewrite using `[e1, ← Module.End.mul_apply, hE f hf]`. Simplify using `only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Module.End.mul_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[ev_MF z z' hD (smooth_comp z z' hD hDU (contDiffOn_wd hU hf (w j))) _ hg]`.
-/
theorem jet_qminor (hD : IsOpen D) (hU : IsOpen U) (hDU : ∀ g ∈ D, zetaL k r z z' i g ∈ U)
    {h : Mx k r → E} (hh : SmoothLev k r i D h) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) {t : ℕ}
    (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    JetT U (zetaL k r z z' i g)
      (fun f => qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u (fun y => f (zetaL k r z z' i y) • h y) g) := by
  obtain ⟨ι, _, w, Tw, hE⟩ := exp_adjoin z z' hD hU hDU (qminor_mem (E := E) hD a b u)
  let v : VS k r i D E := ⟨cut k r i D h, cut_mem hD hh⟩
  refine ⟨ι, inferInstance, w, fun j => (Tw j v : Mx k r → E) g, fun f hf => ?_⟩
  have hf0 := smooth_comp z z' hD hDU hf
  have e1 : qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u (fun y => f (zetaL k r z z' i y) • h y) g =
      (qminor (Eh (E := E) hD) a b u (MF z z' hD f v) : Mx k r → E) g := by
    rw [rep_qminor hD a b u _ g hg]
    refine (good_qminor hD a b u).loc _ _ (fun x hx => ?_) g hg
    rw [ev_MF z z' hD hf0 v hx]
    show f (zetaL k r z z' i x) • h x = f (zetaL k r z z' i x) • cut k r i D h x
    rw [cut_of_mem h hx]
  show qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u (fun y => f (zetaL k r z z' i y) • h y) g = _
  rw [e1, ← Module.End.mul_apply, hE f hf]
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Module.End.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_MF z z' hD (smooth_comp z z' hD hDU (contDiffOn_wd hU hf (w j))) _ hg]

/- English proof (translation)
Establish `jq` using `fun {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) => jet_qminor z z' hD hU hDU hh hg a b u`. Apply the tactic sequence `fin_cases p <;> fin_cases q`. Conclude with `jq id id _`. Conclude with `jet_neg (jet_sum _ fun i' _ => jet_sum _ fun j' _ => jet_smul (jq _ _ _) _)`. Conclude with `jet_neg (jet_sum _ fun i' _ => jet_sum _ fun j' _ => jet_smul (jq _ _ _) _)`.

Conclude with `jet_neg (jet_sum _ fun i₁ _ => jet_sum _ fun i₂ _ => jet_sum _ fun j₁ _ => jet_sum _ fun j₂ _ => jet_ite (jet_smul (jq _ _ _) _) _)`.
-/
theorem jet_tL (hD : IsOpen D) (hU : IsOpen U) (hDU : ∀ g ∈ D, zetaL k r z z' i g ∈ U)
    {h : Mx k r → E} (hh : SmoothLev k r i D h) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) (Y : ℂ) (p q : Fin 2) :
    JetT U (zetaL k r z z' i g) (fun f => tL k r z z' i Y p q (fun y => f (zetaL k r z z' i y) • h y) g) := by
  have jq := fun {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) => jet_qminor z z' hD hU hDU hh hg a b u
  fin_cases p <;> fin_cases q
  · exact jq id id _
  · exact jet_neg (jet_sum _ fun i' _ => jet_sum _ fun j' _ => jet_smul (jq _ _ _) _)
  · exact jet_neg (jet_sum _ fun i' _ => jet_sum _ fun j' _ => jet_smul (jq _ _ _) _)
  · exact jet_neg (jet_sum _ fun i₁ _ => jet_sum _ fun i₂ _ => jet_sum _ fun j₁ _ => jet_sum _ fun j₂ _ =>
      jet_ite (jet_smul (jq _ _ _) _) _)

end Op

end Formalism.FourierDecayAlt.P.NFx4

end
end

section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.NFx4

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.Qx5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Peel

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
  (z z' : Fin (2 * r + k + 1) → ℂ)

/- English proof (translation)
Establish `hs : ContDiff ℝ ∞ (fun x : ℂ => star x)` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff`. Conclude with `fun _ _ => ⟨Set.univ, _, isOpen_univ, trivial, (hs.comp (zetaL_contDiff k r z z' i)).contDiffOn, fun _ _ _ => rfl⟩`.
-/
theorem sm_star : SmoothLev k r i D (fun y => star (zetaL k r z z' i y)) := by
  have hs : ContDiff ℝ ∞ (fun x : ℂ => star x) := (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff
  exact fun _ _ => ⟨Set.univ, _, isOpen_univ, trivial, (hs.comp (zetaL_contDiff k r z z' i)).contDiffOn,
    fun _ _ _ => rfl⟩

/- English proof (translation)
Introduce `_ _` and use `⟨Set.univ, _, isOpen_univ, trivial, ((contDiff_mono ζ0 j l).comp (zetaL_contDiff k r z z' i)).contDiffOn, fun _ _ _ => rfl⟩`.
-/
theorem sm_mono (ζ0 : ℂ) (j l : ℕ) : SmoothLev k r i D (fun y => mono ζ0 j l (zetaL k r z z' i y)) :=
  fun _ _ => ⟨Set.univ, _, isOpen_univ, trivial,
    ((contDiff_mono ζ0 j l).comp (zetaL_contDiff k r z z' i)).contDiffOn, fun _ _ _ => rfl⟩

/- English proof (translation)
Take `⟨c1, c2, c3, c4, c5, c6⟩` from `zeta_comm_level z z' hD hF hg Y`. Establish `e1 : (fun y => (zetaL k r z z' i y - ζ0) • F y) = fun y => zetaL k r z z' i y • F y + (-ζ0) • F y`. Use function extensionality and compare the values at `fun y => by rw [sub_eq_add_neg, add_smul]`. Establish `e2 : (fun y => (star (zetaL k r z z' i y) - star ζ0) • F y) = fun y => star (zetaL k r z z' i y) • F y + (-star ζ0) • F y`. Use function extensionality and compare the values at `fun y => by rw [sub_eq_add_neg, add_smul]`.

Establish `s1` using `smooth_mul (sm_zeta (D := D) z z') hF`. Establish `s2` using `smooth_mul (sm_star (D := D) z z') hF`. Establish `L` using `fun (p q : Fin 2) => (ll_tL (E := E) (i := i) hD z z' Y p q).lin`. Rewrite using `[e1, e2]`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[L 1 0 _ _ _ s1 hF g hg, c1]`. Use `module`. Rewrite using `[L 1 1 _ _ _ s1 hF g hg, c2]`. Use `module`. Rewrite using `[L 0 1 _ _ _ s1 hF g hg, c3]`.

Use `module`. Rewrite using `[L 0 1 _ _ _ s2 hF g hg, c4]`. Use `module`. Rewrite using `[L 1 0 _ _ _ s2 hF g hg, c5]`. Use `module`.

Rewrite using `[L 1 1 _ _ _ s2 hF g hg, c6]`. Use `module`.
-/
theorem peel (hD : IsOpen D) {F : Mx k r → E} (hF : SmoothLev k r i D F) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (Y ζ0 : ℂ) :
    tL k r z z' i Y 1 0 (fun y => (zetaL k r z z' i y - ζ0) • F y) g =
        (zetaL k r z z' i g - ζ0) • tL k r z z' i Y 1 0 F g - tL k r z z' i Y 1 1 F g ∧
    tL k r z z' i Y 1 1 (fun y => (zetaL k r z z' i y - ζ0) • F y) g =
        (zetaL k r z z' i g - ζ0) • tL k r z z' i Y 1 1 F g ∧
    tL k r z z' i Y 0 1 (fun y => (zetaL k r z z' i y - ζ0) • F y) g =
        (zetaL k r z z' i g - ζ0) • tL k r z z' i Y 0 1 F g ∧
    tL k r z z' i Y 0 1 (fun y => (star (zetaL k r z z' i y) - star ζ0) • F y) g =
        (star (zetaL k r z z' i g) - star ζ0) • tL k r z z' i Y 0 1 F g + tL k r z z' i Y 1 1 F g ∧
    tL k r z z' i Y 1 0 (fun y => (star (zetaL k r z z' i y) - star ζ0) • F y) g =
        (star (zetaL k r z z' i g) - star ζ0) • tL k r z z' i Y 1 0 F g ∧
    tL k r z z' i Y 1 1 (fun y => (star (zetaL k r z z' i y) - star ζ0) • F y) g =
        (star (zetaL k r z z' i g) - star ζ0) • tL k r z z' i Y 1 1 F g := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := zeta_comm_level z z' hD hF hg Y
  have e1 : (fun y => (zetaL k r z z' i y - ζ0) • F y) = fun y => zetaL k r z z' i y • F y + (-ζ0) • F y :=
    funext fun y => by rw [sub_eq_add_neg, add_smul]
  have e2 : (fun y => (star (zetaL k r z z' i y) - star ζ0) • F y) =
      fun y => star (zetaL k r z z' i y) • F y + (-star ζ0) • F y :=
    funext fun y => by rw [sub_eq_add_neg, add_smul]
  have s1 := smooth_mul (sm_zeta (D := D) z z') hF
  have s2 := smooth_mul (sm_star (D := D) z z') hF
  have L := fun (p q : Fin 2) => (ll_tL (E := E) (i := i) hD z z' Y p q).lin
  rw [e1, e2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [L 1 0 _ _ _ s1 hF g hg, c1]; module
  · rw [L 1 1 _ _ _ s1 hF g hg, c2]; module
  · rw [L 0 1 _ _ _ s1 hF g hg, c3]; module
  · rw [L 0 1 _ _ _ s2 hF g hg, c4]; module
  · rw [L 1 0 _ _ _ s2 hF g hg, c5]; module
  · rw [L 1 1 _ _ _ s2 hF g hg, c6]; module

/- English proof (translation)
Use function extensionality and compare the values at `y`. Rewrite using `[smul_smul]`. Use `congr 1`. Simplify using `only [mono]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fm_succ_j (ζ0 : ℂ) (j l : ℕ) (h : Mx k r → E) :
    (fun y => mono ζ0 (j + 1) l (zetaL k r z z' i y) • h y) =
      fun y => (zetaL k r z z' i y - ζ0) • (mono ζ0 j l (zetaL k r z z' i y) • h y) := by
  funext y
  rw [smul_smul]
  congr 1
  simp only [mono]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `y`. Rewrite using `[smul_smul]`. Use `congr 1`. Simplify using `only [mono]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fm_succ_l (ζ0 : ℂ) (l : ℕ) (h : Mx k r → E) :
    (fun y => mono ζ0 0 (l + 1) (zetaL k r z z' i y) • h y) =
      fun y => (star (zetaL k r z z' i y) - star ζ0) • (mono ζ0 0 l (zetaL k r z z' i y) • h y) := by
  funext y
  rw [smul_smul]
  congr 1
  simp only [mono]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `[mono]`.
-/
theorem fm_zero (ζ0 : ℂ) (h : Mx k r → E) : (fun y => mono ζ0 0 0 (zetaL k r z z' i y) • h y) = h := by
  funext y
  simp [mono]

variable (hD : IsOpen D) {h : Mx k r → E} (hh : SmoothLev k r i D h) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) (Y : ℂ)
include hD hh hg

/- English proof (translation)
Break down `j with _ | j` into its components or cases. Break down `l with _ | l` into its components or cases. Simplify using `at hjl`. Rewrite using `[fm_succ_l, (peel z z' hD (smooth_mul (sm_mono z z' _ 0 l) hh) hg Y _).2.2.2.2.2, sub_self, zero_smul]`. Rewrite using `[fm_succ_j, (peel z z' hD (smooth_mul (sm_mono z z' _ j l) hh) hg Y _).2.1, sub_self, zero_smul]`.
-/
theorem diagonal_monomial_vanish (j l : ℕ) (hjl : j + l ≠ 0) :
    tL k r z z' i Y 1 1 (fun y => mono (zetaL k r z z' i g) j l (zetaL k r z z' i y) • h y) g = 0 := by
  rcases j with _ | j
  · rcases l with _ | l
    · simp at hjl
    · rw [fm_succ_l, (peel z z' hD (smooth_mul (sm_mono z z' _ 0 l) hh) hg Y _).2.2.2.2.2, sub_self, zero_smul]
  · rw [fm_succ_j, (peel z z' hD (smooth_mul (sm_mono z z' _ j l) hh) hg Y _).2.1, sub_self, zero_smul]

/- English proof (translation)
Distinguish the cases in `hjl : j = 0 ∧ l = 0`. Take `⟨rfl, rfl⟩` from `hjl`. Rewrite using `[fm_zero, if_pos ⟨rfl, rfl⟩]`. Rewrite using `[if_neg hjl, diagonal_monomial_vanish z z' hD hh hg Y j l (by omega)]`.
-/
theorem diagonal_monomial_action (j l : ℕ) :
    tL k r z z' i Y 1 1 (fun y => mono (zetaL k r z z' i g) j l (zetaL k r z z' i y) • h y) g =
      if j = 0 ∧ l = 0 then tL k r z z' i Y 1 1 h g else 0 := by
  by_cases hjl : j = 0 ∧ l = 0
  · obtain ⟨rfl, rfl⟩ := hjl
    rw [fm_zero, if_pos ⟨rfl, rfl⟩]
  · rw [if_neg hjl, diagonal_monomial_vanish z z' hD hh hg Y j l (by omega)]

/- English proof (translation)
Break down `j with _ | j` into its components or cases. Break down `l with _ | l` into its components or cases. Rewrite using `[fm_zero, if_pos ⟨rfl, rfl⟩]`. Rewrite using `[fm_succ_l, (peel z z' hD (smooth_mul (sm_mono z z' _ 0 l) hh) hg Y _).2.2.2.2.1, sub_self, zero_smul]`. Simplify using the standard rewrite rules.

Rewrite using `[fm_succ_j, (peel z z' hD (smooth_mul (sm_mono z z' _ j l) hh) hg Y _).1, sub_self, zero_smul, zero_sub]`. Distinguish the cases in `hjl : j = 0 ∧ l = 0`. Take `⟨rfl, rfl⟩` from `hjl`. Rewrite using `[fm_zero]`. Simplify using the standard rewrite rules.

Rewrite using `[diagonal_monomial_vanish z z' hD hh hg Y j l (by omega), if_neg (by omega), if_neg (by omega), neg_zero]`.
-/
theorem lower_left_monomial_action (j l : ℕ) :
    tL k r z z' i Y 1 0 (fun y => mono (zetaL k r z z' i g) j l (zetaL k r z z' i y) • h y) g =
      if j = 0 ∧ l = 0 then tL k r z z' i Y 1 0 h g else if j = 1 ∧ l = 0 then -tL k r z z' i Y 1 1 h g else 0 := by
  rcases j with _ | j
  · rcases l with _ | l
    · rw [fm_zero, if_pos ⟨rfl, rfl⟩]
    · rw [fm_succ_l, (peel z z' hD (smooth_mul (sm_mono z z' _ 0 l) hh) hg Y _).2.2.2.2.1, sub_self, zero_smul]
      simp
  · rw [fm_succ_j, (peel z z' hD (smooth_mul (sm_mono z z' _ j l) hh) hg Y _).1, sub_self, zero_smul, zero_sub]
    by_cases hjl : j = 0 ∧ l = 0
    · obtain ⟨rfl, rfl⟩ := hjl
      rw [fm_zero]
      simp
    · rw [diagonal_monomial_vanish z z' hD hh hg Y j l (by omega), if_neg (by omega), if_neg (by omega), neg_zero]

/- English proof (translation)
Break down `j with _ | j` into its components or cases. Break down `l with _ | l` into its components or cases. Rewrite using `[fm_zero, if_pos ⟨rfl, rfl⟩]`. Rewrite using `[fm_succ_l, (peel z z' hD (smooth_mul (sm_mono z z' _ 0 l) hh) hg Y _).2.2.2.1, sub_self, zero_smul, zero_add]`. Distinguish the cases in `hl : l = 0`.

Substitute `hl` using the available equality. Rewrite using `[fm_zero]`. Simplify using the standard rewrite rules. Rewrite using `[diagonal_monomial_vanish z z' hD hh hg Y 0 l (by omega), if_neg (by omega), if_neg (by omega)]`. Rewrite using `[fm_succ_j, (peel z z' hD (smooth_mul (sm_mono z z' _ j l) hh) hg Y _).2.2.1, sub_self, zero_smul]`.

Simplify using the standard rewrite rules.
-/
theorem upper_right_monomial_action (j l : ℕ) :
    tL k r z z' i Y 0 1 (fun y => mono (zetaL k r z z' i g) j l (zetaL k r z z' i y) • h y) g =
      if j = 0 ∧ l = 0 then tL k r z z' i Y 0 1 h g else if j = 0 ∧ l = 1 then tL k r z z' i Y 1 1 h g else 0 := by
  rcases j with _ | j
  · rcases l with _ | l
    · rw [fm_zero, if_pos ⟨rfl, rfl⟩]
    · rw [fm_succ_l, (peel z z' hD (smooth_mul (sm_mono z z' _ 0 l) hh) hg Y _).2.2.2.1, sub_self, zero_smul,
        zero_add]
      by_cases hl : l = 0
      · subst hl
        rw [fm_zero]
        simp
      · rw [diagonal_monomial_vanish z z' hD hh hg Y 0 l (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [fm_succ_j, (peel z z' hD (smooth_mul (sm_mono z z' _ j l) hh) hg Y _).2.2.1, sub_self, zero_smul]
    simp

end Peel

/- English proof (translation)
Establish `h1` using `wn_mono ζ0 j l 1 0`. Establish `h2` using `wn_mono ζ0 j l 0 1`. Simplify using `only [wn, Function.iterate_one, Function.iterate_zero, id_eq] at h1 h2`. Use `⟨mono_self ζ0 j l, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`.

Distinguish the cases in `hj : j = 1 ∧ l = 0`. Take `⟨rfl, rfl⟩` from `hj`. Simplify using the standard rewrite rules. Rewrite using `[if_neg (by rintro ⟨⟩; exact hj ⟨rfl, rfl⟩), if_neg hj]`. Rewrite using `[h2]`.

Distinguish the cases in `hj : j = 0 ∧ l = 1`. Take `⟨rfl, rfl⟩` from `hj`. Simplify using the standard rewrite rules. Rewrite using `[if_neg (by rintro ⟨⟩; exact hj ⟨rfl, rfl⟩), if_neg hj]`.
-/
theorem mono_at (ζ0 : ℂ) (j l : ℕ) :
    mono ζ0 j l ζ0 = (if j = 0 ∧ l = 0 then 1 else 0) ∧
      dZ (mono ζ0 j l) ζ0 = (if j = 1 ∧ l = 0 then 1 else 0) ∧
      dZb (mono ζ0 j l) ζ0 = (if j = 0 ∧ l = 1 then 1 else 0) := by
  have h1 := wn_mono ζ0 j l 1 0
  have h2 := wn_mono ζ0 j l 0 1
  simp only [wn, Function.iterate_one, Function.iterate_zero, id_eq] at h1 h2
  refine ⟨mono_self ζ0 j l, ?_, ?_⟩
  · rw [h1]
    by_cases hj : j = 1 ∧ l = 0
    · obtain ⟨rfl, rfl⟩ := hj; simp
    · rw [if_neg (by rintro ⟨⟩; exact hj ⟨rfl, rfl⟩), if_neg hj]
  · rw [h2]
    by_cases hj : j = 0 ∧ l = 1
    · obtain ⟨rfl, rfl⟩ := hj; simp
    · rw [if_neg (by rintro ⟨⟩; exact hj ⟨rfl, rfl⟩), if_neg hj]

section Main

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
  {U : Set ℂ} (z z' : Fin (2 * r + k + 1) → ℂ)

/- English proof (translation)
Use `set ζ0 := zetaL k r z z' i g with hζ0`. Establish `h0 : ζ0 ∈ U` using `hDU g hg.2`. Establish `J` using `fun p q => jet_tL z z' hD hU hDU hh hg Y p q`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hJ` using `jet_sub (J 1 0) (jet_sub (jet_val (U := U) (ζ0 := ζ0) (tL k r z z' i Y 1 0 h g)) (jet_dZ (U := U) (ζ0 := ζ0) (tL k r z z' i Y 1 1 h g)))`.

Use `jet_zero hU h0 hJ (fun j l => by beta_reduce` as an intermediate fact. Rewrite using `[lower_left_monomial_action z z' hD hh hg Y j l, (mono_at ζ0 j l).1, (mono_at ζ0 j l).2.1]`. Apply the tactic sequence `split_ifs <;> simp_all) f hf`. Conclude with `sub_eq_zero.mp this`. Establish `hJ` using `jet_sub (J 1 1) (jet_val (U := U) (ζ0 := ζ0) (tL k r z z' i Y 1 1 h g))`.

Use `jet_zero hU h0 hJ (fun j l => by beta_reduce` as an intermediate fact. Rewrite using `[diagonal_monomial_action z z' hD hh hg Y j l, (mono_at ζ0 j l).1]`. Apply the tactic sequence `split_ifs <;> simp_all) f hf`. Conclude with `sub_eq_zero.mp this`. Establish `hJ` using `jet_sub (J 0 1) (jet_add (jet_val (U := U) (ζ0 := ζ0) (tL k r z z' i Y 0 1 h g)) (jet_dZb (U := U) (ζ0 := ζ0) (tL k r z z' i Y 1 1 h g)))`.

Use `jet_zero hU h0 hJ (fun j l => by beta_reduce` as an intermediate fact. Rewrite using `[upper_right_monomial_action z z' hD hh hg Y j l, (mono_at ζ0 j l).1, (mono_at ζ0 j l).2.2]`. Apply the tactic sequence `split_ifs <;> simp_all) f hf`. Conclude with `sub_eq_zero.mp this`.
-/
theorem zeta_smooth_level (hD : IsOpen D) (hU : IsOpen U) (hDU : ∀ g ∈ D, zetaL k r z z' i g ∈ U) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) {h : Mx k r → E} (hh : SmoothLev k r i D h) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (Y : ℂ) :
    tL k r z z' i Y 1 0 (fun y => f (zetaL k r z z' i y) • h y) g =
        f (zetaL k r z z' i g) • tL k r z z' i Y 1 0 h g - dZ f (zetaL k r z z' i g) • tL k r z z' i Y 1 1 h g ∧
    tL k r z z' i Y 1 1 (fun y => f (zetaL k r z z' i y) • h y) g =
        f (zetaL k r z z' i g) • tL k r z z' i Y 1 1 h g ∧
    tL k r z z' i Y 0 1 (fun y => f (zetaL k r z z' i y) • h y) g =
        f (zetaL k r z z' i g) • tL k r z z' i Y 0 1 h g + dZb f (zetaL k r z z' i g) • tL k r z z' i Y 1 1 h g := by
  set ζ0 := zetaL k r z z' i g with hζ0
  have h0 : ζ0 ∈ U := hDU g hg.2
  have J := fun p q => jet_tL z z' hD hU hDU hh hg Y p q
  refine ⟨?_, ?_, ?_⟩
  · have hJ := jet_sub (J 1 0) (jet_sub (jet_val (U := U) (ζ0 := ζ0) (tL k r z z' i Y 1 0 h g))
      (jet_dZ (U := U) (ζ0 := ζ0) (tL k r z z' i Y 1 1 h g)))
    have := jet_zero hU h0 hJ (fun j l => by
      beta_reduce
      rw [lower_left_monomial_action z z' hD hh hg Y j l, (mono_at ζ0 j l).1, (mono_at ζ0 j l).2.1]
      split_ifs <;> simp_all) f hf
    exact sub_eq_zero.mp this
  · have hJ := jet_sub (J 1 1) (jet_val (U := U) (ζ0 := ζ0) (tL k r z z' i Y 1 1 h g))
    have := jet_zero hU h0 hJ (fun j l => by
      beta_reduce
      rw [diagonal_monomial_action z z' hD hh hg Y j l, (mono_at ζ0 j l).1]
      split_ifs <;> simp_all) f hf
    exact sub_eq_zero.mp this
  · have hJ := jet_sub (J 0 1) (jet_add (jet_val (U := U) (ζ0 := ζ0) (tL k r z z' i Y 0 1 h g))
      (jet_dZb (U := U) (ζ0 := ζ0) (tL k r z z' i Y 1 1 h g)))
    have := jet_zero hU h0 hJ (fun j l => by
      beta_reduce
      rw [upper_right_monomial_action z z' hD hh hg Y j l, (mono_at ζ0 j l).1, (mono_at ζ0 j l).2.2]
      split_ifs <;> simp_all) f hf
    exact sub_eq_zero.mp this

end Main

end Formalism.FourierDecayAlt.P.NFx4

end
end

section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.NFx4

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.Qx5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const Complex.continuous_normSq`.
-/
theorem isOpen_normSq_gt (c : ℝ) : IsOpen {w : ℂ | c < Complex.normSq w} :=
  isOpen_lt continuous_const Complex.continuous_normSq

/- English proof (translation)
Introduce `g hg`. Establish `h : 0 < GGl k r z z' g` using `hg`. Unfold `GGl at h`. Use `show Tz k r z * Tz k r z' < Complex.normSq (zetaL k r z z' (Fin.last r) g)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Dp_maps {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) :
    ∀ g ∈ Dp k r z z', zetaL k r z z' (Fin.last r) g ∈ {w : ℂ | Tz k r z * Tz k r z' < Complex.normSq w} := by
  intro g hg
  have h : 0 < GGl k r z z' g := hg
  unfold GGl at h
  show Tz k r z * Tz k r z' < Complex.normSq (zetaL k r z z' (Fin.last r) g)
  linarith

section Act

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Use `LinearMap.ext fun Φ => Subtype.ext (funext fun c => funext fun g => ?_)` and prove the remaining obligations. Distinguish the cases in `hx : (c, g) ∈ DomR k r z z'`. Conclude with `h Φ (c, g) hx`. Rewrite using `[(A Φ).2.1 (c, g) hx, (B Φ).2.1 (c, g) hx]`.
-/
theorem end_ext_dom {A B : Module.End ℂ (RadSp k r z z' π π')}
    (h : ∀ (Φ : RadSp k r z z' π π') (x : (Fin r → ℂ) × Mx k r), x ∈ DomR k r z z' →
      (A Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = (B Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2) : A = B := by
  refine LinearMap.ext fun Φ => Subtype.ext (funext fun c => funext fun g => ?_)
  by_cases hx : (c, g) ∈ DomR k r z z'
  · exact h Φ (c, g) hx
  · rw [(A Φ).2.1 (c, g) hx, (B Φ).2.1 (c, g) hx]

/- English proof (translation)
Rewrite using `[hV Φ, mulZ_eq φ Φ.2]`.
-/
theorem mulZ_apply {V : Module.End ℂ (RadSp k r z z' π π')} {φ : ℂ → ℂ} (hV : IsMulZ V φ)
    (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (g : Mx k r) :
    (V Φ : Fn k r (Wq →L[ℂ] Wp)) c g = φ (zetaL k r z z' (Fin.last r) g) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g := by
  rw [hV Φ, mulZ_eq φ Φ.2]

/- English proof (translation)
Rewrite using `[X.t_apply Y a b _ x hx, hW Φ, mulZ_eq f Φ.2]`.
-/
theorem t_mulZ (X : ActualOps k r z z' π π') {W : Module.End ℂ (RadSp k r z z' π π')} {f : ℂ → ℂ} (hW : IsMulZ W f)
    (Y : ℂ) (a b : Fin 2) (Φ : RadSp k r z z' π π') {x : (Fin r → ℂ) × Mx k r} (hx : x ∈ DomR k r z z') :
    (X.t Y a b (W Φ) : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
      tL k r z z' (Fin.last r) Y a b
        (fun y => f (zetaL k r z z' (Fin.last r) y) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 y) x.2 := by
  rw [X.t_apply Y a b _ x hx, hW Φ, mulZ_eq f Φ.2]

/- English proof (translation)
Establish `hU` using `isOpen_normSq_gt (Tz k r z * Tz k r z')`. Establish `hDU` using `Dp_maps (k := k) (r := r) z z'`. Establish `hD` using `Dp_open k r z z'`. Establish `key` using `fun (Φ : RadSp k r z z' π π') (x : (Fin r → ℂ) × Mx k r) (hx : x ∈ DomR k r z z') => zeta_smooth_level z z' hD hU hDU hf (slice_smooth Φ.2 hx.1) ⟨hx.2.1, hx.2.2⟩ Y`. Use `⟨end_ext_dom fun Φ x hx => ?_, end_ext_dom fun Φ x hx => ?_, end_ext_dom fun Φ x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[Module.End.mul_apply, t_mulZ X hW Y 1 0 Φ hx, (key Φ x hx).1, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, Pi.sub_apply, mulZ_apply hW, mulZ_apply hW₁, X.t_apply Y 1 0 Φ x hx, X.t_apply Y 1 1 Φ x hx]`. Rewrite using `[Module.End.mul_apply, t_mulZ X hW Y 1 1 Φ hx, (key Φ x hx).2.1, Module.End.mul_apply, mulZ_apply hW, X.t_apply Y 1 1 Φ x hx]`. Rewrite using `[Module.End.mul_apply, t_mulZ X hW Y 0 1 Φ hx, (key Φ x hx).2.2, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply, Pi.add_apply, mulZ_apply hW, mulZ_apply hW₂, X.t_apply Y 0 1 Φ x hx, X.t_apply Y 1 1 Φ x hx]`.
-/
theorem actual_zeta_smooth (X : ActualOps k r z z' π π') {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f {w : ℂ | Tz k r z * Tz k r z' < Complex.normSq w})
    {W W₁ W₂ : Module.End ℂ (RadSp k r z z' π π')} (hW : IsMulZ W f) (hW₁ : IsMulZ W₁ (dZ f))
    (hW₂ : IsMulZ W₂ (dZb f)) (Y : ℂ) :
    X.t Y 1 0 * W = W * X.t Y 1 0 - W₁ * X.t Y 1 1 ∧ X.t Y 1 1 * W = W * X.t Y 1 1 ∧
      X.t Y 0 1 * W = W * X.t Y 0 1 + W₂ * X.t Y 1 1 := by
  have hU := isOpen_normSq_gt (Tz k r z * Tz k r z')
  have hDU := Dp_maps (k := k) (r := r) z z'
  have hD := Dp_open k r z z'
  have key := fun (Φ : RadSp k r z z' π π') (x : (Fin r → ℂ) × Mx k r) (hx : x ∈ DomR k r z z') =>
    zeta_smooth_level z z' hD hU hDU hf (slice_smooth Φ.2 hx.1) ⟨hx.2.1, hx.2.2⟩ Y
  refine ⟨end_ext_dom fun Φ x hx => ?_, end_ext_dom fun Φ x hx => ?_, end_ext_dom fun Φ x hx => ?_⟩
  · rw [Module.End.mul_apply, t_mulZ X hW Y 1 0 Φ hx, (key Φ x hx).1, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, Pi.sub_apply, mulZ_apply hW, mulZ_apply hW₁,
      X.t_apply Y 1 0 Φ x hx, X.t_apply Y 1 1 Φ x hx]
  · rw [Module.End.mul_apply, t_mulZ X hW Y 1 1 Φ hx, (key Φ x hx).2.1, Module.End.mul_apply, mulZ_apply hW,
      X.t_apply Y 1 1 Φ x hx]
  · rw [Module.End.mul_apply, t_mulZ X hW Y 0 1 Φ hx, (key Φ x hx).2.2, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.mul_apply, Submodule.coe_add, Pi.add_apply, Pi.add_apply, mulZ_apply hW, mulZ_apply hW₂,
      X.t_apply Y 0 1 Φ x hx, X.t_apply Y 1 1 Φ x hx]

end Act

end Formalism.FourierDecayAlt.P.NFx4

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF Formalism.FourierDecayAlt.P.NFx4

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P z z' π π' hP f hf`. Rewrite `hf` using `[← TT_eq hP]`. Conclude with `⟨mulZEnd hf, isMulZ_mulZEnd hf⟩`.
-/
theorem multiplication_zeta_exists : Formalism.FourierDecayAlt.NF.MulZExists := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' hP f hf
  rw [← TT_eq hP] at hf
  exact ⟨mulZEnd hf, isMulZ_mulZEnd hf⟩

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P z z' π π' hP X f hf W W₁ W₂ hW hW₁ hW₂ Y`. Rewrite `hf` using `[← TT_eq hP]`. Conclude with `actual_zeta_smooth X hf hW hW₁ hW₂ Y`.
-/
theorem actual_zeta_smooth_alt : Formalism.FourierDecayAlt.NF.ActualZetaSmooth := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' hP X f hf W W₁ W₂ hW hW₁ hW₂ Y
  rw [← TT_eq hP] at hf
  exact actual_zeta_smooth X hf hW hW₁ hW₂ Y

end Formalism.FourierDecayAlt.P

end
end

section

open Matrix Finset
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.NFx4.NO

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

/- English proof (translation)
Introduce `e`. Substitute `e` using the available equality. Establish `hl'` using `Finset.mem_Icc.1 hl`. Establish `a` using `h ⟨l - 1, by omega⟩`. Establish `e1 : (l - 1) + 1 = l` using `by omega`.

Simplify using `only [Fin.val_mk, e1, if_true] at a`. Use linear arithmetic over natural numbers and integers.
-/
theorem up_ne {P : M.Par} {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (h : M.Up P l ρ ρ') :
    ρ' ≠ ρ := by
  intro e
  subst e
  have hl' := Finset.mem_Icc.1 hl
  have a := h ⟨l - 1, by omega⟩
  have e1 : (l - 1) + 1 = l := by omega
  simp only [Fin.val_mk, e1, if_true] at a
  omega

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[h i, h' i]`.
-/
theorem up_unique {P : M.Par} {l : ℕ} {ρ τ τ' : M.Ty P} (h : M.Up P l ρ τ) (h' : M.Up P l ρ τ') : τ = τ' := by
  funext i
  apply Fin.ext
  rw [h i, h' i]

/- English proof (translation)
Establish `hl'` using `Finset.mem_Icc.1 hl`. Establish `a` using `h ⟨l - 1, by omega⟩`. Establish `b` using `h' ⟨l - 1, by omega⟩`. Establish `e1 : (l - 1) + 1 = l` using `by omega`. Simplify using `only [Fin.val_mk, e1, if_true] at a b`.

Use `split_ifs at b with hj`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem up_diff {P : M.Par} {l j : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (h : M.Up P l ρ ρ')
    (h' : M.Up P j ρ ρ') : j = l := by
  have hl' := Finset.mem_Icc.1 hl
  have a := h ⟨l - 1, by omega⟩
  have b := h' ⟨l - 1, by omega⟩
  have e1 : (l - 1) + 1 = l := by omega
  simp only [Fin.val_mk, e1, if_true] at a b
  split_ifs at b with hj
  · omega
  · omega

/- English proof (translation)
Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Conclude with `ne_of_gt (Mx3.rho_inj P hP π i j hi hj h)`. Conclude with `ne_of_lt (Mx3.rho_inj P hP π j i hj hi h)`.
-/
theorem rho_ne (P : M.Par) (hP : P.OK) (π : M.Ty P) {i j : ℕ} (hi : i ∈ Finset.Icc 1 (P.k - 1))
    (hj : j ∈ Finset.Icc 1 (P.k - 1)) (hij : i ≠ j) : M.rho P π i ≠ M.rho P π j := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ne_of_gt (Mx3.rho_inj P hP π i j hi hj h)
  · exact ne_of_lt (Mx3.rho_inj P hP π j i hj hi h)

/- English proof (translation)
Establish `h0 : M.xC P ρ (-(M.rho P ρ i : ℂ)) = 0`. Unfold `M.xC`. Conclude with `Finset.prod_eq_zero hi (by ring)`. Establish `h1 : M.xC P σ (-(M.rho P ρ i : ℂ)) ≠ 0`. Unfold `M.xC`.

Use `Finset.prod_ne_zero_iff.2 fun j hj => ?_` and prove the remaining obligations. Establish `hne : M.rho P σ j ≠ M.rho P ρ i`. Break down `lt_trichotomy j i with h | h | h` into its components or cases. Rewrite using `[← hmin j hj h]`. Conclude with `ne_of_gt (Mx3.rho_inj P hP ρ j i hj hi h)`.

Substitute `h` using the available equality. Conclude with `ne_of_lt hlt`. Use `Mx3.rho_inj P hP σ i j hi hj h` as an intermediate fact. Conclude with `ne_of_lt (lt_trans this hlt)`. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Establish `: ((M.rho P σ j : ℝ) : ℂ) = ((M.rho P ρ i : ℝ) : ℂ)` using `by linear_combination h0`. Conclude with `this` after adjusting the coercions. Rewrite using `[h0]`. Conclude with `fun h => h1 h.symm`.
-/
theorem localization_quotient_separated_dvd (P : M.Par) (hP : P.OK) {ρ σ : M.Ty P} {i : ℕ} (hi : i ∈ Finset.Icc 1 (P.k - 1))
    (hlt : M.rho P σ i < M.rho P ρ i)
    (hmin : ∀ m ∈ Finset.Icc 1 (P.k - 1), m < i → M.rho P ρ m = M.rho P σ m) :
    M.xC P ρ (-(M.rho P ρ i : ℂ)) ≠ M.xC P σ (-(M.rho P ρ i : ℂ)) := by
  have h0 : M.xC P ρ (-(M.rho P ρ i : ℂ)) = 0 := by
    unfold M.xC
    exact Finset.prod_eq_zero hi (by ring)
  have h1 : M.xC P σ (-(M.rho P ρ i : ℂ)) ≠ 0 := by
    unfold M.xC
    refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
    have hne : M.rho P σ j ≠ M.rho P ρ i := by
      rcases lt_trichotomy j i with h | h | h
      · rw [← hmin j hj h]
        exact ne_of_gt (Mx3.rho_inj P hP ρ j i hj hi h)
      · subst h; exact ne_of_lt hlt
      · have := Mx3.rho_inj P hP σ i j hi hj h
        exact ne_of_lt (lt_trans this hlt)
    intro h0
    apply hne
    have : ((M.rho P σ j : ℝ) : ℂ) = ((M.rho P ρ i : ℝ) : ℂ) := by linear_combination h0
    exact_mod_cast this
  rw [h0]
  exact fun h => h1 h.symm

/- English proof (translation)
Establish `hex : ∃ i, i ∈ Finset.Icc 1 (P.k - 1) ∧ M.rho P ρ i ≠ M.rho P σ i`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h ((Mx3.tyComplete P hP).2 ρ σ hc)`. Set `i` to `Nat.find hex`.

Establish `hi : i ∈ Finset.Icc 1 (P.k - 1) ∧ M.rho P ρ i ≠ M.rho P σ i` using `Nat.find_spec hex`. Establish `hmin : ∀ m ∈ Finset.Icc 1 (P.k - 1), m < i → M.rho P ρ m = M.rho P σ m`. Introduce `m hm hmi`. Assume the negation of the conclusion as `hc`. Conclude with `Nat.find_min hex hmi ⟨hm, hc⟩`.

Break down `lt_or_gt_of_ne hi.2 with hl | hl` into its components or cases. Conclude with `⟨_, fun e => localization_quotient_separated_dvd P hP hi.1 hl (fun m hm hmi => (hmin m hm hmi).symm) e.symm⟩`. Conclude with `⟨_, localization_quotient_separated_dvd P hP hi.1 hl hmin⟩`.
-/
theorem sep (P : M.Par) (hP : P.OK) {ρ σ : M.Ty P} (h : ρ ≠ σ) : ∃ Y : ℂ, M.xC P ρ Y ≠ M.xC P σ Y := by
  classical
  have hex : ∃ i, i ∈ Finset.Icc 1 (P.k - 1) ∧ M.rho P ρ i ≠ M.rho P σ i := by
    by_contra hc
    push_neg at hc
    exact h ((Mx3.tyComplete P hP).2 ρ σ hc)
  let i := Nat.find hex
  have hi : i ∈ Finset.Icc 1 (P.k - 1) ∧ M.rho P ρ i ≠ M.rho P σ i := Nat.find_spec hex
  have hmin : ∀ m ∈ Finset.Icc 1 (P.k - 1), m < i → M.rho P ρ m = M.rho P σ m := by
    intro m hm hmi
    by_contra hc
    exact Nat.find_min hex hmi ⟨hm, hc⟩
  rcases lt_or_gt_of_ne hi.2 with hl | hl
  · exact ⟨_, fun e => localization_quotient_separated_dvd P hP hi.1 hl (fun m hm hmi => (hmin m hm hmi).symm) e.symm⟩
  · exact ⟨_, localization_quotient_separated_dvd P hP hi.1 hl hmin⟩

/- English proof (translation)
Set `S : Subalgebra ℂ (T → ℂ)` to `{ carrier := {g | Commute (κ g) w} mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, map_mul] at *`. Conclude with `ha.mul_left hb`. Use the proof step `add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, map_add] at *`.

Conclude with `ha.add_left hb`. Use the proof step `algebraMap_mem' := fun c => by`. Simplify using `only [Set.mem_setOf_eq, AlgHom.commutes]`. Conclude with `Algebra.commutes c w }`. Establish `hS : ∀ g, g ∈ S ↔ Commute (κ g) w` using `fun g => Iff.rfl`.

Establish `hsep' : ∀ ρ σ : T, ∃ Y, ρ ≠ σ → e Y ρ ≠ e Y σ`. Introduce `ρ σ`. Distinguish the cases in `h : ρ = σ`. Conclude with `⟨0, fun h' => (h' h).elim⟩`. Take `⟨Y, hY⟩` from `hsep ρ σ h`.

Conclude with `⟨Y, fun _ => hY⟩`. Use `choose Yf hYf using hsep'`. Set `F : T → T → (T → ℂ)` to `fun ρ σ => (e (Yf ρ σ) - algebraMap ℂ (T → ℂ) (e (Yf ρ σ) σ)) * algebraMap ℂ (T → ℂ) ((e (Yf ρ σ) ρ - e (Yf ρ σ) σ)⁻¹)`. Establish `hF : ∀ ρ σ, F ρ σ ∈ S` using `fun ρ σ => S.mul_mem (S.sub_mem ((hS _).2 (he _)) (S.algebraMap_mem _)) (S.algebraMap_mem _)`. Set `δ : T → (T → ℂ)` to `fun ρ => ∏ σ ∈ Finset.univ.erase ρ, F ρ σ`.

Establish `hδS : ∀ ρ, δ ρ ∈ S` using `fun ρ => Subalgebra.prod_mem S fun σ _ => hF ρ σ`. Establish `hδ : ∀ ρ τ, δ ρ τ = if τ = ρ then 1 else 0`. Introduce `ρ τ`. Simplify using `only [δ, F, Finset.prod_apply, Pi.mul_apply, Pi.sub_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Use `split_ifs with hτ`.

Substitute `hτ` using the available equality. Use `Finset.prod_eq_one fun σ hσ => ?_` and prove the remaining obligations. Establish `hne : τ ≠ σ` using `(Finset.ne_of_mem_erase hσ).symm`. Conclude with `mul_inv_cancel₀ (sub_ne_zero.2 (hYf τ σ hne))`. Conclude with `Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hτ, Finset.mem_univ τ⟩) (by ring)`.

Establish `hg : g = ∑ ρ, g ρ • δ ρ`. Use function extensionality and compare the values at `τ`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, hδ, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules.

Establish `: g ∈ S`. Rewrite using `[hg]`. Conclude with `Subalgebra.sum_mem S fun ρ _ => Subalgebra.smul_mem S (hδS ρ) _`. Conclude with `this`.
-/
theorem comm_of_sep {T : Type} [Fintype T] [DecidableEq T] {A : Type} [Ring A] [Algebra ℂ A]
    (κ : (T → ℂ) →ₐ[ℂ] A) (w : A) (e : ℂ → T → ℂ)
    (hsep : ∀ ρ σ : T, ρ ≠ σ → ∃ Y, e Y ρ ≠ e Y σ) (he : ∀ Y, Commute (κ (e Y)) w) (g : T → ℂ) :
    Commute (κ g) w := by
  classical
  let S : Subalgebra ℂ (T → ℂ) :=
    { carrier := {g | Commute (κ g) w}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul] at *
        exact ha.mul_left hb
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at *
        exact ha.add_left hb
      algebraMap_mem' := fun c => by
        simp only [Set.mem_setOf_eq, AlgHom.commutes]
        exact Algebra.commutes c w }
  have hS : ∀ g, g ∈ S ↔ Commute (κ g) w := fun g => Iff.rfl
  have hsep' : ∀ ρ σ : T, ∃ Y, ρ ≠ σ → e Y ρ ≠ e Y σ := by
    intro ρ σ
    by_cases h : ρ = σ
    · exact ⟨0, fun h' => (h' h).elim⟩
    · obtain ⟨Y, hY⟩ := hsep ρ σ h
      exact ⟨Y, fun _ => hY⟩
  choose Yf hYf using hsep'
  let F : T → T → (T → ℂ) := fun ρ σ =>
    (e (Yf ρ σ) - algebraMap ℂ (T → ℂ) (e (Yf ρ σ) σ)) * algebraMap ℂ (T → ℂ) ((e (Yf ρ σ) ρ - e (Yf ρ σ) σ)⁻¹)
  have hF : ∀ ρ σ, F ρ σ ∈ S := fun ρ σ =>
    S.mul_mem (S.sub_mem ((hS _).2 (he _)) (S.algebraMap_mem _)) (S.algebraMap_mem _)
  let δ : T → (T → ℂ) := fun ρ => ∏ σ ∈ Finset.univ.erase ρ, F ρ σ
  have hδS : ∀ ρ, δ ρ ∈ S := fun ρ => Subalgebra.prod_mem S fun σ _ => hF ρ σ
  have hδ : ∀ ρ τ, δ ρ τ = if τ = ρ then 1 else 0 := by
    intro ρ τ
    simp only [δ, F, Finset.prod_apply, Pi.mul_apply, Pi.sub_apply, Pi.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    split_ifs with hτ
    · subst hτ
      refine Finset.prod_eq_one fun σ hσ => ?_
      have hne : τ ≠ σ := (Finset.ne_of_mem_erase hσ).symm
      exact mul_inv_cancel₀ (sub_ne_zero.2 (hYf τ σ hne))
    · exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hτ, Finset.mem_univ τ⟩) (by ring)
  have hg : g = ∑ ρ, g ρ • δ ρ := by
    funext τ
    simp only [Finset.sum_apply, Pi.smul_apply, hδ, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  have : g ∈ S := by
    rw [hg]
    exact Subalgebra.sum_mem S fun ρ _ => Subalgebra.smul_mem S (hδS ρ) _
  exact this

/- English proof (translation)
Establish `h1 : ContDiffOn ℝ ∞ (fun ζ => fderiv ℝ g ζ) U` using `hg.fderiv_of_isOpen hU (by simp)`. Conclude with `h1.clm_apply contDiffOn_const`.
-/
theorem fderiv_apply_smooth {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (v : ℂ) :
    ContDiffOn ℝ ∞ (fun ζ => fderiv ℝ g ζ v) U := by
  have h1 : ContDiffOn ℝ ∞ (fun ζ => fderiv ℝ g ζ) U := hg.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply contDiffOn_const

/- English proof (translation)
Unfold `NF.dZ`. Conclude with `contDiffOn_const.mul ((fderiv_apply_smooth hU hg 1).sub (contDiffOn_const.mul (fderiv_apply_smooth hU hg Complex.I)))`.
-/
theorem dZ_smooth {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (NF.dZ g) U := by
  unfold NF.dZ
  exact contDiffOn_const.mul ((fderiv_apply_smooth hU hg 1).sub
    (contDiffOn_const.mul (fderiv_apply_smooth hU hg Complex.I)))

/- English proof (translation)
Unfold `NF.dZb`. Conclude with `contDiffOn_const.mul ((fderiv_apply_smooth hU hg 1).add (contDiffOn_const.mul (fderiv_apply_smooth hU hg Complex.I)))`.
-/
theorem dZb_smooth {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (NF.dZb g) U := by
  unfold NF.dZb
  exact contDiffOn_const.mul ((fderiv_apply_smooth hU hg 1).add
    (contDiffOn_const.mul (fderiv_apply_smooth hU hg Complex.I)))

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const Complex.continuous_normSq`.
-/
theorem isOpen_U (t : ℝ) : IsOpen {ζ : ℂ | t < Complex.normSq ζ} :=
  isOpen_lt continuous_const Complex.continuous_normSq

section Pair

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def fstA (V : Type) [AddCommGroup V] [Module ℂ V] : Q.Pr V →ₐ[ℂ] Module.End ℂ V where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fstA_apply (a : Q.Pr V) : fstA V a = a.1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fst_mul (a b : Q.Pr V) : (a * b).1 = a.1 * b.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fst_add (a b : Q.Pr V) : (a + b).1 = a.1 + b.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fst_sub (a b : Q.Pr V) : (a - b).1 = a.1 - b.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fst_neg (a : Q.Pr V) : (-a).1 = -a.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fst_one : (1 : Q.Pr V).1 = 1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fst_zero : (0 : Q.Pr V).1 = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fst_alg (c : ℂ) : (algebraMap ℂ (Q.Pr V) c).1 = algebraMap ℂ (Module.End ℂ V) c := rfl
/- English proof (translation)
Rewrite using `[Algebra.smul_def, fst_mul, fst_alg, ← Algebra.smul_def]`.
-/
theorem fst_smul (c : ℂ) (a : Q.Pr V) : (c • a).1 = c • a.1 := by
  rw [Algebra.smul_def, fst_mul, fst_alg, ← Algebra.smul_def]
/- English proof (translation)
The claim follows from `map_sum (fstA V) f s`.
-/
theorem fst_sum {ι : Type} (s : Finset ι) (f : ι → Q.Pr V) : (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 :=
  map_sum (fstA V) f s
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fst_mkP (A B : Module.End ℂ V) : (Q.mkP A B).1 = A := rfl

end Pair

section RingLem

variable {R : Type} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] [NoZeroSMulDivisors ℂ R]

/- English proof (translation)
Establish `e : c • (B * W) = c • (W * B)`. Rewrite using `[← smul_mul_assoc, ← hE, ← mul_smul_comm, ← hE]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `smul_right_injective R hc e`.
-/
theorem blk {c : ℂ} (hc : c ≠ 0) {Q1 Q2 T T22 W U B : R} (hE : Q1 * T * Q2 = c • B) (h22 : T22 * Q2 = 0)
    (hcomm : T * W = W * T + U * T22) (h1 : Q1 * W = W * Q1) (h2 : Q2 * W = W * Q2) : B * W = W * B := by
  have e : c • (B * W) = c • (W * B) := by
    rw [← smul_mul_assoc, ← hE, ← mul_smul_comm, ← hE]
    calc Q1 * T * Q2 * W = Q1 * (T * W) * Q2 := by rw [mul_assoc (Q1 * T), h2]; simp only [mul_assoc]
      _ = Q1 * (W * T + U * T22) * Q2 := by rw [hcomm]
      _ = (Q1 * W) * T * Q2 + Q1 * U * (T22 * Q2) := by simp only [mul_add, add_mul, mul_assoc]
      _ = W * (Q1 * T * Q2) := by rw [h22, h1]; simp only [mul_zero, add_zero, mul_assoc]
  exact smul_right_injective R hc e

/- English proof (translation)
Establish `e0 : Pp * T * Pp * W = W * (Pp * T * Pp) + U * (Pp * T22 * Pp)`. Combine the equalities or inequalities in the displayed calculation. Establish `e1 : c • (G * L * Pp * W) = c • (W * (G * L * Pp) + U * (G * Pp))`. Rewrite `e0` using `[hE, h22, smul_mul_assoc, mul_smul_comm, mul_smul_comm, ← smul_add]`. Conclude with `e0`.

Establish `e2` using `smul_right_injective R hc e1`. Establish `e3 : G * ((L * W - W * L) * Pp) = G * (U * Pp)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [sub_mul, mul_sub, mul_assoc]`. Rewrite using `[hPW, ← mul_assoc W G, ← hGW]`.

Simplify using `only [mul_assoc]`. Use `_ = U * (G * Pp) := by rw [e2]; abel`. Use `_ = G * (U * Pp) := by rw [← mul_assoc, ← hGU, mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem diag {c : ℂ} (hc : c ≠ 0) {Pp T T22 W U G L Gi : R} (hE : Pp * T * Pp = c • (G * L * Pp))
    (h22 : Pp * T22 * Pp = c • (G * Pp)) (hcomm : T * W = W * T + U * T22) (hPW : Pp * W = W * Pp)
    (hPU : Pp * U = U * Pp) (hGW : G * W = W * G) (hGU : G * U = U * G) (hGi : Gi * G = 1) :
    (L * W - W * L) * Pp = U * Pp := by
  have e0 : Pp * T * Pp * W = W * (Pp * T * Pp) + U * (Pp * T22 * Pp) := by
    calc Pp * T * Pp * W = Pp * (T * W) * Pp := by rw [mul_assoc (Pp * T), hPW]; simp only [mul_assoc]
      _ = Pp * (W * T + U * T22) * Pp := by rw [hcomm]
      _ = (Pp * W) * T * Pp + (Pp * U) * T22 * Pp := by simp only [mul_add, add_mul, mul_assoc]
      _ = W * (Pp * T * Pp) + U * (Pp * T22 * Pp) := by rw [hPW, hPU]; simp only [mul_assoc]
  have e1 : c • (G * L * Pp * W) = c • (W * (G * L * Pp) + U * (G * Pp)) := by
    rw [hE, h22, smul_mul_assoc, mul_smul_comm, mul_smul_comm, ← smul_add] at e0
    exact e0
  have e2 := smul_right_injective R hc e1
  have e3 : G * ((L * W - W * L) * Pp) = G * (U * Pp) := by
    calc G * ((L * W - W * L) * Pp) = G * L * Pp * W - W * (G * L * Pp) := by
          simp only [sub_mul, mul_sub, mul_assoc]
          rw [hPW, ← mul_assoc W G, ← hGW]
          simp only [mul_assoc]
      _ = U * (G * Pp) := by rw [e2]; abel
      _ = G * (U * Pp) := by rw [← mul_assoc, ← hGU, mul_assoc]
  calc (L * W - W * L) * Pp = Gi * G * ((L * W - W * L) * Pp) := by rw [hGi, one_mul]
    _ = Gi * G * (U * Pp) := by rw [mul_assoc, e3, ← mul_assoc]
    _ = U * Pp := by rw [hGi, one_mul]

end RingLem

section Blocks

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A)

noncomputable def Pj (ρ : M.Ty P) : A := d.κ fun ρ' => if ρ' = ρ then 1 else 0

/- English proof (translation)
Unfold `Pj`. Rewrite using `[← map_mul, ← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Simplify using `only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]`.

Use `split_ifs with hτ`. Substitute `hτ` using the available equality. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kap_Pj (h : M.Ty P → ℂ) (ρ : M.Ty P) : d.κ h * Pj d ρ = h ρ • Pj d ρ := by
  unfold Pj
  rw [← map_mul, ← map_smul]
  congr 1
  funext τ
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with hτ
  · subst hτ; ring
  · ring

/- English proof (translation)
Rewrite using `[← map_mul, ← map_mul, mul_comm]`.
-/
theorem kap_comm (h h' : M.Ty P → ℂ) : d.κ h * d.κ h' = d.κ h' * d.κ h := by
  rw [← map_mul, ← map_mul, mul_comm]

/- English proof (translation)
Rewrite using `[show Pj d ρ * d.κ h = d.κ h * Pj d ρ from kap_comm d _ _]`. Conclude with `kap_Pj d h ρ`.
-/
theorem Pj_kap (h : M.Ty P → ℂ) (ρ : M.Ty P) : Pj d ρ * d.κ h = h ρ • Pj d ρ := by
  rw [show Pj d ρ * d.κ h = d.κ h * Pj d ρ from kap_comm d _ _]
  exact kap_Pj d h ρ

/- English proof (translation)
Rewrite using `[show Pj d σ = d.κ fun ρ' => if ρ' = σ then 1 else 0 from rfl, Pj_kap]`. Simplify using `[h]`.
-/
theorem Pj_mul_ne {ρ σ : M.Ty P} (h : ρ ≠ σ) : Pj d ρ * Pj d σ = 0 := by
  rw [show Pj d σ = d.κ fun ρ' => if ρ' = σ then 1 else 0 from rfl, Pj_kap]
  simp [h]

/- English proof (translation)
Rewrite using `[show Pj d ρ * Pj d ρ = Pj d ρ * d.κ fun ρ' => if ρ' = ρ then 1 else 0 from rfl, Pj_kap]`. Simplify using the standard rewrite rules.
-/
theorem Pj_idem (ρ : M.Ty P) : Pj d ρ * Pj d ρ = Pj d ρ := by
  rw [show Pj d ρ * Pj d ρ = Pj d ρ * d.κ fun ρ' => if ρ' = ρ then 1 else 0 from rfl, Pj_kap]
  simp

/- English proof (translation)
Unfold `Pj`. Rewrite using `[← map_sum, ← map_one d.κ]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Simplify using `only [Finset.sum_apply, Pi.one_apply]`.

Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules.
-/
theorem sum_Pj : ∑ ρ, Pj d ρ = 1 := by
  unfold Pj
  rw [← map_sum, ← map_one d.κ]
  congr 1
  funext τ
  simp only [Finset.sum_apply, Pi.one_apply]
  rw [Finset.sum_ite_eq]
  simp

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem decomp (a : A) : a = ∑ ρ', ∑ ρ, Pj d ρ' * a * Pj d ρ := by
  calc a = (∑ ρ', Pj d ρ') * a * (∑ ρ, Pj d ρ) := by rw [sum_Pj, one_mul, mul_one]
    _ = _ := by simp only [Finset.sum_mul, Finset.mul_sum]; exact Finset.sum_comm

/- English proof (translation)
The claim follows from `(h _).eq`.
-/
theorem comm_Pj_of {a : A} (h : ∀ f : M.Ty P → ℂ, Commute (d.κ f) a) (ρ : M.Ty P) : Pj d ρ * a = a * Pj d ρ :=
  (h _).eq

variable {d}

/- English proof (translation)
The claim follows from `hRel.2.1 f g hg`.
-/
theorem kap_comm_fn (hRel : d.Rel) (f : M.Ty P → ℂ) {g : A} (hg : g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs}) :
    Commute (d.κ f) g := hRel.2.1 f g hg

/- English proof (translation)
The claim follows from `kap_comm_fn hRel f (Or.inl (by simp [R.LevelData.fns]))`.
-/
theorem kap_GG (hRel : d.Rel) (f : M.Ty P → ℂ) : Commute (d.κ f) d.L.GG :=
  kap_comm_fn hRel f (Or.inl (by simp [R.LevelData.fns]))

/- English proof (translation)
Unfold `R.LevelData.l0`. Establish `h1 : Commute (d.κ f) d.L.nab` using `kap_comm_fn hRel f (Or.inr (by simp))`. Establish `h2 : Commute (d.κ f) d.L.ζb` using `kap_comm_fn hRel f (Or.inl (by simp [R.LevelData.fns]))`. Establish `h3 : Commute (d.κ f) d.L.GGi` using `kap_comm_fn hRel f (Or.inl (by simp [R.LevelData.fns]))`. Conclude with `h1.neg_right.sub_right ((Algebra.commute_algebraMap_left _ _).symm.mul_right (h2.mul_right h3))`.
-/
theorem kappa_commute_l0 (hRel : d.Rel) (f : M.Ty P → ℂ) (Y : ℂ) : Commute (d.κ f) (d.L.l0 Y) := by
  unfold R.LevelData.l0
  have h1 : Commute (d.κ f) d.L.nab := kap_comm_fn hRel f (Or.inr (by simp))
  have h2 : Commute (d.κ f) d.L.ζb := kap_comm_fn hRel f (Or.inl (by simp [R.LevelData.fns]))
  have h3 : Commute (d.κ f) d.L.GGi := kap_comm_fn hRel f (Or.inl (by simp [R.LevelData.fns]))
  exact h1.neg_right.sub_right ((Algebra.commute_algebraMap_left _ _).symm.mul_right (h2.mul_right h3))

/- English proof (translation)
Unfold `R.LevelData.m0`. Establish `h1 : Commute (d.κ f) d.L.nabs` using `kap_comm_fn hRel f (Or.inr (by simp))`. Establish `h2 : Commute (d.κ f) d.L.ζ` using `kap_comm_fn hRel f (Or.inl (by simp [R.LevelData.fns]))`. Establish `h3 : Commute (d.κ f) d.L.GGi` using `kap_comm_fn hRel f (Or.inl (by simp [R.LevelData.fns]))`. Conclude with `h1.neg_right.sub_right ((Algebra.commute_algebraMap_left _ _).symm.mul_right (h2.mul_right h3))`.
-/
theorem kappa_commute_raising_constant (hRel : d.Rel) (f : M.Ty P → ℂ) (Y : ℂ) : Commute (d.κ f) (d.L.m0 Y) := by
  unfold R.LevelData.m0
  have h1 : Commute (d.κ f) d.L.nabs := kap_comm_fn hRel f (Or.inr (by simp))
  have h2 : Commute (d.κ f) d.L.ζ := kap_comm_fn hRel f (Or.inl (by simp [R.LevelData.fns]))
  have h3 : Commute (d.κ f) d.L.GGi := kap_comm_fn hRel f (Or.inl (by simp [R.LevelData.fns]))
  exact h1.neg_right.sub_right ((Algebra.commute_algebraMap_left _ _).symm.mul_right (h2.mul_right h3))

/- English proof (translation)
Simplify using `[Q.NFData.QQ]`.
-/
theorem normal_form_lower_left (Y : ℂ) : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := by simp [Q.NFData.QQ]
/- English proof (translation)
Simplify using `[Q.NFData.QQ]`.
-/
theorem normal_form_upper_right (Y : ℂ) : d.QQ Y 0 1 = d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y := by simp [Q.NFData.QQ]
/- English proof (translation)
Simplify using `[Q.NFData.QQ]`.
-/
theorem normal_form_diagonal (Y : ℂ) : d.QQ Y 1 1 = d.L.GG * d.x Y := by simp [Q.NFData.QQ]

/- English proof (translation)
Establish `hr` using `hRel.2.2.2.1 l (fun σ => if M.Up P l σ ρ' then 1 else 0) (fun τ => if τ = ρ' then 1 else 0) (by`. Introduce `σ τ hστ`. Distinguish the cases in `hτ : τ = ρ'`. Substitute `hτ` using the available equality. Simplify using `[hστ]`.

Establish `: ¬ M.Up P l σ ρ'` using `fun h' => hτ (NO.up_unique hστ h')`. Simplify using `[hτ, this])`. Use `show (d.κ fun τ => if τ = ρ' then (1 : ℂ) else 0) * d.SS l * Pj d ρ = 0`. Rewrite using `[hr, mul_assoc, kap_Pj]`. Simplify using `[h]`.
-/
theorem block_zero (hRel : d.Rel) {l : ℕ} {ρ ρ' : M.Ty P} (h : ¬ M.Up P l ρ ρ') :
    Pj d ρ' * d.SS l * Pj d ρ = 0 := by
  classical
  have hr := hRel.2.2.2.1 l (fun σ => if M.Up P l σ ρ' then 1 else 0) (fun τ => if τ = ρ' then 1 else 0) (by
    intro σ τ hστ
    by_cases hτ : τ = ρ'
    · subst hτ; simp [hστ]
    · have : ¬ M.Up P l σ ρ' := fun h' => hτ (NO.up_unique hστ h')
      simp [hτ, this])
  show (d.κ fun τ => if τ = ρ' then (1 : ℂ) else 0) * d.SS l * Pj d ρ = 0
  rw [hr, mul_assoc, kap_Pj]
  simp [h]

/- English proof (translation)
Unfold `Pj`. Rewrite using `[hRel.1]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Pj_star (hRel : d.Rel) (ρ : M.Ty P) : star (Pj d ρ) = Pj d ρ := by
  unfold Pj
  rw [hRel.1]
  congr 1
  funext τ
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[star_mul, star_mul, Pj_star hRel, Pj_star hRel, mul_assoc]`.
-/
theorem star_block (hRel : d.Rel) (l : ℕ) (ρ ρ' : M.Ty P) :
    Pj d ρ * star (d.SS l) * Pj d ρ' = star (Pj d ρ' * d.SS l * Pj d ρ) := by
  rw [star_mul, star_mul, Pj_star hRel, Pj_star hRel, mul_assoc]

/- English proof (translation)
Rewrite using `[star_block hRel, block_zero hRel h, star_zero]`.
-/
theorem star_block_zero (hRel : d.Rel) {l : ℕ} {ρ ρ' : M.Ty P} (h : ¬ M.Up P l ρ ρ') :
    Pj d ρ * star (d.SS l) * Pj d ρ' = 0 := by
  rw [star_block hRel, block_zero hRel h, star_zero]

/- English proof (translation)
The claim follows from `kap_Pj d _ ρ`.
-/
theorem x_Pj (Y : ℂ) (ρ : M.Ty P) : d.x Y * Pj d ρ = M.xC P ρ Y • Pj d ρ := kap_Pj d _ ρ

/- English proof (translation)
Rewrite using `[mul_assoc, ← comm_Pj_of d hB ρ, ← mul_assoc, Pj_mul_ne d hne, zero_mul]`.
-/
theorem mid_zero {ρ ρ' : M.Ty P} (hne : ρ' ≠ ρ) {B : A} (hB : ∀ f, Commute (d.κ f) B) :
    Pj d ρ' * B * Pj d ρ = 0 := by
  rw [mul_assoc, ← comm_Pj_of d hB ρ, ← mul_assoc, Pj_mul_ne d hne, zero_mul]

/- English proof (translation)
The claim follows from `((kap_GG hRel f).mul_right (kap_comm d f _)).mul_right (hB f)`.
-/
theorem GxB_comm (hRel : d.Rel) (Y : ℂ) {B : A} (hB : ∀ f, Commute (d.κ f) B) (f : M.Ty P → ℂ) :
    Commute (d.κ f) (d.L.GG * d.x Y * B) :=
  ((kap_GG hRel f).mul_right (kap_comm d f _)).mul_right (hB f)

/- English proof (translation)
Rewrite using `[normal_form_lower_left, mul_add, add_mul, mid_zero (NO.up_ne hl hU) (GxB_comm hRel Y (fun f => kappa_commute_l0 hRel f Y)), zero_add]`. Unfold `Q.NFData.weightedSumBis`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_eq_single l]`. Rewrite using `[mul_assoc (Pj d ρ'), mul_assoc (d.SS l), kap_Pj, mul_smul_comm, mul_smul_comm, ← mul_assoc]`.

Introduce `j _ hjl`. Establish `: ¬ M.Up P j ρ ρ'` using `fun h => hjl (NO.up_diff hl hU h)`. Rewrite using `[mul_assoc (Pj d ρ'), mul_assoc (d.SS j), kap_Pj, mul_smul_comm, mul_smul_comm, ← mul_assoc, block_zero hRel this, smul_zero]`. Introduce `h`. Conclude with `absurd hl h`.
-/
theorem B1 (hRel : d.Rel) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (hU : M.Up P l ρ ρ') (Y : ℂ) :
    Pj d ρ' * d.QQ Y 1 0 * Pj d ρ = M.xEx P {l} ρ Y • (Pj d ρ' * d.SS l * Pj d ρ) := by
  classical
  rw [normal_form_lower_left, mul_add, add_mul, mid_zero (NO.up_ne hl hU) (GxB_comm hRel Y (fun f => kappa_commute_l0 hRel f Y)), zero_add]
  unfold Q.NFData.weightedSumBis
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_eq_single l]
  · rw [mul_assoc (Pj d ρ'), mul_assoc (d.SS l), kap_Pj, mul_smul_comm, mul_smul_comm, ← mul_assoc]
  · intro j _ hjl
    have : ¬ M.Up P j ρ ρ' := fun h => hjl (NO.up_diff hl hU h)
    rw [mul_assoc (Pj d ρ'), mul_assoc (d.SS j), kap_Pj, mul_smul_comm, mul_smul_comm, ← mul_assoc,
      block_zero hRel this, smul_zero]
  · intro h; exact absurd hl h

/- English proof (translation)
Rewrite using `[normal_form_upper_right, mul_add, add_mul, mid_zero (NO.up_ne hl hU).symm (GxB_comm hRel Y (fun f => kappa_commute_raising_constant hRel f Y)), zero_add]`. Unfold `Q.NFData.S12`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_eq_single l]`. Rewrite using `[← mul_assoc (Pj d ρ), Pj_kap, smul_mul_assoc, smul_mul_assoc]`.

Introduce `j _ hjl`. Establish `: ¬ M.Up P j ρ ρ'` using `fun h => hjl (NO.up_diff hl hU h)`. Rewrite using `[← mul_assoc (Pj d ρ), Pj_kap, smul_mul_assoc, smul_mul_assoc, star_block_zero hRel this, smul_zero]`. Introduce `h`. Conclude with `absurd hl h`.
-/
theorem B4 (hRel : d.Rel) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (hU : M.Up P l ρ ρ') (Y : ℂ) :
    Pj d ρ * d.QQ Y 0 1 * Pj d ρ' = M.xEx P {l} ρ Y • (Pj d ρ * star (d.SS l) * Pj d ρ') := by
  classical
  rw [normal_form_upper_right, mul_add, add_mul, mid_zero (NO.up_ne hl hU).symm (GxB_comm hRel Y (fun f => kappa_commute_raising_constant hRel f Y)), zero_add]
  unfold Q.NFData.S12
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_eq_single l]
  · rw [← mul_assoc (Pj d ρ), Pj_kap, smul_mul_assoc, smul_mul_assoc]
  · intro j _ hjl
    have : ¬ M.Up P j ρ ρ' := fun h => hjl (NO.up_diff hl hU h)
    rw [← mul_assoc (Pj d ρ), Pj_kap, smul_mul_assoc, smul_mul_assoc, star_block_zero hRel this, smul_zero]
  · intro h; exact absurd hl h

/- English proof (translation)
Unfold `Q.NFData.weightedSumBis`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Establish `: ¬ M.Up P j ρ ρ` using `fun h => NO.up_ne hj h rfl`. Rewrite using `[mul_assoc (Pj d ρ), mul_assoc (d.SS j), kap_Pj, mul_smul_comm, mul_smul_comm, ← mul_assoc, block_zero hRel this, smul_zero]`.
-/
theorem lower_sum_diagonal_zero (hRel : d.Rel) (Y : ℂ) (ρ : M.Ty P) : Pj d ρ * d.weightedSumBis Y * Pj d ρ = 0 := by
  unfold Q.NFData.weightedSumBis
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun j hj => ?_
  have : ¬ M.Up P j ρ ρ := fun h => NO.up_ne hj h rfl
  rw [mul_assoc (Pj d ρ), mul_assoc (d.SS j), kap_Pj, mul_smul_comm, mul_smul_comm, ← mul_assoc,
    block_zero hRel this, smul_zero]

/- English proof (translation)
Unfold `Q.NFData.S12`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Establish `: ¬ M.Up P j ρ ρ` using `fun h => NO.up_ne hj h rfl`. Rewrite using `[← mul_assoc (Pj d ρ), Pj_kap, smul_mul_assoc, smul_mul_assoc, star_block_zero hRel this, smul_zero]`.
-/
theorem upper_sum_diagonal_zero (hRel : d.Rel) (Y : ℂ) (ρ : M.Ty P) : Pj d ρ * d.S12 Y * Pj d ρ = 0 := by
  unfold Q.NFData.S12
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun j hj => ?_
  have : ¬ M.Up P j ρ ρ := fun h => NO.up_ne hj h rfl
  rw [← mul_assoc (Pj d ρ), Pj_kap, smul_mul_assoc, smul_mul_assoc, star_block_zero hRel this, smul_zero]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[comm_Pj_of d (GxB_comm hRel Y hB) ρ]`. Simplify using `only [mul_assoc]`. Use `_ = d.L.GG * d.x Y * B * Pj d ρ := by rw [Pj_idem]`. Use `_ = d.L.GG * (d.x Y * Pj d ρ) * B := by`.

Rewrite using `[mul_assoc (d.L.GG * d.x Y) B, ← comm_Pj_of d hB ρ]`. Simplify using `only [mul_assoc]`. Use `_ = M.xC P ρ Y • (d.L.GG * B * Pj d ρ) := by`. Rewrite using `[x_Pj, mul_smul_comm, smul_mul_assoc, mul_assoc d.L.GG (Pj d ρ) B, comm_Pj_of d hB ρ, ← mul_assoc]`.
-/
theorem diag_GxB (hRel : d.Rel) (Y : ℂ) (ρ : M.Ty P) {B : A} (hB : ∀ f, Commute (d.κ f) B) :
    Pj d ρ * (d.L.GG * d.x Y * B) * Pj d ρ = M.xC P ρ Y • (d.L.GG * B * Pj d ρ) := by
  calc Pj d ρ * (d.L.GG * d.x Y * B) * Pj d ρ = d.L.GG * d.x Y * B * (Pj d ρ * Pj d ρ) := by
        rw [comm_Pj_of d (GxB_comm hRel Y hB) ρ]; simp only [mul_assoc]
    _ = d.L.GG * d.x Y * B * Pj d ρ := by rw [Pj_idem]
    _ = d.L.GG * (d.x Y * Pj d ρ) * B := by
        rw [mul_assoc (d.L.GG * d.x Y) B, ← comm_Pj_of d hB ρ]; simp only [mul_assoc]
    _ = M.xC P ρ Y • (d.L.GG * B * Pj d ρ) := by
        rw [x_Pj, mul_smul_comm, smul_mul_assoc, mul_assoc d.L.GG (Pj d ρ) B, comm_Pj_of d hB ρ, ← mul_assoc]

/- English proof (translation)
Rewrite using `[normal_form_lower_left, mul_add, add_mul, lower_sum_diagonal_zero hRel, add_zero, diag_GxB hRel Y ρ (fun f => kappa_commute_l0 hRel f Y)]`.
-/
theorem B3 (hRel : d.Rel) (Y : ℂ) (ρ : M.Ty P) :
    Pj d ρ * d.QQ Y 1 0 * Pj d ρ = M.xC P ρ Y • (d.L.GG * d.L.l0 Y * Pj d ρ) := by
  rw [normal_form_lower_left, mul_add, add_mul, lower_sum_diagonal_zero hRel, add_zero, diag_GxB hRel Y ρ (fun f => kappa_commute_l0 hRel f Y)]

/- English proof (translation)
Rewrite using `[normal_form_upper_right, mul_add, add_mul, upper_sum_diagonal_zero hRel, add_zero, diag_GxB hRel Y ρ (fun f => kappa_commute_raising_constant hRel f Y)]`.
-/
theorem B5 (hRel : d.Rel) (Y : ℂ) (ρ : M.Ty P) :
    Pj d ρ * d.QQ Y 0 1 * Pj d ρ = M.xC P ρ Y • (d.L.GG * d.L.m0 Y * Pj d ρ) := by
  rw [normal_form_upper_right, mul_add, add_mul, upper_sum_diagonal_zero hRel, add_zero, diag_GxB hRel Y ρ (fun f => kappa_commute_raising_constant hRel f Y)]

/- English proof (translation)
Establish `h` using `diag_GxB hRel Y ρ (B := 1) (fun f => Commute.one_right _)`. Simplify `h` using `[normal_form_diagonal]`.
-/
theorem B6 (hRel : d.Rel) (Y : ℂ) (ρ : M.Ty P) :
    Pj d ρ * d.QQ Y 1 1 * Pj d ρ = M.xC P ρ Y • (d.L.GG * Pj d ρ) := by
  have h := diag_GxB hRel Y ρ (B := 1) (fun f => Commute.one_right _)
  simpa [normal_form_diagonal] using h

/- English proof (translation)
Rewrite using `[normal_form_diagonal, mul_assoc, x_Pj, h, zero_smul, mul_zero]`.
-/
theorem diagonal_kill_of_zero (Y : ℂ) (ρ : M.Ty P) (h : M.xC P ρ Y = 0) : d.QQ Y 1 1 * Pj d ρ = 0 := by
  rw [normal_form_diagonal, mul_assoc, x_Pj, h, zero_smul, mul_zero]

end Blocks

end Formalism.FourierDecayAlt.P.NFx4.NO

namespace Formalism.FourierDecayAlt.P.NFx4.NO

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section RingFin

/- English proof (translation)
Establish `h2 : (-N - Z) * W - W * (-N - Z) = U`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : W * N - N * W = U`. Rewrite using `[← h2]`. Simplify using `only [sub_mul, mul_sub, neg_mul, mul_neg, hZ]`.

Normalize the expressions using the abelian group laws. Rewrite using `[← h3]`. Normalize the expressions using the abelian group laws.
-/
theorem fin_nab {R : Type} [Ring R] {ι : Type} (s : Finset ι) (Ps : ι → R) (hsum : ∑ i ∈ s, Ps i = 1)
    (N Z W U : R) (hZ : Z * W = W * Z) (h : ∀ i ∈ s, ((-N - Z) * W - W * (-N - Z)) * Ps i = U * Ps i) :
    N * W = W * N - U := by
  have h2 : (-N - Z) * W - W * (-N - Z) = U := by
    calc (-N - Z) * W - W * (-N - Z) = ((-N - Z) * W - W * (-N - Z)) * ∑ i ∈ s, Ps i := by rw [hsum, mul_one]
      _ = ∑ i ∈ s, U * Ps i := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl h
      _ = U := by rw [← Finset.mul_sum, hsum, mul_one]
  have h3 : W * N - N * W = U := by
    rw [← h2]
    simp only [sub_mul, mul_sub, neg_mul, mul_neg, hZ]
    abel
  rw [← h3]
  abel

end RingFin

section Act

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `Φ`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `c g0`. Use `show ((X.fn j (V Φ) : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) c g0 = ((V (X.fn j Φ) : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) c g0`.

Distinguish the cases in `hx : (c, g0) ∈ Q.DomR k r z z'`. Establish `h1` using `X.fn_apply j (V Φ) (c, g0) hx`. Establish `h2` using `X.fn_apply j Φ (c, g0) hx`. Simplify using `only at h1 h2`. Rewrite using `[h1, hV, hV]`.

Simplify using `only [NF.mulZ, Set.indicator_of_mem hx]`. Rewrite using `[h2, smul_comm]`. Establish `m1` using `(X.fn j (V Φ)).2`. Establish `m2` using `(V (X.fn j Φ)).2`. Rewrite using `[m1.1 (c, g0) hx, m2.1 (c, g0) hx]`.
-/
theorem fn_comm {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
    (X : Q.ActualOps k r z z' π π') (V : Module.End ℂ (Q.RadSp k r z z' π π')) (g : ℂ → ℂ)
    (hV : NF.IsMulZ V g) (j : Fin 6) : X.fn j * V = V * X.fn j := by
  apply LinearMap.ext
  intro Φ
  apply Subtype.ext
  funext c g0
  show ((X.fn j (V Φ) : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) c g0 =
    ((V (X.fn j Φ) : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) c g0
  by_cases hx : (c, g0) ∈ Q.DomR k r z z'
  · have h1 := X.fn_apply j (V Φ) (c, g0) hx
    have h2 := X.fn_apply j Φ (c, g0) hx
    dsimp only at h1 h2
    rw [h1, hV, hV]
    simp only [NF.mulZ, Set.indicator_of_mem hx]
    rw [h2, smul_comm]
  · have m1 := (X.fn j (V Φ)).2
    have m2 := (V (X.fn j Φ)).2
    rw [m1.1 (c, g0) hx, m2.1 (c, g0) hx]

/- English proof (translation)
Take `⟨V₁, hV₁⟩` from `hMZ Wp Wq P z z' π π' hPl (NF.dZ g) (dZ_smooth (isOpen_U _) hg)`. Take `⟨V₂, hV₂⟩` from `hMZ Wp Wq P z z' π π' hPl (NF.dZb g) (dZb_smooth (isOpen_U _) hg)`. Establish `ht : ∀ Y, X.t Y 1 1 * V = V * X.t Y 1 1` using `fun Y => (hAZ Wp Wq P z z' π π' hPl X g hg V V₁ V₂ hV hV₁ hV₂ Y).2.1`. Take `⟨-, -, -, -, -, -, -, -, -, -, hGG, hGGi, -⟩` from `hL`. Establish `hGiG : X.fn 5 * X.fn 4 = 1`.

Establish `e : (d.L.GGi * d.L.GG).1 = (1 : Q.Pr (Q.RadSp P.k P.r z z' π π')).1` using `by rw [d.L.GGi_GG]`. Rewrite `e` using `[fst_mul, hGGi, hGG, fst_mkP, fst_mkP, fst_one]`. Conclude with `e`. Establish `hx : ∀ Y, (d.κ (fun ρ => M.xC P ρ Y)).1 = X.fn 5 * X.t Y 1 1`. Introduce `Y`.

Establish `e1 : X.t Y 1 1 = (d.QQ Y 1 1).1` using `by rw [← hQQ Y]; rfl`. Rewrite using `[e1, normal_form_diagonal, fst_mul, hGG, fst_mkP, ← mul_assoc, hGiG, one_mul]`. Both sides reduce to the same expression. Establish `key` using `comm_of_sep ((fstA _).comp d.κ) V (fun Y ρ => M.xC P ρ Y) (fun ρ σ hh => sep P hPl.1 hh) (fun Y => by show Commute (d.κ (fun ρ => M.xC P ρ Y)).1 V`. Rewrite using `[hx Y]`.

Conclude with `Commute.mul_left (fn_comm X V g hV 5) (ht Y)) h`. Conclude with `key`.
-/
theorem kcomm [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (hMZ : NF.MulZExists) (hAZ : NF.ActualZetaSmooth)
    {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)}
    (hPl : Q.IsPlace P z z' π π') (X : Q.ActualOps P.k P.r z z' π π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r z z' π π')))
    (hL : Q.IsActualLevel X d.L) (hQQ : ∀ Y, X.QQ Y = d.QQ Y)
    (g : ℂ → ℂ) (hg : ContDiffOn ℝ ∞ g {ζ | P.TT < Complex.normSq ζ})
    (V : Module.End ℂ (Q.RadSp P.k P.r z z' π π')) (hV : NF.IsMulZ V g) (h : M.Ty P → ℂ) :
    Commute (d.κ h).1 V := by
  obtain ⟨V₁, hV₁⟩ := hMZ Wp Wq P z z' π π' hPl (NF.dZ g) (dZ_smooth (isOpen_U _) hg)
  obtain ⟨V₂, hV₂⟩ := hMZ Wp Wq P z z' π π' hPl (NF.dZb g) (dZb_smooth (isOpen_U _) hg)
  have ht : ∀ Y, X.t Y 1 1 * V = V * X.t Y 1 1 := fun Y =>
    (hAZ Wp Wq P z z' π π' hPl X g hg V V₁ V₂ hV hV₁ hV₂ Y).2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGG, hGGi, -⟩ := hL
  have hGiG : X.fn 5 * X.fn 4 = 1 := by
    have e : (d.L.GGi * d.L.GG).1 = (1 : Q.Pr (Q.RadSp P.k P.r z z' π π')).1 := by rw [d.L.GGi_GG]
    rw [fst_mul, hGGi, hGG, fst_mkP, fst_mkP, fst_one] at e
    exact e
  have hx : ∀ Y, (d.κ (fun ρ => M.xC P ρ Y)).1 = X.fn 5 * X.t Y 1 1 := by
    intro Y
    have e1 : X.t Y 1 1 = (d.QQ Y 1 1).1 := by rw [← hQQ Y]; rfl
    rw [e1, normal_form_diagonal, fst_mul, hGG, fst_mkP, ← mul_assoc, hGiG, one_mul]
    rfl
  have key := comm_of_sep ((fstA _).comp d.κ) V (fun Y ρ => M.xC P ρ Y) (fun ρ σ hh => sep P hPl.1 hh)
    (fun Y => by
      show Commute (d.κ (fun ρ => M.xC P ρ Y)).1 V
      rw [hx Y]
      exact Commute.mul_left (fn_comm X V g hV 5) (ht Y)) h
  exact key

/- English proof (translation)
Introduce `hMZ hAZ Wp Wq _ _ _ _ _ _ P z z' π π' hPl X d hL hSL hRel hQQ f hf W W₁ W₂ hW hW1 hW2`. Establish `hU` using `isOpen_U P.TT`. Establish `hf1` using `dZ_smooth hU hf`. Establish `hf2` using `dZb_smooth hU hf`. Establish `kW` using `kcomm hMZ hAZ hPl X d hL hQQ f hf W hW`.

Establish `kW1` using `kcomm hMZ hAZ hPl X d hL hQQ _ hf1 W₁ hW1`. Establish `kW2` using `kcomm hMZ hAZ hPl X d hL hQQ _ hf2 W₂ hW2`. Establish `hc` using `fun Y => hAZ Wp Wq P z z' π π' hPl X f hf W W₁ W₂ hW hW1 hW2 Y`. Establish `e10 : ∀ Y, X.t Y 1 0 = (d.QQ Y 1 0).1` using `fun Y => by rw [← hQQ Y]; rfl`. Establish `e01 : ∀ Y, X.t Y 0 1 = (d.QQ Y 0 1).1` using `fun Y => by rw [← hQQ Y]; rfl`.

Establish `e11 : ∀ Y, X.t Y 1 1 = (d.QQ Y 1 1).1` using `fun Y => by rw [← hQQ Y]; rfl`. Establish `hL'` using `hL`. Take `⟨-, -, -, -, -, -, hζ, -, hζb, -, hGG, hGGi, -⟩` from `hL'`. Establish `hGiG : X.fn 5 * X.fn 4 = 1`. Establish `e : (d.L.GGi * d.L.GG).1 = (1 : Q.Pr (Q.RadSp P.k P.r z z' π π')).1` using `by rw [d.L.GGi_GG]`.

Rewrite `e` using `[fst_mul, hGGi, hGG, fst_mkP, fst_mkP, fst_one]`. Conclude with `e`. Establish `hPW : ∀ σ, (Pj d σ).1 * W = W * (Pj d σ).1` using `fun σ => (kW _).eq`. Establish `hPW1 : ∀ σ, (Pj d σ).1 * W₁ = W₁ * (Pj d σ).1` using `fun σ => (kW1 _).eq`. Establish `hPW2 : ∀ σ, (Pj d σ).1 * W₂ = W₂ * (Pj d σ).1` using `fun σ => (kW2 _).eq`.

Establish `hsum : ∑ σ, (Pj d σ).1 = 1` using `by rw [← fst_sum, sum_Pj, fst_one]`. Establish `hP` using `hPl.1`. Use `⟨fun g => kW g, fun l hl => ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[decomp d (d.SS l)]`. Simplify using `only [fst_sum]`.

Use `Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hUp : M.Up P l b a`. Use `set Y : ℂ := -(M.rho P b l : ℂ) with hY`. Establish `hx0 : M.xC P b Y = 0`. Unfold `M.xC`.

Conclude with `Finset.prod_eq_zero hl (by rw [hY]; ring)`. Establish `hc0 : M.xEx P {l} b Y ≠ 0`. Unfold `M.xEx`. Use `Finset.prod_ne_zero_iff.2 fun i hi => ?_` and prove the remaining obligations. Establish `hi'` using `Finset.mem_sdiff.1 hi`.

Establish `hne : M.rho P b i ≠ M.rho P b l` using `rho_ne P hP b hi'.1 hl (fun e => hi'.2 (by simp [e]))`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Establish `: ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ)` using `by rw [hY] at h0; linear_combination h0`. Conclude with `this` after adjusting the coercions.

Establish `hE` using `congrArg Prod.fst (B1 hRel hl hUp Y)`. Rewrite `hE` using `[fst_mul, fst_mul, ← e10, fst_smul]`. Establish `h22` using `congrArg Prod.fst (diagonal_kill_of_zero (d := d) Y b hx0)`. Rewrite `h22` using `[fst_mul, ← e11, fst_zero]`. Establish `hcm : X.t Y 1 0 * W = W * X.t Y 1 0 + (-W₁) * X.t Y 1 1`.

Rewrite using `[(hc Y).1, neg_mul, ← sub_eq_add_neg]`. Conclude with `blk hc0 hE h22 hcm (hPW a) (hPW b)`. Rewrite using `[block_zero hRel hUp, fst_zero]`. Conclude with `Commute.zero_left _`. Rewrite using `[decomp d (star (d.SS l))]`.

Simplify using `only [fst_sum]`. Use `Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hUp : M.Up P l a b`. Use `set Y : ℂ := -(M.rho P b l : ℂ) with hY`. Establish `hx0 : M.xC P b Y = 0`.

Unfold `M.xC`. Conclude with `Finset.prod_eq_zero hl (by rw [hY]; ring)`. Establish `hc0 : M.xEx P {l} a Y ≠ 0`. Unfold `M.xEx`. Use `Finset.prod_ne_zero_iff.2 fun i hi => ?_` and prove the remaining obligations.

Establish `hi'` using `Finset.mem_sdiff.1 hi`. Establish `hil : i ≠ l` using `fun e => hi'.2 (by simp [e])`. Establish `hup` using `Mx3.rhoUp P l a b hUp i hi'.1`. Rewrite `hup` using `[if_neg hil, add_zero]`. Establish `hne : M.rho P b i ≠ M.rho P b l` using `rho_ne P hP b hi'.1 hl hil`.

Introduce `h0`. Apply `hne` to reduce the goal to its premises. Establish `: ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ)`. Rewrite `h0` using `[hY]`. Rewrite using `[hup]`.

Take the linear combination `h0`. Conclude with `this` after adjusting the coercions. Establish `hE` using `congrArg Prod.fst (B4 hRel hl hUp Y)`. Rewrite `hE` using `[fst_mul, fst_mul, ← e01, fst_smul]`. Establish `h22` using `congrArg Prod.fst (diagonal_kill_of_zero (d := d) Y b hx0)`.

Rewrite `h22` using `[fst_mul, ← e11, fst_zero]`. Conclude with `blk hc0 hE h22 (hc Y).2.2 (hPW a) (hPW b)`. Rewrite using `[star_block_zero hRel hUp, fst_zero]`. Conclude with `Commute.zero_left _`. Establish `hxI : ∀ ρ, M.xC P ρ Complex.I ≠ 0`.

Introduce `ρ`. Unfold `M.xC`. Use `Finset.prod_ne_zero_iff.2 fun i _ => ?_` and prove the remaining obligations. Introduce `h0`. Use `congrArg Complex.im h0` as an intermediate fact.

Simplify using `at this`. Establish `hZ : (algebraMap ℂ (Module.End ℂ _) (Complex.I + 1 / 2) * (d.L.ζb.1 * d.L.GGi.1)) * W = W * (algebraMap ℂ (Module.End ℂ _) (Complex.I + 1 / 2) * (d.L.ζb.1 * d.L.GGi.1))`. Rewrite using `[hζb, hGGi, fst_mkP, fst_mkP]`. Conclude with `((Algebra.commute_algebraMap_left _ _).mul_left (Commute.mul_left (fn_comm X W f hW 2) (fn_comm X W f hW 5))).eq`. Establish `key` using `fin_nab Finset.univ (fun ρ => (Pj d ρ).1) hsum d.L.nab.1 _ W (-W₁) hZ (fun ρ _ => by`.

Establish `hE` using `congrArg Prod.fst (B3 hRel Complex.I ρ)`. Rewrite `hE` using `[fst_mul, fst_mul, ← e10, fst_smul, fst_mul, fst_mul]`. Establish `h22` using `congrArg Prod.fst (B6 hRel Complex.I ρ)`. Rewrite `h22` using `[fst_mul, fst_mul, ← e11, fst_smul, fst_mul]`. Establish `hcm : X.t Complex.I 1 0 * W = W * X.t Complex.I 1 0 + (-W₁) * X.t Complex.I 1 1`.

Rewrite using `[(hc Complex.I).1, neg_mul, ← sub_eq_add_neg]`. Establish `hG : d.L.GG.1 = X.fn 4` using `by rw [hGG]; rfl`. Establish `hGi : d.L.GGi.1 * d.L.GG.1 = 1` using `by rw [hGG, hGGi]; exact hGiG`. Establish `hd` using `diag (hxI ρ) hE h22 hcm (hPW ρ) (by rw [mul_neg, neg_mul, hPW1 ρ]) (by rw [hG]; exact fn_comm X W f hW 4) (by rw [hG, mul_neg, neg_mul, fn_comm X W₁ _ hW1 4]) hGi`. Establish `hl0 : (d.L.l0 Complex.I).1 = -d.L.nab.1 - algebraMap ℂ (Module.End ℂ _) (Complex.I + 1 / 2) * (d.L.ζb.1 * d.L.GGi.1)`.

Simplify using `only [R.LevelData.l0, fst_sub, fst_neg, fst_mul, fst_alg]`. Rewrite `hd` using `[hl0]`. Conclude with `hd)`. Rewrite using `[key, sub_neg_eq_add]`. Establish `hxI : ∀ ρ, M.xC P ρ Complex.I ≠ 0`.

Introduce `ρ`. Unfold `M.xC`. Use `Finset.prod_ne_zero_iff.2 fun i _ => ?_` and prove the remaining obligations. Introduce `h0`. Use `congrArg Complex.im h0` as an intermediate fact.

Simplify using `at this`. Establish `hZ : (algebraMap ℂ (Module.End ℂ _) (Complex.I - 1 / 2) * (d.L.ζ.1 * d.L.GGi.1)) * W = W * (algebraMap ℂ (Module.End ℂ _) (Complex.I - 1 / 2) * (d.L.ζ.1 * d.L.GGi.1))`. Rewrite using `[hζ, hGGi, fst_mkP, fst_mkP]`. Conclude with `((Algebra.commute_algebraMap_left _ _).mul_left (Commute.mul_left (fn_comm X W f hW 0) (fn_comm X W f hW 5))).eq`. Establish `key` using `fin_nab Finset.univ (fun ρ => (Pj d ρ).1) hsum d.L.nabs.1 _ W W₂ hZ (fun ρ _ => by`.

Establish `hE` using `congrArg Prod.fst (B5 hRel Complex.I ρ)`. Rewrite `hE` using `[fst_mul, fst_mul, ← e01, fst_smul, fst_mul, fst_mul]`. Establish `h22` using `congrArg Prod.fst (B6 hRel Complex.I ρ)`. Rewrite `h22` using `[fst_mul, fst_mul, ← e11, fst_smul, fst_mul]`. Establish `hG : d.L.GG.1 = X.fn 4` using `by rw [hGG]; rfl`.

Establish `hGi : d.L.GGi.1 * d.L.GG.1 = 1` using `by rw [hGG, hGGi]; exact hGiG`. Establish `hd` using `diag (hxI ρ) hE h22 (hc Complex.I).2.2 (hPW ρ) (hPW2 ρ) (by rw [hG]; exact fn_comm X W f hW 4) (by rw [hG]; exact fn_comm X W₂ _ hW2 4) hGi`. Establish `hm0 : (d.L.m0 Complex.I).1 = -d.L.nabs.1 - algebraMap ℂ (Module.End ℂ _) (Complex.I - 1 / 2) * (d.L.ζ.1 * d.L.GGi.1)`. Simplify using `only [R.LevelData.m0, fst_sub, fst_neg, fst_mul, fst_alg]`. Rewrite `hd` using `[hm0]`.

Conclude with `hd)`. Conclude with `key`.
-/
theorem nFOrder0OfParts : NF.NFOrder0OfParts := by
  intro hMZ hAZ Wp Wq _ _ _ _ _ _ P z z' π π' hPl X d hL hSL hRel hQQ f hf W W₁ W₂ hW hW1 hW2
  have hU := isOpen_U P.TT
  have hf1 := dZ_smooth hU hf
  have hf2 := dZb_smooth hU hf
  have kW := kcomm hMZ hAZ hPl X d hL hQQ f hf W hW
  have kW1 := kcomm hMZ hAZ hPl X d hL hQQ _ hf1 W₁ hW1
  have kW2 := kcomm hMZ hAZ hPl X d hL hQQ _ hf2 W₂ hW2
  have hc := fun Y => hAZ Wp Wq P z z' π π' hPl X f hf W W₁ W₂ hW hW1 hW2 Y
  have e10 : ∀ Y, X.t Y 1 0 = (d.QQ Y 1 0).1 := fun Y => by rw [← hQQ Y]; rfl
  have e01 : ∀ Y, X.t Y 0 1 = (d.QQ Y 0 1).1 := fun Y => by rw [← hQQ Y]; rfl
  have e11 : ∀ Y, X.t Y 1 1 = (d.QQ Y 1 1).1 := fun Y => by rw [← hQQ Y]; rfl
  have hL' := hL
  obtain ⟨-, -, -, -, -, -, hζ, -, hζb, -, hGG, hGGi, -⟩ := hL'
  have hGiG : X.fn 5 * X.fn 4 = 1 := by
    have e : (d.L.GGi * d.L.GG).1 = (1 : Q.Pr (Q.RadSp P.k P.r z z' π π')).1 := by rw [d.L.GGi_GG]
    rw [fst_mul, hGGi, hGG, fst_mkP, fst_mkP, fst_one] at e
    exact e
  have hPW : ∀ σ, (Pj d σ).1 * W = W * (Pj d σ).1 := fun σ => (kW _).eq
  have hPW1 : ∀ σ, (Pj d σ).1 * W₁ = W₁ * (Pj d σ).1 := fun σ => (kW1 _).eq
  have hPW2 : ∀ σ, (Pj d σ).1 * W₂ = W₂ * (Pj d σ).1 := fun σ => (kW2 _).eq
  have hsum : ∑ σ, (Pj d σ).1 = 1 := by rw [← fst_sum, sum_Pj, fst_one]
  have hP := hPl.1
  refine ⟨fun g => kW g, fun l hl => ⟨?_, ?_⟩, ?_, ?_⟩
  ·
    rw [decomp d (d.SS l)]
    simp only [fst_sum]
    refine Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ => ?_
    by_cases hUp : M.Up P l b a
    · set Y : ℂ := -(M.rho P b l : ℂ) with hY
      have hx0 : M.xC P b Y = 0 := by
        unfold M.xC
        exact Finset.prod_eq_zero hl (by rw [hY]; ring)
      have hc0 : M.xEx P {l} b Y ≠ 0 := by
        unfold M.xEx
        refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
        have hi' := Finset.mem_sdiff.1 hi
        have hne : M.rho P b i ≠ M.rho P b l :=
          rho_ne P hP b hi'.1 hl (fun e => hi'.2 (by simp [e]))
        intro h0
        apply hne
        have : ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ) := by rw [hY] at h0; linear_combination h0
        exact_mod_cast this
      have hE := congrArg Prod.fst (B1 hRel hl hUp Y)
      rw [fst_mul, fst_mul, ← e10, fst_smul] at hE
      have h22 := congrArg Prod.fst (diagonal_kill_of_zero (d := d) Y b hx0)
      rw [fst_mul, ← e11, fst_zero] at h22
      have hcm : X.t Y 1 0 * W = W * X.t Y 1 0 + (-W₁) * X.t Y 1 1 := by
        rw [(hc Y).1, neg_mul, ← sub_eq_add_neg]
      exact blk hc0 hE h22 hcm (hPW a) (hPW b)
    · rw [block_zero hRel hUp, fst_zero]
      exact Commute.zero_left _
  ·
    rw [decomp d (star (d.SS l))]
    simp only [fst_sum]
    refine Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ => ?_
    by_cases hUp : M.Up P l a b
    · set Y : ℂ := -(M.rho P b l : ℂ) with hY
      have hx0 : M.xC P b Y = 0 := by
        unfold M.xC
        exact Finset.prod_eq_zero hl (by rw [hY]; ring)
      have hc0 : M.xEx P {l} a Y ≠ 0 := by
        unfold M.xEx
        refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
        have hi' := Finset.mem_sdiff.1 hi
        have hil : i ≠ l := fun e => hi'.2 (by simp [e])
        have hup := Mx3.rhoUp P l a b hUp i hi'.1
        rw [if_neg hil, add_zero] at hup
        have hne : M.rho P b i ≠ M.rho P b l := rho_ne P hP b hi'.1 hl hil
        intro h0
        apply hne
        have : ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ) := by
          rw [hY] at h0; rw [hup]; linear_combination h0
        exact_mod_cast this
      have hE := congrArg Prod.fst (B4 hRel hl hUp Y)
      rw [fst_mul, fst_mul, ← e01, fst_smul] at hE
      have h22 := congrArg Prod.fst (diagonal_kill_of_zero (d := d) Y b hx0)
      rw [fst_mul, ← e11, fst_zero] at h22
      exact blk hc0 hE h22 (hc Y).2.2 (hPW a) (hPW b)
    · rw [star_block_zero hRel hUp, fst_zero]
      exact Commute.zero_left _
  ·
    have hxI : ∀ ρ, M.xC P ρ Complex.I ≠ 0 := by
      intro ρ
      unfold M.xC
      refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      intro h0
      have := congrArg Complex.im h0
      simp at this
    have hZ : (algebraMap ℂ (Module.End ℂ _) (Complex.I + 1 / 2) * (d.L.ζb.1 * d.L.GGi.1)) * W =
        W * (algebraMap ℂ (Module.End ℂ _) (Complex.I + 1 / 2) * (d.L.ζb.1 * d.L.GGi.1)) := by
      rw [hζb, hGGi, fst_mkP, fst_mkP]
      exact ((Algebra.commute_algebraMap_left _ _).mul_left
        (Commute.mul_left (fn_comm X W f hW 2) (fn_comm X W f hW 5))).eq
    have key := fin_nab Finset.univ (fun ρ => (Pj d ρ).1) hsum d.L.nab.1 _ W (-W₁) hZ (fun ρ _ => by
      have hE := congrArg Prod.fst (B3 hRel Complex.I ρ)
      rw [fst_mul, fst_mul, ← e10, fst_smul, fst_mul, fst_mul] at hE
      have h22 := congrArg Prod.fst (B6 hRel Complex.I ρ)
      rw [fst_mul, fst_mul, ← e11, fst_smul, fst_mul] at h22
      have hcm : X.t Complex.I 1 0 * W = W * X.t Complex.I 1 0 + (-W₁) * X.t Complex.I 1 1 := by
        rw [(hc Complex.I).1, neg_mul, ← sub_eq_add_neg]
      have hG : d.L.GG.1 = X.fn 4 := by rw [hGG]; rfl
      have hGi : d.L.GGi.1 * d.L.GG.1 = 1 := by rw [hGG, hGGi]; exact hGiG
      have hd := diag (hxI ρ) hE h22 hcm (hPW ρ) (by rw [mul_neg, neg_mul, hPW1 ρ])
        (by rw [hG]; exact fn_comm X W f hW 4)
        (by rw [hG, mul_neg, neg_mul, fn_comm X W₁ _ hW1 4]) hGi
      have hl0 : (d.L.l0 Complex.I).1 = -d.L.nab.1 -
          algebraMap ℂ (Module.End ℂ _) (Complex.I + 1 / 2) * (d.L.ζb.1 * d.L.GGi.1) := by
        simp only [R.LevelData.l0, fst_sub, fst_neg, fst_mul, fst_alg]
      rw [hl0] at hd
      exact hd)
    rw [key, sub_neg_eq_add]
  ·
    have hxI : ∀ ρ, M.xC P ρ Complex.I ≠ 0 := by
      intro ρ
      unfold M.xC
      refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      intro h0
      have := congrArg Complex.im h0
      simp at this
    have hZ : (algebraMap ℂ (Module.End ℂ _) (Complex.I - 1 / 2) * (d.L.ζ.1 * d.L.GGi.1)) * W =
        W * (algebraMap ℂ (Module.End ℂ _) (Complex.I - 1 / 2) * (d.L.ζ.1 * d.L.GGi.1)) := by
      rw [hζ, hGGi, fst_mkP, fst_mkP]
      exact ((Algebra.commute_algebraMap_left _ _).mul_left
        (Commute.mul_left (fn_comm X W f hW 0) (fn_comm X W f hW 5))).eq
    have key := fin_nab Finset.univ (fun ρ => (Pj d ρ).1) hsum d.L.nabs.1 _ W W₂ hZ (fun ρ _ => by
      have hE := congrArg Prod.fst (B5 hRel Complex.I ρ)
      rw [fst_mul, fst_mul, ← e01, fst_smul, fst_mul, fst_mul] at hE
      have h22 := congrArg Prod.fst (B6 hRel Complex.I ρ)
      rw [fst_mul, fst_mul, ← e11, fst_smul, fst_mul] at h22
      have hG : d.L.GG.1 = X.fn 4 := by rw [hGG]; rfl
      have hGi : d.L.GGi.1 * d.L.GG.1 = 1 := by rw [hGG, hGGi]; exact hGiG
      have hd := diag (hxI ρ) hE h22 (hc Complex.I).2.2 (hPW ρ) (hPW2 ρ)
        (by rw [hG]; exact fn_comm X W f hW 4)
        (by rw [hG]; exact fn_comm X W₂ _ hW2 4) hGi
      have hm0 : (d.L.m0 Complex.I).1 = -d.L.nabs.1 -
          algebraMap ℂ (Module.End ℂ _) (Complex.I - 1 / 2) * (d.L.ζ.1 * d.L.GGi.1) := by
        simp only [R.LevelData.m0, fst_sub, fst_neg, fst_mul, fst_alg]
      rw [hm0] at hd
      exact hd)
    exact key

end Act

end Formalism.FourierDecayAlt.P.NFx4.NO

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `NFx4.NO.nFOrder0OfParts`.
-/
theorem normal_form_order_zero_of_parts : Formalism.FourierDecayAlt.NF.NFOrder0OfParts := NFx4.NO.nFOrder0OfParts

end Formalism.FourierDecayAlt.P

end

section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {P : M.Par}

def Off (δ : ℕ → ℤ) (ρ σ : M.Ty P) : Prop := ∀ i : Fin (P.k - 1), ((σ i : ℕ) : ℤ) = ((ρ i : ℕ) : ℤ) + δ ((i : ℕ) + 1)

def ee (l : ℕ) : ℕ → ℤ := fun m => if m = l then 1 else 0

/- English proof (translation)
Apply the tactic sequence `intro i; rw [h i]; simp only [ee]; split_ifs <;> simp`.
-/
theorem off_of_up {l : ℕ} {ρ σ : M.Ty P} (h : M.Up P l ρ σ) : Off (ee l) ρ σ := by
  intro i; rw [h i]; simp only [ee]; split_ifs <;> simp

/- English proof (translation)
Apply the tactic sequence `intro i; have := h i; simp only [ee] at this; split_ifs at this ⊢ <;> omega`.
-/
theorem up_of_off {l : ℕ} {ρ σ : M.Ty P} (h : Off (ee l) ρ σ) : M.Up P l ρ σ := by
  intro i; have := h i; simp only [ee] at this; split_ifs at this ⊢ <;> omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `i`. Apply `Fin.ext` to reduce the goal to its premises. Use `h i` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `rfl i`. Simplify using the standard rewrite rules.
-/
theorem off_zero {ρ σ : M.Ty P} : Off (0 : ℕ → ℤ) ρ σ ↔ σ = ρ := by
  constructor
  · intro h; funext i; apply Fin.ext; have := h i; simp at this; omega
  · rintro rfl i; simp

/- English proof (translation)
Introduce `i`. Rewrite using `[h' i, h i]`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem off_comp {δ δ' : ℕ → ℤ} {ρ τ σ : M.Ty P} (h : Off δ ρ τ) (h' : Off δ' τ σ) : Off (δ + δ') ρ σ := by
  intro i; rw [h' i, h i]; simp only [Pi.add_apply]; ring

/- English proof (translation)
Introduce `m hm`. Rewrite `hm` using `[Finset.mem_Icc]`. Establish `e1` using `h ⟨m - 1, by omega⟩; have e2 := h' ⟨m - 1, by omega⟩`. Simplify using `only at e1 e2`. Establish `e : δ (m - 1 + 1) = δ' (m - 1 + 1)` using `by linarith`.

Rewrite `e` using `[show m - 1 + 1 = m by omega]`. Then use the resulting hypothesis.
-/
theorem off_eq {δ δ' : ℕ → ℤ} {ρ σ : M.Ty P} (h : Off δ ρ σ) (h' : Off δ' ρ σ) :
    ∀ m ∈ Icc 1 (P.k - 1), δ m = δ' m := by
  intro m hm; rw [Finset.mem_Icc] at hm
  have e1 := h ⟨m - 1, by omega⟩; have e2 := h' ⟨m - 1, by omega⟩
  simp only at e1 e2
  have e : δ (m - 1 + 1) = δ' (m - 1 + 1) := by linarith
  rwa [show m - 1 + 1 = m by omega] at e

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply `Fin.ext` to reduce the goal to its premises. Use `h i` as an intermediate fact. Use `h' i` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem off_unique {δ : ℕ → ℤ} {ρ σ σ' : M.Ty P} (h : Off δ ρ σ) (h' : Off δ ρ σ') : σ = σ' := by
  funext i; apply Fin.ext; have := h i; have := h' i; omega

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

def dl (ρ : M.Ty P) : M.Ty P → ℂ := fun σ => if σ = ρ then 1 else 0

variable (κ : (M.Ty P → ℂ) →ₐ[ℂ] A)

def Pj (ρ : M.Ty P) : A := κ (dl ρ)

/- English proof (translation)
Unfold `Pj`. Rewrite using `[← map_mul]`. Use `split_ifs with h`. Apply the tactic sequence `subst h; congr 1; funext x; simp only [dl, Pi.mul_apply]; split_ifs <;> simp`. Apply the tactic sequence `rw [show dl ρ * dl σ = 0 from ?_, map_zero]; funext x; simp only [dl, Pi.mul_apply, Pi.zero_apply] split_ifs <;> simp_all`.
-/
theorem Pj_mul (ρ σ : M.Ty P) : Pj κ ρ * Pj κ σ = if ρ = σ then Pj κ ρ else 0 := by
  unfold Pj; rw [← map_mul]; split_ifs with h
  · subst h; congr 1; funext x; simp only [dl, Pi.mul_apply]; split_ifs <;> simp
  · rw [show dl ρ * dl σ = 0 from ?_, map_zero]; funext x; simp only [dl, Pi.mul_apply, Pi.zero_apply]
    split_ifs <;> simp_all

/- English proof (translation)
Rewrite using `[Pj_mul, if_pos rfl]`.
-/
theorem Pj_idem (ρ : M.Ty P) : Pj κ ρ * Pj κ ρ = Pj κ ρ := by rw [Pj_mul, if_pos rfl]

/- English proof (translation)
Rewrite using `[Pj_mul, if_neg h]`.
-/
theorem Pj_orth {ρ σ : M.Ty P} (h : ρ ≠ σ) : Pj κ ρ * Pj κ σ = 0 := by rw [Pj_mul, if_neg h]

/- English proof (translation)
Unfold `Pj`. Rewrite using `[← map_sum, ← map_one κ]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `[dl]`.
-/
theorem sum_Pj : ∑ ρ, Pj κ ρ = 1 := by
  unfold Pj; rw [← map_sum, ← map_one κ]; congr 1; funext x; simp [dl]

/- English proof (translation)
Unfold `Pj`. Rewrite using `[← map_mul, ← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [dl, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]`.

Apply the tactic sequence `split_ifs with h <;> simp [h]`.
-/
theorem kap_Pj (f : M.Ty P → ℂ) (ρ : M.Ty P) : κ f * Pj κ ρ = f ρ • Pj κ ρ := by
  unfold Pj; rw [← map_mul, ← map_smul]; congr 1; funext x; simp only [dl, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h <;> simp [h]

/- English proof (translation)
Rewrite using `[← kap_Pj]`. Unfold `Pj`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`.
-/
theorem Pj_kap (f : M.Ty P → ℂ) (ρ : M.Ty P) : Pj κ ρ * κ f = f ρ • Pj κ ρ := by
  rw [← kap_Pj]; unfold Pj; rw [← map_mul, ← map_mul, mul_comm]

/- English proof (translation)
Rewrite using `[← Finset.sum_mul, sum_Pj, one_mul]`.
-/
theorem eq_sum_left (X : A) : X = ∑ σ, Pj κ σ * X := by rw [← Finset.sum_mul, sum_Pj, one_mul]

/- English proof (translation)
Rewrite using `[← Finset.mul_sum, sum_Pj, mul_one]`.
-/
theorem eq_sum_right (X : A) : X = ∑ ρ, X * Pj κ ρ := by rw [← Finset.mul_sum, sum_Pj, mul_one]

def Supp (δ : ℕ → ℤ) (X : A) : Prop := ∀ ρ σ : M.Ty P, ¬ Off δ ρ σ → Pj κ σ * X * Pj κ ρ = 0

/- English proof (translation)
Introduce `ρ σ h`. Establish `: Pj κ σ * (X * Y) * Pj κ ρ = ∑ τ, (Pj κ σ * X * Pj κ τ) * (Pj κ τ * Y * Pj κ ρ)`. Establish `e : ∀ τ, (Pj κ σ * X * Pj κ τ) * (Pj κ τ * Y * Pj κ ρ) = Pj κ σ * (X * (Pj κ τ * (Y * Pj κ ρ)))`. Introduce `τ`. Simplify using `only [mul_assoc]`.

Rewrite using `[← mul_assoc (Pj κ τ) (Pj κ τ), Pj_idem]`. Rewrite using `[Finset.sum_congr rfl (fun τ _ => e τ), ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul, sum_Pj, one_mul]`. Simplify using `only [mul_assoc]`. Rewrite using `[this]`. Use `Finset.sum_eq_zero fun τ _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h1 : Off δ' ρ τ`. Distinguish the cases in `h2 : Off δ τ σ`. Conclude with `absurd (off_comp h1 h2) h`. Rewrite using `[hX τ σ h2, zero_mul]`. Rewrite using `[hY ρ τ h1, mul_zero]`.
-/
theorem supp_mul {δ δ' : ℕ → ℤ} {X Y : A} (hX : Supp κ δ X) (hY : Supp κ δ' Y) : Supp κ (δ' + δ) (X * Y) := by
  intro ρ σ h
  have : Pj κ σ * (X * Y) * Pj κ ρ = ∑ τ, (Pj κ σ * X * Pj κ τ) * (Pj κ τ * Y * Pj κ ρ) := by
    have e : ∀ τ, (Pj κ σ * X * Pj κ τ) * (Pj κ τ * Y * Pj κ ρ) = Pj κ σ * (X * (Pj κ τ * (Y * Pj κ ρ))) := by
      intro τ; simp only [mul_assoc]; rw [← mul_assoc (Pj κ τ) (Pj κ τ), Pj_idem]
    rw [Finset.sum_congr rfl (fun τ _ => e τ), ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul, sum_Pj, one_mul]
    simp only [mul_assoc]
  rw [this]; refine Finset.sum_eq_zero fun τ _ => ?_
  by_cases h1 : Off δ' ρ τ
  · by_cases h2 : Off δ τ σ
    · exact absurd (off_comp h1 h2) h
    · rw [hX τ σ h2, zero_mul]
  · rw [hY ρ τ h1, mul_zero]

/- English proof (translation)
Introduce `ρ σ h`. Rewrite using `[mul_add, add_mul, hX ρ σ h, hY ρ σ h, add_zero]`.
-/
theorem supp_add {δ : ℕ → ℤ} {X Y : A} (hX : Supp κ δ X) (hY : Supp κ δ Y) : Supp κ δ (X + Y) := by
  intro ρ σ h; rw [mul_add, add_mul, hX ρ σ h, hY ρ σ h, add_zero]

/- English proof (translation)
Introduce `ρ σ h`. Rewrite using `[mul_smul_comm, smul_mul_assoc, hX ρ σ h, smul_zero]`.
-/
theorem supp_smul {δ : ℕ → ℤ} {X : A} (c : ℂ) (hX : Supp κ δ X) : Supp κ δ (c • X) := by
  intro ρ σ h; rw [mul_smul_comm, smul_mul_assoc, hX ρ σ h, smul_zero]

/- English proof (translation)
Introduce `ρ σ h`. Rewrite using `[mul_neg, neg_mul, hX ρ σ h, neg_zero]`.
-/
theorem supp_neg {δ : ℕ → ℤ} {X : A} (hX : Supp κ δ X) : Supp κ δ (-X) := by
  intro ρ σ h; rw [mul_neg, neg_mul, hX ρ σ h, neg_zero]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `supp_add κ hX (supp_neg κ hY)`.
-/
theorem supp_sub {δ : ℕ → ℤ} {X Y : A} (hX : Supp κ δ X) (hY : Supp κ δ Y) : Supp κ δ (X - Y) := by
  rw [sub_eq_add_neg]; exact supp_add κ hX (supp_neg κ hY)

/- English proof (translation)
Introduce `ρ σ h`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_eq_zero fun i hi => hX i hi ρ σ h`.
-/
theorem supp_sum {ι : Type*} (s : Finset ι) {δ : ℕ → ℤ} {X : ι → A} (hX : ∀ i ∈ s, Supp κ δ (X i)) :
    Supp κ δ (∑ i ∈ s, X i) := by
  intro ρ σ h; rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_eq_zero fun i hi => hX i hi ρ σ h

/- English proof (translation)
Introduce `ρ σ _`. Simplify using the standard rewrite rules.
-/
theorem supp_zero (δ : ℕ → ℤ) : Supp κ δ (0 : A) := by intro ρ σ _; simp

/- English proof (translation)
Introduce `ρ σ h`. Rewrite `h` using `[off_zero]`. Rewrite using `[show Pj κ σ * X = X * Pj κ σ from (hX _).eq, mul_assoc, Pj_orth κ h, mul_zero]`.
-/
theorem supp_comm {X : A} (hX : ∀ f, Commute (κ f) X) : Supp κ 0 X := by
  intro ρ σ h; rw [off_zero] at h
  rw [show Pj κ σ * X = X * Pj κ σ from (hX _).eq, mul_assoc, Pj_orth κ h, mul_zero]

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

/- English proof (translation)
Introduce `i`. Use `h i` as an intermediate fact. Simplify using `only [Pi.neg_apply]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem off_neg {δ : ℕ → ℤ} {ρ σ : M.Ty P} (h : Off δ ρ σ) : Off (-δ) σ ρ := by
  intro i; have := h i; simp only [Pi.neg_apply]; linarith

structure Hyp (d : Q.NFData P A) : Prop where
  kstar : ∀ f : M.Ty P → ℂ, star (d.κ f) = d.κ (fun ρ => star (f ρ))
  kc : ∀ f : M.Ty P → ℂ, Commute (d.κ f) d.L.nab ∧ Commute (d.κ f) d.L.nabs ∧ Commute (d.κ f) d.L.ζ ∧
    Commute (d.κ f) d.L.ζb ∧ Commute (d.κ f) d.L.GG ∧ Commute (d.κ f) d.L.GGi
  rai : ∀ l (f g : M.Ty P → ℂ), (∀ ρ ρ', M.Up P l ρ ρ' → g ρ' = f ρ) → d.κ g * d.SS l = d.SS l * d.κ f
  nrm : ∀ l ∈ Icc 1 (P.k - 1), star (d.SS l) * d.SS l = d.κ fun ρ => ((M.Nrm P l ρ : ℝ) : ℂ)

/- English proof (translation)
Take `⟨h1, h2, -, h4, -, h6⟩` from `h`. Use `⟨h1, fun f => ⟨h2 f _ (by simp), h2 f _ (by simp), h2 f _ (by simp [R.LevelData.fns]), h2 f _ (by simp [R.LevelData.fns]), h2 f _ (by simp [R.LevelData.fns]), h2 f _ (by simp [R.LevelData.fns])⟩, h4, h6⟩` and prove the remaining obligations.
-/
theorem hyp_of_rel (d : Q.NFData P A) (h : d.Rel) : Hyp d := by
  obtain ⟨h1, h2, -, h4, -, h6⟩ := h
  refine ⟨h1, fun f => ⟨h2 f _ (by simp), h2 f _ (by simp), h2 f _ (by simp [R.LevelData.fns]),
    h2 f _ (by simp [R.LevelData.fns]), h2 f _ (by simp [R.LevelData.fns]), h2 f _ (by simp [R.LevelData.fns])⟩, h4, h6⟩

variable {d : Q.NFData P A} (hd : Hyp d)
include hd

/- English proof (translation)
Apply the tactic sequence `unfold Pj; rw [hd.kstar]; congr 1; funext x; simp only [dl]; split_ifs <;> simp`.
-/
theorem Pj_star (ρ : M.Ty P) : star (Pj d.κ ρ) = Pj d.κ ρ := by
  unfold Pj; rw [hd.kstar]; congr 1; funext x; simp only [dl]; split_ifs <;> simp

/- English proof (translation)
Use `hd.rai l (fun ρ => if M.Up P l ρ σ then 1 else 0) (dl σ) (by` as an intermediate fact. Introduce `ρ ρ' h`. Simplify using `only [dl]`. Distinguish the cases in `e : ρ' = σ`. Substitute `e` using the available equality.

Simplify using `[h]`. Rewrite using `[if_neg e, if_neg]`. Introduce `h'`. Conclude with `e (off_unique (off_of_up h) (off_of_up h')))`. Apply the tactic sequence `rw [Pj, this, mul_assoc, kap_Pj]; split_ifs <;> simp`.
-/
theorem P_SS_P (l : ℕ) (σ ρ : M.Ty P) :
    Pj d.κ σ * d.SS l * Pj d.κ ρ = if M.Up P l ρ σ then d.SS l * Pj d.κ ρ else 0 := by
  have := hd.rai l (fun ρ => if M.Up P l ρ σ then 1 else 0) (dl σ) (by
    intro ρ ρ' h; simp only [dl]
    by_cases e : ρ' = σ
    · subst e; simp [h]
    · rw [if_neg e, if_neg]; intro h'; exact e (off_unique (off_of_up h) (off_of_up h')))
  rw [Pj, this, mul_assoc, kap_Pj]; split_ifs <;> simp

/- English proof (translation)
Introduce `ρ σ h`. Rewrite using `[P_SS_P hd, if_neg]`. Conclude with `fun h' => h (off_of_up h')`.
-/
theorem supp_SS (l : ℕ) : Supp d.κ (ee l) (d.SS l) := by
  intro ρ σ h; rw [P_SS_P hd, if_neg]; exact fun h' => h (off_of_up h')

/- English proof (translation)
Use `congrArg star (P_SS_P hd l ρ σ)` as an intermediate fact. Simplify using `only [star_mul, Pj_star hd, ← mul_assoc] at this`. Apply the tactic sequence `rw [this]; split_ifs <;> simp [star_mul, Pj_star hd]`.
-/
theorem P_SSs_P (l : ℕ) (σ ρ : M.Ty P) :
    Pj d.κ σ * star (d.SS l) * Pj d.κ ρ = if M.Up P l σ ρ then Pj d.κ σ * star (d.SS l) else 0 := by
  have := congrArg star (P_SS_P hd l ρ σ)
  simp only [star_mul, Pj_star hd, ← mul_assoc] at this
  rw [this]; split_ifs <;> simp [star_mul, Pj_star hd]

/- English proof (translation)
Introduce `ρ σ h`. Rewrite using `[P_SSs_P hd, if_neg]`. Introduce `h'`. Conclude with `h (off_neg (off_of_up h'))`.
-/
theorem supp_SSs (l : ℕ) : Supp d.κ (-ee l) (star (d.SS l)) := by
  intro ρ σ h; rw [P_SSs_P hd, if_neg]; intro h'; exact h (off_neg (off_of_up h'))

/- English proof (translation)
The claim follows from `supp_comm d.κ hX`.
-/
theorem supp_kcomm {X : A} (hX : ∀ f, Commute (d.κ f) X) : Supp d.κ 0 X := supp_comm d.κ hX

/- English proof (translation)
Use `conv_lhs => rw [eq_sum_left d.κ (X * Pj d.κ ρ)]`. Rewrite using `[Finset.sum_eq_single τ (fun σ _ hσ => by rw [← mul_assoc]; exact hX ρ σ (fun h' => hσ (off_unique h' h))) (fun h' => absurd (Finset.mem_univ _) h'), mul_assoc]`.
-/
theorem left_single {δ : ℕ → ℤ} {X : A} (hX : Supp d.κ δ X) {ρ τ : M.Ty P} (h : Off δ ρ τ) :
    X * Pj d.κ ρ = Pj d.κ τ * X * Pj d.κ ρ := by
  conv_lhs => rw [eq_sum_left d.κ (X * Pj d.κ ρ)]
  rw [Finset.sum_eq_single τ (fun σ _ hσ => by rw [← mul_assoc]; exact hX ρ σ (fun h' => hσ (off_unique h' h)))
    (fun h' => absurd (Finset.mem_univ _) h'), mul_assoc]

/- English proof (translation)
Rewrite using `[eq_sum_left d.κ (X * Pj d.κ ρ)]`. Conclude with `Finset.sum_eq_zero fun σ _ => by rw [← mul_assoc]; exact hX ρ σ (h σ)`.
-/
theorem left_none {δ : ℕ → ℤ} {X : A} (hX : Supp d.κ δ X) {ρ : M.Ty P} (h : ∀ τ, ¬ Off δ ρ τ) :
    X * Pj d.κ ρ = 0 := by
  rw [eq_sum_left d.κ (X * Pj d.κ ρ)]
  exact Finset.sum_eq_zero fun σ _ => by rw [← mul_assoc]; exact hX ρ σ (h σ)

/- English proof (translation)
Use `conv_lhs => rw [eq_sum_right d.κ (Pj d.κ ρ * X)]`. Conclude with `Finset.sum_eq_single τ (fun σ _ hσ => hX σ ρ (fun h' => hσ (off_unique (off_neg h') (off_neg h)))) (fun h' => absurd (Finset.mem_univ _) h')`.
-/
theorem right_single {δ : ℕ → ℤ} {X : A} (hX : Supp d.κ δ X) {ρ τ : M.Ty P} (h : Off δ τ ρ) :
    Pj d.κ ρ * X = Pj d.κ ρ * X * Pj d.κ τ := by
  conv_lhs => rw [eq_sum_right d.κ (Pj d.κ ρ * X)]
  exact Finset.sum_eq_single τ (fun σ _ hσ => hX σ ρ (fun h' => hσ (off_unique (off_neg h') (off_neg h))))
    (fun h' => absurd (Finset.mem_univ _) h')

/- English proof (translation)
Rewrite using `[eq_sum_right d.κ (Pj d.κ ρ * X)]`. Conclude with `Finset.sum_eq_zero fun σ _ => hX σ ρ (h σ)`.
-/
theorem right_none {δ : ℕ → ℤ} {X : A} (hX : Supp d.κ δ X) {ρ : M.Ty P} (h : ∀ τ, ¬ Off δ τ ρ) :
    Pj d.κ ρ * X = 0 := by
  rw [eq_sum_right d.κ (Pj d.κ ρ * X)]
  exact Finset.sum_eq_zero fun σ _ => hX σ ρ (h σ)

/- English proof (translation)
Use `conv_lhs => rw [eq_sum_right d.κ (d.κ f)]`. Conclude with `Finset.sum_congr rfl fun ρ _ => kap_Pj d.κ f ρ`.
-/
theorem kap_eq_sum (f : M.Ty P → ℂ) : d.κ f = ∑ ρ, f ρ • Pj d.κ ρ := by
  conv_lhs => rw [eq_sum_right d.κ (d.κ f)]
  exact Finset.sum_congr rfl fun ρ _ => kap_Pj d.κ f ρ

/- English proof (translation)
Rewrite using `[eq_sum_right d.κ X, eq_sum_right d.κ Y]`. Conclude with `Finset.sum_congr rfl fun ρ _ => h ρ`.
-/
theorem ext_right {X Y : A} (h : ∀ ρ, X * Pj d.κ ρ = Y * Pj d.κ ρ) : X = Y := by
  rw [eq_sum_right d.κ X, eq_sum_right d.κ Y]; exact Finset.sum_congr rfl fun ρ _ => h ρ

/- English proof (translation)
The claim follows from `(Algebra.commutes c _).symm`.
-/
theorem kc_alg (f : M.Ty P → ℂ) (c : ℂ) : Commute (d.κ f) (algebraMap ℂ A c) := (Algebra.commutes c _).symm

/- English proof (translation)
Take `⟨h1, -, -, h4, -, h6⟩` from `hd.kc f`. Unfold `R.LevelData.l0`. Conclude with `(h1.neg_right).sub_right ((kc_alg hd f _).mul_right (h4.mul_right h6))`.
-/
theorem kappa_commute_lowering_data (f : M.Ty P → ℂ) (Y : ℂ) : Commute (d.κ f) (d.L.l0 Y) := by
  obtain ⟨h1, -, -, h4, -, h6⟩ := hd.kc f
  unfold R.LevelData.l0; exact (h1.neg_right).sub_right ((kc_alg hd f _).mul_right (h4.mul_right h6))

/- English proof (translation)
Take `⟨-, h2, h3, -, -, h6⟩` from `hd.kc f`. Unfold `R.LevelData.m0`. Conclude with `(h2.neg_right).sub_right ((kc_alg hd f _).mul_right (h3.mul_right h6))`.
-/
theorem kappa_commute_raising_data (f : M.Ty P → ℂ) (Y : ℂ) : Commute (d.κ f) (d.L.m0 Y) := by
  obtain ⟨-, h2, h3, -, -, h6⟩ := hd.kc f
  unfold R.LevelData.m0; exact (h2.neg_right).sub_right ((kc_alg hd f _).mul_right (h3.mul_right h6))

/- English proof (translation)
Use `show d.κ f * d.κ g = d.κ g * d.κ f`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`.
-/
theorem kc_kap (f g : M.Ty P → ℂ) : Commute (d.κ f) (d.κ g) := by
  show d.κ f * d.κ g = d.κ g * d.κ f; rw [← map_mul, ← map_mul, mul_comm]

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

/- English proof (translation)
Simplify using `[Q.NFData.QQ]`.
-/
theorem normal_form_upper_left (d : Q.NFData P A) (Y : ℂ) : d.QQ Y 0 0 = d.L.GGi * (d.κ fun ρ => M.wC P ρ Y) +
    d.L.GG * d.x Y * d.L.m0 Y * d.L.l0 Y + d.L.GG * d.L.m0 Y * d.L.GGi * d.weightedSumBis Y + d.S12 Y * d.L.l0 Y +
    d.L.GGi * d.S4 Y := by simp [Q.NFData.QQ]
/- English proof (translation)
Simplify using `[Q.NFData.QQ]`.
-/
theorem normal_form_upper_right (d : Q.NFData P A) (Y : ℂ) : d.QQ Y 0 1 = d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y := by simp [Q.NFData.QQ]
/- English proof (translation)
Simplify using `[Q.NFData.QQ]`.
-/
theorem normal_form_lower_left (d : Q.NFData P A) (Y : ℂ) : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := by simp [Q.NFData.QQ]
/- English proof (translation)
Simplify using `[Q.NFData.QQ]`.
-/
theorem normal_form_diagonal (d : Q.NFData P A) (Y : ℂ) : d.QQ Y 1 1 = d.L.GG * d.x Y := by simp [Q.NFData.QQ]

/- English proof (translation)
Establish `h` using `congrFun (congrFun (hS.det Y).2 1) 0`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] at h`. Rewrite using `[← h]`. Normalize the expressions using the abelian group laws.
-/
theorem lower_determinant_relation (d : Q.NFData P A) (hS : Wd.IsStart d.QQ (M.qC P)) (Y : ℂ) :
    d.QQ Y 1 0 * d.QQ (Y + 1) 0 1 - d.QQ Y 1 1 * d.QQ (Y + 1) 0 0 = -algebraMap ℂ A (M.qC P Y) := by
  have h := congrFun (congrFun (hS.det Y).2 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] at h
  rw [← h]; abel

/- English proof (translation)
Introduce `h`. Use `off_eq h (off_zero.2 rfl) l hl` as an intermediate fact. Simplify using `[ee] at this`.
-/
theorem ee_not_self {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (ρ : M.Ty P) : ¬ Off (ee l) ρ ρ := by
  intro h; have := off_eq h (off_zero.2 rfl) l hl; simp [ee] at this

/- English proof (translation)
Apply the tactic sequence `have := off_eq h1 h2 m hm; simp only [ee] at this; split_ifs at this with e <;> simp_all`.
-/
theorem ee_ne {m i : ℕ} (hm : m ∈ Icc 1 (P.k - 1)) (hi : i ∈ Icc 1 (P.k - 1)) {ρ τ : M.Ty P}
    (h1 : Off (ee m) τ ρ) (h2 : Off (ee i) τ ρ) : i = m := by
  have := off_eq h1 h2 m hm; simp only [ee] at this; split_ifs at this with e <;> simp_all

variable {d : Q.NFData P A} (hd : Hyp d)
include hd

/- English proof (translation)
Establish `e : Pj d.κ ρ * (d.SS i * d.κ (fun ρ => M.xEx P {i} ρ Y) * (d.κ (fun ρ => M.xEx P {m} ρ Y') * star (d.SS m))) * Pj d.κ ρ = Pj d.κ ρ * d.SS i * (d.κ (fun ρ => M.xEx P {i} ρ Y) * d.κ (fun ρ => M.xEx P {m} ρ Y') * (star (d.SS m) * Pj d.κ ρ))` using `by simp only [mul_assoc]`. Rewrite using `[e]`. Distinguish the cases in `h : ∃ τ, M.Up P m τ ρ`. Establish `hτ` using `h.choose_spec set τ := h.choose`. Establish `hs : star (d.SS m) * Pj d.κ ρ = Pj d.κ τ * star (d.SS m) * Pj d.κ ρ` using `left_single hd (supp_SSs hd m) (off_neg (off_of_up hτ))`.

Establish `e2 : d.κ (fun ρ => M.xEx P {i} ρ Y) * d.κ (fun ρ => M.xEx P {m} ρ Y') * (Pj d.κ τ * star (d.SS m) * Pj d.κ ρ) = (M.xEx P {i} τ Y * M.xEx P {m} τ Y') • (Pj d.κ τ * star (d.SS m) * Pj d.κ ρ)`. Rewrite using `[← map_mul, ← mul_assoc, ← mul_assoc, kap_Pj]`. Simplify using `only [Pi.mul_apply, smul_mul_assoc]`. Rewrite using `[hs, e2, mul_smul_comm, show Pj d.κ ρ * d.SS i * (Pj d.κ τ * star (d.SS m) * Pj d.κ ρ) = Pj d.κ ρ * d.SS i * Pj d.κ τ * star (d.SS m) * Pj d.κ ρ by simp only [mul_assoc], P_SS_P hd]`. Distinguish the cases in `him : i = m`.

Substitute `him` using the available equality. Rewrite using `[if_pos hτ, if_pos rfl, dif_pos h]`. Use `congr 1`. Rewrite using `[show d.SS i * Pj d.κ τ * star (d.SS i) * Pj d.κ ρ = d.SS i * (Pj d.κ τ * star (d.SS i) * Pj d.κ ρ) by`. Simplify using `only [mul_assoc], ← hs, ← mul_assoc]`.

Rewrite using `[if_neg (fun h1 => him (ee_ne hm hi (off_of_up hτ) (off_of_up h1))), if_neg him]`. Simplify using the standard rewrite rules. Establish `hs : star (d.SS m) * Pj d.κ ρ = 0` using `left_none hd (supp_SSs hd m) (fun τ hτ => h ⟨τ, by`. Use `off_neg hτ` as an intermediate fact. Rewrite `this` using `[neg_neg]`.

Conclude with `up_of_off this⟩)`. Apply the tactic sequence `rw [hs]; split_ifs <;> simp`.
-/
theorem term_21_12 (Y Y' : ℂ) (ρ : M.Ty P) (i m : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) (hm : m ∈ Icc 1 (P.k - 1)) :
    Pj d.κ ρ * (d.SS i * d.κ (fun ρ => M.xEx P {i} ρ Y) * (d.κ (fun ρ => M.xEx P {m} ρ Y') * star (d.SS m))) *
      Pj d.κ ρ = if i = m then
        (if h : ∃ τ, M.Up P m τ ρ then M.xEx P {m} h.choose Y * M.xEx P {m} h.choose Y' else 0) •
          (d.SS m * star (d.SS m) * Pj d.κ ρ) else 0 := by
  have e : Pj d.κ ρ * (d.SS i * d.κ (fun ρ => M.xEx P {i} ρ Y) * (d.κ (fun ρ => M.xEx P {m} ρ Y') *
      star (d.SS m))) * Pj d.κ ρ =
      Pj d.κ ρ * d.SS i * (d.κ (fun ρ => M.xEx P {i} ρ Y) * d.κ (fun ρ => M.xEx P {m} ρ Y') *
        (star (d.SS m) * Pj d.κ ρ)) := by simp only [mul_assoc]
  rw [e]
  by_cases h : ∃ τ, M.Up P m τ ρ
  · have hτ := h.choose_spec
    set τ := h.choose
    have hs : star (d.SS m) * Pj d.κ ρ = Pj d.κ τ * star (d.SS m) * Pj d.κ ρ :=
      left_single hd (supp_SSs hd m) (off_neg (off_of_up hτ))
    have e2 : d.κ (fun ρ => M.xEx P {i} ρ Y) * d.κ (fun ρ => M.xEx P {m} ρ Y') * (Pj d.κ τ * star (d.SS m) * Pj d.κ ρ)
        = (M.xEx P {i} τ Y * M.xEx P {m} τ Y') • (Pj d.κ τ * star (d.SS m) * Pj d.κ ρ) := by
      rw [← map_mul, ← mul_assoc, ← mul_assoc, kap_Pj]; simp only [Pi.mul_apply, smul_mul_assoc]
    rw [hs, e2, mul_smul_comm, show Pj d.κ ρ * d.SS i * (Pj d.κ τ * star (d.SS m) * Pj d.κ ρ) =
      Pj d.κ ρ * d.SS i * Pj d.κ τ * star (d.SS m) * Pj d.κ ρ by simp only [mul_assoc], P_SS_P hd]
    by_cases him : i = m
    · subst him
      rw [if_pos hτ, if_pos rfl, dif_pos h]
      congr 1
      rw [show d.SS i * Pj d.κ τ * star (d.SS i) * Pj d.κ ρ = d.SS i * (Pj d.κ τ * star (d.SS i) * Pj d.κ ρ) by
        simp only [mul_assoc], ← hs, ← mul_assoc]
    · rw [if_neg (fun h1 => him (ee_ne hm hi (off_of_up hτ) (off_of_up h1))), if_neg him]; simp
  · have hs : star (d.SS m) * Pj d.κ ρ = 0 := left_none hd (supp_SSs hd m) (fun τ hτ => h ⟨τ, by
      have := off_neg hτ; rw [neg_neg] at this; exact up_of_off this⟩)
    rw [hs]; split_ifs <;> simp

/- English proof (translation)
Unfold `Q.NFData.weightedSumBis Q.NFData.S12`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun i hi => term_21_12 hd Y Y' ρ i m hi hm]`. Simplify using `only [Finset.sum_ite_eq']`. Conclude with `Finset.sum_congr rfl fun m hm => if_pos hm`.
-/
theorem blk_21_12 (Y Y' : ℂ) (ρ : M.Ty P) :
    Pj d.κ ρ * (d.weightedSumBis Y * d.S12 Y') * Pj d.κ ρ = ∑ m ∈ Icc 1 (P.k - 1),
      (if h : ∃ τ, M.Up P m τ ρ then M.xEx P {m} h.choose Y * M.xEx P {m} h.choose Y' else 0) •
        (d.SS m * star (d.SS m) * Pj d.κ ρ) := by
  unfold Q.NFData.weightedSumBis Q.NFData.S12
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun i hi => term_21_12 hd Y Y' ρ i m hi hm]
  simp only [Finset.sum_ite_eq']
  exact Finset.sum_congr rfl fun m hm => if_pos hm

/- English proof (translation)
Establish `e : Pj d.κ ρ * (d.κ (fun ρ => M.xEx P {m} ρ Y) * star (d.SS m) * (d.SS i * d.κ (fun ρ => M.xEx P {i} ρ Y'))) * Pj d.κ ρ = (Pj d.κ ρ * d.κ (fun ρ => M.xEx P {m} ρ Y)) * (star (d.SS m) * d.SS i) * (d.κ (fun ρ => M.xEx P {i} ρ Y') * Pj d.κ ρ)` using `by simp only [mul_assoc]`. Rewrite using `[e, Pj_kap, kap_Pj]`. Simplify using `only [smul_mul_assoc, mul_smul_comm, smul_smul]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Rewrite using `[show Pj d.κ ρ * (star (d.SS m) * d.SS m) * Pj d.κ ρ = star (d.SS m) * d.SS m * Pj d.κ ρ by`. Rewrite using `[hd.nrm m hm, mul_assoc, kap_Pj, mul_smul_comm, Pj_idem], mul_comm (M.xEx P {m} ρ Y')]`. Rewrite using `[supp_mul d.κ (supp_SSs hd m) (supp_SS hd i) ρ ρ, smul_zero]`. Introduce `h'`. Use `off_eq h' (off_zero.2 rfl) i hi` as an intermediate fact.

Simplify using `only [Pi.add_apply, Pi.neg_apply, ee, Pi.zero_apply] at this`. Apply the tactic sequence `split_ifs at this <;> simp_all`.
-/
theorem term_12_21 (Y Y' : ℂ) (ρ : M.Ty P) (m i : ℕ) (hm : m ∈ Icc 1 (P.k - 1)) (hi : i ∈ Icc 1 (P.k - 1)) :
    Pj d.κ ρ * (d.κ (fun ρ => M.xEx P {m} ρ Y) * star (d.SS m) * (d.SS i * d.κ (fun ρ => M.xEx P {i} ρ Y'))) *
      Pj d.κ ρ = if m = i then (M.xEx P {m} ρ Y * M.xEx P {m} ρ Y') • (star (d.SS m) * d.SS m * Pj d.κ ρ)
        else 0 := by
  have e : Pj d.κ ρ * (d.κ (fun ρ => M.xEx P {m} ρ Y) * star (d.SS m) * (d.SS i * d.κ (fun ρ => M.xEx P {i} ρ Y')))
      * Pj d.κ ρ = (Pj d.κ ρ * d.κ (fun ρ => M.xEx P {m} ρ Y)) * (star (d.SS m) * d.SS i) *
        (d.κ (fun ρ => M.xEx P {i} ρ Y') * Pj d.κ ρ) := by simp only [mul_assoc]
  rw [e, Pj_kap, kap_Pj]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  split_ifs with h
  · subst h
    rw [show Pj d.κ ρ * (star (d.SS m) * d.SS m) * Pj d.κ ρ = star (d.SS m) * d.SS m * Pj d.κ ρ by
      rw [hd.nrm m hm, mul_assoc, kap_Pj, mul_smul_comm, Pj_idem], mul_comm (M.xEx P {m} ρ Y')]
  · rw [supp_mul d.κ (supp_SSs hd m) (supp_SS hd i) ρ ρ, smul_zero]
    intro h'
    have := off_eq h' (off_zero.2 rfl) i hi
    simp only [Pi.add_apply, Pi.neg_apply, ee, Pi.zero_apply] at this
    split_ifs at this <;> simp_all

/- English proof (translation)
Unfold `Q.NFData.weightedSumBis Q.NFData.S12`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i hi => term_12_21 hd Y Y' ρ i x hi hx]`. Simplify using `only [Finset.sum_ite_eq']`. Conclude with `Finset.sum_congr rfl fun m hm => if_pos hm`.
-/
theorem blk_12_21 (Y Y' : ℂ) (ρ : M.Ty P) :
    Pj d.κ ρ * (d.S12 Y * d.weightedSumBis Y') * Pj d.κ ρ = ∑ m ∈ Icc 1 (P.k - 1),
      (M.xEx P {m} ρ Y * M.xEx P {m} ρ Y') • (star (d.SS m) * d.SS m * Pj d.κ ρ) := by
  unfold Q.NFData.weightedSumBis Q.NFData.S12
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i hi => term_12_21 hd Y Y' ρ i x hi hx]
  simp only [Finset.sum_ite_eq']
  exact Finset.sum_congr rfl fun m hm => if_pos hm

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply `Fin.ext` to reduce the goal to its premises. Use `h i` as an intermediate fact. Use `h' i` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem up_inj {l : ℕ} {ρ ρ' σ : M.Ty P} (h : M.Up P l ρ σ) (h' : M.Up P l ρ' σ) : ρ = ρ' := by
  funext i; apply Fin.ext; have := h i; have := h' i; omega

/- English proof (translation)
The claim follows from `Finset.prod_eq_zero hl (by ring)`.
-/
theorem xC_root (ρ : M.Ty P) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) : M.xC P ρ (-(M.rho P ρ l : ℂ)) = 0 :=
  Finset.prod_eq_zero hl (by ring)

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.rho_raise P l τ ρ h i hi`.
-/
theorem rho_up {l : ℕ} {τ ρ : M.Ty P} (h : M.Up P l τ ρ) {i : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) :
    M.rho P ρ i = M.rho P τ i + if i = l then 1 else 0 := Formalism.FourierDecayAlt.P.rho_raise P l τ ρ h i hi

/- English proof (translation)
Unfold `M.xEx`. Rewrite using `[Finset.sdiff_singleton_eq_erase]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_erase]`. Rewrite using `[rho_up h hi.2, if_neg hi.1, add_zero]`.
-/
theorem xEx_below {l : ℕ} {τ ρ : M.Ty P} (h : M.Up P l τ ρ) (Y : ℂ) :
    M.xEx P {l} τ Y = ∏ i ∈ (Icc 1 (P.k - 1)).erase l, (Y + (M.rho P ρ i : ℂ)) := by
  unfold M.xEx; rw [Finset.sdiff_singleton_eq_erase]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_erase] at hi; rw [rho_up h hi.2, if_neg hi.1, add_zero]

/- English proof (translation)
Unfold `M.xEx`. Use `Finset.prod_eq_zero (i := l) (by simp [Finset.mem_sdiff, hl, hlm]) ?_` and prove the remaining obligations. Rewrite using `[rho_up h hl, if_neg hlm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem xEx_below_zero {l m : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (hlm : l ≠ m) {τ ρ : M.Ty P} (h : M.Up P m τ ρ) :
    M.xEx P {m} τ (-(M.rho P ρ l : ℂ)) = 0 := by
  unfold M.xEx
  refine Finset.prod_eq_zero (i := l) (by simp [Finset.mem_sdiff, hl, hlm]) ?_
  rw [rho_up h hl, if_neg hlm]; push_cast; ring

variable {d : Q.NFData P A} (hd : Hyp d)
include hd

/- English proof (translation)
The claim follows from `(hX (dl ρ)).eq`.
-/
theorem comm_Pj {X : A} (hX : ∀ f, Commute (d.κ f) X) (ρ : M.Ty P) : Pj d.κ ρ * X = X * Pj d.κ ρ := (hX (dl ρ)).eq

/- English proof (translation)
The claim follows from `(hd.kc f).2.2.2.2.1`.
-/
theorem kc_GG (f : M.Ty P → ℂ) : Commute (d.κ f) d.L.GG := (hd.kc f).2.2.2.2.1
/- English proof (translation)
The claim follows from `(hd.kc f).2.2.2.2.2`.
-/
theorem kc_GGi (f : M.Ty P → ℂ) : Commute (d.κ f) d.L.GGi := (hd.kc f).2.2.2.2.2
/- English proof (translation)
The claim follows from `kc_kap hd f _`.
-/
theorem kappa_commute_coordinate (f : M.Ty P → ℂ) (Y : ℂ) : Commute (d.κ f) (d.x Y) := kc_kap hd f _

/- English proof (translation)
The claim follows from `((kc_GG hd f).mul_right (kappa_commute_coordinate hd f Y)).mul_right (kappa_commute_lowering_data hd f Y)`.
-/
theorem kappa_commute_lower_diagonal (f : M.Ty P → ℂ) (Y : ℂ) : Commute (d.κ f) (d.L.GG * d.x Y * d.L.l0 Y) :=
  ((kc_GG hd f).mul_right (kappa_commute_coordinate hd f Y)).mul_right (kappa_commute_lowering_data hd f Y)
/- English proof (translation)
The claim follows from `((kc_GG hd f).mul_right (kappa_commute_coordinate hd f Y)).mul_right (kappa_commute_raising_data hd f Y)`.
-/
theorem kappa_commute_upper_diagonal (f : M.Ty P → ℂ) (Y : ℂ) : Commute (d.κ f) (d.L.GG * d.x Y * d.L.m0 Y) :=
  ((kc_GG hd f).mul_right (kappa_commute_coordinate hd f Y)).mul_right (kappa_commute_raising_data hd f Y)

/- English proof (translation)
Rewrite using `[← mul_assoc, comm_Pj hd (kc_GG hd) ρ, mul_assoc, Q.NFData.x, Pj_kap, mul_smul_comm]`.
-/
theorem Pj_GGx (Y : ℂ) (ρ : M.Ty P) : Pj d.κ ρ * (d.L.GG * d.x Y) = M.xC P ρ Y • (d.L.GG * Pj d.κ ρ) := by
  rw [← mul_assoc, comm_Pj hd (kc_GG hd) ρ, mul_assoc, Q.NFData.x, Pj_kap, mul_smul_comm]

/- English proof (translation)
Unfold `Q.NFData.weightedSumBis`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, mul_assoc, kap_Pj, mul_smul_comm, P_SS_P hd, if_neg (fun h => ee_not_self hi ρ (off_of_up h)), smul_zero]`.
-/
theorem projection_lower_sum_zero (Y : ℂ) (ρ : M.Ty P) : Pj d.κ ρ * d.weightedSumBis Y * Pj d.κ ρ = 0 := by
  unfold Q.NFData.weightedSumBis
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← mul_assoc, mul_assoc, kap_Pj, mul_smul_comm, P_SS_P hd, if_neg (fun h => ee_not_self hi ρ (off_of_up h)),
    smul_zero]

/- English proof (translation)
Use `ext_right hd fun ρ => ?_` and prove the remaining obligations. Rewrite using `[kap_Pj]`. Establish `hNF` using `Formalism.FourierDecayAlt.P.nrmFacts_statement P hP l hl`. Distinguish the cases in `h : ∃ τ, M.Up P l τ ρ`. Take `⟨τ, hτ⟩` from `h`.

Take `⟨Y, hY⟩ : ∃ Y : ℂ, Y = -(M.rho P ρ l : ℂ)` from `⟨_, rfl⟩`. Establish `hx0 : M.xC P ρ Y = 0` using `by rw [hY]; exact xC_root ρ hl`. Establish `e1` using `congrArg (fun X => Pj d.κ ρ * X * Pj d.κ ρ) (lower_determinant_relation d hS Y)`. Rewrite `e1` using `[mul_sub, sub_mul, show Pj d.κ ρ * (d.QQ Y 1 1 * d.QQ (Y + 1) 0 0) = Pj d.κ ρ * d.QQ Y 1 1 * d.QQ (Y + 1) 0 0 by rw [mul_assoc], normal_form_diagonal, Pj_GGx hd, hx0, zero_smul, zero_mul, zero_mul, sub_zero]`. Rewrite using `[show Pj d.κ ρ * -algebraMap ℂ A (M.qC P Y) * Pj d.κ ρ = -(M.qC P Y • Pj d.κ ρ) by`.

Rewrite `e1` using `[mul_neg, neg_mul, ← Algebra.commutes, mul_assoc, Pj_idem, ← Algebra.smul_def]]`. Rewrite `e1` using `[normal_form_lower_left, normal_form_upper_right]`. Simplify using `only [add_mul, mul_add] at e1`. Establish `z1 : Pj d.κ ρ * (d.L.GG * d.x Y * d.L.l0 Y * (d.L.GG * d.x (Y + 1) * d.L.m0 (Y + 1))) * Pj d.κ ρ = 0`. Rewrite using `[show d.L.GG * d.x Y * d.L.l0 Y * (d.L.GG * d.x (Y + 1) * d.L.m0 (Y + 1)) = d.L.GG * d.x Y * (d.L.l0 Y * (d.L.GG * d.x (Y + 1) * d.L.m0 (Y + 1))) by simp only [mul_assoc], ← mul_assoc, Pj_GGx hd, hx0]; simp`.

Establish `z2 : Pj d.κ ρ * (d.L.GG * d.x Y * d.L.l0 Y * d.S12 (Y + 1)) * Pj d.κ ρ = 0`. Rewrite using `[show d.L.GG * d.x Y * d.L.l0 Y * d.S12 (Y + 1) = d.L.GG * d.x Y * (d.L.l0 Y * d.S12 (Y + 1)) by simp only [mul_assoc], ← mul_assoc, Pj_GGx hd, hx0]; simp`. Establish `z3 : Pj d.κ ρ * (d.weightedSumBis Y * (d.L.GG * d.x (Y + 1) * d.L.m0 (Y + 1))) * Pj d.κ ρ = 0`. Rewrite using `[show Pj d.κ ρ * (d.weightedSumBis Y * (d.L.GG * d.x (Y + 1) * d.L.m0 (Y + 1))) * Pj d.κ ρ = Pj d.κ ρ * d.weightedSumBis Y * ((d.L.GG * d.x (Y + 1) * d.L.m0 (Y + 1)) * Pj d.κ ρ) by simp only [mul_assoc], ← comm_Pj hd (kappa_commute_upper_diagonal hd · (Y + 1)) ρ, ← mul_assoc, pro …`. Rewrite `e1` using `[z1, z2, z3, zero_add, zero_add, zero_add, blk_21_12 hd, Finset.sum_eq_single l]`.

Rewrite `e1` using `[dif_pos ⟨τ, hτ⟩]`. Establish `hc` using `(⟨τ, hτ⟩ : ∃ τ, M.Up P l τ ρ).choose_spec`. Establish `hτ' : (⟨τ, hτ⟩ : ∃ τ, M.Up P l τ ρ).choose = τ` using `up_inj hc hτ`. Rewrite `e1` using `[hτ', xEx_below hτ, xEx_below hτ]`. Take `⟨hpos, hND⟩` from `(hNF τ).1 ρ hτ`.

Use `set D1 : ℝ := ∏ i ∈ (Icc 1 (P.k - 1)).erase l, (M.rho P ρ i - M.rho P ρ l) with hD1`. Use `set D2 : ℝ := ∏ i ∈ (Icc 1 (P.k - 1)).erase l, (M.rho P ρ i - M.rho P ρ l + 1) with hD2`. Establish `hN : M.Nrm P l τ = -I.qpoly P.k P.T P.T' P.u P.u' (-M.rho P ρ l) / (D2 * D1)`. Unfold `M.Nrm`. Establish `e3 : M.rho P τ l = M.rho P ρ l - 1` using `by rw [rho_up hτ hl, if_pos rfl]; ring`.

Rewrite using `[e3, hD1, hD2, show -(M.rho P ρ l - 1) - 1 = -M.rho P ρ l by ring]`. Use `congr 2`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_erase]`. Rewrite using `[rho_up hτ hi.2, if_neg hi.1]`.

Expand and normalize the polynomial expressions, which then agree. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_erase]`. Rewrite using `[rho_up hτ hi.2, if_neg hi.1]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hDne : D2 * D1 ≠ 0`. Introduce `h0`. Rewrite `hpos` using `[hN, h0, div_zero]`. Conclude with `lt_irrefl _ hpos`. Establish `hq : M.qC P Y = (I.qpoly P.k P.T P.T' P.u P.u' (-M.rho P ρ l) : ℂ)`.

Rewrite using `[hY, ← (Formalism.FourierDecayAlt.P.realPoints_statement P ρ (-M.rho P ρ l)).2]`. Use `push_cast`. Put the polynomial expressions in normal form. Establish `hc1 : (∏ i ∈ (Icc 1 (P.k - 1)).erase l, (Y + (M.rho P ρ i : ℂ))) = (D1 : ℂ)`. Rewrite using `[hD1]`.

Use `push_cast`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hY]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc2 : (∏ i ∈ (Icc 1 (P.k - 1)).erase l, (Y + 1 + (M.rho P ρ i : ℂ))) = (D2 : ℂ)`.

Rewrite using `[hD2]`. Use `push_cast`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hY]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `e1` using `[hc1, hc2, hq]`. Establish `hcne : ((D1 : ℂ) * (D2 : ℂ)) ≠ 0`. Rewrite using `[mul_comm]`. Conclude with `hDne` after adjusting the coercions. Establish `e4 : ((M.NrmDown P l ρ : ℝ) : ℂ) = -(I.qpoly P.k P.T P.T' P.u P.u' (-M.rho P ρ l) : ℂ) / ((D1 : ℂ) * (D2 : ℂ))`.

Rewrite using `[hND, hN]`. Use `push_cast`. Rewrite using `[mul_comm (D2 : ℂ)]`. Establish `e5 : d.SS l * star (d.SS l) * Pj d.κ ρ = ((D1 : ℂ) * (D2 : ℂ))⁻¹ • (((D1 : ℂ) * (D2 : ℂ)) • (d.SS l * star (d.SS l) * Pj d.κ ρ))`. Rewrite using `[smul_smul, inv_mul_cancel₀ hcne, one_smul]`.

Rewrite using `[e4, e5, e1, smul_neg, smul_smul, ← neg_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Introduce `m hm hml split_ifs with h'`. Rewrite using `[hY, xEx_below_zero hl (Ne.symm hml) h'.choose_spec]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce `h'`. Conclude with `absurd hl h'`. Establish `hs : star (d.SS l) * Pj d.κ ρ = 0` using `left_none hd (supp_SSs hd l) (fun τ hτ => h ⟨τ, by`.

Use `off_neg hτ` as an intermediate fact. Rewrite `this` using `[neg_neg]`. Conclude with `up_of_off this⟩)`. Rewrite using `[mul_assoc, hs, mul_zero, (hNF ρ).2.2 h]`. Simplify using the standard rewrite rules.
-/
theorem ssDown (hP : P.OK) (hS : Wd.IsStart d.QQ (M.qC P)) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) :
    d.SS l * star (d.SS l) = d.κ fun ρ => ((M.NrmDown P l ρ : ℝ) : ℂ) := by
  refine ext_right hd fun ρ => ?_
  rw [kap_Pj]
  have hNF := Formalism.FourierDecayAlt.P.nrmFacts_statement P hP l hl
  by_cases h : ∃ τ, M.Up P l τ ρ
  · obtain ⟨τ, hτ⟩ := h
    obtain ⟨Y, hY⟩ : ∃ Y : ℂ, Y = -(M.rho P ρ l : ℂ) := ⟨_, rfl⟩
    have hx0 : M.xC P ρ Y = 0 := by rw [hY]; exact xC_root ρ hl

    have e1 := congrArg (fun X => Pj d.κ ρ * X * Pj d.κ ρ) (lower_determinant_relation d hS Y)
    rw [mul_sub, sub_mul, show Pj d.κ ρ * (d.QQ Y 1 1 * d.QQ (Y + 1) 0 0) = Pj d.κ ρ * d.QQ Y 1 1 * d.QQ (Y + 1) 0 0
      by rw [mul_assoc], normal_form_diagonal, Pj_GGx hd, hx0, zero_smul, zero_mul, zero_mul, sub_zero] at e1
    rw [show Pj d.κ ρ * -algebraMap ℂ A (M.qC P Y) * Pj d.κ ρ = -(M.qC P Y • Pj d.κ ρ) by
      rw [mul_neg, neg_mul, ← Algebra.commutes, mul_assoc, Pj_idem, ← Algebra.smul_def]] at e1
    rw [normal_form_lower_left, normal_form_upper_right] at e1
    simp only [add_mul, mul_add] at e1
    have z1 : Pj d.κ ρ * (d.L.GG * d.x Y * d.L.l0 Y * (d.L.GG * d.x (Y + 1) * d.L.m0 (Y + 1))) * Pj d.κ ρ = 0 := by
      rw [show d.L.GG * d.x Y * d.L.l0 Y * (d.L.GG * d.x (Y + 1) * d.L.m0 (Y + 1)) =
        d.L.GG * d.x Y * (d.L.l0 Y * (d.L.GG * d.x (Y + 1) * d.L.m0 (Y + 1))) by simp only [mul_assoc], ← mul_assoc,
        Pj_GGx hd, hx0]; simp
    have z2 : Pj d.κ ρ * (d.L.GG * d.x Y * d.L.l0 Y * d.S12 (Y + 1)) * Pj d.κ ρ = 0 := by
      rw [show d.L.GG * d.x Y * d.L.l0 Y * d.S12 (Y + 1) =
        d.L.GG * d.x Y * (d.L.l0 Y * d.S12 (Y + 1)) by simp only [mul_assoc], ← mul_assoc,
        Pj_GGx hd, hx0]; simp
    have z3 : Pj d.κ ρ * (d.weightedSumBis Y * (d.L.GG * d.x (Y + 1) * d.L.m0 (Y + 1))) * Pj d.κ ρ = 0 := by
      rw [show Pj d.κ ρ * (d.weightedSumBis Y * (d.L.GG * d.x (Y + 1) * d.L.m0 (Y + 1))) * Pj d.κ ρ =
        Pj d.κ ρ * d.weightedSumBis Y * ((d.L.GG * d.x (Y + 1) * d.L.m0 (Y + 1)) * Pj d.κ ρ) by simp only [mul_assoc],
        ← comm_Pj hd (kappa_commute_upper_diagonal hd · (Y + 1)) ρ, ← mul_assoc, projection_lower_sum_zero hd, zero_mul]
    rw [z1, z2, z3, zero_add, zero_add, zero_add, blk_21_12 hd, Finset.sum_eq_single l] at e1
    · rw [dif_pos ⟨τ, hτ⟩] at e1
      have hc := (⟨τ, hτ⟩ : ∃ τ, M.Up P l τ ρ).choose_spec
      have hτ' : (⟨τ, hτ⟩ : ∃ τ, M.Up P l τ ρ).choose = τ := up_inj hc hτ
      rw [hτ', xEx_below hτ, xEx_below hτ] at e1
      obtain ⟨hpos, hND⟩ := (hNF τ).1 ρ hτ
      set D1 : ℝ := ∏ i ∈ (Icc 1 (P.k - 1)).erase l, (M.rho P ρ i - M.rho P ρ l) with hD1
      set D2 : ℝ := ∏ i ∈ (Icc 1 (P.k - 1)).erase l, (M.rho P ρ i - M.rho P ρ l + 1) with hD2
      have hN : M.Nrm P l τ = -I.qpoly P.k P.T P.T' P.u P.u' (-M.rho P ρ l) / (D2 * D1) := by
        unfold M.Nrm
        have e3 : M.rho P τ l = M.rho P ρ l - 1 := by rw [rho_up hτ hl, if_pos rfl]; ring
        rw [e3, hD1, hD2, show -(M.rho P ρ l - 1) - 1 = -M.rho P ρ l by ring]
        congr 2
        · refine Finset.prod_congr rfl fun i hi => ?_
          rw [Finset.mem_erase] at hi; rw [rho_up hτ hi.2, if_neg hi.1]; ring
        · refine Finset.prod_congr rfl fun i hi => ?_
          rw [Finset.mem_erase] at hi; rw [rho_up hτ hi.2, if_neg hi.1]; ring
      have hDne : D2 * D1 ≠ 0 := by
        intro h0; rw [hN, h0, div_zero] at hpos; exact lt_irrefl _ hpos
      have hq : M.qC P Y = (I.qpoly P.k P.T P.T' P.u P.u' (-M.rho P ρ l) : ℂ) := by
        rw [hY, ← (Formalism.FourierDecayAlt.P.realPoints_statement P ρ (-M.rho P ρ l)).2]; push_cast; ring_nf
      have hc1 : (∏ i ∈ (Icc 1 (P.k - 1)).erase l, (Y + (M.rho P ρ i : ℂ))) = (D1 : ℂ) := by
        rw [hD1]; push_cast; refine Finset.prod_congr rfl fun i _ => ?_; rw [hY]; ring
      have hc2 : (∏ i ∈ (Icc 1 (P.k - 1)).erase l, (Y + 1 + (M.rho P ρ i : ℂ))) = (D2 : ℂ) := by
        rw [hD2]; push_cast; refine Finset.prod_congr rfl fun i _ => ?_; rw [hY]; ring
      rw [hc1, hc2, hq] at e1
      have hcne : ((D1 : ℂ) * (D2 : ℂ)) ≠ 0 := by
        rw [mul_comm]; exact_mod_cast hDne
      have e4 : ((M.NrmDown P l ρ : ℝ) : ℂ) = -(I.qpoly P.k P.T P.T' P.u P.u' (-M.rho P ρ l) : ℂ) / ((D1 : ℂ) * (D2 : ℂ)) := by
        rw [hND, hN]; push_cast; rw [mul_comm (D2 : ℂ)]
      have e5 : d.SS l * star (d.SS l) * Pj d.κ ρ =
          ((D1 : ℂ) * (D2 : ℂ))⁻¹ • (((D1 : ℂ) * (D2 : ℂ)) • (d.SS l * star (d.SS l) * Pj d.κ ρ)) := by
        rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
      rw [e4, e5, e1, smul_neg, smul_smul, ← neg_smul]
      congr 1; ring
    · intro m hm hml
      split_ifs with h'
      · rw [hY, xEx_below_zero hl (Ne.symm hml) h'.choose_spec]; simp
      · simp
    · intro h'; exact absurd hl h'
  · have hs : star (d.SS l) * Pj d.κ ρ = 0 := left_none hd (supp_SSs hd l) (fun τ hτ => h ⟨τ, by
      have := off_neg hτ; rw [neg_neg] at this; exact up_of_off this⟩)
    rw [mul_assoc, hs, mul_zero, (hNF ρ).2.2 h]; simp

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.rtt_relation_entries ℂ A d.QQ v u (hS.rtt v u) i j k l`.
-/
theorem rtt_ent (d : Q.NFData P A) (hS : Wd.IsStart d.QQ (M.qC P)) (u v : ℂ) (i j k l : Fin 2) :
    (u - v) • (d.QQ u i j * d.QQ v k l - d.QQ v k l * d.QQ u i j) =
      d.QQ u k j * d.QQ v i l - d.QQ v k j * d.QQ u i l :=
  Formalism.FourierDecayAlt.P.rtt_relation_entries ℂ A d.QQ v u (hS.rtt v u) i j k l

/- English proof (translation)
Introduce `h'` and use `hne (off_eq h' h m hm)`.
-/
theorem off_contra {δ δ' : ℕ → ℤ} {ρ σ : M.Ty P} (h : Off δ ρ σ) {m : ℕ} (hm : m ∈ Icc 1 (P.k - 1))
    (hne : δ' m ≠ δ m) : ¬ Off δ' ρ σ := fun h' => hne (off_eq h' h m hm)

/- English proof (translation)
Rewrite `hl` using `[Finset.mem_Icc]`. Establish `hρ : 1 ≤ ((ρ ⟨l - 1, by omega⟩ : Fin _) : ℕ)`. Use `h ⟨l - 1, by omega⟩; simp only [show l - 1 + 1 = l by omega, hδ] at this; omega` as an intermediate fact. Use `⟨fun i => if hi : (i : ℕ) + 1 = l then ⟨(ρ i : ℕ) - 1, by have := (ρ i).isLt; omega⟩ else ρ i, ?_⟩` and prove the remaining obligations. Introduce `i`.

Distinguish the cases in `hi : (i : ℕ) + 1 = l`. Simplify using `only [dif_pos hi, if_pos hi]`. Establish `e` using `h i`. Establish `e2 : δ ((i : ℕ) + 1) = -1` using `by rw [hi]; exact hδ`. Use linear arithmetic over natural numbers and integers.

Simplify using `[dif_neg hi, if_neg hi]`.
-/
theorem box_down {δ : ℕ → ℤ} {ρ σ : M.Ty P} (h : Off δ ρ σ) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (hδ : δ l = -1) :
    ∃ τ, M.Up P l τ ρ := by
  rw [Finset.mem_Icc] at hl
  have hρ : 1 ≤ ((ρ ⟨l - 1, by omega⟩ : Fin _) : ℕ) := by
    have := h ⟨l - 1, by omega⟩; simp only [show l - 1 + 1 = l by omega, hδ] at this; omega
  refine ⟨fun i => if hi : (i : ℕ) + 1 = l then ⟨(ρ i : ℕ) - 1, by have := (ρ i).isLt; omega⟩ else ρ i, ?_⟩
  intro i
  by_cases hi : (i : ℕ) + 1 = l
  · simp only [dif_pos hi, if_pos hi]
    have e := h i
    have e2 : δ ((i : ℕ) + 1) = -1 := by rw [hi]; exact hδ
    omega
  · simp [dif_neg hi, if_neg hi]

/- English proof (translation)
Rewrite `hl` using `[Finset.mem_Icc]`. Use `⟨fun i => if hi : (i : ℕ) + 1 = l then ⟨(ρ i : ℕ) + 1, by` and prove the remaining obligations. Establish `e` using `h i; have e2 : δ ((i : ℕ) + 1) = 1 := by rw [hi]; exact hδ`. Use `(σ i).isLt` as an intermediate fact. Use the proof step `omega⟩ else ρ i, ?_⟩`.

Introduce `i`. Distinguish the cases in `hi : (i : ℕ) + 1 = l`. Simplify using `only [dif_pos hi, if_pos hi]`. Simplify using `[dif_neg hi, if_neg hi]`.
-/
theorem box_up {δ : ℕ → ℤ} {ρ σ : M.Ty P} (h : Off δ ρ σ) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (hδ : δ l = 1) :
    ∃ τ, M.Up P l ρ τ := by
  rw [Finset.mem_Icc] at hl
  refine ⟨fun i => if hi : (i : ℕ) + 1 = l then ⟨(ρ i : ℕ) + 1, by
      have e := h i; have e2 : δ ((i : ℕ) + 1) = 1 := by rw [hi]; exact hδ
      have := (σ i).isLt; omega⟩ else ρ i, ?_⟩
  intro i
  by_cases hi : (i : ℕ) + 1 = l
  · simp only [dif_pos hi, if_pos hi]
  · simp [dif_neg hi, if_neg hi]

/- English proof (translation)
Establish `h` using `Formalism.FourierDecayAlt.P.types_interlace P hP π`. Establish `a` using `h i hi`. Establish `b` using `h (i + 1) hi'`. Combine the linear relations using `[a.2.2.1, b.1]`.
-/
theorem gap1 (hP : P.OK) (π : M.Ty P) {i : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (hi' : i + 1 ∈ Icc 1 (P.k - 1)) :
    M.rho P π (i + 1) + 1 ≤ M.rho P π i := by
  have h := Formalism.FourierDecayAlt.P.types_interlace P hP π
  have a := h i hi; have b := h (i + 1) hi'
  linarith [a.2.2.1, b.1]

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, i' = i + 1 + n` from `⟨i' - i - 1, by omega⟩`. Proceed by induction on `n with`. Consider the case `zero => exact gap1 hP π hi hi'`. Consider the case `succ n ih`. Rewrite `hi`, `hi'` using `[Finset.mem_Icc]`.

Establish `h1` using `ih (by rw [Finset.mem_Icc]; omega) (by omega)`. Establish `h2` using `gap1 hP π (i := i + 1 + n) (by rw [Finset.mem_Icc]; omega) (by rw [Finset.mem_Icc]; omega)`. Rewrite using `[show i + 1 + (n + 1) = i + 1 + n + 1 by ring]; linarith`.
-/
theorem gap (hP : P.OK) (π : M.Ty P) {i i' : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (hi' : i' ∈ Icc 1 (P.k - 1)) (h : i < i') :
    M.rho P π i' + 1 ≤ M.rho P π i := by
  obtain ⟨n, rfl⟩ : ∃ n, i' = i + 1 + n := ⟨i' - i - 1, by omega⟩
  induction n with
  | zero => exact gap1 hP π hi hi'
  | succ n ih =>
    rw [Finset.mem_Icc] at hi hi'
    have h1 := ih (by rw [Finset.mem_Icc]; omega) (by omega)
    have h2 := gap1 hP π (i := i + 1 + n) (by rw [Finset.mem_Icc]; omega) (by rw [Finset.mem_Icc]; omega)
    rw [show i + 1 + (n + 1) = i + 1 + n + 1 by ring]; linarith

/- English proof (translation)
Break down `Nat.lt_or_gt_of_ne h with h | h` into its components or cases. Use `gap hP π hi hi' h` as an intermediate fact. Introduce `e`. Combine the linear equalities and inequalities to obtain the conclusion. Use `gap hP π hi' hi h` as an intermediate fact.

Introduce `e`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rho_ne (hP : P.OK) (π : M.Ty P) {i i' : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (hi' : i' ∈ Icc 1 (P.k - 1))
    (h : i ≠ i') : M.rho P π i ≠ M.rho P π i' := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have := gap hP π hi hi' h; intro e; linarith
  · have := gap hP π hi' hi h; intro e; linarith

/- English proof (translation)
Unfold `M.xEx`. Rewrite using `[Finset.sdiff_singleton_eq_erase]`.
-/
theorem xEx_erase (l : ℕ) (π : M.Ty P) (Y : ℂ) :
    M.xEx P {l} π Y = ∏ i ∈ (Icc 1 (P.k - 1)).erase l, (Y + (M.rho P π i : ℂ)) := by
  unfold M.xEx; rw [Finset.sdiff_singleton_eq_erase]

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

/- English proof (translation)
The claim follows from `e ▸ h`.
-/
theorem off_congr {δ δ' : ℕ → ℤ} {ρ σ : M.Ty P} (h : Off δ ρ σ) (e : δ = δ') : Off δ' ρ σ := e ▸ h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ee_val (l m : ℕ) : ee l m = if m = l then 1 else 0 := rfl

variable {d : Q.NFData P A} (hd : Hyp d)
include hd

/- English proof (translation)
The claim follows from `supp_mul d.κ (supp_SS hd i) (supp_kcomm hd (kc_kap hd · g))`.
-/
theorem supp_SSk (i : ℕ) (g : M.Ty P → ℂ) : Supp d.κ (0 + ee i) (d.SS i * d.κ g) :=
  supp_mul d.κ (supp_SS hd i) (supp_kcomm hd (kc_kap hd · g))

/- English proof (translation)
The claim follows from `supp_mul d.κ (supp_kcomm hd (kc_kap hd · g)) (supp_SSs hd m)`.
-/
theorem supp_kSSs (m : ℕ) (g : M.Ty P → ℂ) : Supp d.κ (-ee m + 0) (d.κ g * star (d.SS m)) :=
  supp_mul d.κ (supp_kcomm hd (kc_kap hd · g)) (supp_SSs hd m)

/- English proof (translation)
Establish `hs : star (d.SS m) * Pj d.κ ρ = Pj d.κ τ * star (d.SS m) * Pj d.κ ρ` using `left_single hd (supp_SSs hd m) (off_neg (off_of_up hτ))`. Establish `e : Pj d.κ σ * (d.SS i * d.κ g * (d.κ h * star (d.SS m))) * Pj d.κ ρ = Pj d.κ σ * d.SS i * (d.κ g * d.κ h * (star (d.SS m) * Pj d.κ ρ))` using `by simp only [mul_assoc]`. Rewrite using `[e, hs, ← map_mul, show d.κ (g * h) * (Pj d.κ τ * star (d.SS m) * Pj d.κ ρ) = d.κ (g * h) * Pj d.κ τ * star (d.SS m) * Pj d.κ ρ by simp only [mul_assoc], kap_Pj, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]`. Simplify using `only [Pi.mul_apply]`. Use `congr 1`.

Rewrite using `[show Pj d.κ τ * star (d.SS m) * Pj d.κ ρ = star (d.SS m) * Pj d.κ ρ from hs.symm]`. Simplify using `only [mul_assoc]`.
-/
theorem term_dn {i m : ℕ} {τ ρ : M.Ty P} (hτ : M.Up P m τ ρ) (σ : M.Ty P) (g h : M.Ty P → ℂ) :
    Pj d.κ σ * (d.SS i * d.κ g * (d.κ h * star (d.SS m))) * Pj d.κ ρ =
      (g τ * h τ) • (Pj d.κ σ * (d.SS i * star (d.SS m)) * Pj d.κ ρ) := by
  have hs : star (d.SS m) * Pj d.κ ρ = Pj d.κ τ * star (d.SS m) * Pj d.κ ρ :=
    left_single hd (supp_SSs hd m) (off_neg (off_of_up hτ))
  have e : Pj d.κ σ * (d.SS i * d.κ g * (d.κ h * star (d.SS m))) * Pj d.κ ρ =
      Pj d.κ σ * d.SS i * (d.κ g * d.κ h * (star (d.SS m) * Pj d.κ ρ)) := by simp only [mul_assoc]
  rw [e, hs, ← map_mul, show d.κ (g * h) * (Pj d.κ τ * star (d.SS m) * Pj d.κ ρ) =
    d.κ (g * h) * Pj d.κ τ * star (d.SS m) * Pj d.κ ρ by simp only [mul_assoc], kap_Pj, smul_mul_assoc,
    smul_mul_assoc, mul_smul_comm]
  simp only [Pi.mul_apply]
  congr 1
  rw [show Pj d.κ τ * star (d.SS m) * Pj d.κ ρ = star (d.SS m) * Pj d.κ ρ from hs.symm]
  simp only [mul_assoc]

/- English proof (translation)
Rewrite using `[show Pj d.κ σ * (d.κ g * star (d.SS m) * (d.SS i * d.κ h)) * Pj d.κ ρ = (Pj d.κ σ * d.κ g) * (star (d.SS m) * d.SS i) * (d.κ h * Pj d.κ ρ) by simp only [mul_assoc], Pj_kap, kap_Pj]`. Simplify using `only [smul_mul_assoc, mul_smul_comm, smul_smul]`. Rewrite using `[mul_comm (h ρ)]`.
-/
theorem term_up (i m : ℕ) (σ ρ : M.Ty P) (g h : M.Ty P → ℂ) :
    Pj d.κ σ * (d.κ g * star (d.SS m) * (d.SS i * d.κ h)) * Pj d.κ ρ =
      (g σ * h ρ) • (Pj d.κ σ * (star (d.SS m) * d.SS i) * Pj d.κ ρ) := by
  rw [show Pj d.κ σ * (d.κ g * star (d.SS m) * (d.SS i * d.κ h)) * Pj d.κ ρ =
    (Pj d.κ σ * d.κ g) * (star (d.SS m) * d.SS i) * (d.κ h * Pj d.κ ρ) by simp only [mul_assoc], Pj_kap, kap_Pj]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm (h ρ)]

section Mixed

variable {l j : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l)
  {ρ σ : M.Ty P} (hσ : Off (ee j + -ee l) ρ σ)
include hl hj hjl hσ

/- English proof (translation)
Use `off_contra hσ hl ?_` and prove the remaining obligations. Rewrite using `[show (ee j + -ee l) l = -1 by simp [ee, Ne.symm hjl]]; omega`.
-/
theorem mixed_not_off_l {δ : ℕ → ℤ} (h : 0 ≤ δ l) : ¬ Off δ ρ σ := by
  refine off_contra hσ hl ?_
  rw [show (ee j + -ee l) l = -1 by simp [ee, Ne.symm hjl]]; omega

/- English proof (translation)
Use `off_contra hσ hj ?_` and prove the remaining obligations. Rewrite using `[show (ee j + -ee l) j = 1 by simp [ee, hjl]]; omega`.
-/
theorem mixed_not_off_j {δ : ℕ → ℤ} (h : δ j ≤ 0) : ¬ Off δ ρ σ := by
  refine off_contra hσ hj ?_
  rw [show (ee j + -ee l) j = 1 by simp [ee, hjl]]; omega

/- English proof (translation)
Rewrite using `[normal_form_upper_right, normal_form_lower_left]`. Simplify using `only [add_mul, mul_add]`. Establish `z1 : Pj d.κ σ * (d.L.GG * d.x u * d.L.m0 u * (d.L.GG * d.x v * d.L.l0 v)) * Pj d.κ ρ = 0` using `supp_kcomm hd (fun f => (kappa_commute_upper_diagonal hd f u).mul_right (kappa_commute_lower_diagonal hd f v)) ρ σ (mixed_not_off_j hd hl hj hjl hσ (by simp))`. Establish `z2 : Pj d.κ σ * (d.L.GG * d.x u * d.L.m0 u * d.weightedSumBis v) * Pj d.κ ρ = 0`. Unfold `Q.NFData.weightedSumBis`.

Rewrite using `[Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `exact supp_mul d.κ (supp_kcomm hd (kappa_commute_upper_diagonal hd · u)) (supp_SSk hd i _) ρ σ (mixed_not_off_l hd hl hj hjl hσ (by simp only [Pi.add_apply, Pi.zero_apply, ee]; split_ifs <;> omega))`. Establish `z3 : Pj d.κ σ * (d.S12 u * (d.L.GG * d.x v * d.L.l0 v)) * Pj d.κ ρ = 0`. Unfold `Q.NFData.S12`.

Rewrite using `[Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Apply the tactic sequence `exact supp_mul d.κ (supp_kSSs hd m _) (supp_kcomm hd (kappa_commute_lower_diagonal hd · v)) ρ σ (mixed_not_off_j hd hl hj hjl hσ (by simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, ee]; split_ifs <;> omega))`. Rewrite using `[z1, z2, z3, zero_add, zero_add, zero_add]`. Unfold `Q.NFData.S12 Q.NFData.weightedSumBis`.

Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_eq_single j, Finset.sum_eq_single l]`. Rewrite using `[term_up hd]`. Introduce `m _ hml`. Rewrite using `[term_up hd, supp_mul d.κ (supp_SSs hd m) (supp_SS hd j) ρ σ, smul_zero]`.

Conclude with `mixed_not_off_l hd hl hj hjl hσ (by simp only [Pi.add_apply, Pi.neg_apply, ee, if_neg hjl, if_neg (Ne.symm hml)]; omega)`. Introduce `h'`. Conclude with `absurd hl h'`. Introduce `i _ hij`. Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[term_up hd, supp_mul d.κ (supp_SSs hd m) (supp_SS hd i) ρ σ, smul_zero]`. Apply the tactic sequence `exact mixed_not_off_j hd hl hj hjl hσ (by simp only [Pi.add_apply, Pi.neg_apply, ee, if_neg (Ne.symm hij)]; split_ifs <;> omega)`. Introduce `h'`. Conclude with `absurd hj h'`.
-/
theorem blk_mixed1 (u v : ℂ) :
    Pj d.κ σ * (d.QQ u 0 1 * d.QQ v 1 0) * Pj d.κ ρ =
      (M.xEx P {l} σ u * M.xEx P {j} ρ v) • (Pj d.κ σ * (star (d.SS l) * d.SS j) * Pj d.κ ρ) := by
  rw [normal_form_upper_right, normal_form_lower_left]
  simp only [add_mul, mul_add]
  have z1 : Pj d.κ σ * (d.L.GG * d.x u * d.L.m0 u * (d.L.GG * d.x v * d.L.l0 v)) * Pj d.κ ρ = 0 :=
    supp_kcomm hd (fun f => (kappa_commute_upper_diagonal hd f u).mul_right (kappa_commute_lower_diagonal hd f v)) ρ σ
      (mixed_not_off_j hd hl hj hjl hσ (by simp))
  have z2 : Pj d.κ σ * (d.L.GG * d.x u * d.L.m0 u * d.weightedSumBis v) * Pj d.κ ρ = 0 := by
    unfold Q.NFData.weightedSumBis; rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact supp_mul d.κ (supp_kcomm hd (kappa_commute_upper_diagonal hd · u)) (supp_SSk hd i _) ρ σ
      (mixed_not_off_l hd hl hj hjl hσ (by simp only [Pi.add_apply, Pi.zero_apply, ee]; split_ifs <;> omega))
  have z3 : Pj d.κ σ * (d.S12 u * (d.L.GG * d.x v * d.L.l0 v)) * Pj d.κ ρ = 0 := by
    unfold Q.NFData.S12; rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun m _ => ?_
    exact supp_mul d.κ (supp_kSSs hd m _) (supp_kcomm hd (kappa_commute_lower_diagonal hd · v)) ρ σ
      (mixed_not_off_j hd hl hj hjl hσ (by simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, ee]; split_ifs <;> omega))
  rw [z1, z2, z3, zero_add, zero_add, zero_add]
  unfold Q.NFData.S12 Q.NFData.weightedSumBis
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_eq_single j, Finset.sum_eq_single l]
  · rw [term_up hd]
  · intro m _ hml
    rw [term_up hd, supp_mul d.κ (supp_SSs hd m) (supp_SS hd j) ρ σ, smul_zero]
    exact mixed_not_off_l hd hl hj hjl hσ (by simp only [Pi.add_apply, Pi.neg_apply, ee, if_neg hjl, if_neg (Ne.symm hml)]; omega)
  · intro h'; exact absurd hl h'
  · intro i _ hij
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [term_up hd, supp_mul d.κ (supp_SSs hd m) (supp_SS hd i) ρ σ, smul_zero]
    exact mixed_not_off_j hd hl hj hjl hσ (by simp only [Pi.add_apply, Pi.neg_apply, ee, if_neg (Ne.symm hij)]; split_ifs <;> omega)
  · intro h'; exact absurd hj h'

/- English proof (translation)
Rewrite using `[normal_form_upper_right, normal_form_lower_left]`. Simplify using `only [add_mul, mul_add]`. Establish `z1 : Pj d.κ σ * (d.L.GG * d.x v * d.L.l0 v * (d.L.GG * d.x u * d.L.m0 u)) * Pj d.κ ρ = 0` using `supp_kcomm hd (fun f => (kappa_commute_lower_diagonal hd f v).mul_right (kappa_commute_upper_diagonal hd f u)) ρ σ (mixed_not_off_j hd hl hj hjl hσ (by simp))`. Establish `z2 : Pj d.κ σ * (d.L.GG * d.x v * d.L.l0 v * d.S12 u) * Pj d.κ ρ = 0`. Unfold `Q.NFData.S12`.

Rewrite using `[Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Apply the tactic sequence `exact supp_mul d.κ (supp_kcomm hd (kappa_commute_lower_diagonal hd · v)) (supp_kSSs hd m _) ρ σ (mixed_not_off_j hd hl hj hjl hσ (by simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, ee]; split_ifs <;> omega))`. Establish `z3 : Pj d.κ σ * (d.weightedSumBis v * (d.L.GG * d.x u * d.L.m0 u)) * Pj d.κ ρ = 0`. Unfold `Q.NFData.weightedSumBis`.

Rewrite using `[Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `exact supp_mul d.κ (supp_SSk hd i _) (supp_kcomm hd (kappa_commute_upper_diagonal hd · u)) ρ σ (mixed_not_off_l hd hl hj hjl hσ (by simp only [Pi.add_apply, Pi.zero_apply, ee]; split_ifs <;> omega))`. Rewrite using `[z1, z2, z3, zero_add, zero_add, zero_add]`. Unfold `Q.NFData.S12 Q.NFData.weightedSumBis`.

Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_eq_single l, Finset.sum_eq_single j]`. Rewrite using `[term_dn hd hτ]`. Introduce `i _ hij`. Conclude with `supp_mul d.κ (supp_SSk hd i _) (supp_kSSs hd l _) ρ σ (mixed_not_off_j hd hl hj hjl hσ (by simp [ee, Ne.symm hij, hjl]))`.

Introduce `h'`. Conclude with `absurd hj h'`. Introduce `m _ hml`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `exact supp_mul d.κ (supp_SSk hd i _) (supp_kSSs hd m _) ρ σ (mixed_not_off_l hd hl hj hjl hσ (by simp [ee, Ne.symm hml]; try (split_ifs <;> norm_num)))`.

Introduce `h'`. Conclude with `absurd hl h'`.
-/
theorem blk_mixed2 {τ : M.Ty P} (hτ : M.Up P l τ ρ) (u v : ℂ) :
    Pj d.κ σ * (d.QQ v 1 0 * d.QQ u 0 1) * Pj d.κ ρ =
      (M.xEx P {j} τ v * M.xEx P {l} τ u) • (Pj d.κ σ * (d.SS j * star (d.SS l)) * Pj d.κ ρ) := by
  rw [normal_form_upper_right, normal_form_lower_left]
  simp only [add_mul, mul_add]
  have z1 : Pj d.κ σ * (d.L.GG * d.x v * d.L.l0 v * (d.L.GG * d.x u * d.L.m0 u)) * Pj d.κ ρ = 0 :=
    supp_kcomm hd (fun f => (kappa_commute_lower_diagonal hd f v).mul_right (kappa_commute_upper_diagonal hd f u)) ρ σ
      (mixed_not_off_j hd hl hj hjl hσ (by simp))
  have z2 : Pj d.κ σ * (d.L.GG * d.x v * d.L.l0 v * d.S12 u) * Pj d.κ ρ = 0 := by
    unfold Q.NFData.S12; rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun m _ => ?_
    exact supp_mul d.κ (supp_kcomm hd (kappa_commute_lower_diagonal hd · v)) (supp_kSSs hd m _) ρ σ
      (mixed_not_off_j hd hl hj hjl hσ (by simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, ee]; split_ifs <;> omega))
  have z3 : Pj d.κ σ * (d.weightedSumBis v * (d.L.GG * d.x u * d.L.m0 u)) * Pj d.κ ρ = 0 := by
    unfold Q.NFData.weightedSumBis; rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact supp_mul d.κ (supp_SSk hd i _) (supp_kcomm hd (kappa_commute_upper_diagonal hd · u)) ρ σ
      (mixed_not_off_l hd hl hj hjl hσ (by simp only [Pi.add_apply, Pi.zero_apply, ee]; split_ifs <;> omega))
  rw [z1, z2, z3, zero_add, zero_add, zero_add]
  unfold Q.NFData.S12 Q.NFData.weightedSumBis
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_eq_single l, Finset.sum_eq_single j]
  · rw [term_dn hd hτ]
  · intro i _ hij
    exact supp_mul d.κ (supp_SSk hd i _) (supp_kSSs hd l _) ρ σ
      (mixed_not_off_j hd hl hj hjl hσ (by simp [ee, Ne.symm hij, hjl]))
  · intro h'; exact absurd hj h'
  · intro m _ hml
    refine Finset.sum_eq_zero fun i _ => ?_
    exact supp_mul d.κ (supp_SSk hd i _) (supp_kSSs hd m _) ρ σ
      (mixed_not_off_l hd hl hj hjl hσ (by simp [ee, Ne.symm hml]; try (split_ifs <;> norm_num)))
  · intro h'; exact absurd hl h'

end Mixed

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

/- English proof (translation)
Rewrite using `[xEx_erase, Finset.mul_prod_erase _ (fun i => Y + (M.rho P π i : ℂ)) (Finset.mem_erase.2 ⟨hjl, hj⟩)]`.
-/
theorem xEx_split (l j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) (π : M.Ty P) (Y : ℂ) :
    M.xEx P {l} π Y = (Y + (M.rho P π j : ℂ)) * ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (Y + (M.rho P π i : ℂ)) := by
  rw [xEx_erase, Finset.mul_prod_erase _ (fun i => Y + (M.rho P π i : ℂ)) (Finset.mem_erase.2 ⟨hjl, hj⟩)]

/- English proof (translation)
Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_erase] at hi`. Rewrite using `[h i hi.2.2 hi.2.1 hi.1]`.
-/
theorem prod_shift {l j : ℕ} {τ π : M.Ty P} (h : ∀ i ∈ Icc 1 (P.k - 1), i ≠ l → i ≠ j → M.rho P π i = M.rho P τ i)
    (Y : ℂ) : ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (Y + (M.rho P π i : ℂ)) =
      ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (Y + (M.rho P τ i : ℂ)) := by
  refine Finset.prod_congr rfl fun i hi => ?_
  simp only [Finset.mem_erase] at hi
  rw [h i hi.2.2 hi.2.1 hi.1]

/- English proof (translation)
The claim follows from `Finset.erase_right_comm`.
-/
theorem erase_comm' (s : Finset ℕ) (a b : ℕ) : (s.erase a).erase b = (s.erase b).erase a := Finset.erase_right_comm

/- English proof (translation)
Introduce `u v`. Establish `hρi : ∀ i ∈ Icc 1 (P.k - 1), M.rho P ρ i = M.rho P τ i + if i = l then 1 else 0` using `fun i hi => rho_up hτ hi`. Establish `hσi : ∀ i ∈ Icc 1 (P.k - 1), M.rho P σ i = M.rho P τ i + if i = j then 1 else 0` using `fun i hi => rho_up hτσ hi`. Establish `sl : M.rho P σ l = M.rho P τ l` using `by rw [hσi l hl, if_neg (Ne.symm hjl), add_zero]`. Establish `sj : M.rho P σ j = M.rho P τ j + 1` using `by rw [hσi j hj, if_pos rfl]`.

Establish `rl : M.rho P ρ l = M.rho P τ l + 1` using `by rw [hρi l hl, if_pos rfl]`. Establish `A1` using `xEx_split l j hj hjl σ u`. Establish `A2` using `xEx_split l j hj hjl τ u`. Establish `A3` using `xEx_split j l hl (Ne.symm hjl) ρ v`. Establish `A4` using `xEx_split j l hl (Ne.symm hjl) τ v`.

Rewrite `A1` using `[prod_shift (τ := τ) (fun i hi h1 h2 => by rw [hσi i hi, if_neg h2, add_zero])]`. Rewrite `A3` using `[prod_shift (τ := τ) (fun i hi h1 h2 => by rw [hρi i hi, if_neg h2, add_zero])]`. Use `set Qu := ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (u + (M.rho P τ i : ℂ)) with hQu`. Use `set Qv := ∏ i ∈ ((Icc 1 (P.k - 1)).erase j).erase l, (v + (M.rho P τ i : ℂ)) with hQv`. Establish `hu : u = -(M.rho P τ l : ℂ)` using `by simp only [u, sl]`.

Establish `hv : v = -(M.rho P τ j : ℂ) - 1` using `by simp only [v, sj]; push_cast; ring`. Establish `ne1 : (M.rho P τ j : ℂ) - M.rho P τ l + 1 ≠ 0`. Use `rho_ne hP σ hj hl hjl` as an intermediate fact. Rewrite `this` using `[sj, sl]`. Introduce `h; apply this; exact_mod_cast (by push_cast; linear_combination h : ((M.rho P τ j + 1 : ℝ) : ℂ) = (M.rho P τ l : ℂ))`.

Establish `ne2 : (M.rho P τ l : ℂ) - M.rho P τ j ≠ 0`. Use `rho_ne hP τ hl hj (Ne.symm hjl)` as an intermediate fact. Introduce `h; apply this; exact_mod_cast (by linear_combination h : ((M.rho P τ l : ℝ) : ℂ) = (M.rho P τ j : ℂ))`. Establish `nQu : Qu ≠ 0`. Rewrite using `[hQu]`.

Use `Finset.prod_ne_zero_iff.2 fun i hi => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_erase] at hi`. Use `rho_ne hP τ hi.2.2 hl hi.2.1` as an intermediate fact. Rewrite using `[hu]; intro h; apply this; exact_mod_cast (by linear_combination h : ((M.rho P τ i : ℝ) : ℂ) = (M.rho P τ l : ℂ))`. Establish `nQv : Qv ≠ 0`.

Rewrite using `[hQv]`. Use `Finset.prod_ne_zero_iff.2 fun i hi => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_erase] at hi`. Use `rho_ne hP σ hi.2.2 hj hi.2.1` as an intermediate fact. Rewrite `this` using `[hσi i hi.2.2, if_neg hi.2.1, add_zero, sj]`.

Rewrite using `[hv]; intro h; apply this; exact_mod_cast (by push_cast; linear_combination h : ((M.rho P τ i : ℝ) : ℂ) = ((M.rho P τ j + 1 : ℝ) : ℂ))`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[A1, A2, A3, A4, sj, rl, hu, hv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[A1, A3, sj, rl, hu, hv]`. Use `push_cast`. Establish `e : (-(M.rho P τ l : ℂ) + ((M.rho P τ j : ℂ) + 1)) * Qu * ((-(M.rho P τ j : ℂ) - 1 + ((M.rho P τ l : ℂ) + 1)) * Qv) = ((M.rho P τ j : ℂ) - M.rho P τ l + 1) * ((M.rho P τ l : ℂ) - M.rho P τ j) * Qu * Qv` using `by ring`. Rewrite using `[e]`. Conclude with `mul_ne_zero (mul_ne_zero (mul_ne_zero ne1 ne2) nQu) nQv`.

Rewrite using `[hu, hv]`. Introduce `h`. Apply `ne1` to reduce the goal to its premises. Take the linear combination `h`.
-/
theorem mixed_scalar (hP : P.OK) {l j : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l)
    {τ ρ σ : M.Ty P} (hτ : M.Up P l τ ρ) (hτσ : M.Up P j τ σ) :
    let u : ℂ := -(M.rho P σ l : ℂ)
    let v : ℂ := -(M.rho P σ j : ℂ)
    M.xEx P {l} σ u * M.xEx P {j} ρ v = M.xEx P {j} τ v * M.xEx P {l} τ u ∧
      M.xEx P {l} σ u * M.xEx P {j} ρ v ≠ 0 ∧ u - v ≠ 0 := by
  intro u v
  have hρi : ∀ i ∈ Icc 1 (P.k - 1), M.rho P ρ i = M.rho P τ i + if i = l then 1 else 0 := fun i hi => rho_up hτ hi
  have hσi : ∀ i ∈ Icc 1 (P.k - 1), M.rho P σ i = M.rho P τ i + if i = j then 1 else 0 := fun i hi => rho_up hτσ hi
  have sl : M.rho P σ l = M.rho P τ l := by rw [hσi l hl, if_neg (Ne.symm hjl), add_zero]
  have sj : M.rho P σ j = M.rho P τ j + 1 := by rw [hσi j hj, if_pos rfl]
  have rl : M.rho P ρ l = M.rho P τ l + 1 := by rw [hρi l hl, if_pos rfl]
  have A1 := xEx_split l j hj hjl σ u
  have A2 := xEx_split l j hj hjl τ u
  have A3 := xEx_split j l hl (Ne.symm hjl) ρ v
  have A4 := xEx_split j l hl (Ne.symm hjl) τ v
  rw [prod_shift (τ := τ) (fun i hi h1 h2 => by rw [hσi i hi, if_neg h2, add_zero])] at A1
  rw [prod_shift (τ := τ) (fun i hi h1 h2 => by rw [hρi i hi, if_neg h2, add_zero])] at A3
  set Qu := ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (u + (M.rho P τ i : ℂ)) with hQu
  set Qv := ∏ i ∈ ((Icc 1 (P.k - 1)).erase j).erase l, (v + (M.rho P τ i : ℂ)) with hQv
  have hu : u = -(M.rho P τ l : ℂ) := by simp only [u, sl]
  have hv : v = -(M.rho P τ j : ℂ) - 1 := by simp only [v, sj]; push_cast; ring
  have ne1 : (M.rho P τ j : ℂ) - M.rho P τ l + 1 ≠ 0 := by
    have := rho_ne hP σ hj hl hjl; rw [sj, sl] at this
    intro h; apply this; exact_mod_cast (by push_cast; linear_combination h : ((M.rho P τ j + 1 : ℝ) : ℂ) = (M.rho P τ l : ℂ))
  have ne2 : (M.rho P τ l : ℂ) - M.rho P τ j ≠ 0 := by
    have := rho_ne hP τ hl hj (Ne.symm hjl)
    intro h; apply this; exact_mod_cast (by linear_combination h : ((M.rho P τ l : ℝ) : ℂ) = (M.rho P τ j : ℂ))
  have nQu : Qu ≠ 0 := by
    rw [hQu]; refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    simp only [Finset.mem_erase] at hi
    have := rho_ne hP τ hi.2.2 hl hi.2.1
    rw [hu]; intro h; apply this; exact_mod_cast (by linear_combination h : ((M.rho P τ i : ℝ) : ℂ) = (M.rho P τ l : ℂ))
  have nQv : Qv ≠ 0 := by
    rw [hQv]; refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    simp only [Finset.mem_erase] at hi
    have := rho_ne hP σ hi.2.2 hj hi.2.1
    rw [hσi i hi.2.2, if_neg hi.2.1, add_zero, sj] at this
    rw [hv]; intro h; apply this; exact_mod_cast (by push_cast; linear_combination h : ((M.rho P τ i : ℝ) : ℂ) = ((M.rho P τ j + 1 : ℝ) : ℂ))
  refine ⟨?_, ?_, ?_⟩
  · rw [A1, A2, A3, A4, sj, rl, hu, hv]; push_cast; ring
  · rw [A1, A3, sj, rl, hu, hv]; push_cast
    have e : (-(M.rho P τ l : ℂ) + ((M.rho P τ j : ℂ) + 1)) * Qu * ((-(M.rho P τ j : ℂ) - 1 + ((M.rho P τ l : ℂ) + 1)) * Qv)
      = ((M.rho P τ j : ℂ) - M.rho P τ l + 1) * ((M.rho P τ l : ℂ) - M.rho P τ j) * Qu * Qv := by ring
    rw [e]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero ne1 ne2) nQu) nQv
  · rw [hu, hv]; intro h; apply ne1; linear_combination h

variable {d : Q.NFData P A} (hd : Hyp d)
include hd

/- English proof (translation)
Use `ext_right hd fun ρ => ?_` and prove the remaining obligations. Establish `s1 : Supp d.κ (ee j + -ee l) (star (d.SS l) * d.SS j)` using `supp_mul d.κ (supp_SSs hd l) (supp_SS hd j)`. Establish `s2 : Supp d.κ (-ee l + ee j) (d.SS j * star (d.SS l))` using `supp_mul d.κ (supp_SS hd j) (supp_SSs hd l)`. Distinguish the cases in `hex : ∃ σ, Off (ee j + -ee l) ρ σ`. Take `⟨σ, hσ⟩` from `hex`.

Take `⟨τ, hτ⟩` from `box_down hσ hl (by simp [ee, Ne.symm hjl])`. Establish `hfun : ee l + (ee j + -ee l) = ee j`. Use function extensionality and compare the values at `m`. Simplify using `only [Pi.add_apply, Pi.neg_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hτσ : M.Up P j τ σ` using `up_of_off (off_congr (off_comp (off_of_up hτ) hσ) hfun)`. Rewrite using `[left_single hd s1 hσ, left_single hd s2 (off_congr hσ (add_comm _ _))]`. Take `⟨hαβ, hα, huv⟩` from `mixed_scalar hP hl hj hjl hτ hτσ`. Establish `e` using `congrArg (fun X => Pj d.κ σ * X * Pj d.κ ρ) (rtt_ent d hS (-(M.rho P σ l : ℂ)) (-(M.rho P σ j : ℂ)) 0 1 1 0)`. Establish `ea : ∀ (Y : ℂ) (X : A), Pj d.κ σ * (d.QQ Y 1 1 * X) * Pj d.κ ρ = Pj d.κ σ * d.QQ Y 1 1 * X * Pj d.κ ρ`.

Introduce `Y X`. Simplify using `only [mul_assoc]`. Rewrite `e` using `[mul_sub, sub_mul, ea, ea, normal_form_diagonal, normal_form_diagonal, Pj_GGx hd, Pj_GGx hd, xC_root σ hl, xC_root σ hj]`. Rewrite `e` using `[mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, blk_mixed1 hd hl hj hjl hσ, blk_mixed2 hd hl hj hjl hσ hτ, ← hαβ]`. Simplify using `only [zero_smul, zero_mul, sub_zero] at e`.

Rewrite `e` using `[← smul_sub, smul_smul, smul_eq_zero]`. Break down `e with h | h` into its components or cases. Conclude with `absurd h (mul_ne_zero huv hα)`. Conclude with `sub_eq_zero.1 h`. Simplify using `only [not_exists] at hex`.

Rewrite using `[left_none hd s1 hex, left_none hd s2 (fun σ h => hex σ (off_congr h (add_comm _ _)))]`.
-/
theorem ssMixed (hP : P.OK) (hS : Wd.IsStart d.QQ (M.qC P)) {l j : ℕ} (hl : l ∈ Icc 1 (P.k - 1))
    (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) : star (d.SS l) * d.SS j = d.SS j * star (d.SS l) := by
  refine ext_right hd fun ρ => ?_
  have s1 : Supp d.κ (ee j + -ee l) (star (d.SS l) * d.SS j) := supp_mul d.κ (supp_SSs hd l) (supp_SS hd j)
  have s2 : Supp d.κ (-ee l + ee j) (d.SS j * star (d.SS l)) := supp_mul d.κ (supp_SS hd j) (supp_SSs hd l)
  by_cases hex : ∃ σ, Off (ee j + -ee l) ρ σ
  · obtain ⟨σ, hσ⟩ := hex
    obtain ⟨τ, hτ⟩ := box_down hσ hl (by simp [ee, Ne.symm hjl])
    have hfun : ee l + (ee j + -ee l) = ee j := by
      funext m; simp only [Pi.add_apply, Pi.neg_apply]; ring
    have hτσ : M.Up P j τ σ := up_of_off (off_congr (off_comp (off_of_up hτ) hσ) hfun)
    rw [left_single hd s1 hσ, left_single hd s2 (off_congr hσ (add_comm _ _))]
    obtain ⟨hαβ, hα, huv⟩ := mixed_scalar hP hl hj hjl hτ hτσ
    have e := congrArg (fun X => Pj d.κ σ * X * Pj d.κ ρ) (rtt_ent d hS (-(M.rho P σ l : ℂ)) (-(M.rho P σ j : ℂ)) 0 1 1 0)
    have ea : ∀ (Y : ℂ) (X : A), Pj d.κ σ * (d.QQ Y 1 1 * X) * Pj d.κ ρ = Pj d.κ σ * d.QQ Y 1 1 * X * Pj d.κ ρ := by
      intro Y X; simp only [mul_assoc]
    rw [mul_sub, sub_mul, ea, ea, normal_form_diagonal, normal_form_diagonal, Pj_GGx hd, Pj_GGx hd, xC_root σ hl, xC_root σ hj] at e
    rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, blk_mixed1 hd hl hj hjl hσ, blk_mixed2 hd hl hj hjl hσ hτ,
      ← hαβ] at e
    simp only [zero_smul, zero_mul, sub_zero] at e
    rw [← smul_sub, smul_smul, smul_eq_zero] at e
    rcases e with h | h
    · exact absurd h (mul_ne_zero huv hα)
    · exact sub_eq_zero.1 h
  · simp only [not_exists] at hex
    rw [left_none hd s1 hex, left_none hd s2 (fun σ h => hex σ (off_congr h (add_comm _ _)))]

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

/- English proof (translation)
Establish `hli : ∀ i ∈ Icc 1 (P.k - 1), M.rho P τl i = M.rho P ρ i + if i = l then 1 else 0` using `fun i hi => rho_up hτl hi`. Establish `hji : ∀ i ∈ Icc 1 (P.k - 1), M.rho P τj i = M.rho P ρ i + if i = j then 1 else 0` using `fun i hi => rho_up hτj hi`. Use `set B1 := ∏ i ∈ ((Icc 1 (P.k - 1)).erase j).erase l, (-(M.rho P ρ j : ℂ) + (M.rho P ρ i : ℂ)) with hB1`. Use `set B2 := ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (-(M.rho P ρ l : ℂ) + (M.rho P ρ i : ℂ)) with hB2`. Establish `eC` using `xEx_split l j hj hjl ρ (-(M.rho P ρ l : ℂ))`.

Establish `eA` using `xEx_split j l hl (Ne.symm hjl) ρ (-(M.rho P ρ j : ℂ))`. Establish `e1` using `xEx_split j l hl (Ne.symm hjl) τl (-(M.rho P ρ j : ℂ))`. Establish `e2` using `xEx_split l j hj hjl τj (-(M.rho P ρ l : ℂ))`. Rewrite `e1` using `[prod_shift (τ := ρ) (fun i hi h1 h2 => by rw [hli i hi, if_neg h2, add_zero])]`. Rewrite `e2` using `[prod_shift (τ := ρ) (fun i hi h1 h2 => by rw [hji i hi, if_neg h2, add_zero])]`.

Rewrite `eA`, `e1` using `[← hB1]`. Rewrite `eC`, `e2` using `[← hB2]`. Rewrite `e1` using `[hli l hl, if_pos rfl]`. Rewrite `e2` using `[hji j hj, if_pos rfl]`. Establish `nB1 : B1 ≠ 0`.

Rewrite using `[hB1]`. Use `Finset.prod_ne_zero_iff.2 fun i hi => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_erase] at hi`. Use `rho_ne hP ρ hi.2.2 hj hi.2.1` as an intermediate fact. Introduce `h; apply this; exact_mod_cast (by linear_combination h : ((M.rho P ρ i : ℝ) : ℂ) = (M.rho P ρ j : ℂ))`.

Establish `nB2 : B2 ≠ 0`. Rewrite using `[hB2]`. Use `Finset.prod_ne_zero_iff.2 fun i hi => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_erase] at hi`. Use `rho_ne hP ρ hi.2.2 hl hi.2.1` as an intermediate fact.

Introduce `h; apply this; exact_mod_cast (by linear_combination h : ((M.rho P ρ i : ℝ) : ℂ) = (M.rho P ρ l : ℂ))`. Establish `nd : ((M.rho P ρ j : ℂ) - M.rho P ρ l) ≠ 0`. Use `rho_ne hP ρ hj hl hjl` as an intermediate fact. Introduce `h; apply this; exact_mod_cast (by linear_combination h : ((M.rho P ρ j : ℝ) : ℂ) = (M.rho P ρ l : ℂ))`. Use `⟨((M.rho P ρ j : ℂ) - M.rho P ρ l) * B1 * B2, mul_ne_zero (mul_ne_zero nd nB1) nB2, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[xEx_split l j hj hjl ρ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[xEx_split j l hl (Ne.symm hjl) ρ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eC, e1]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eA, e2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem comm_scalar (hP : P.OK) {l j : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l)
    {ρ τl τj : M.Ty P} (hτl : M.Up P l ρ τl) (hτj : M.Up P j ρ τj) :
    ∃ c : ℂ, c ≠ 0 ∧
      M.xEx P {l} ρ (-(M.rho P ρ j : ℂ)) * M.xEx P {j} τl (-(M.rho P ρ l : ℂ)) = 0 ∧
      M.xEx P {j} ρ (-(M.rho P ρ l : ℂ)) * M.xEx P {l} τj (-(M.rho P ρ j : ℂ)) = 0 ∧
      M.xEx P {l} ρ (-(M.rho P ρ l : ℂ)) * M.xEx P {j} τl (-(M.rho P ρ j : ℂ)) =
        c * -((M.rho P ρ j - M.rho P ρ l - 1 : ℝ) : ℂ) ∧
      M.xEx P {j} ρ (-(M.rho P ρ j : ℂ)) * M.xEx P {l} τj (-(M.rho P ρ l : ℂ)) =
        c * -((M.rho P ρ j - M.rho P ρ l + 1 : ℝ) : ℂ) := by
  have hli : ∀ i ∈ Icc 1 (P.k - 1), M.rho P τl i = M.rho P ρ i + if i = l then 1 else 0 := fun i hi => rho_up hτl hi
  have hji : ∀ i ∈ Icc 1 (P.k - 1), M.rho P τj i = M.rho P ρ i + if i = j then 1 else 0 := fun i hi => rho_up hτj hi
  set B1 := ∏ i ∈ ((Icc 1 (P.k - 1)).erase j).erase l, (-(M.rho P ρ j : ℂ) + (M.rho P ρ i : ℂ)) with hB1
  set B2 := ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (-(M.rho P ρ l : ℂ) + (M.rho P ρ i : ℂ)) with hB2
  have eC := xEx_split l j hj hjl ρ (-(M.rho P ρ l : ℂ))
  have eA := xEx_split j l hl (Ne.symm hjl) ρ (-(M.rho P ρ j : ℂ))
  have e1 := xEx_split j l hl (Ne.symm hjl) τl (-(M.rho P ρ j : ℂ))
  have e2 := xEx_split l j hj hjl τj (-(M.rho P ρ l : ℂ))
  rw [prod_shift (τ := ρ) (fun i hi h1 h2 => by rw [hli i hi, if_neg h2, add_zero])] at e1
  rw [prod_shift (τ := ρ) (fun i hi h1 h2 => by rw [hji i hi, if_neg h2, add_zero])] at e2
  rw [← hB1] at eA e1; rw [← hB2] at eC e2
  rw [hli l hl, if_pos rfl] at e1; rw [hji j hj, if_pos rfl] at e2
  have nB1 : B1 ≠ 0 := by
    rw [hB1]; refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    simp only [Finset.mem_erase] at hi
    have := rho_ne hP ρ hi.2.2 hj hi.2.1
    intro h; apply this; exact_mod_cast (by linear_combination h : ((M.rho P ρ i : ℝ) : ℂ) = (M.rho P ρ j : ℂ))
  have nB2 : B2 ≠ 0 := by
    rw [hB2]; refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    simp only [Finset.mem_erase] at hi
    have := rho_ne hP ρ hi.2.2 hl hi.2.1
    intro h; apply this; exact_mod_cast (by linear_combination h : ((M.rho P ρ i : ℝ) : ℂ) = (M.rho P ρ l : ℂ))
  have nd : ((M.rho P ρ j : ℂ) - M.rho P ρ l) ≠ 0 := by
    have := rho_ne hP ρ hj hl hjl
    intro h; apply this; exact_mod_cast (by linear_combination h : ((M.rho P ρ j : ℝ) : ℂ) = (M.rho P ρ l : ℂ))
  refine ⟨((M.rho P ρ j : ℂ) - M.rho P ρ l) * B1 * B2, mul_ne_zero (mul_ne_zero nd nB1) nB2, ?_, ?_, ?_, ?_⟩
  · rw [xEx_split l j hj hjl ρ]; ring
  · rw [xEx_split j l hl (Ne.symm hjl) ρ]; ring
  · rw [eC, e1]; push_cast; ring
  · rw [eA, e2]; push_cast; ring

/- English proof (translation)
Rewrite using `[← Finset.add_sum_erase s _ hl, ← Finset.add_sum_erase (s.erase l) _ (Finset.mem_erase.2 ⟨hjl, hj⟩)]`. Rewrite using `[Finset.sum_eq_single_of_mem j hj (fun i hi hij => h0 l hl i hi (by tauto)), Finset.sum_eq_single_of_mem l hl (fun i hi hil => h0 j hj i hi (by tauto))]`. Rewrite using `[Finset.sum_eq_zero (fun m hm => Finset.sum_eq_zero fun i hi => h0 m (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm)) i hi (by`. Simplify using `only [Finset.mem_erase] at hm`. Use the proof step `tauto))]`.

Rewrite using `[add_zero]`.
-/
theorem sum2 {X : Type*} [AddCommMonoid X] (s : Finset ℕ) (F : ℕ → ℕ → X) {j l : ℕ} (hj : j ∈ s) (hl : l ∈ s)
    (hjl : j ≠ l) (h0 : ∀ m ∈ s, ∀ i ∈ s, ¬ ((i = j ∧ m = l) ∨ (i = l ∧ m = j)) → F i m = 0) :
    ∑ m ∈ s, ∑ i ∈ s, F i m = F j l + F l j := by
  rw [← Finset.add_sum_erase s _ hl, ← Finset.add_sum_erase (s.erase l) _ (Finset.mem_erase.2 ⟨hjl, hj⟩)]
  rw [Finset.sum_eq_single_of_mem j hj (fun i hi hij => h0 l hl i hi (by tauto)),
    Finset.sum_eq_single_of_mem l hl (fun i hi hil => h0 j hj i hi (by tauto))]
  rw [Finset.sum_eq_zero (fun m hm => Finset.sum_eq_zero fun i hi => h0 m (Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase hm)) i hi (by
      simp only [Finset.mem_erase] at hm; tauto))]
  rw [add_zero]

variable {d : Q.NFData P A} (hd : Hyp d)
include hd

/- English proof (translation)
Establish `hs : d.SS m * Pj d.κ ρ = Pj d.κ τ * d.SS m * Pj d.κ ρ` using `left_single hd (supp_SS hd m) (off_of_up hτ)`. Rewrite using `[show Pj d.κ σ * (d.SS i * d.κ g * (d.SS m * d.κ h)) * Pj d.κ ρ = Pj d.κ σ * d.SS i * (d.κ g * (d.SS m * (d.κ h * Pj d.κ ρ))) by simp only [mul_assoc], kap_Pj, mul_smul_comm, mul_smul_comm, mul_smul_comm, hs, show d.κ g * (Pj d.κ τ * d.SS m * Pj d.κ ρ) = d.κ g * Pj d.κ τ * d.SS m …`. Simplify using `only [mul_assoc], kap_Pj, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, ← hs]`. Simplify using `only [mul_assoc]`.
-/
theorem term_upup {i m : ℕ} {ρ τ : M.Ty P} (hτ : M.Up P m ρ τ) (σ : M.Ty P) (g h : M.Ty P → ℂ) :
    Pj d.κ σ * (d.SS i * d.κ g * (d.SS m * d.κ h)) * Pj d.κ ρ =
      (h ρ * g τ) • (Pj d.κ σ * (d.SS i * d.SS m) * Pj d.κ ρ) := by
  have hs : d.SS m * Pj d.κ ρ = Pj d.κ τ * d.SS m * Pj d.κ ρ := left_single hd (supp_SS hd m) (off_of_up hτ)
  rw [show Pj d.κ σ * (d.SS i * d.κ g * (d.SS m * d.κ h)) * Pj d.κ ρ =
      Pj d.κ σ * d.SS i * (d.κ g * (d.SS m * (d.κ h * Pj d.κ ρ))) by simp only [mul_assoc], kap_Pj, mul_smul_comm,
    mul_smul_comm, mul_smul_comm, hs, show d.κ g * (Pj d.κ τ * d.SS m * Pj d.κ ρ) = d.κ g * Pj d.κ τ * d.SS m * Pj d.κ ρ by
      simp only [mul_assoc], kap_Pj, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, ← hs]
  simp only [mul_assoc]

section Comm

variable {l j : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l)
  {ρ ρ'' : M.Ty P} (hσ : Off (ee l + ee j) ρ ρ'')
include hl hj hjl hσ

/- English proof (translation)
Break down `h with h | h` into its components or cases. Use `off_contra hσ hl ?_; rw [show (ee l + ee j) l = 1 by simp [ee, Ne.symm hjl]]; exact h` and prove the remaining obligations. Use `off_contra hσ hj ?_; rw [show (ee l + ee j) j = 1 by simp [ee, hjl]]; exact h` and prove the remaining obligations.
-/
theorem comm_not_off {δ : ℕ → ℤ} (h : δ l ≠ 1 ∨ δ j ≠ 1) : ¬ Off δ ρ ρ'' := by
  rcases h with h | h
  · refine off_contra hσ hl ?_; rw [show (ee l + ee j) l = 1 by simp [ee, Ne.symm hjl]]; exact h
  · refine off_contra hσ hj ?_; rw [show (ee l + ee j) j = 1 by simp [ee, hjl]]; exact h

/- English proof (translation)
Rewrite using `[normal_form_lower_left, normal_form_lower_left]`. Simplify using `only [add_mul, mul_add]`. Establish `z1 : Pj d.κ ρ'' * (d.L.GG * d.x u * d.L.l0 u * (d.L.GG * d.x v * d.L.l0 v)) * Pj d.κ ρ = 0` using `supp_kcomm hd (fun f => (kappa_commute_lower_diagonal hd f u).mul_right (kappa_commute_lower_diagonal hd f v)) ρ ρ'' (comm_not_off hd hl hj hjl hσ (Or.inl (by simp)))`. Establish `z2 : Pj d.κ ρ'' * (d.L.GG * d.x u * d.L.l0 u * d.weightedSumBis v) * Pj d.κ ρ = 0`. Unfold `Q.NFData.weightedSumBis`.

Rewrite using `[Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `supp_mul d.κ (supp_kcomm hd (kappa_commute_lower_diagonal hd · u)) (supp_SSk hd i _) ρ ρ'' (comm_not_off hd hl hj hjl hσ ?_)` and prove the remaining obligations. Distinguish the cases in `hi : i = l`. Substitute `hi` using the available equality.

Use `right`. Simplify using `[ee, hjl]`. Use `left`. Simplify using `[ee, Ne.symm hi]`. Establish `z3 : Pj d.κ ρ'' * (d.weightedSumBis u * (d.L.GG * d.x v * d.L.l0 v)) * Pj d.κ ρ = 0`.

Unfold `Q.NFData.weightedSumBis`. Rewrite using `[Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `supp_mul d.κ (supp_SSk hd i _) (supp_kcomm hd (kappa_commute_lower_diagonal hd · v)) ρ ρ'' (comm_not_off hd hl hj hjl hσ ?_)` and prove the remaining obligations. Distinguish the cases in `hi : i = l`.

Substitute `hi` using the available equality. Use `right`. Simplify using `[ee, hjl]`. Use `left`. Simplify using `[ee, Ne.symm hi]`.

Rewrite using `[z1, z2, z3, zero_add, zero_add, zero_add]`. Unfold `Q.NFData.weightedSumBis`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Establish `zz : ∀ m ∈ Icc 1 (P.k - 1), ∀ i ∈ Icc 1 (P.k - 1), ¬ ((i = j ∧ m = l) ∨ (i = l ∧ m = j)) → Pj d.κ ρ'' * (d.SS i * d.κ (fun ρ => M.xEx P {i} ρ u) * (d.SS m * d.κ (fun ρ => M.xEx P {m} ρ v))) * Pj d.κ ρ = 0`. Introduce `m _ i _ hn`.

Use `supp_mul d.κ (supp_SSk hd i _) (supp_SSk hd m _) ρ ρ'' (comm_not_off hd hl hj hjl hσ ?_)` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Pi.zero_apply, ee]`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Take `⟨h1, h2⟩` from `hc`.

Apply the tactic sequence `apply hn; split_ifs at h1 h2 <;> simp_all <;> omega`. Rewrite using `[sum2 _ _ hj hl hjl zz, term_upup hd hτl, term_upup hd hτj]`.
-/
theorem blk_comm {τl τj : M.Ty P} (hτl : M.Up P l ρ τl) (hτj : M.Up P j ρ τj) (u v : ℂ) :
    Pj d.κ ρ'' * (d.QQ u 1 0 * d.QQ v 1 0) * Pj d.κ ρ =
      (M.xEx P {l} ρ v * M.xEx P {j} τl u) • (Pj d.κ ρ'' * (d.SS j * d.SS l) * Pj d.κ ρ) +
      (M.xEx P {j} ρ v * M.xEx P {l} τj u) • (Pj d.κ ρ'' * (d.SS l * d.SS j) * Pj d.κ ρ) := by
  rw [normal_form_lower_left, normal_form_lower_left]
  simp only [add_mul, mul_add]
  have z1 : Pj d.κ ρ'' * (d.L.GG * d.x u * d.L.l0 u * (d.L.GG * d.x v * d.L.l0 v)) * Pj d.κ ρ = 0 :=
    supp_kcomm hd (fun f => (kappa_commute_lower_diagonal hd f u).mul_right (kappa_commute_lower_diagonal hd f v)) ρ ρ''
      (comm_not_off hd hl hj hjl hσ (Or.inl (by simp)))
  have z2 : Pj d.κ ρ'' * (d.L.GG * d.x u * d.L.l0 u * d.weightedSumBis v) * Pj d.κ ρ = 0 := by
    unfold Q.NFData.weightedSumBis; rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine supp_mul d.κ (supp_kcomm hd (kappa_commute_lower_diagonal hd · u)) (supp_SSk hd i _) ρ ρ'' (comm_not_off hd hl hj hjl hσ ?_)
    by_cases hi : i = l
    · subst hi; right; simp [ee, hjl]
    · left; simp [ee, Ne.symm hi]
  have z3 : Pj d.κ ρ'' * (d.weightedSumBis u * (d.L.GG * d.x v * d.L.l0 v)) * Pj d.κ ρ = 0 := by
    unfold Q.NFData.weightedSumBis; rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine supp_mul d.κ (supp_SSk hd i _) (supp_kcomm hd (kappa_commute_lower_diagonal hd · v)) ρ ρ'' (comm_not_off hd hl hj hjl hσ ?_)
    by_cases hi : i = l
    · subst hi; right; simp [ee, hjl]
    · left; simp [ee, Ne.symm hi]
  rw [z1, z2, z3, zero_add, zero_add, zero_add]
  unfold Q.NFData.weightedSumBis
  simp only [Finset.mul_sum, Finset.sum_mul]
  have zz : ∀ m ∈ Icc 1 (P.k - 1), ∀ i ∈ Icc 1 (P.k - 1), ¬ ((i = j ∧ m = l) ∨ (i = l ∧ m = j)) →
      Pj d.κ ρ'' * (d.SS i * d.κ (fun ρ => M.xEx P {i} ρ u) * (d.SS m * d.κ (fun ρ => M.xEx P {m} ρ v))) *
        Pj d.κ ρ = 0 := by
    intro m _ i _ hn
    refine supp_mul d.κ (supp_SSk hd i _) (supp_SSk hd m _) ρ ρ'' (comm_not_off hd hl hj hjl hσ ?_)
    simp only [Pi.add_apply, Pi.zero_apply, ee]
    by_contra hc; push Not at hc; obtain ⟨h1, h2⟩ := hc
    apply hn; split_ifs at h1 h2 <;> simp_all <;> omega
  rw [sum2 _ _ hj hl hjl zz, term_upup hd hτl, term_upup hd hτj]

end Comm

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {d : Q.NFData P A} (hd : Hyp d)
include hd

/- English proof (translation)
Distinguish the cases in `h : u - v = 1`. Conclude with `Or.inr h`. Use `left`. Establish `e` using `rtt_ent d hS u v 1 0 1 0`. Establish `e2 : (u - v - 1) • (d.QQ u 1 0 * d.QQ v 1 0 - d.QQ v 1 0 * d.QQ u 1 0) = 0`.

Rewrite using `[sub_smul, e, one_smul, sub_self]`. Establish `e3 : d.QQ u 1 0 * d.QQ v 1 0 - d.QQ v 1 0 * d.QQ u 1 0 = 0`. Break down `smul_eq_zero.1 e2 with h' | h'` into its components or cases. Conclude with `absurd (by linear_combination h') h`. Conclude with `h'`.

Rewrite using `[e3, mul_zero, zero_mul]`.
-/
theorem comm_zero (hS : Wd.IsStart d.QQ (M.qC P)) (σ ρ : M.Ty P) (u v : ℂ) :
    Pj d.κ σ * (d.QQ u 1 0 * d.QQ v 1 0 - d.QQ v 1 0 * d.QQ u 1 0) * Pj d.κ ρ = 0 ∨ u - v = 1 := by
  by_cases h : u - v = 1
  · exact Or.inr h
  · left
    have e := rtt_ent d hS u v 1 0 1 0
    have e2 : (u - v - 1) • (d.QQ u 1 0 * d.QQ v 1 0 - d.QQ v 1 0 * d.QQ u 1 0) = 0 := by
      rw [sub_smul, e, one_smul, sub_self]
    have e3 : d.QQ u 1 0 * d.QQ v 1 0 - d.QQ v 1 0 * d.QQ u 1 0 = 0 := by
      rcases smul_eq_zero.1 e2 with h' | h'
      · exact absurd (by linear_combination h') h
      · exact h'
    rw [e3, mul_zero, zero_mul]

/- English proof (translation)
Use `ext_right hd fun ρ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, kap_Pj, mul_smul_comm, mul_assoc (d.SS l * d.SS j), kap_Pj, mul_smul_comm]`. Establish `s1 : Supp d.κ (ee l + ee j) (d.SS j * d.SS l)` using `supp_mul d.κ (supp_SS hd j) (supp_SS hd l)`. Establish `s2 : Supp d.κ (ee j + ee l) (d.SS l * d.SS j)` using `supp_mul d.κ (supp_SS hd l) (supp_SS hd j)`. Distinguish the cases in `hex : ∃ σ, Off (ee l + ee j) ρ σ`.

Take `⟨σ, hσ⟩` from `hex`. Take `⟨τl, hτl⟩` from `box_up hσ hl (by simp [ee, Ne.symm hjl])`. Take `⟨τj, hτj⟩` from `box_up hσ hj (by simp [ee, hjl])`. Rewrite using `[left_single hd s1 hσ, left_single hd s2 (off_congr hσ (add_comm _ _))]`. Take `⟨c, hc, h1, h2, h3, h4⟩` from `comm_scalar hP hl hj hjl hτl hτj`.

Use `set u : ℂ := -(M.rho P ρ l : ℂ)`. Use `set v : ℂ := -(M.rho P ρ j : ℂ)`. Establish `hC : Pj d.κ σ * (d.QQ u 1 0 * d.QQ v 1 0 - d.QQ v 1 0 * d.QQ u 1 0) * Pj d.κ ρ = 0`. Break down `comm_zero hd hS σ ρ u v with h | h` into its components or cases. Conclude with `h`.

Break down `comm_zero hd hS σ ρ v u with h' | h'` into its components or cases. Rewrite using `[← neg_sub, mul_neg, neg_mul, h', neg_zero]`. Use the proof step `exfalso; have : (2 : ℂ) = 0 := by linear_combination -(h + h')`. Evaluate the numerical expressions using `at this`. Rewrite `hC` using `[mul_sub, sub_mul, blk_comm hd hl hj hjl hσ hτl hτj, blk_comm hd hl hj hjl hσ hτl hτj, h1, h2, h3, h4]`.

Establish `hC' : c • (((M.rho P ρ j - M.rho P ρ l - 1 : ℝ) : ℂ) • (Pj d.κ σ * (d.SS j * d.SS l) * Pj d.κ ρ) - ((M.rho P ρ j - M.rho P ρ l + 1 : ℝ) : ℂ) • (Pj d.κ σ * (d.SS l * d.SS j) * Pj d.κ ρ)) = 0`. Rewrite using `[← hC]`. Simplify using `only [zero_smul, zero_add, add_zero, smul_sub, smul_smul, mul_neg, neg_smul]`. Normalize the expressions using the abelian group laws. Break down `smul_eq_zero.1 hC' with h | h` into its components or cases.

Conclude with `absurd h hc`. Conclude with `sub_eq_zero.1 h`. Simplify using `only [not_exists] at hex`. Rewrite using `[left_none hd s1 hex, left_none hd s2 (fun σ h => hex σ (off_congr h (add_comm _ _)))]`. Simplify using the standard rewrite rules.
-/
theorem ssComm (hP : P.OK) (hS : Wd.IsStart d.QQ (M.qC P)) {l j : ℕ} (hl : l ∈ Icc 1 (P.k - 1))
    (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    d.SS j * d.SS l * (d.κ fun ρ => ((M.rho P ρ j - M.rho P ρ l - 1 : ℝ) : ℂ)) =
      d.SS l * d.SS j * d.κ fun ρ => ((M.rho P ρ j - M.rho P ρ l + 1 : ℝ) : ℂ) := by
  refine ext_right hd fun ρ => ?_
  rw [mul_assoc, kap_Pj, mul_smul_comm, mul_assoc (d.SS l * d.SS j), kap_Pj, mul_smul_comm]
  have s1 : Supp d.κ (ee l + ee j) (d.SS j * d.SS l) := supp_mul d.κ (supp_SS hd j) (supp_SS hd l)
  have s2 : Supp d.κ (ee j + ee l) (d.SS l * d.SS j) := supp_mul d.κ (supp_SS hd l) (supp_SS hd j)
  by_cases hex : ∃ σ, Off (ee l + ee j) ρ σ
  · obtain ⟨σ, hσ⟩ := hex
    obtain ⟨τl, hτl⟩ := box_up hσ hl (by simp [ee, Ne.symm hjl])
    obtain ⟨τj, hτj⟩ := box_up hσ hj (by simp [ee, hjl])
    rw [left_single hd s1 hσ, left_single hd s2 (off_congr hσ (add_comm _ _))]
    obtain ⟨c, hc, h1, h2, h3, h4⟩ := comm_scalar hP hl hj hjl hτl hτj
    set u : ℂ := -(M.rho P ρ l : ℂ)
    set v : ℂ := -(M.rho P ρ j : ℂ)
    have hC : Pj d.κ σ * (d.QQ u 1 0 * d.QQ v 1 0 - d.QQ v 1 0 * d.QQ u 1 0) * Pj d.κ ρ = 0 := by
      rcases comm_zero hd hS σ ρ u v with h | h
      · exact h
      · rcases comm_zero hd hS σ ρ v u with h' | h'
        · rw [← neg_sub, mul_neg, neg_mul, h', neg_zero]
        · exfalso; have : (2 : ℂ) = 0 := by linear_combination -(h + h')
          norm_num at this
    rw [mul_sub, sub_mul, blk_comm hd hl hj hjl hσ hτl hτj, blk_comm hd hl hj hjl hσ hτl hτj, h1, h2, h3, h4] at hC
    have hC' : c • (((M.rho P ρ j - M.rho P ρ l - 1 : ℝ) : ℂ) • (Pj d.κ σ * (d.SS j * d.SS l) * Pj d.κ ρ) -
        ((M.rho P ρ j - M.rho P ρ l + 1 : ℝ) : ℂ) • (Pj d.κ σ * (d.SS l * d.SS j) * Pj d.κ ρ)) = 0 := by
      rw [← hC]; simp only [zero_smul, zero_add, add_zero, smul_sub, smul_smul, mul_neg, neg_smul]; abel
    rcases smul_eq_zero.1 hC' with h | h
    · exact absurd h hc
    · exact sub_eq_zero.1 h
  · simp only [not_exists] at hex
    rw [left_none hd s1 hex, left_none hd s2 (fun σ h => hex σ (off_congr h (add_comm _ _)))]; simp

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

section Op

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : R.LevelData A r)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem zeta_mem_functions : L.ζ ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪
    {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi} := by simp
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem fnmem_zb : L.ζb ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪
    {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi} := by simp
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem fnmem_G : L.GG ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪
    {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi} := by simp
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem fnmem_Gi : L.GGi ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪
    {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi} := by simp

/- English proof (translation)
The claim follows from `L.fns_comm _ (zeta_mem_functions L) _ (fnmem_G L)`.
-/
theorem zG : L.ζ * L.GG = L.GG * L.ζ := L.fns_comm _ (zeta_mem_functions L) _ (fnmem_G L)
/- English proof (translation)
The claim follows from `L.fns_comm _ (fnmem_zb L) _ (fnmem_G L)`.
-/
theorem zbG : L.ζb * L.GG = L.GG * L.ζb := L.fns_comm _ (fnmem_zb L) _ (fnmem_G L)
/- English proof (translation)
The claim follows from `L.fns_comm _ (zeta_mem_functions L) _ (fnmem_Gi L)`.
-/
theorem zGi : L.ζ * L.GGi = L.GGi * L.ζ := L.fns_comm _ (zeta_mem_functions L) _ (fnmem_Gi L)
/- English proof (translation)
The claim follows from `L.fns_comm _ (fnmem_zb L) _ (fnmem_Gi L)`.
-/
theorem zbGi : L.ζb * L.GGi = L.GGi * L.ζb := L.fns_comm _ (fnmem_zb L) _ (fnmem_Gi L)
/- English proof (translation)
The claim follows from `L.fns_comm _ (fnmem_zb L) _ (zeta_mem_functions L)`.
-/
theorem zzb : L.ζb * L.ζ = L.ζ * L.ζb := L.fns_comm _ (fnmem_zb L) _ (zeta_mem_functions L)

/- English proof (translation)
Rewrite using `[L.nabs_GG]`. Normalize the expressions using the abelian group laws.
-/
theorem Gs : L.GG * L.nabs = L.nabs * L.GG + L.ζ := by rw [L.nabs_GG]; abel
/- English proof (translation)
Rewrite using `[L.nab_GG]`. Normalize the expressions using the abelian group laws.
-/
theorem Gn : L.GG * L.nab = L.nab * L.GG - L.ζb := by rw [L.nab_GG]; abel

/- English proof (translation)
Rewrite using `[← mul_assoc, ← zbG, mul_assoc, L.GG_GGi, mul_one]`.
-/
theorem M3 : L.GG * (L.ζb * L.GGi) = L.ζb := by rw [← mul_assoc, ← zbG, mul_assoc, L.GG_GGi, mul_one]
/- English proof (translation)
Rewrite using `[← mul_assoc, ← zG, mul_assoc, L.GG_GGi, mul_one]`.
-/
theorem M6 : L.GG * (L.ζ * L.GGi) = L.ζ := by rw [← mul_assoc, ← zG, mul_assoc, L.GG_GGi, mul_one]
/- English proof (translation)
Rewrite using `[← mul_assoc, L.GGi_GG, one_mul]`.
-/
theorem GiG (X : A) : L.GGi * (L.GG * X) = X := by rw [← mul_assoc, L.GGi_GG, one_mul]
/- English proof (translation)
Rewrite using `[← mul_assoc, L.GG_GGi, one_mul]`.
-/
theorem GGi' (X : A) : L.GG * (L.GGi * X) = X := by rw [← mul_assoc, L.GG_GGi, one_mul]

/- English proof (translation)
Rewrite using `[← mul_assoc L.nabs, L.nabs_GG, sub_mul, mul_sub, mul_assoc]`.
-/
theorem M1 : L.GG * (L.nabs * (L.GG * L.nab)) = L.GG * (L.GG * (L.nabs * L.nab)) - L.GG * (L.ζ * L.nab) := by
  rw [← mul_assoc L.nabs, L.nabs_GG, sub_mul, mul_sub, mul_assoc]
/- English proof (translation)
Rewrite using `[← mul_assoc L.nab, L.nab_GG, add_mul, mul_add, mul_assoc]`.
-/
theorem M2 : L.GG * (L.nab * (L.GG * L.nabs)) = L.GG * (L.GG * (L.nab * L.nabs)) + L.GG * (L.ζb * L.nabs) := by
  rw [← mul_assoc L.nab, L.nab_GG, add_mul, mul_add, mul_assoc]
/- English proof (translation)
Rewrite using `[M3]`.
-/
theorem M3' : L.GG * (L.nabs * (L.GG * (L.ζb * L.GGi))) = L.GG * (L.nabs * L.ζb) := by rw [M3]
/- English proof (translation)
Rewrite using `[GiG]`.
-/
theorem M4 : L.GG * (L.ζ * (L.GGi * (L.GG * L.nab))) = L.GG * (L.ζ * L.nab) := by rw [GiG]
/- English proof (translation)
Rewrite using `[GiG, ← mul_assoc, ← zG, mul_assoc, M3]`.
-/
theorem M5 : L.GG * (L.ζ * (L.GGi * (L.GG * (L.ζb * L.GGi)))) = L.ζ * L.ζb := by
  rw [GiG, ← mul_assoc, ← zG, mul_assoc, M3]
/- English proof (translation)
Rewrite using `[M6]`.
-/
theorem M6' : L.GG * (L.nab * (L.GG * (L.ζ * L.GGi))) = L.GG * (L.nab * L.ζ) := by rw [M6]
/- English proof (translation)
Rewrite using `[GiG]`.
-/
theorem M7 : L.GG * (L.ζb * (L.GGi * (L.GG * L.nabs))) = L.GG * (L.ζb * L.nabs) := by rw [GiG]
/- English proof (translation)
Rewrite using `[GiG, ← mul_assoc, ← zbG, mul_assoc, M6, zzb]`.
-/
theorem M8 : L.GG * (L.ζb * (L.GGi * (L.GG * (L.ζ * L.GGi)))) = L.ζ * L.ζb := by
  rw [GiG, ← mul_assoc, ← zbG, mul_assoc, M6, zzb]
/- English proof (translation)
Rewrite using `[← mul_assoc L.GG L.nabs, Gs, add_mul, mul_add, mul_assoc, M3, ← mul_assoc L.GG L.ζ, ← zG, mul_assoc, M3]`.
-/
theorem M9 : L.GG * (L.GG * (L.nabs * (L.ζb * L.GGi))) = L.GG * (L.nabs * L.ζb) + L.ζ * L.ζb := by
  rw [← mul_assoc L.GG L.nabs, Gs, add_mul, mul_add, mul_assoc, M3, ← mul_assoc L.GG L.ζ, ← zG, mul_assoc, M3]
/- English proof (translation)
Rewrite using `[← mul_assoc L.GG L.ζ, ← zG, mul_assoc, GGi']`.
-/
theorem gamma_zeta_nabla_cancel : L.GG * (L.GG * (L.ζ * (L.GGi * L.nab))) = L.GG * (L.ζ * L.nab) := by
  rw [← mul_assoc L.GG L.ζ, ← zG, mul_assoc, GGi']
/- English proof (translation)
Rewrite using `[← mul_assoc L.GG L.ζ, ← zG, mul_assoc, GGi', ← mul_assoc, ← zG, mul_assoc, M3]`.
-/
theorem gamma_zeta_conj_cancel : L.GG * (L.GG * (L.ζ * (L.GGi * (L.ζb * L.GGi)))) = L.ζ * L.ζb := by
  rw [← mul_assoc L.GG L.ζ, ← zG, mul_assoc, GGi', ← mul_assoc, ← zG, mul_assoc, M3]

/- English proof (translation)
Rewrite using `[L.nabs_ζb, mul_sub, mul_one]`.
-/
theorem s_zb : L.GG * (L.nabs * L.ζb) = L.GG * (L.ζb * L.nabs) - L.GG := by rw [L.nabs_ζb, mul_sub, mul_one]
/- English proof (translation)
Rewrite using `[L.nab_ζ, mul_add, mul_one]`.
-/
theorem gamma_nabla_zeta_commutator : L.GG * (L.nab * L.ζ) = L.GG * (L.ζ * L.nab) + L.GG := by rw [L.nab_ζ, mul_add, mul_one]

/- English proof (translation)
The claim follows from `(Algebra.smul_def c X).symm`.
-/
theorem alg_mul (c : ℂ) (X : A) : algebraMap ℂ A c * X = c • X := (Algebra.smul_def c X).symm

/- English proof (translation)
Unfold `R.LevelData.m0 R.LevelData.l0`. Simplify using `only [alg_mul, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, neg_neg, smul_mul_assoc, mul_smul_comm, mul_assoc, smul_add, smul_sub, smul_neg, neg_sub, neg_add]`. Simplify using `only [M1, M2, M3', M4, M5, M6', M7, M8, M9, gamma_zeta_nabla_cancel, gamma_zeta_conj_cancel, s_zb, gamma_nabla_zeta_commutator]`. Use `module`.
-/
theorem op_identity (u v : ℂ) :
    (u - v) • (L.GG * L.m0 u * L.GG * L.l0 v - L.GG * L.l0 v * L.GG * L.m0 u) -
      L.GG * L.GG * (L.m0 v * L.l0 v - L.m0 u * L.l0 u) =
    (u - v) • (L.GG * L.GG * (L.nabs * L.nab - L.nab * L.nabs) +
      (1 + u + v) • (L.ζ * L.ζb - L.GG)) := by
  unfold R.LevelData.m0 R.LevelData.l0
  simp only [alg_mul, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, neg_neg, smul_mul_assoc,
    mul_smul_comm, mul_assoc, smul_add, smul_sub, smul_neg, neg_sub, neg_add]
  simp only [M1, M2, M3', M4, M5, M6', M7, M8, M9, gamma_zeta_nabla_cancel, gamma_zeta_conj_cancel, s_zb, gamma_nabla_zeta_commutator]
  module

end Op

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

def cdn (ρ : M.Ty P) (m : ℕ) (Y Y' : ℂ) : ℂ :=
  if h : ∃ τ, M.Up P m τ ρ then M.xEx P {m} h.choose Y * M.xEx P {m} h.choose Y' else 0

def Cf (ρ : M.Ty P) (u v : ℂ) : ℂ :=
  M.xC P ρ u * M.wC P ρ v - M.xC P ρ v * M.wC P ρ u -
    (u - v) * (∑ m ∈ Icc 1 (P.k - 1), M.xEx P {m} ρ u * M.xEx P {m} ρ v * ((M.Nrm P m ρ : ℝ) : ℂ) -
      ∑ m ∈ Icc 1 (P.k - 1), cdn ρ m v u * ((M.NrmDown P m ρ : ℝ) : ℂ))

variable {d : Q.NFData P A} (hd : Hyp d)
include hd

/- English proof (translation)
Rewrite using `[comm_Pj hd hZ, mul_assoc, Pj_idem]`.
-/
theorem Pj_Z_Pj {Z : A} (hZ : ∀ f, Commute (d.κ f) Z) (ρ : M.Ty P) : Pj d.κ ρ * Z * Pj d.κ ρ = Z * Pj d.κ ρ := by
  rw [comm_Pj hd hZ, mul_assoc, Pj_idem]

/- English proof (translation)
Rewrite using `[show Pj d.κ ρ * (d.κ f * d.κ g * Z) * Pj d.κ ρ = Pj d.κ ρ * d.κ f * d.κ g * Z * Pj d.κ ρ by simp only [mul_assoc], Pj_kap, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, Pj_kap, smul_mul_assoc, smul_mul_assoc, smul_smul, Pj_Z_Pj hd hZ]`.
-/
theorem Pj_kkZ {Z : A} (hZ : ∀ f, Commute (d.κ f) Z) (f g : M.Ty P → ℂ) (ρ : M.Ty P) :
    Pj d.κ ρ * (d.κ f * d.κ g * Z) * Pj d.κ ρ = (f ρ * g ρ) • (Z * Pj d.κ ρ) := by
  rw [show Pj d.κ ρ * (d.κ f * d.κ g * Z) * Pj d.κ ρ = Pj d.κ ρ * d.κ f * d.κ g * Z * Pj d.κ ρ by simp only [mul_assoc],
    Pj_kap, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, Pj_kap, smul_mul_assoc, smul_mul_assoc, smul_smul,
    Pj_Z_Pj hd hZ]

/- English proof (translation)
Rewrite using `[← mul_assoc, Pj_kap, smul_mul_assoc, smul_mul_assoc, Pj_Z_Pj hd hZ]`.
-/
theorem Pj_kZ {Z : A} (hZ : ∀ f, Commute (d.κ f) Z) (f : M.Ty P → ℂ) (ρ : M.Ty P) :
    Pj d.κ ρ * (d.κ f * Z) * Pj d.κ ρ = f ρ • (Z * Pj d.κ ρ) := by
  rw [← mul_assoc, Pj_kap, smul_mul_assoc, smul_mul_assoc, Pj_Z_Pj hd hZ]

/- English proof (translation)
Unfold `Q.NFData.S12`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, Pj_kap, smul_mul_assoc, smul_mul_assoc, P_SSs_P hd, if_neg (fun h => ee_not_self hi ρ (off_of_up h)), smul_zero]`.
-/
theorem projection_upper_sum_zero (Y : ℂ) (ρ : M.Ty P) : Pj d.κ ρ * d.S12 Y * Pj d.κ ρ = 0 := by
  unfold Q.NFData.S12
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← mul_assoc, Pj_kap, smul_mul_assoc, smul_mul_assoc, P_SSs_P hd, if_neg (fun h => ee_not_self hi ρ (off_of_up h)),
    smul_zero]

/- English proof (translation)
Unfold `Q.NFData.S4`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun l hl => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations.

Rewrite `hj` using `[Finset.mem_erase]`. Use `supp_mul d.κ (supp_mul d.κ (supp_SSs hd l) (supp_SS hd j)) (supp_kcomm hd (kc_kap hd · _)) ρ ρ ?_` and prove the remaining obligations. Introduce `h`. Use `off_eq h (off_zero.2 rfl) j hj.2` as an intermediate fact. Simplify using `[ee, hj.1] at this`.
-/
theorem projection_quartic_zero (Y : ℂ) (ρ : M.Ty P) : Pj d.κ ρ * d.S4 Y * Pj d.κ ρ = 0 := by
  unfold Q.NFData.S4
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun l hl => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_erase] at hj
  refine supp_mul d.κ (supp_mul d.κ (supp_SSs hd l) (supp_SS hd j)) (supp_kcomm hd (kc_kap hd · _)) ρ ρ ?_
  intro h
  have := off_eq h (off_zero.2 rfl) j hj.2
  simp [ee, hj.1] at this

/- English proof (translation)
The claim follows from `(((kc_GG hd f).mul_right (kappa_commute_raising_data hd f u)).mul_right (kc_GG hd f)).mul_right (kappa_commute_lowering_data hd f v)`.
-/
theorem kappa_commute_lowering_gamma (f : M.Ty P → ℂ) (u v : ℂ) : Commute (d.κ f) (d.L.GG * d.L.m0 u * d.L.GG * d.L.l0 v) :=
  (((kc_GG hd f).mul_right (kappa_commute_raising_data hd f u)).mul_right (kc_GG hd f)).mul_right (kappa_commute_lowering_data hd f v)
/- English proof (translation)
The claim follows from `(((kc_GG hd f).mul_right (kappa_commute_lowering_data hd f v)).mul_right (kc_GG hd f)).mul_right (kappa_commute_raising_data hd f u)`.
-/
theorem kappa_commute_gamma_pair (f : M.Ty P → ℂ) (u v : ℂ) : Commute (d.κ f) (d.L.GG * d.L.l0 v * d.L.GG * d.L.m0 u) :=
  (((kc_GG hd f).mul_right (kappa_commute_lowering_data hd f v)).mul_right (kc_GG hd f)).mul_right (kappa_commute_raising_data hd f u)
/- English proof (translation)
The claim follows from `((kc_GG hd f).mul_right (kappa_commute_raising_data hd f v)).mul_right (kappa_commute_lowering_data hd f v)`.
-/
theorem kappa_commute_gamma_product (f : M.Ty P → ℂ) (v : ℂ) : Commute (d.κ f) (d.L.GG * d.L.m0 v * d.L.l0 v) :=
  ((kc_GG hd f).mul_right (kappa_commute_raising_data hd f v)).mul_right (kappa_commute_lowering_data hd f v)

/- English proof (translation)
Establish `c1` using `(kc_GG hd (fun ρ => M.xC P ρ u)).eq`. Establish `c2` using `((kappa_commute_raising_data hd (fun ρ => M.xC P ρ v) u).mul_right (kc_GG hd (fun ρ => M.xC P ρ v))).eq`. Establish `c3` using `(kc_GG hd (fun ρ => M.xC P ρ v)).eq`. Unfold `Q.NFData.x at *`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [mul_assoc]`. Use `_ = (d.κ (fun ρ => M.xC P ρ u) * d.L.GG) * (d.κ (fun ρ => M.xC P ρ v) * (d.L.m0 u * d.L.GG)) * d.L.l0 v := by`. Rewrite using `[c1, c2]`. Use `_ = d.κ (fun ρ => M.xC P ρ u) * (d.L.GG * d.κ (fun ρ => M.xC P ρ v)) * (d.L.m0 u * d.L.GG) * d.L.l0 v := by`. Simplify using `only [mul_assoc]`.

Use `_ = d.κ (fun ρ => M.xC P ρ u) * (d.κ (fun ρ => M.xC P ρ v) * d.L.GG) * (d.L.m0 u * d.L.GG) * d.L.l0 v := by`. Rewrite using `[c3]`. Use `_ = _ := by simp only [mul_assoc]`.
-/
theorem upper_lower_diagonal_product (u v : ℂ) : d.L.GG * d.x u * d.L.m0 u * (d.L.GG * d.x v * d.L.l0 v) =
    d.x u * d.x v * (d.L.GG * d.L.m0 u * d.L.GG * d.L.l0 v) := by
  have c1 := (kc_GG hd (fun ρ => M.xC P ρ u)).eq
  have c2 := ((kappa_commute_raising_data hd (fun ρ => M.xC P ρ v) u).mul_right (kc_GG hd (fun ρ => M.xC P ρ v))).eq
  have c3 := (kc_GG hd (fun ρ => M.xC P ρ v)).eq
  unfold Q.NFData.x at *
  calc d.L.GG * d.κ (fun ρ => M.xC P ρ u) * d.L.m0 u * (d.L.GG * d.κ (fun ρ => M.xC P ρ v) * d.L.l0 v)
      = (d.L.GG * d.κ (fun ρ => M.xC P ρ u)) * ((d.L.m0 u * d.L.GG) * d.κ (fun ρ => M.xC P ρ v)) * d.L.l0 v := by
        simp only [mul_assoc]
    _ = (d.κ (fun ρ => M.xC P ρ u) * d.L.GG) * (d.κ (fun ρ => M.xC P ρ v) * (d.L.m0 u * d.L.GG)) * d.L.l0 v := by
        rw [c1, c2]
    _ = d.κ (fun ρ => M.xC P ρ u) * (d.L.GG * d.κ (fun ρ => M.xC P ρ v)) * (d.L.m0 u * d.L.GG) * d.L.l0 v := by
        simp only [mul_assoc]
    _ = d.κ (fun ρ => M.xC P ρ u) * (d.κ (fun ρ => M.xC P ρ v) * d.L.GG) * (d.L.m0 u * d.L.GG) * d.L.l0 v := by
        rw [c3]
    _ = _ := by simp only [mul_assoc]

/- English proof (translation)
Establish `c1` using `(kc_GG hd (fun ρ => M.xC P ρ v)).eq`. Establish `c2` using `((kappa_commute_lowering_data hd (fun ρ => M.xC P ρ u) v).mul_right (kc_GG hd (fun ρ => M.xC P ρ u))).eq`. Establish `c3` using `(kc_GG hd (fun ρ => M.xC P ρ u)).eq`. Unfold `Q.NFData.x at *`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [mul_assoc]`. Use `_ = (d.κ (fun ρ => M.xC P ρ v) * d.L.GG) * (d.κ (fun ρ => M.xC P ρ u) * (d.L.l0 v * d.L.GG)) * d.L.m0 u := by`. Rewrite using `[c1, c2]`. Use `_ = d.κ (fun ρ => M.xC P ρ v) * (d.L.GG * d.κ (fun ρ => M.xC P ρ u)) * (d.L.l0 v * d.L.GG) * d.L.m0 u := by`. Simplify using `only [mul_assoc]`.

Use `_ = d.κ (fun ρ => M.xC P ρ v) * (d.κ (fun ρ => M.xC P ρ u) * d.L.GG) * (d.L.l0 v * d.L.GG) * d.L.m0 u := by`. Rewrite using `[c3]`. Use `_ = _ := by simp only [mul_assoc]`.
-/
theorem lower_upper_diagonal_product (u v : ℂ) : d.L.GG * d.x v * d.L.l0 v * (d.L.GG * d.x u * d.L.m0 u) =
    d.x v * d.x u * (d.L.GG * d.L.l0 v * d.L.GG * d.L.m0 u) := by
  have c1 := (kc_GG hd (fun ρ => M.xC P ρ v)).eq
  have c2 := ((kappa_commute_lowering_data hd (fun ρ => M.xC P ρ u) v).mul_right (kc_GG hd (fun ρ => M.xC P ρ u))).eq
  have c3 := (kc_GG hd (fun ρ => M.xC P ρ u)).eq
  unfold Q.NFData.x at *
  calc d.L.GG * d.κ (fun ρ => M.xC P ρ v) * d.L.l0 v * (d.L.GG * d.κ (fun ρ => M.xC P ρ u) * d.L.m0 u)
      = (d.L.GG * d.κ (fun ρ => M.xC P ρ v)) * ((d.L.l0 v * d.L.GG) * d.κ (fun ρ => M.xC P ρ u)) * d.L.m0 u := by
        simp only [mul_assoc]
    _ = (d.κ (fun ρ => M.xC P ρ v) * d.L.GG) * (d.κ (fun ρ => M.xC P ρ u) * (d.L.l0 v * d.L.GG)) * d.L.m0 u := by
        rw [c1, c2]
    _ = d.κ (fun ρ => M.xC P ρ v) * (d.L.GG * d.κ (fun ρ => M.xC P ρ u)) * (d.L.l0 v * d.L.GG) * d.L.m0 u := by
        simp only [mul_assoc]
    _ = d.κ (fun ρ => M.xC P ρ v) * (d.κ (fun ρ => M.xC P ρ u) * d.L.GG) * (d.L.l0 v * d.L.GG) * d.L.m0 u := by
        rw [c3]
    _ = _ := by simp only [mul_assoc]

/- English proof (translation)
Establish `c1` using `(kc_GG hd (fun ρ => M.xC P ρ v)).eq`. Unfold `Q.NFData.x at *`. Rewrite using `[← c1]`. Simplify using `only [mul_assoc]`.
-/
theorem diagonal_upper_lowering_factor (v : ℂ) : d.L.GG * d.x v * d.L.m0 v * d.L.l0 v = d.x v * (d.L.GG * d.L.m0 v * d.L.l0 v) := by
  have c1 := (kc_GG hd (fun ρ => M.xC P ρ v)).eq
  unfold Q.NFData.x at *
  rw [← c1]; simp only [mul_assoc]

/- English proof (translation)
Rewrite using `[normal_form_upper_left]`. Simplify using `only [mul_add, add_mul]`. Establish `z1 : Pj d.κ ρ * (d.L.GG * d.L.m0 v * d.L.GGi * d.weightedSumBis v) * Pj d.κ ρ = 0`. Rewrite using `[show Pj d.κ ρ * (d.L.GG * d.L.m0 v * d.L.GGi * d.weightedSumBis v) * Pj d.κ ρ = (Pj d.κ ρ * (d.L.GG * d.L.m0 v * d.L.GGi)) * d.weightedSumBis v * Pj d.κ ρ by simp only [mul_assoc], comm_Pj hd (fun f => ((kc_GG hd f).mul_right (kappa_commute_raising_data hd f v)).mul_right (kc_GG …`. Establish `z2 : Pj d.κ ρ * (d.S12 v * d.L.l0 v) * Pj d.κ ρ = 0`.

Rewrite using `[show Pj d.κ ρ * (d.S12 v * d.L.l0 v) * Pj d.κ ρ = Pj d.κ ρ * d.S12 v * (d.L.l0 v * Pj d.κ ρ) by`. Simplify using `only [mul_assoc], ← comm_Pj hd (kappa_commute_lowering_data hd · v), ← mul_assoc, projection_upper_sum_zero hd, zero_mul]`. Establish `z3 : Pj d.κ ρ * (d.L.GGi * d.S4 v) * Pj d.κ ρ = 0`. Rewrite using `[← mul_assoc, comm_Pj hd (kc_GGi hd), mul_assoc, mul_assoc, ← mul_assoc (Pj d.κ ρ), projection_quartic_zero hd, mul_zero]`. Rewrite using `[z1, z2, z3, add_zero, add_zero, add_zero]`.

Use `congr 1`. Rewrite using `[show Pj d.κ ρ * (d.L.GGi * d.κ (fun ρ => M.wC P ρ v)) * Pj d.κ ρ = (Pj d.κ ρ * d.L.GGi) * (d.κ (fun ρ => M.wC P ρ v) * Pj d.κ ρ) by simp only [mul_assoc], kap_Pj, comm_Pj hd (kc_GGi hd), mul_smul_comm, mul_assoc, Pj_idem]`. Rewrite using `[diagonal_upper_lowering_factor hd, Q.NFData.x, Pj_kZ hd (kappa_commute_gamma_product hd · v)]`.
-/
theorem projection_upper_left_block (v : ℂ) (ρ : M.Ty P) :
    Pj d.κ ρ * d.QQ v 0 0 * Pj d.κ ρ = M.wC P ρ v • (d.L.GGi * Pj d.κ ρ) +
      M.xC P ρ v • (d.L.GG * d.L.m0 v * d.L.l0 v * Pj d.κ ρ) := by
  rw [normal_form_upper_left]
  simp only [mul_add, add_mul]
  have z1 : Pj d.κ ρ * (d.L.GG * d.L.m0 v * d.L.GGi * d.weightedSumBis v) * Pj d.κ ρ = 0 := by
    rw [show Pj d.κ ρ * (d.L.GG * d.L.m0 v * d.L.GGi * d.weightedSumBis v) * Pj d.κ ρ =
      (Pj d.κ ρ * (d.L.GG * d.L.m0 v * d.L.GGi)) * d.weightedSumBis v * Pj d.κ ρ by simp only [mul_assoc],
      comm_Pj hd (fun f => ((kc_GG hd f).mul_right (kappa_commute_raising_data hd f v)).mul_right (kc_GGi hd f)),
      show d.L.GG * d.L.m0 v * d.L.GGi * Pj d.κ ρ * d.weightedSumBis v * Pj d.κ ρ =
        d.L.GG * d.L.m0 v * d.L.GGi * (Pj d.κ ρ * d.weightedSumBis v * Pj d.κ ρ) by simp only [mul_assoc], projection_lower_sum_zero hd, mul_zero]
  have z2 : Pj d.κ ρ * (d.S12 v * d.L.l0 v) * Pj d.κ ρ = 0 := by
    rw [show Pj d.κ ρ * (d.S12 v * d.L.l0 v) * Pj d.κ ρ = Pj d.κ ρ * d.S12 v * (d.L.l0 v * Pj d.κ ρ) by
      simp only [mul_assoc], ← comm_Pj hd (kappa_commute_lowering_data hd · v), ← mul_assoc, projection_upper_sum_zero hd, zero_mul]
  have z3 : Pj d.κ ρ * (d.L.GGi * d.S4 v) * Pj d.κ ρ = 0 := by
    rw [← mul_assoc, comm_Pj hd (kc_GGi hd), mul_assoc, mul_assoc, ← mul_assoc (Pj d.κ ρ), projection_quartic_zero hd, mul_zero]
  rw [z1, z2, z3, add_zero, add_zero, add_zero]
  congr 1
  · rw [show Pj d.κ ρ * (d.L.GGi * d.κ (fun ρ => M.wC P ρ v)) * Pj d.κ ρ =
      (Pj d.κ ρ * d.L.GGi) * (d.κ (fun ρ => M.wC P ρ v) * Pj d.κ ρ) by simp only [mul_assoc], kap_Pj,
      comm_Pj hd (kc_GGi hd), mul_smul_comm, mul_assoc, Pj_idem]
  · rw [diagonal_upper_lowering_factor hd, Q.NFData.x, Pj_kZ hd (kappa_commute_gamma_product hd · v)]

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {d : Q.NFData P A} (hd : Hyp d)
include hd

/- English proof (translation)
Rewrite using `[normal_form_upper_right, normal_form_lower_left]`. Simplify using `only [add_mul, mul_add]`. Establish `z1 : Pj d.κ ρ * (d.L.GG * d.x u * d.L.m0 u * d.weightedSumBis v) * Pj d.κ ρ = 0`. Rewrite using `[show Pj d.κ ρ * (d.L.GG * d.x u * d.L.m0 u * d.weightedSumBis v) * Pj d.κ ρ = (Pj d.κ ρ * (d.L.GG * d.x u * d.L.m0 u)) * d.weightedSumBis v * Pj d.κ ρ by simp only [mul_assoc], comm_Pj hd (kappa_commute_upper_diagonal hd · u), mul_assoc, mul_assoc, ← mul_assoc (Pj d.κ ρ), projec …`. Establish `z2 : Pj d.κ ρ * (d.S12 u * (d.L.GG * d.x v * d.L.l0 v)) * Pj d.κ ρ = 0`.

Rewrite using `[show Pj d.κ ρ * (d.S12 u * (d.L.GG * d.x v * d.L.l0 v)) * Pj d.κ ρ = Pj d.κ ρ * d.S12 u * ((d.L.GG * d.x v * d.L.l0 v) * Pj d.κ ρ) by simp only [mul_assoc], ← comm_Pj hd (kappa_commute_lower_diagonal hd · v), ← mul_assoc, projection_upper_sum_zero hd, zero_mul]`. Rewrite using `[z1, z2, add_zero, zero_add, upper_lower_diagonal_product hd, Q.NFData.x, Q.NFData.x, Pj_kkZ hd (kappa_commute_lowering_gamma hd · u v), blk_12_21 hd, Finset.sum_smul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[hd.nrm m hm, kap_Pj, smul_smul]`.
-/
theorem blk_12_21' (u v : ℂ) (ρ : M.Ty P) :
    Pj d.κ ρ * (d.QQ u 0 1 * d.QQ v 1 0) * Pj d.κ ρ =
      (M.xC P ρ u * M.xC P ρ v) • (d.L.GG * d.L.m0 u * d.L.GG * d.L.l0 v * Pj d.κ ρ) +
      (∑ m ∈ Icc 1 (P.k - 1), M.xEx P {m} ρ u * M.xEx P {m} ρ v * ((M.Nrm P m ρ : ℝ) : ℂ)) • Pj d.κ ρ := by
  rw [normal_form_upper_right, normal_form_lower_left]
  simp only [add_mul, mul_add]
  have z1 : Pj d.κ ρ * (d.L.GG * d.x u * d.L.m0 u * d.weightedSumBis v) * Pj d.κ ρ = 0 := by
    rw [show Pj d.κ ρ * (d.L.GG * d.x u * d.L.m0 u * d.weightedSumBis v) * Pj d.κ ρ =
      (Pj d.κ ρ * (d.L.GG * d.x u * d.L.m0 u)) * d.weightedSumBis v * Pj d.κ ρ by simp only [mul_assoc],
      comm_Pj hd (kappa_commute_upper_diagonal hd · u), mul_assoc, mul_assoc, ← mul_assoc (Pj d.κ ρ), projection_lower_sum_zero hd, mul_zero]
  have z2 : Pj d.κ ρ * (d.S12 u * (d.L.GG * d.x v * d.L.l0 v)) * Pj d.κ ρ = 0 := by
    rw [show Pj d.κ ρ * (d.S12 u * (d.L.GG * d.x v * d.L.l0 v)) * Pj d.κ ρ =
      Pj d.κ ρ * d.S12 u * ((d.L.GG * d.x v * d.L.l0 v) * Pj d.κ ρ) by simp only [mul_assoc],
      ← comm_Pj hd (kappa_commute_lower_diagonal hd · v), ← mul_assoc, projection_upper_sum_zero hd, zero_mul]
  rw [z1, z2, add_zero, zero_add, upper_lower_diagonal_product hd, Q.NFData.x, Q.NFData.x, Pj_kkZ hd (kappa_commute_lowering_gamma hd · u v), blk_12_21 hd,
    Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hd.nrm m hm, kap_Pj, smul_smul]

/- English proof (translation)
Rewrite using `[normal_form_upper_right, normal_form_lower_left]`. Simplify using `only [add_mul, mul_add]`. Establish `z1 : Pj d.κ ρ * (d.L.GG * d.x v * d.L.l0 v * d.S12 u) * Pj d.κ ρ = 0`. Rewrite using `[show Pj d.κ ρ * (d.L.GG * d.x v * d.L.l0 v * d.S12 u) * Pj d.κ ρ = (Pj d.κ ρ * (d.L.GG * d.x v * d.L.l0 v)) * d.S12 u * Pj d.κ ρ by simp only [mul_assoc], comm_Pj hd (kappa_commute_lower_diagonal hd · v), mul_assoc, mul_assoc, ← mul_assoc (Pj d.κ ρ), projection_upper_sum_zero hd …`. Establish `z2 : Pj d.κ ρ * (d.weightedSumBis v * (d.L.GG * d.x u * d.L.m0 u)) * Pj d.κ ρ = 0`.

Rewrite using `[show Pj d.κ ρ * (d.weightedSumBis v * (d.L.GG * d.x u * d.L.m0 u)) * Pj d.κ ρ = Pj d.κ ρ * d.weightedSumBis v * ((d.L.GG * d.x u * d.L.m0 u) * Pj d.κ ρ) by simp only [mul_assoc], ← comm_Pj hd (kappa_commute_upper_diagonal hd · u), ← mul_assoc, projection_lower_sum_zero hd, zero_ …`. Rewrite using `[z1, z2, add_zero, zero_add, lower_upper_diagonal_product hd, Q.NFData.x, Q.NFData.x, Pj_kkZ hd (kappa_commute_gamma_pair hd · u v), blk_21_12 hd, Finset.sum_smul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[hND m hm, kap_Pj, smul_smul]`.

Both sides reduce to the same expression.
-/
theorem blk_21_12' (hND : ∀ m ∈ Icc 1 (P.k - 1), d.SS m * star (d.SS m) = d.κ fun ρ => ((M.NrmDown P m ρ : ℝ) : ℂ))
    (u v : ℂ) (ρ : M.Ty P) :
    Pj d.κ ρ * (d.QQ v 1 0 * d.QQ u 0 1) * Pj d.κ ρ =
      (M.xC P ρ v * M.xC P ρ u) • (d.L.GG * d.L.l0 v * d.L.GG * d.L.m0 u * Pj d.κ ρ) +
      (∑ m ∈ Icc 1 (P.k - 1), cdn ρ m v u * ((M.NrmDown P m ρ : ℝ) : ℂ)) • Pj d.κ ρ := by
  rw [normal_form_upper_right, normal_form_lower_left]
  simp only [add_mul, mul_add]
  have z1 : Pj d.κ ρ * (d.L.GG * d.x v * d.L.l0 v * d.S12 u) * Pj d.κ ρ = 0 := by
    rw [show Pj d.κ ρ * (d.L.GG * d.x v * d.L.l0 v * d.S12 u) * Pj d.κ ρ =
      (Pj d.κ ρ * (d.L.GG * d.x v * d.L.l0 v)) * d.S12 u * Pj d.κ ρ by simp only [mul_assoc],
      comm_Pj hd (kappa_commute_lower_diagonal hd · v), mul_assoc, mul_assoc, ← mul_assoc (Pj d.κ ρ), projection_upper_sum_zero hd, mul_zero]
  have z2 : Pj d.κ ρ * (d.weightedSumBis v * (d.L.GG * d.x u * d.L.m0 u)) * Pj d.κ ρ = 0 := by
    rw [show Pj d.κ ρ * (d.weightedSumBis v * (d.L.GG * d.x u * d.L.m0 u)) * Pj d.κ ρ =
      Pj d.κ ρ * d.weightedSumBis v * ((d.L.GG * d.x u * d.L.m0 u) * Pj d.κ ρ) by simp only [mul_assoc],
      ← comm_Pj hd (kappa_commute_upper_diagonal hd · u), ← mul_assoc, projection_lower_sum_zero hd, zero_mul]
  rw [z1, z2, add_zero, zero_add, lower_upper_diagonal_product hd, Q.NFData.x, Q.NFData.x, Pj_kkZ hd (kappa_commute_gamma_pair hd · u v), blk_21_12 hd,
    Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hND m hm, kap_Pj, smul_smul]
  rfl

/- English proof (translation)
Establish `e1 : Pj d.κ ρ * (d.QQ u 1 1 * d.QQ v 0 0) * Pj d.κ ρ = M.xC P ρ u • (d.L.GG * (Pj d.κ ρ * d.QQ v 0 0 * Pj d.κ ρ))`. Rewrite using `[show Pj d.κ ρ * (d.QQ u 1 1 * d.QQ v 0 0) * Pj d.κ ρ = (Pj d.κ ρ * d.QQ u 1 1) * (d.QQ v 0 0 * Pj d.κ ρ) by`. Simplify using `only [mul_assoc]]`. Rewrite using `[normal_form_diagonal d u, Pj_GGx hd, smul_mul_assoc]`. Use `congr 1`.

Simplify using `only [mul_assoc]`. Rewrite using `[e1, projection_upper_left_block hd, mul_add, mul_smul_comm, mul_smul_comm, smul_add, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[← mul_assoc, d.L.GG_GGi, one_mul]`. Use `congr 1`.

Simplify using `only [mul_assoc]`.
-/
theorem rhs_diag (u v : ℂ) (ρ : M.Ty P) :
    Pj d.κ ρ * (d.QQ u 1 1 * d.QQ v 0 0) * Pj d.κ ρ = (M.xC P ρ u * M.wC P ρ v) • Pj d.κ ρ +
      (M.xC P ρ u * M.xC P ρ v) • (d.L.GG * d.L.GG * (d.L.m0 v * d.L.l0 v) * Pj d.κ ρ) := by
  have e1 : Pj d.κ ρ * (d.QQ u 1 1 * d.QQ v 0 0) * Pj d.κ ρ =
      M.xC P ρ u • (d.L.GG * (Pj d.κ ρ * d.QQ v 0 0 * Pj d.κ ρ)) := by
    rw [show Pj d.κ ρ * (d.QQ u 1 1 * d.QQ v 0 0) * Pj d.κ ρ = (Pj d.κ ρ * d.QQ u 1 1) * (d.QQ v 0 0 * Pj d.κ ρ) by
      simp only [mul_assoc]]
    rw [normal_form_diagonal d u, Pj_GGx hd, smul_mul_assoc]
    congr 1
    simp only [mul_assoc]
  rw [e1, projection_upper_left_block hd, mul_add, mul_smul_comm, mul_smul_comm, smul_add, smul_smul, smul_smul]
  congr 1
  · rw [← mul_assoc, d.L.GG_GGi, one_mul]
  · congr 1; simp only [mul_assoc]

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {d : Q.NFData P A} (hd : Hyp d)
include hd

/- English proof (translation)
Establish `e` using `congrArg (fun X => Pj d.κ ρ * X * Pj d.κ ρ) (hR u v)`. Simplify using `only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul] at e`. Rewrite `e` using `[blk_12_21' hd, blk_21_12' hd hND, rhs_diag hd, rhs_diag hd]`. Establish `hop` using `congrArg (· * Pj d.κ ρ) (op_identity d.L u v)`. Simplify using `only [sub_mul, smul_mul_assoc, add_mul, mul_sub] at hop`.

Unfold `Cf`. Simplify using `only [add_mul, sub_mul, mul_sub, smul_mul_assoc]`. Take the linear combination `(norm := module) e - (M.xC P ρ u * M.xC P ρ v) • hop`.
-/
theorem diag_id (hND : ∀ m ∈ Icc 1 (P.k - 1), d.SS m * star (d.SS m) = d.κ fun ρ => ((M.NrmDown P m ρ : ℝ) : ℂ))
    (hR : ∀ u v : ℂ, (u - v) • (d.QQ u 0 1 * d.QQ v 1 0 - d.QQ v 1 0 * d.QQ u 0 1) =
      d.QQ u 1 1 * d.QQ v 0 0 - d.QQ v 1 1 * d.QQ u 0 0) (ρ : M.Ty P) (u v : ℂ) :
    ((u - v) * M.xC P ρ u * M.xC P ρ v) • ((d.L.GG * d.L.GG * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) +
      (1 + u + v) • (d.L.ζ * d.L.ζb - d.L.GG)) * Pj d.κ ρ) = Cf ρ u v • Pj d.κ ρ := by
  have e := congrArg (fun X => Pj d.κ ρ * X * Pj d.κ ρ) (hR u v)
  simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul] at e
  rw [blk_12_21' hd, blk_21_12' hd hND, rhs_diag hd, rhs_diag hd] at e
  have hop := congrArg (· * Pj d.κ ρ) (op_identity d.L u v)
  simp only [sub_mul, smul_mul_assoc, add_mul, mul_sub] at hop
  unfold Cf
  simp only [add_mul, sub_mul, mul_sub, smul_mul_assoc]
  linear_combination (norm := module) e - (M.xC P ρ u * M.xC P ρ v) • hop

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

section Model

variable (P : M.Par)

def dM (L : R.LevelData (M.A P) P.r) : Q.NFData P (M.A P) := ⟨L, M.kap P, M.SS P⟩

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hz, -, hzb, -, hG, hGi, hn, hns, -⟩` from `hL`. Use `⟨fun f => Formalism.FourierDecayAlt.P.Mx7.star_kap P f, fun f => ?_, fun l f g h => Formalism.FourierDecayAlt.P.shift_shift_relation P l f g h, fun l hl => (Formalism.FourierDecayAlt.P.shift_norm_relation P hP l hl).1⟩` and prove the remaining obligations. Use `show Commute (M.kap P f) L.nab ∧ Commute (M.kap P f) L.nabs ∧ Commute (M.kap P f) L.ζ ∧ Commute (M.kap P f) L.ζb ∧ Commute (M.kap P f) L.GG ∧ Commute (M.kap P f) L.GGi`. Rewrite using `[hz, hzb, hG, hGi, hn, hns]`. Conclude with `⟨Formalism.FourierDecayAlt.P.Mx7.kap_comm_nab P f, Formalism.FourierDecayAlt.P.Mx7.kap_comm_nabs P f, Formalism.FourierDecayAlt.P.Mx7.kap_comm_sc P f _, Formalism.FourierDecayAlt.P.Mx7.kap_comm_sc P f _, Formalism.FourierDecayAlt.P.Mx7.kap_comm_sc P f _, Formalism.FourierDecayAlt …`.
-/
theorem model_hyp (hP : P.OK) (L : R.LevelData (M.A P) P.r) (hL : M.IsModelLevel P L) : Hyp (dM P L) := by
  obtain ⟨-, -, -, -, -, -, hz, -, hzb, -, hG, hGi, hn, hns, -⟩ := hL
  refine ⟨fun f => Formalism.FourierDecayAlt.P.Mx7.star_kap P f, fun f => ?_, fun l f g h => Formalism.FourierDecayAlt.P.shift_shift_relation P l f g h,
    fun l hl => (Formalism.FourierDecayAlt.P.shift_norm_relation P hP l hl).1⟩
  show Commute (M.kap P f) L.nab ∧ Commute (M.kap P f) L.nabs ∧ Commute (M.kap P f) L.ζ ∧
    Commute (M.kap P f) L.ζb ∧ Commute (M.kap P f) L.GG ∧ Commute (M.kap P f) L.GGi
  rw [hz, hzb, hG, hGi, hn, hns]
  exact ⟨Formalism.FourierDecayAlt.P.Mx7.kap_comm_nab P f, Formalism.FourierDecayAlt.P.Mx7.kap_comm_nabs P f, Formalism.FourierDecayAlt.P.Mx7.kap_comm_sc P f _,
    Formalism.FourierDecayAlt.P.Mx7.kap_comm_sc P f _, Formalism.FourierDecayAlt.P.Mx7.kap_comm_sc P f _, Formalism.FourierDecayAlt.P.Mx7.kap_comm_sc P f _⟩

/- English proof (translation)
Establish `hnt : Nontrivial (M.A P)` using `(Formalism.FourierDecayAlt.P.model_nontrivial P).1`. Establish `hPr : Nontrivial (M.Pr P.r)`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Take `⟨x, y, hxy⟩` from `hnt.exists_pair_ne`.

Conclude with `hxy (Matrix.ext fun i j => Subsingleton.elim _ _)`. Introduce `h0`. Use `haveI := hPr`. Establish `e` using `congrFun (congrFun h0 ρ) ρ`. Establish `e1 : (Pj (M.kap P) ρ) ρ ρ = 1` using `by simp [Pj, dl, M.kap]`.

Rewrite `e` using `[e1]`. Conclude with `one_ne_zero e`.
-/
theorem model_Pj_ne (ρ : M.Ty P) : Pj (M.kap P) ρ ≠ 0 := by
  have hnt : Nontrivial (M.A P) := (Formalism.FourierDecayAlt.P.model_nontrivial P).1
  have hPr : Nontrivial (M.Pr P.r) := by
    by_contra h; rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨x, y, hxy⟩ := hnt.exists_pair_ne
    exact hxy (Matrix.ext fun i j => Subsingleton.elim _ _)
  intro h0
  haveI := hPr
  have e := congrFun (congrFun h0 ρ) ρ
  have e1 : (Pj (M.kap P) ρ) ρ ρ = 1 := by simp [Pj, dl, M.kap]
  rw [e1] at e
  exact one_ne_zero e

/- English proof (translation)
Take `⟨L, hL⟩` from `Formalism.FourierDecayAlt.P.level_exists_model P`. Establish `hd` using `model_hyp P hP L hL`. Establish `hQ : ∀ Y, (dM P L).QQ Y = M.QQr P Y` using `Formalism.FourierDecayAlt.P.model_is_normal_form P L hL`. Establish `hND : ∀ m ∈ Icc 1 (P.k - 1), (dM P L).SS m * star ((dM P L).SS m) = (dM P L).κ fun ρ => ((M.NrmDown P m ρ : ℝ) : ℂ)` using `fun m hm => (Formalism.FourierDecayAlt.P.shift_norm_relation P hP m hm).2`. Establish `hR : ∀ u v : ℂ, (u - v) • ((dM P L).QQ u 0 1 * (dM P L).QQ v 1 0 - (dM P L).QQ v 1 0 * (dM P L).QQ u 0 1) = (dM P L).QQ u 1 1 * (dM P L).QQ v 0 0 - (dM P L).QQ v 1 1 * (dM P L).QQ u 0 0`.

Introduce `u v`. Rewrite using `[hQ, hQ]`. Conclude with `Formalism.FourierDecayAlt.P.transfer_rtt_entries P hP u v 0 1 1 0`. Establish `e` using `diag_id hd hND hR ρ u v`. Take `⟨-, -, -, -, -, -, -, -, -, -, hG, hGi, hn, hns, hT⟩` from `hL`.

Establish `hcurv` using `Formalism.FourierDecayAlt.P.m_curvature_proof P`. Establish `hGdef` using `L.GG_def`. Establish `hY : (dM P L).L.GG * (dM P L).L.GG * ((dM P L).L.nabs * (dM P L).L.nab - (dM P L).L.nab * (dM P L).L.nabs) + (1 + u + v) • ((dM P L).L.ζ * (dM P L).L.ζb - (dM P L).L.GG) = M.kap P (fun π => ((2 * M.aC P π * P.TT : ℝ) : ℂ)) + (1 + u + v) • algebraMap ℂ (M.A P) (P.TT : ℂ)` using `by show L.GG * L.GG * (L.nabs * L.nab - L.nab * L.nabs) + (1 + u + v) • (L.ζ * L.ζb - L.GG) = _`. Establish `eT : L.ζ * L.ζb - L.GG = algebraMap ℂ (M.A P) (P.TT : ℂ)` using `by rw [hGdef, hT]; abel`. Rewrite using `[eT, hn, hns, hcurv, hG]`.

Use `congr 1`. Establish `c` using `(Formalism.FourierDecayAlt.P.Mx7.kap_comm_sc P (fun π => ((2 * M.aC P π * P.TT : ℝ) : ℂ)) (M.ggP P.TT)).eq`. Establish `gg : M.ggA P * M.ggiA P = 1` using `by rw [← hG, ← hGi]; exact L.GG_GGi`. Express the relevant statement in the definitionally equal form `M.kap P _ * M.ggA P = M.ggA P * M.kap P _ at c`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [mul_assoc]`. Use `_ = M.ggA P * ((M.kap P (fun π => ((2 * M.aC P π * P.TT : ℝ) : ℂ)) * M.ggA P) * (M.ggiA P * M.ggiA P)) := by`. Rewrite using `[← c]`. Use `_ = (M.ggA P * M.kap P (fun π => ((2 * M.aC P π * P.TT : ℝ) : ℂ))) * (M.ggA P * M.ggiA P) * M.ggiA P := by`. Simplify using `only [mul_assoc]`.

Use `_ = (M.kap P (fun π => ((2 * M.aC P π * P.TT : ℝ) : ℂ)) * M.ggA P) * 1 * M.ggiA P := by rw [← c, gg]`. Use `_ = M.kap P (fun π => ((2 * M.aC P π * P.TT : ℝ) : ℂ)) * (M.ggA P * M.ggiA P) := by simp only [mul_one, mul_assoc]`. Use `_ = _ := by rw [gg, mul_one]`. Rewrite `e` using `[hY, add_mul, smul_mul_assoc]`. Simplify using `only [dM] at e`.

Rewrite `e` using `[kap_Pj, ← Algebra.smul_def, smul_smul, ← add_smul, smul_smul]`. Establish `e2 : ((u - v) * M.xC P ρ u * M.xC P ρ v * (((2 * M.aC P ρ * P.TT : ℝ) : ℂ) + (1 + u + v) * (P.TT : ℂ)) - Cf ρ u v) • Pj (M.kap P) ρ = 0` using `by rw [sub_smul, e, sub_self]`. Break down `smul_eq_zero.1 e2 with h | h` into its components or cases. Conclude with `(sub_eq_zero.1 h).symm`. Conclude with `absurd h (model_Pj_ne P ρ)`.
-/
theorem model_scalar (hP : P.OK) (ρ : M.Ty P) (u v : ℂ) :
    Cf ρ u v = (u - v) * M.xC P ρ u * M.xC P ρ v * (((2 * M.aC P ρ * P.TT : ℝ) : ℂ) + (1 + u + v) * (P.TT : ℂ)) := by
  obtain ⟨L, hL⟩ := Formalism.FourierDecayAlt.P.level_exists_model P
  have hd := model_hyp P hP L hL
  have hQ : ∀ Y, (dM P L).QQ Y = M.QQr P Y := Formalism.FourierDecayAlt.P.model_is_normal_form P L hL
  have hND : ∀ m ∈ Icc 1 (P.k - 1), (dM P L).SS m * star ((dM P L).SS m) =
      (dM P L).κ fun ρ => ((M.NrmDown P m ρ : ℝ) : ℂ) := fun m hm => (Formalism.FourierDecayAlt.P.shift_norm_relation P hP m hm).2
  have hR : ∀ u v : ℂ, (u - v) • ((dM P L).QQ u 0 1 * (dM P L).QQ v 1 0 - (dM P L).QQ v 1 0 * (dM P L).QQ u 0 1) =
      (dM P L).QQ u 1 1 * (dM P L).QQ v 0 0 - (dM P L).QQ v 1 1 * (dM P L).QQ u 0 0 := by
    intro u v; rw [hQ, hQ]; exact Formalism.FourierDecayAlt.P.transfer_rtt_entries P hP u v 0 1 1 0
  have e := diag_id hd hND hR ρ u v
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, hGi, hn, hns, hT⟩ := hL
  have hcurv := Formalism.FourierDecayAlt.P.m_curvature_proof P
  have hGdef := L.GG_def
  have hY : (dM P L).L.GG * (dM P L).L.GG * ((dM P L).L.nabs * (dM P L).L.nab - (dM P L).L.nab * (dM P L).L.nabs) +
      (1 + u + v) • ((dM P L).L.ζ * (dM P L).L.ζb - (dM P L).L.GG) =
      M.kap P (fun π => ((2 * M.aC P π * P.TT : ℝ) : ℂ)) + (1 + u + v) • algebraMap ℂ (M.A P) (P.TT : ℂ) := by
    show L.GG * L.GG * (L.nabs * L.nab - L.nab * L.nabs) + (1 + u + v) • (L.ζ * L.ζb - L.GG) = _
    have eT : L.ζ * L.ζb - L.GG = algebraMap ℂ (M.A P) (P.TT : ℂ) := by rw [hGdef, hT]; abel
    rw [eT, hn, hns, hcurv, hG]
    congr 1
    have c := (Formalism.FourierDecayAlt.P.Mx7.kap_comm_sc P (fun π => ((2 * M.aC P π * P.TT : ℝ) : ℂ)) (M.ggP P.TT)).eq
    have gg : M.ggA P * M.ggiA P = 1 := by rw [← hG, ← hGi]; exact L.GG_GGi
    change M.kap P _ * M.ggA P = M.ggA P * M.kap P _ at c
    calc M.ggA P * M.ggA P * (M.kap P (fun π => ((2 * M.aC P π * P.TT : ℝ) : ℂ)) * M.ggiA P * M.ggiA P)
        = M.ggA P * ((M.ggA P * M.kap P (fun π => ((2 * M.aC P π * P.TT : ℝ) : ℂ))) * (M.ggiA P * M.ggiA P)) := by
          simp only [mul_assoc]
      _ = M.ggA P * ((M.kap P (fun π => ((2 * M.aC P π * P.TT : ℝ) : ℂ)) * M.ggA P) * (M.ggiA P * M.ggiA P)) := by
          rw [← c]
      _ = (M.ggA P * M.kap P (fun π => ((2 * M.aC P π * P.TT : ℝ) : ℂ))) * (M.ggA P * M.ggiA P) * M.ggiA P := by
          simp only [mul_assoc]
      _ = (M.kap P (fun π => ((2 * M.aC P π * P.TT : ℝ) : ℂ)) * M.ggA P) * 1 * M.ggiA P := by rw [← c, gg]
      _ = M.kap P (fun π => ((2 * M.aC P π * P.TT : ℝ) : ℂ)) * (M.ggA P * M.ggiA P) := by simp only [mul_one, mul_assoc]
      _ = _ := by rw [gg, mul_one]
  rw [hY, add_mul, smul_mul_assoc] at e
  simp only [dM] at e
  rw [kap_Pj, ← Algebra.smul_def, smul_smul, ← add_smul, smul_smul] at e
  have e2 : ((u - v) * M.xC P ρ u * M.xC P ρ v * (((2 * M.aC P ρ * P.TT : ℝ) : ℂ) + (1 + u + v) * (P.TT : ℂ)) - Cf ρ u v) •
      Pj (M.kap P) ρ = 0 := by rw [sub_smul, e, sub_self]
  rcases smul_eq_zero.1 e2 with h | h
  · exact (sub_eq_zero.1 h).symm
  · exact absurd h (model_Pj_ne P ρ)

end Model

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P.NFx4.SX

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun i _ hz => h (by have := congrArg Complex.im hz; simpa using this)`.
-/
theorem xC_ne (ρ : M.Ty P) (Y : ℂ) (h : Y.im ≠ 0) : M.xC P ρ Y ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ hz => h (by have := congrArg Complex.im hz; simpa using this)

/- English proof (translation)
Use `mul_ne_zero (mul_ne_zero ?_ (xC_ne ρ _ (by simpa using ha))) (xC_ne ρ _ (by simpa using hb))` and prove the remaining obligations. Rewrite using `[← sub_mul]`. Use `mul_ne_zero ?_ Complex.I_ne_zero` and prove the remaining obligations. Conclude with `sub_ne_zero.2 hab` after adjusting the coercions.
-/
theorem cI_ne (ρ : M.Ty P) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ((a * Complex.I : ℂ) - b * Complex.I) * M.xC P ρ (a * Complex.I) * M.xC P ρ (b * Complex.I) ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero ?_ (xC_ne ρ _ (by simpa using ha))) (xC_ne ρ _ (by simpa using hb))
  rw [← sub_mul]; refine mul_ne_zero ?_ Complex.I_ne_zero
  exact_mod_cast sub_ne_zero.2 hab

variable {d : Q.NFData P A} (hd : Hyp d)
include hd

/- English proof (translation)
Establish `hR : ∀ u v : ℂ, (u - v) • (d.QQ u 0 1 * d.QQ v 1 0 - d.QQ v 1 0 * d.QQ u 0 1) = d.QQ u 1 1 * d.QQ v 0 0 - d.QQ v 1 1 * d.QQ u 0 0` using `fun u v => rtt_ent d hS u v 0 1 1 0`. Use `ext_right hd fun ρ => ?_` and prove the remaining obligations. Establish `eT : d.L.ζ * d.L.ζb - d.L.GG = algebraMap ℂ A d.L.TT` using `by rw [d.L.GG_def]; abel`. Establish `key : ∀ u v : ℂ, (u - v) * M.xC P ρ u * M.xC P ρ v ≠ 0 → d.L.GG * d.L.GG * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * Pj d.κ ρ + (1 + u + v) • (d.L.TT • Pj d.κ ρ) = ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) • Pj d.κ ρ + (1 + u + v) • ((P.TT : ℂ) • Pj d.κ ρ)`. Introduce `u v hc`.

Establish `e` using `diag_id hd hND hR ρ u v`. Establish `e1 : ((u - v) * M.xC P ρ u * M.xC P ρ v) • ((d.L.GG * d.L.GG * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) + (1 + u + v) • (d.L.ζ * d.L.ζb - d.L.GG)) * Pj d.κ ρ) = ((u - v) * M.xC P ρ u * M.xC P ρ v) • ((((2 * M.aC P ρ * P.TT : ℝ) : ℂ) + (1 + u + v) * (P.TT : ℂ)) • Pj d.κ ρ)`. Rewrite using `[e, model_scalar P hP ρ u v]`. Conclude with `mul_smul _ _ _`. Establish `e2` using `smul_right_injective A hc e1`.

Rewrite `e2` using `[eT, add_mul, smul_mul_assoc, ← Algebra.smul_def]`. Rewrite using `[e2, add_smul, mul_smul]`. Establish `k1` using `key (1 * Complex.I) (2 * Complex.I) (by exact_mod_cast cI_ne ρ 1 2 (by norm_num) (by norm_num) (by norm_num))`. Establish `k2` using `key (2 * Complex.I) (3 * Complex.I) (by exact_mod_cast cI_ne ρ 2 3 (by norm_num) (by norm_num) (by norm_num))`. Establish `e3 : (2 * Complex.I) • (d.L.TT • Pj d.κ ρ - (P.TT : ℂ) • Pj d.κ ρ) = 0`.

Take the linear combination `(norm := module) k2 - k1`. Establish `hX : d.L.TT • Pj d.κ ρ = (P.TT : ℂ) • Pj d.κ ρ`. Break down `smul_eq_zero.1 e3 with h | h` into its components or cases. Conclude with `absurd h (mul_ne_zero two_ne_zero Complex.I_ne_zero)`. Conclude with `sub_eq_zero.1 h`.

Establish `hK : d.L.GG * d.L.GG * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * Pj d.κ ρ = ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) • Pj d.κ ρ`. Take the linear combination `(norm := module) k1 - (1 + 1 * Complex.I + 2 * Complex.I) • hX`. Establish `inv : d.L.GGi * d.L.GGi * (d.L.GG * d.L.GG) = 1`. Rewrite using `[mul_assoc, ← mul_assoc d.L.GGi d.L.GG, d.L.GGi_GG, one_mul, d.L.GGi_GG]`. Rewrite using `[show (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * Pj d.κ ρ = d.L.GGi * d.L.GGi * (d.L.GG * d.L.GG * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * Pj d.κ ρ) by`.

Rewrite using `[← mul_assoc, ← mul_assoc, inv, one_mul], hK]`. Establish `r1 : (d.κ fun ρ => ((2 * M.aC P ρ * P.TT : ℝ) : ℂ)) * d.L.GGi * d.L.GGi * Pj d.κ ρ = d.L.GGi * d.L.GGi * ((d.κ fun ρ => ((2 * M.aC P ρ * P.TT : ℝ) : ℂ)) * Pj d.κ ρ)`. Rewrite using `[(kc_GGi hd _).eq, mul_assoc d.L.GGi, (kc_GGi hd _).eq]`. Simplify using `only [mul_assoc]`. Rewrite using `[r1, kap_Pj]`.
-/
theorem curv (hP : P.OK) (hS : Wd.IsStart d.QQ (M.qC P))
    (hND : ∀ m ∈ Icc 1 (P.k - 1), d.SS m * star (d.SS m) = d.κ fun ρ => ((M.NrmDown P m ρ : ℝ) : ℂ)) :
    d.L.nabs * d.L.nab - d.L.nab * d.L.nabs =
      (d.κ fun ρ => ((2 * M.aC P ρ * P.TT : ℝ) : ℂ)) * d.L.GGi * d.L.GGi := by
  have hR : ∀ u v : ℂ, (u - v) • (d.QQ u 0 1 * d.QQ v 1 0 - d.QQ v 1 0 * d.QQ u 0 1) =
      d.QQ u 1 1 * d.QQ v 0 0 - d.QQ v 1 1 * d.QQ u 0 0 := fun u v => rtt_ent d hS u v 0 1 1 0
  refine ext_right hd fun ρ => ?_
  have eT : d.L.ζ * d.L.ζb - d.L.GG = algebraMap ℂ A d.L.TT := by rw [d.L.GG_def]; abel
  have key : ∀ u v : ℂ, (u - v) * M.xC P ρ u * M.xC P ρ v ≠ 0 →
      d.L.GG * d.L.GG * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * Pj d.κ ρ + (1 + u + v) • (d.L.TT • Pj d.κ ρ) =
        ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) • Pj d.κ ρ + (1 + u + v) • ((P.TT : ℂ) • Pj d.κ ρ) := by
    intro u v hc
    have e := diag_id hd hND hR ρ u v
    have e1 : ((u - v) * M.xC P ρ u * M.xC P ρ v) • ((d.L.GG * d.L.GG * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) +
        (1 + u + v) • (d.L.ζ * d.L.ζb - d.L.GG)) * Pj d.κ ρ) = ((u - v) * M.xC P ρ u * M.xC P ρ v) •
        ((((2 * M.aC P ρ * P.TT : ℝ) : ℂ) + (1 + u + v) * (P.TT : ℂ)) • Pj d.κ ρ) := by
      rw [e, model_scalar P hP ρ u v]; exact mul_smul _ _ _
    have e2 := smul_right_injective A hc e1
    rw [eT, add_mul, smul_mul_assoc, ← Algebra.smul_def] at e2
    rw [e2, add_smul, mul_smul]
  have k1 := key (1 * Complex.I) (2 * Complex.I) (by exact_mod_cast cI_ne ρ 1 2 (by norm_num) (by norm_num) (by norm_num))
  have k2 := key (2 * Complex.I) (3 * Complex.I) (by exact_mod_cast cI_ne ρ 2 3 (by norm_num) (by norm_num) (by norm_num))
  have e3 : (2 * Complex.I) • (d.L.TT • Pj d.κ ρ - (P.TT : ℂ) • Pj d.κ ρ) = 0 := by
    linear_combination (norm := module) k2 - k1
  have hX : d.L.TT • Pj d.κ ρ = (P.TT : ℂ) • Pj d.κ ρ := by
    rcases smul_eq_zero.1 e3 with h | h
    · exact absurd h (mul_ne_zero two_ne_zero Complex.I_ne_zero)
    · exact sub_eq_zero.1 h
  have hK : d.L.GG * d.L.GG * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * Pj d.κ ρ =
      ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) • Pj d.κ ρ := by
    linear_combination (norm := module) k1 - (1 + 1 * Complex.I + 2 * Complex.I) • hX
  have inv : d.L.GGi * d.L.GGi * (d.L.GG * d.L.GG) = 1 := by
    rw [mul_assoc, ← mul_assoc d.L.GGi d.L.GG, d.L.GGi_GG, one_mul, d.L.GGi_GG]
  rw [show (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * Pj d.κ ρ =
      d.L.GGi * d.L.GGi * (d.L.GG * d.L.GG * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * Pj d.κ ρ) by
    rw [← mul_assoc, ← mul_assoc, inv, one_mul], hK]
  have r1 : (d.κ fun ρ => ((2 * M.aC P ρ * P.TT : ℝ) : ℂ)) * d.L.GGi * d.L.GGi * Pj d.κ ρ =
      d.L.GGi * d.L.GGi * ((d.κ fun ρ => ((2 * M.aC P ρ * P.TT : ℝ) : ℂ)) * Pj d.κ ρ) := by
    rw [(kc_GGi hd _).eq, mul_assoc d.L.GGi, (kc_GGi hd _).eq]; simp only [mul_assoc]
  rw [r1, kap_Pj]

end

end Formalism.FourierDecayAlt.P.NFx4.SX

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Introduce `P A _ _ _ d hP _ hRel hS`. Establish `hd` using `NFx4.SX.hyp_of_rel d hRel`. Establish `hND` using `fun l (hl : l ∈ Finset.Icc 1 (P.k - 1)) => NFx4.SX.ssDown hd hP hS hl`. Conclude with `⟨NFx4.SX.curv hd hP hS hND, fun l hl => ⟨hND l hl, fun j hj hjl => ⟨NFx4.SX.ssComm hd hP hS hl hj hjl, NFx4.SX.ssMixed hd hP hS hl hj hjl⟩⟩⟩`.
-/
theorem shift_extra : Formalism.FourierDecayAlt.NF.SExtra := by
  intro P A _ _ _ d hP _ hRel hS
  have hd := NFx4.SX.hyp_of_rel d hRel
  have hND := fun l (hl : l ∈ Finset.Icc 1 (P.k - 1)) => NFx4.SX.ssDown hd hP hS hl
  exact ⟨NFx4.SX.curv hd hP hS hND, fun l hl => ⟨hND l hl, fun j hj hjl =>
    ⟨NFx4.SX.ssComm hd hP hS hl hj hjl, NFx4.SX.ssMixed hd hP hS hl hj hjl⟩⟩⟩

end Formalism.FourierDecayAlt.P

end

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `normal_form_order_zero_of_parts multiplication_zeta_exists actual_zeta_smooth_alt`.
-/
theorem normal_form_order_zero : Formalism.FourierDecayAlt.NF.NFOrder0 :=
  normal_form_order_zero_of_parts multiplication_zeta_exists actual_zeta_smooth_alt

end Formalism.FourierDecayAlt.P
