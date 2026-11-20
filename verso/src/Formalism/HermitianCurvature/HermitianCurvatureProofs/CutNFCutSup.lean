import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtw

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Filter Topology

noncomputable section

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [xD]`. Establish `h : (fun y => φ (y / ε)) = fun y => φ (ε⁻¹ * y)`. Use function extensionality and compare the values at `y`. Rewrite using `[div_eq_inv_mul]`.

Rewrite using `[h, deriv_comp_mul_left, smul_eq_mul, div_eq_inv_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem xD_dil (φ : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    xD (fun y => φ (y / ε)) = fun x => xD φ (x / ε) := by
  funext x
  simp only [xD]
  have h : (fun y => φ (y / ε)) = fun y => φ (ε⁻¹ * y) := by
    funext y
    rw [div_eq_inv_mul]
  rw [h, deriv_comp_mul_left, smul_eq_mul, div_eq_inv_mul]
  ring

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => rfl`. Consider the case `succ q ih`. Rewrite using `[Function.iterate_succ_apply', ih, xD_dil _ hε]`. Use function extensionality and compare the values at `x`.

Rewrite using `[Function.iterate_succ_apply']`.
-/
theorem xD_iter_dil (φ : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    xD^[q] (fun y => φ (y / ε)) = fun x => (xD^[q] φ) (x / ε) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply', ih, xD_dil _ hε]
    funext x
    rw [Function.iterate_succ_apply']

/- English proof (translation)
Establish `hd` using `(contDiff_infty_iff_deriv.mp hφ).2`. Conclude with `contDiff_id.mul hd`.
-/
theorem xD_contDiff {φ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD φ) := by
  have hd := (contDiff_infty_iff_deriv.mp hφ).2
  exact contDiff_id.mul hd

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => simpa using hφ`. Consider the case `succ q ih`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `xD_contDiff ih`.
-/
theorem xD_iter_contDiff {φ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (q : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD^[q] φ) := by
  induction q with
  | zero => simpa using hφ
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    exact xD_contDiff ih

/- English proof (translation)
Introduce `y hy`. Establish `h : φ =ᶠ[nhds y] fun _ => c` using `Filter.eventually_of_mem (hU.mem_nhds hy) hφ`. Use `show y * deriv φ y = 0`. Rewrite using `[h.deriv_eq]`. Simplify using the standard rewrite rules.
-/
theorem xD_zero_of_const {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (c : ℝ) (hφ : ∀ y ∈ U, φ y = c) :
    ∀ y ∈ U, xD φ y = 0 := by
  intro y hy
  have h : φ =ᶠ[nhds y] fun _ => c := Filter.eventually_of_mem (hU.mem_nhds hy) hφ
  show y * deriv φ y = 0
  rw [h.deriv_eq]
  simp

/- English proof (translation)
Introduce `q`. Proceed by induction on `q with`. Consider the case `zero => intro y hy`. Simplify using `using hφ y hy`. Consider the case `succ q ih`.

Introduce `y hy`. Rewrite using `[Function.iterate_succ_apply']`. Simplify using `only [Nat.succ_ne_zero, if_false]`. Conclude with `xD_zero_of_const hU _ ih y hy`.
-/
private theorem xD_iterate_eq_ite_of_const_on_open {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (c : ℝ)
    (hφ : ∀ y ∈ U, φ y = c) : ∀ q : ℕ, ∀ y ∈ U, (xD^[q] φ) y = if q = 0 then c else 0 := by
  intro q
  induction q with
  | zero => intro y hy; simpa using hφ y hy
  | succ q ih =>
    intro y hy
    rw [Function.iterate_succ_apply']
    simp only [Nat.succ_ne_zero, if_false]
    exact xD_zero_of_const hU _ ih y hy

/- English proof (translation)
Unfold `NFCutSup`. Introduce `χ hχ q`. Take `⟨hs, -, h1⟩` from `hχ`. Establish `hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD^[q] χ)` using `xD_iter_contDiff hs q`. Take `⟨K0, hK0⟩` from `(isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuous.continuousOn`.

Use `⟨max K0 1, fun ε hε x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[xD_iter_dil χ hε q]`. Use `show |(xD^[q] χ) (x / ε)| ≤ max K0 1`. Establish `hy : 0 < x / ε` using `div_pos hx hε`. Break down `le_or_gt (x / ε) 1 with hy1 | hy1` into its components or cases.

Establish `hb` using `hK0 (x / ε) ⟨hy.le, hy1⟩`. Rewrite `hb` using `[Real.norm_eq_abs]`. Conclude with `hb.trans (le_max_left _ _)`. Rewrite using `[xD_iterate_eq_ite_of_const_on_open isOpen_Ioi 1 (fun z hz => h1 z (le_of_lt hz)) q (x / ε) hy1]`. Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem truncated_supremum_bound_holds : NFCutSup := by
  unfold NFCutSup
  intro χ hχ q
  obtain ⟨hs, -, h1⟩ := hχ
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD^[q] χ) := xD_iter_contDiff hs q
  obtain ⟨K0, hK0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuous.continuousOn
  refine ⟨max K0 1, fun ε hε x hx => ?_⟩
  rw [xD_iter_dil χ hε q]
  show |(xD^[q] χ) (x / ε)| ≤ max K0 1
  have hy : 0 < x / ε := div_pos hx hε
  rcases le_or_gt (x / ε) 1 with hy1 | hy1
  · have hb := hK0 (x / ε) ⟨hy.le, hy1⟩
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (le_max_left _ _)
  · rw [xD_iterate_eq_ite_of_const_on_open isOpen_Ioi 1 (fun z hz => h1 z (le_of_lt hz)) q (x / ε) hy1]
    refine le_trans ?_ (le_max_right _ _)
    split_ifs <;> simp

end

end Formalism.FourierDecayAlt.P.CutBP
