import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalBound
import GroundTheory.AutomorphicForms.GL2.GJGlobalEntire

open MeasureTheory Set Filter NumberField ComplexConjugate Asymptotics
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction AutomorphicForm RightCosetSpace GJMatrix

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Rewrite using `[continuousOn_iff_continuous_domRestrict]`. Establish `e : (Ioi (0 : ℝ)).domRestrict (fun t : ℝ => if h : 0 < t then f ⟨t, h⟩ else 0) = fun t : Ioi (0 : ℝ) => f ⟨t.1, t.2⟩`. Use function extensionality and compare the values at `t`. Rewrite using `[Set.domRestrict_apply, dif_pos (show (0 : ℝ) < t.1 from t.2)]`. Rewrite using `[e]`.

Conclude with `hf.comp (continuous_subtype_val.subtype_mk _)`.
-/
theorem continuousOn_dite {f : {r : ℝ // 0 < r} → ℂ} (hf : Continuous f) :
    ContinuousOn (fun t : ℝ => if h : 0 < t then f ⟨t, h⟩ else 0) (Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have e : (Ioi (0 : ℝ)).domRestrict (fun t : ℝ => if h : 0 < t then f ⟨t, h⟩ else 0) =
      fun t : Ioi (0 : ℝ) => f ⟨t.1, t.2⟩ := by
    funext t
    rw [Set.domRestrict_apply, dif_pos (show (0 : ℝ) < t.1 from t.2)]
  rw [e]
  exact hf.comp (continuous_subtype_val.subtype_mk _)

/- English proof (translation)
Unfold `MellinConvergent`. Establish `hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • J t) (Ioi 0)`. Use `ContinuousOn.smul (f := fun t : ℝ => (t : ℂ) ^ (w - 1)) (g := J) (fun t ht => ?_) hJ` and prove the remaining obligations. Conclude with `(Complex.continuousAt_ofReal_cpow_const t (w - 1) (Or.inr (ne_of_gt (show (0 : ℝ) < t from ht)))).continuousWithinAt`. Use `Integrable.mono' (hint.const_mul V) (hc.aestronglyMeasurable measurableSet_Ioi) ?_` and prove the remaining obligations.

Use `(ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)` and prove the remaining obligations. Rewrite using `[norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mellinConvergent_of_bound {J : ℝ → ℂ} (hJ : ContinuousOn J (Ioi 0)) {B : ℝ → ℝ} {V : ℝ}
    (hB : ∀ t : ℝ, 0 < t → ‖J t‖ ≤ V * B t) {w : ℂ}
    (hint : IntegrableOn (fun t : ℝ => t ^ (w.re - 1) * B t) (Ioi 0)) :
    MellinConvergent J w := by
  unfold MellinConvergent
  have hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • J t) (Ioi 0) := by
    refine ContinuousOn.smul (f := fun t : ℝ => (t : ℂ) ^ (w - 1)) (g := J) (fun t ht => ?_) hJ
    exact (Complex.continuousAt_ofReal_cpow_const t (w - 1)
      (Or.inr (ne_of_gt (show (0 : ℝ) < t from ht)))).continuousWithinAt
  refine Integrable.mono' (hint.const_mul V) (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  calc t ^ (w.re - 1) * ‖J t‖ ≤ t ^ (w.re - 1) * (V * B t) :=
        mul_le_mul_of_nonneg_left (hB t ht) (Real.rpow_nonneg ht.le _)
    _ = V * (t ^ (w.re - 1) * B t) := by ring

/- English proof (translation)
Establish `h : Continuous fun s : {r : ℝ // 0 < r} => ((s : ℝ))⁻¹` using `continuous_subtype_val.inv₀ fun s => s.2.ne'`. Conclude with `h.subtype_mk _`.
-/
theorem continuous_posInv : Continuous fun s : {r : ℝ // 0 < r} => s⁻¹ := by
  have h : Continuous fun s : {r : ℝ // 0 < r} => ((s : ℝ))⁻¹ :=
    continuous_subtype_val.inv₀ fun s => s.2.ne'
  exact h.subtype_mk _

/- English proof (translation)
Establish `hc` using `continuous_tsum_GL hΦ`. Establish `hm : Continuous fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n => (p.1⁻¹, p.2.2⁻¹, p.2.1⁻¹)` using `(continuous_posInv.comp continuous_fst).prodMk ((continuous_snd.comp continuous_snd).inv.prodMk (continuous_fst.comp continuous_snd).inv)`. Establish `h` using `hc.comp hm`. Use `h.congr fun p => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`.

Rewrite using `[← (Equiv.inv (GL (Fin n) K)).tsum_eq]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Establish `e` using `inv_centralSection_mul p.1 p.2.1⁻¹ p.2.2 γ`. Rewrite `e` using `[inv_inv]`. Simplify using `only [Equiv.inv_apply]`.

Rewrite using `[e]`.
-/
theorem continuous_tsum_inv {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) :
    Continuous (fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ∑' γ : GL (Fin n) K, Φ (((centralSection K n p.1 * p.2.1 * AdelicGLn.diagonal K n γ *
        p.2.2)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  have hc := continuous_tsum_GL hΦ
  have hm : Continuous fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      (p.1⁻¹, p.2.2⁻¹, p.2.1⁻¹) :=
    (continuous_posInv.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_snd).inv.prodMk (continuous_fst.comp continuous_snd).inv)
  have h := hc.comp hm
  refine h.congr fun p => ?_
  simp only [Function.comp_apply]
  rw [← (Equiv.inv (GL (Fin n) K)).tsum_eq]
  refine tsum_congr fun γ => ?_
  have e := inv_centralSection_mul p.1 p.2.1⁻¹ p.2.2 γ
  rw [inv_inv] at e
  simp only [Equiv.inv_apply]
  rw [e]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `hn0 : 0 < n` using `by omega`. Establish `hΦh` using `adelicMatrixFourier_mem hΦ`. Establish `hΦc : Continuous Φ` using `continuous_of_mem_matrixSchwartzBruhat hΦ`. Establish `hΦhc : Continuous (adelicMatrixFourier K Φ)` using `continuous_of_mem_matrixSchwartzBruhat hΦh`. Establish `h₁c : Continuous φ₁` using `h₁.1.continuous`.

Establish `h₂c : Continuous φ₂` using `h₂.1.continuous`. Use `set V : ℝ := (μ (fundamentalDomain (rationalGLOne K n))).toReal ^ 2 with hV`. Use `set Ξ₁ : AdelicGLn.AdelicGL K n → ℂ := fun g => Φ (g : Matrix (Fin n) (Fin n) 𝔸[K]) with hΞ₁`. Use `set Ξ₂ : AdelicGLn.AdelicGL K n → ℂ := fun g => adelicMatrixFourier K Φ ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) with hΞ₂`. Establish `hΞ₁c : Continuous Ξ₁` using `hΦc.comp Units.continuous_val`.

Establish `hΞ₂c : Continuous Ξ₂` using `hΦhc.comp (Units.continuous_val.comp continuous_inv)`. Use `set J₁ : ℝ → ℂ := fun t => if h : 0 < t then thetaPairing μ φ₁ φ₂ Ξ₁ ⟨t, h⟩ else 0 with hJ₁`. Use `set J₂ : ℝ → ℂ := fun t => if h : 0 < t then thetaPairing μ φ₁ φ₂ Ξ₂ ⟨t, h⟩ else 0 with hJ₂`. Use `set J' : ℝ → ℂ := fun u => J₂ u⁻¹ with hJ'`. Take `⟨C₁, M₁, -, hC₁⟩` from `exists_bound_tsum hΦ h₁ h₂`.

Take `⟨C₂, M₂, -, hC₂⟩` from `exists_bound_tsum hΦh h₂ h₁`. Take `⟨_, _, _, hsum₂⟩` from `exists_bound_GL_inv hn0 hΦ h₁ h₂ 0`. Establish `hB₁ : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n), ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ * ‖∑' γ : GL (Fin n) K, Ξ₁ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤ C₁ * (max 1 …`. Introduce `t x y`. Take `⟨hs, hb⟩` from `hC₁ x x.2 y y.2 t`.

Establish `hGL` using `tsum_norm_GL_le _ _ hs`. Use `le_trans ?_ hb` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))` and prove the remaining obligations. Simplify using `only [hΞ₁, coe_mul_diagonal_mul]`. Conclude with `(norm_tsum_le_tsum_norm hGL.1).trans hGL.2`.

Establish `hB₂ : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n), ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ * ‖∑' γ : GL (Fin n) K, Ξ₂ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤ C₂ * (max 1 …`. Introduce `t x y`. Take `⟨hs, hb⟩` from `hC₂ y y.2 x x.2 t⁻¹`. Establish `hGL` using `tsum_norm_GL_le _ _ hs`. Establish `hsm` using `(hsum₂ t x y).1`.

Rewrite using `[mul_comm ‖φ₂ _‖]`. Establish `e : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹ = (t : ℝ)` using `inv_inv (t : ℝ)`. Rewrite `hb` using `[e]`. Use `le_trans ?_ hb` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))` and prove the remaining obligations.

Use `(norm_tsum_le_tsum_norm hsm).trans ?_` and prove the remaining obligations. Rewrite using `[tsum_norm_inv_eq]`. Conclude with `hGL.2`. Establish `hB₁c : Continuous fun t : {r : ℝ // 0 < r} => C₁ * (max 1 (t : ℝ)⁻¹) ^ M₁` using `continuous_const.mul ((continuous_const.max (continuous_subtype_val.inv₀ fun t => t.2.ne')).rpow_const fun t => Or.inl (ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _))))`. Establish `hB₂c : Continuous fun t : {r : ℝ // 0 < r} => C₂ * (max 1 (t : ℝ)) ^ M₂` using `continuous_const.mul ((continuous_const.max continuous_subtype_val).rpow_const fun t => Or.inl (ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _))))`.

Establish `hTP₁c : Continuous (thetaPairing μ φ₁ φ₂ Ξ₁)` using `continuous_thetaPairing μ h₁c h₂c (continuous_tsum_GL hΦ) hB₁c hB₁`. Establish `hTP₂c : Continuous (thetaPairing μ φ₁ φ₂ Ξ₂)` using `continuous_thetaPairing μ h₁c h₂c (continuous_tsum_inv hΦh) hB₂c hB₂`. Establish `hJ₁c : ContinuousOn J₁ (Ioi 0)` using `continuousOn_dite hTP₁c`. Establish `hJ₂c : ContinuousOn J₂ (Ioi 0)` using `continuousOn_dite hTP₂c`. Establish `hJ'c : ContinuousOn J' (Ioi 0)` using `hJ₂c.comp (continuousOn_inv₀.mono fun t (ht : 0 < t) => ht.ne') fun t (ht : 0 < t) => (show (0 : ℝ) < t⁻¹ from inv_pos.2 ht)`.

Establish `hsym : ∀ t : ℝ, 0 < t → J₁ t = (t : ℂ) ^ (-((n : ℝ) : ℂ)) * J' t⁻¹`. Introduce `t ht`. Establish `hti : (0 : ℝ) < t⁻¹⁻¹` using `by rw [inv_inv]; exact ht`. Simplify using `only [hJ₁, hJ', hJ₂, dif_pos ht, dif_pos hti]`. Establish `e : (⟨t⁻¹⁻¹, hti⟩ : {r : ℝ // 0 < r}) = ⟨t, ht⟩` using `Subtype.ext (inv_inv t)`.

Rewrite using `[e, thetaPairing_eq μ hn h₁ h₂ hΦ ⟨t, ht⟩]`. Use `congr 1`. Rewrite using `[Complex.ofReal_natCast, Complex.cpow_neg, Complex.cpow_natCast]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hdec₁ : ∀ a : ℝ, J₁ =O[atTop] (· ^ (-a))`. Introduce `a`. Take `⟨C, M, D, hb⟩` from `exists_bound_GL hn0 hΦ h₁ h₂ a`. Use `IsBigO.of_bound (V * D) ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht`.

Establish `ht0 : 0 < t` using `lt_of_lt_of_le one_pos ht`. Simplify using `only [hJ₁, dif_pos ht0]`. Establish `h` using `norm_thetaPairing_le μ (Ξ := Ξ₁) (φ₁ := φ₁) (φ₂ := φ₂) ⟨t, ht0⟩ (b := D * t ^ (-a)) fun x y => by`. Use `hb ⟨t, ht0⟩ x y` as an intermediate fact. Rewrite `this` using `[if_neg (not_lt.2 ht)]`.

Conclude with `this`. Rewrite using `[Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hdec' : ∀ a : ℝ, J' =O[atTop] (· ^ (-a))`. Introduce `a`.

Take `⟨C, M, D, hb⟩` from `exists_bound_GL_inv hn0 hΦ h₁ h₂ a`. Use `IsBigO.of_bound (V * D) ?_` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu`. Establish `hu0 : 0 < u` using `lt_trans one_pos hu`. Establish `hi0 : 0 < u⁻¹` using `inv_pos.2 hu0`.

Establish `hi1 : u⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hu`. Simplify using `only [hJ', hJ₂, dif_pos hi0]`. Establish `h` using `norm_thetaPairing_le μ (Ξ := Ξ₂) (φ₁ := φ₁) (φ₂ := φ₂) ⟨u⁻¹, hi0⟩ (b := D * (u⁻¹) ^ a) fun x y => by`. Use `hb ⟨u⁻¹, hi0⟩ x y` as an intermediate fact. Rewrite `this` using `[if_pos hi1]`.

Conclude with `this`. Rewrite using `[Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hu0 _)]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨Λw, Λw', hΛ, hΛ', hΛeq, hΛ'eq, hfe⟩` from `exists_entire_of_symm (κ := (n : ℝ)) hJ₁c hJ'c hsym hdec₁ hdec'`. Take `⟨c, -, hK⟩` from `exists_integral_eq_mellin_thetaPairing μ hn0 ν`.

Take `⟨C₁', M₁', D₀, hb₁₀⟩` from `exists_bound_GL hn0 hΦ h₁ h₂ 0`. Take `⟨C₂', M₂', D₀', hb₂₀⟩` from `exists_bound_GL_inv hn0 hΦ h₁ h₂ 0`. Use `set w₀ : ℂ := ((n : ℂ) - 1) / 2 with hw₀`. Use `⟨max (max M₁' 0) (max M₂' 0) - ((n : ℝ) - 1) / 2, fun s => (c : ℂ) * Λw (s + w₀), fun s => (c : ℂ) * Λw' (s + w₀), (hΛ.comp (differentiable_id.add_const _)).const_mul _, (hΛ'.comp (differentiable_id.add_const _)).const_mul _, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`.

Use `set σ : ℝ := (s + w₀).re with hσ`. Establish `hσre : σ = s.re + ((n : ℝ) - 1) / 2`. Rewrite using `[hσ, Complex.add_re, hw₀]`. Simplify using the standard rewrite rules. Establish `hσM : max M₁' 0 < σ`.

Use `le_max_left (max M₁' 0) (max M₂' 0)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨C, M, D, hb⟩` from `exists_bound_GL hn0 hΦ h₁ h₂ (σ + 1)`. Use `set B : ℝ → ℝ := fun t => if t < 1 then C₁' * t ^ (-max M₁' 0) else D * t ^ (-(σ + 1)) with hBdef`. Establish `hbB : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n), Summable (fun γ : GL (Fin n) K => ‖Ξ₁ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖) ∧ ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ …`.

Introduce `t x y`. Use `⟨(hb t x y).1, ?_⟩` and prove the remaining obligations. Distinguish the cases in `ht : (t : ℝ) < 1`. Use `(hb₁₀ t x y).2` as an intermediate fact. Rewrite `this` using `[if_pos ht]`.

Simplify using `only [hBdef, if_pos ht]`. Conclude with `this`. Use `(hb t x y).2` as an intermediate fact. Rewrite `this` using `[if_neg ht]`. Simplify using `only [hBdef, if_neg ht]`.

Conclude with `this`. Establish `hint : IntegrableOn (fun t : ℝ => t ^ ((s + w₀).re - 1) * B t) (Ioi 0)` using `integrableOn_rpow_mul_ite (by linarith) (by linarith)`. Take `⟨hI, hEq⟩` from `hK φ₁ φ₂ Ξ₁ (s + w₀) B h₁c h₂c hΞ₁c h₁.1.isLeftInvariant hA (fun t x y hx hy => hbB t ⟨x, hx⟩ ⟨y, hy⟩) hint`. Use `⟨hI, ?_⟩` and prove the remaining obligations. Establish `hconv : MellinConvergent J₁ (s + w₀)`.

Use `mellinConvergent_of_bound hJ₁c (V := V) (fun t ht => ?_) hint` and prove the remaining obligations. Simplify using `only [hJ₁, dif_pos ht]`. Conclude with `norm_thetaPairing_le μ ⟨t, ht⟩ fun x y => hbB ⟨t, ht⟩ x y`. Use `show ∫ g, Ξ₁ g * matrixCoeff μ φ₁ φ₂ g * detPow g (s + w₀) ∂ν = (c : ℂ) * Λw (s + w₀)`. Rewrite using `[hEq]`.

Use `show (c : ℂ) * mellin J₁ (s + w₀) = (c : ℂ) * Λw (s + w₀)`. Rewrite using `[hΛeq _ hconv]`. Introduce `s hs`. Use `set σ : ℝ := (s + w₀).re with hσ`. Establish `hσre : σ = s.re + ((n : ℝ) - 1) / 2`.

Rewrite using `[hσ, Complex.add_re, hw₀]`. Simplify using the standard rewrite rules. Establish `hσM : max M₂' 0 < σ`. Use `le_max_right (max M₁' 0) (max M₂' 0)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨C, M, D, hb⟩` from `exists_bound_GL_inv hn0 hΦ h₁ h₂ (σ + 1)`. Use `set B : ℝ → ℝ := fun t => if t < 1 then D * t ^ (σ + 1) else C₂' * t ^ max M₂' 0 with hBdef`. Establish `hbB : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n), Summable (fun γ : GL (Fin n) K => ‖Ξ₂ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖) ∧ ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ …`. Introduce `t x y`. Use `⟨(hb t x y).1, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `ht : (t : ℝ) < 1`. Use `(hb t x y).2` as an intermediate fact. Rewrite `this` using `[if_pos ht]`. Simplify using `only [hBdef, if_pos ht]`. Conclude with `this`.

Use `(hb₂₀ t x y).2` as an intermediate fact. Rewrite `this` using `[if_neg ht]`. Simplify using `only [hBdef, if_neg ht]`. Conclude with `this`. Establish `hint : IntegrableOn (fun t : ℝ => t ^ ((-(s + w₀)).re - 1) * B t) (Ioi 0)`.

Rewrite using `[Complex.neg_re]`. Conclude with `integrableOn_rpow_mul_ite (by linarith) (by linarith)`. Take `⟨hI, hEq⟩` from `hK φ₁ φ₂ Ξ₂ (-(s + w₀)) B h₁c h₂c hΞ₂c h₁.1.isLeftInvariant hA (fun t x y hx hy => hbB t ⟨x, hx⟩ ⟨y, hy⟩) hint`. Use `isInvInvariant_haar ν hn0` as an intermediate fact. Establish `hfun : zetaIntegrand (adelicMatrixFourier K Φ) (fun g => matrixCoeff μ φ₁ φ₂ g⁻¹) s = fun g => (fun h => Ξ₂ h * matrixCoeff μ φ₁ φ₂ h * detPow h (-(s + w₀))) g⁻¹`.

Use function extensionality and compare the values at `g`. Simplify using `only [zetaIntegrand, hΞ₂, inv_inv, detPow_inv, neg_neg, ← hw₀]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfun]`. Conclude with `hI.comp_inv`.

Establish `hconv2 : MellinConvergent J₂ (-(s + w₀))`. Use `mellinConvergent_of_bound hJ₂c (V := V) (fun t ht => ?_) hint` and prove the remaining obligations. Simplify using `only [hJ₂, dif_pos ht]`. Conclude with `norm_thetaPairing_le μ ⟨t, ht⟩ fun x y => hbB ⟨t, ht⟩ x y`. Establish `hconv : MellinConvergent J' (s + w₀)`.

Establish `h` using `(MellinConvergent.comp_rpow (f := J₂) (s := s + w₀) (a := -1) (by norm_num)).2 (by`. Rewrite using `[show (s + w₀) / ((-1 : ℝ) : ℂ) = -(s + w₀) by push_cast; ring]`. Conclude with `hconv2)`. Unfold `MellinConvergent at h ⊢`. Use `h.congr_fun (fun t _ => ?_) measurableSet_Ioi` and prove the remaining obligations.

Simplify using `only [hJ', Real.rpow_neg_one]`. Use `show ∫ g, zetaIntegrand (adelicMatrixFourier K Φ) (fun g => matrixCoeff μ φ₁ φ₂ g⁻¹) s g ∂ν = (c : ℂ) * Λw' (s + w₀)`. Rewrite using `[hfun, integral_comp_inv ν hn0 (fun h => Ξ₂ h * matrixCoeff μ φ₁ φ₂ h * detPow h (-(s + w₀))), hEq]`. Use `show (c : ℂ) * mellin J₂ (-(s + w₀)) = (c : ℂ) * Λw' (s + w₀)`. Rewrite using `[hΛ'eq _ hconv, hJ', mellin_comp_inv]`.

Introduce `s`. Simplify using `only`. Rewrite using `[hfe]`. Use `congr 2`. Rewrite using `[hw₀]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem globalZeta_entire_functionalEquation (hn : 2 ≤ n) (μ : Measure (normOneGL K n))
    [μ.IsHaarMeasure] (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ} (h₁ : φ₁ ∈ cuspForms K n) (h₂ : φ₂ ∈ cuspForms K n)
    (hA : ∀ (s : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
      φ₁ (centralSection K n s * x) = φ₁ x)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Φ ∈ matrixSchwartzBruhat K n) :
    ∃ σ₀ : ℝ, ∃ Λ Λ' : ℂ → ℂ, Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (∀ s : ℂ, σ₀ < s.re → Integrable (zetaIntegrand Φ (matrixCoeff μ φ₁ φ₂) s) ν ∧
        globalZeta ν Φ (matrixCoeff μ φ₁ φ₂) s = Λ s) ∧
      (∀ s : ℂ, σ₀ < s.re → Integrable (zetaIntegrand (adelicMatrixFourier K Φ)
          (fun g => matrixCoeff μ φ₁ φ₂ g⁻¹) s) ν ∧
        globalZeta ν (adelicMatrixFourier K Φ) (fun g => matrixCoeff μ φ₁ φ₂ g⁻¹) s = Λ' s) ∧
      ∀ s : ℂ, Λ s = Λ' (1 - s) := by
  have hn0 : 0 < n := by omega
  have hΦh := adelicMatrixFourier_mem hΦ
  have hΦc : Continuous Φ := continuous_of_mem_matrixSchwartzBruhat hΦ
  have hΦhc : Continuous (adelicMatrixFourier K Φ) := continuous_of_mem_matrixSchwartzBruhat hΦh
  have h₁c : Continuous φ₁ := h₁.1.continuous
  have h₂c : Continuous φ₂ := h₂.1.continuous
  set V : ℝ := (μ (fundamentalDomain (rationalGLOne K n))).toReal ^ 2 with hV

  set Ξ₁ : AdelicGLn.AdelicGL K n → ℂ := fun g => Φ (g : Matrix (Fin n) (Fin n) 𝔸[K]) with hΞ₁
  set Ξ₂ : AdelicGLn.AdelicGL K n → ℂ := fun g => adelicMatrixFourier K Φ
    ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) with hΞ₂
  have hΞ₁c : Continuous Ξ₁ := hΦc.comp Units.continuous_val
  have hΞ₂c : Continuous Ξ₂ := hΦhc.comp (Units.continuous_val.comp continuous_inv)
  set J₁ : ℝ → ℂ := fun t => if h : 0 < t then thetaPairing μ φ₁ φ₂ Ξ₁ ⟨t, h⟩ else 0 with hJ₁
  set J₂ : ℝ → ℂ := fun t => if h : 0 < t then thetaPairing μ φ₁ φ₂ Ξ₂ ⟨t, h⟩ else 0 with hJ₂
  set J' : ℝ → ℂ := fun u => J₂ u⁻¹ with hJ'

  obtain ⟨C₁, M₁, -, hC₁⟩ := exists_bound_tsum hΦ h₁ h₂
  obtain ⟨C₂, M₂, -, hC₂⟩ := exists_bound_tsum hΦh h₂ h₁
  obtain ⟨_, _, _, hsum₂⟩ := exists_bound_GL_inv hn0 hΦ h₁ h₂ 0
  have hB₁ : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
        ‖∑' γ : GL (Fin n) K, Ξ₁ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤
        C₁ * (max 1 (t : ℝ)⁻¹) ^ M₁ := by
    intro t x y
    obtain ⟨hs, hb⟩ := hC₁ x x.2 y y.2 t
    have hGL := tsum_norm_GL_le _ _ hs
    refine le_trans ?_ hb
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simp only [hΞ₁, coe_mul_diagonal_mul]
    exact (norm_tsum_le_tsum_norm hGL.1).trans hGL.2
  have hB₂ : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
        ‖∑' γ : GL (Fin n) K, Ξ₂ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤
        C₂ * (max 1 (t : ℝ)) ^ M₂ := by
    intro t x y
    obtain ⟨hs, hb⟩ := hC₂ y y.2 x x.2 t⁻¹
    have hGL := tsum_norm_GL_le _ _ hs
    have hsm := (hsum₂ t x y).1
    rw [mul_comm ‖φ₂ _‖]
    have e : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹ = (t : ℝ) := inv_inv (t : ℝ)
    rw [e] at hb
    refine le_trans ?_ hb
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    refine (norm_tsum_le_tsum_norm hsm).trans ?_
    rw [tsum_norm_inv_eq]
    exact hGL.2
  have hB₁c : Continuous fun t : {r : ℝ // 0 < r} => C₁ * (max 1 (t : ℝ)⁻¹) ^ M₁ :=
    continuous_const.mul ((continuous_const.max (continuous_subtype_val.inv₀ fun t => t.2.ne')).rpow_const
      fun t => Or.inl (ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _))))
  have hB₂c : Continuous fun t : {r : ℝ // 0 < r} => C₂ * (max 1 (t : ℝ)) ^ M₂ :=
    continuous_const.mul ((continuous_const.max continuous_subtype_val).rpow_const
      fun t => Or.inl (ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _))))
  have hTP₁c : Continuous (thetaPairing μ φ₁ φ₂ Ξ₁) :=
    continuous_thetaPairing μ h₁c h₂c (continuous_tsum_GL hΦ) hB₁c hB₁
  have hTP₂c : Continuous (thetaPairing μ φ₁ φ₂ Ξ₂) :=
    continuous_thetaPairing μ h₁c h₂c (continuous_tsum_inv hΦh) hB₂c hB₂
  have hJ₁c : ContinuousOn J₁ (Ioi 0) := continuousOn_dite hTP₁c
  have hJ₂c : ContinuousOn J₂ (Ioi 0) := continuousOn_dite hTP₂c
  have hJ'c : ContinuousOn J' (Ioi 0) :=
    hJ₂c.comp (continuousOn_inv₀.mono fun t (ht : 0 < t) => ht.ne') fun t (ht : 0 < t) =>
      (show (0 : ℝ) < t⁻¹ from inv_pos.2 ht)

  have hsym : ∀ t : ℝ, 0 < t → J₁ t = (t : ℂ) ^ (-((n : ℝ) : ℂ)) * J' t⁻¹ := by
    intro t ht
    have hti : (0 : ℝ) < t⁻¹⁻¹ := by rw [inv_inv]; exact ht
    simp only [hJ₁, hJ', hJ₂, dif_pos ht, dif_pos hti]
    have e : (⟨t⁻¹⁻¹, hti⟩ : {r : ℝ // 0 < r}) = ⟨t, ht⟩ := Subtype.ext (inv_inv t)
    rw [e, thetaPairing_eq μ hn h₁ h₂ hΦ ⟨t, ht⟩]
    congr 1
    rw [Complex.ofReal_natCast, Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    rfl

  have hdec₁ : ∀ a : ℝ, J₁ =O[atTop] (· ^ (-a)) := by
    intro a
    obtain ⟨C, M, D, hb⟩ := exists_bound_GL hn0 hΦ h₁ h₂ a
    refine IsBigO.of_bound (V * D) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    simp only [hJ₁, dif_pos ht0]
    have h := norm_thetaPairing_le μ (Ξ := Ξ₁) (φ₁ := φ₁) (φ₂ := φ₂) ⟨t, ht0⟩
      (b := D * t ^ (-a)) fun x y => by
        have := hb ⟨t, ht0⟩ x y
        rw [if_neg (not_lt.2 ht)] at this
        exact this
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    calc _ ≤ V * (D * t ^ (-a)) := h
      _ = V * D * t ^ (-a) := by ring
  have hdec' : ∀ a : ℝ, J' =O[atTop] (· ^ (-a)) := by
    intro a
    obtain ⟨C, M, D, hb⟩ := exists_bound_GL_inv hn0 hΦ h₁ h₂ a
    refine IsBigO.of_bound (V * D) ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    have hu0 : 0 < u := lt_trans one_pos hu
    have hi0 : 0 < u⁻¹ := inv_pos.2 hu0
    have hi1 : u⁻¹ < 1 := inv_lt_one_of_one_lt₀ hu
    simp only [hJ', hJ₂, dif_pos hi0]
    have h := norm_thetaPairing_le μ (Ξ := Ξ₂) (φ₁ := φ₁) (φ₂ := φ₂) ⟨u⁻¹, hi0⟩
      (b := D * (u⁻¹) ^ a) fun x y => by
        have := hb ⟨u⁻¹, hi0⟩ x y
        rw [if_pos hi1] at this
        exact this
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hu0 _)]
    calc _ ≤ V * (D * (u⁻¹) ^ a) := h
      _ = V * D * u ^ (-a) := by rw [Real.inv_rpow hu0.le, Real.rpow_neg hu0.le]; ring
  obtain ⟨Λw, Λw', hΛ, hΛ', hΛeq, hΛ'eq, hfe⟩ :=
    exists_entire_of_symm (κ := (n : ℝ)) hJ₁c hJ'c hsym hdec₁ hdec'

  obtain ⟨c, -, hK⟩ := exists_integral_eq_mellin_thetaPairing μ hn0 ν
  obtain ⟨C₁', M₁', D₀, hb₁₀⟩ := exists_bound_GL hn0 hΦ h₁ h₂ 0
  obtain ⟨C₂', M₂', D₀', hb₂₀⟩ := exists_bound_GL_inv hn0 hΦ h₁ h₂ 0
  set w₀ : ℂ := ((n : ℂ) - 1) / 2 with hw₀
  refine ⟨max (max M₁' 0) (max M₂' 0) - ((n : ℝ) - 1) / 2,
    fun s => (c : ℂ) * Λw (s + w₀), fun s => (c : ℂ) * Λw' (s + w₀),
    (hΛ.comp (differentiable_id.add_const _)).const_mul _,
    (hΛ'.comp (differentiable_id.add_const _)).const_mul _, ?_, ?_, ?_⟩
  ·
    intro s hs
    set σ : ℝ := (s + w₀).re with hσ
    have hσre : σ = s.re + ((n : ℝ) - 1) / 2 := by
      rw [hσ, Complex.add_re, hw₀]
      simp
    have hσM : max M₁' 0 < σ := by
      have := le_max_left (max M₁' 0) (max M₂' 0)
      linarith
    obtain ⟨C, M, D, hb⟩ := exists_bound_GL hn0 hΦ h₁ h₂ (σ + 1)
    set B : ℝ → ℝ := fun t => if t < 1 then C₁' * t ^ (-max M₁' 0) else D * t ^ (-(σ + 1))
      with hBdef
    have hbB : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
        Summable (fun γ : GL (Fin n) K => ‖Ξ₁ (centralSection K n t *
          (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ *
            (y : AdelicGLn.AdelicGL K n))‖) ∧
        ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
          ∑' γ : GL (Fin n) K, ‖Ξ₁ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
            AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤ B t := by
      intro t x y
      refine ⟨(hb t x y).1, ?_⟩
      by_cases ht : (t : ℝ) < 1
      · have := (hb₁₀ t x y).2
        rw [if_pos ht] at this
        simp only [hBdef, if_pos ht]
        exact this
      · have := (hb t x y).2
        rw [if_neg ht] at this
        simp only [hBdef, if_neg ht]
        exact this
    have hint : IntegrableOn (fun t : ℝ => t ^ ((s + w₀).re - 1) * B t) (Ioi 0) :=
      integrableOn_rpow_mul_ite (by linarith) (by linarith)
    obtain ⟨hI, hEq⟩ := hK φ₁ φ₂ Ξ₁ (s + w₀) B h₁c h₂c hΞ₁c h₁.1.isLeftInvariant hA
      (fun t x y hx hy => hbB t ⟨x, hx⟩ ⟨y, hy⟩) hint
    refine ⟨hI, ?_⟩
    have hconv : MellinConvergent J₁ (s + w₀) := by
      refine mellinConvergent_of_bound hJ₁c (V := V) (fun t ht => ?_) hint
      simp only [hJ₁, dif_pos ht]
      exact norm_thetaPairing_le μ ⟨t, ht⟩ fun x y => hbB ⟨t, ht⟩ x y
    show ∫ g, Ξ₁ g * matrixCoeff μ φ₁ φ₂ g * detPow g (s + w₀) ∂ν = (c : ℂ) * Λw (s + w₀)
    rw [hEq]
    show (c : ℂ) * mellin J₁ (s + w₀) = (c : ℂ) * Λw (s + w₀)
    rw [hΛeq _ hconv]
  ·
    intro s hs
    set σ : ℝ := (s + w₀).re with hσ
    have hσre : σ = s.re + ((n : ℝ) - 1) / 2 := by
      rw [hσ, Complex.add_re, hw₀]
      simp
    have hσM : max M₂' 0 < σ := by
      have := le_max_right (max M₁' 0) (max M₂' 0)
      linarith
    obtain ⟨C, M, D, hb⟩ := exists_bound_GL_inv hn0 hΦ h₁ h₂ (σ + 1)
    set B : ℝ → ℝ := fun t => if t < 1 then D * t ^ (σ + 1) else C₂' * t ^ max M₂' 0
      with hBdef
    have hbB : ∀ (t : {r : ℝ // 0 < r}) (x y : normOneGL K n),
        Summable (fun γ : GL (Fin n) K => ‖Ξ₂ (centralSection K n t *
          (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ *
            (y : AdelicGLn.AdelicGL K n))‖) ∧
        ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
          ∑' γ : GL (Fin n) K, ‖Ξ₂ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
            AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤ B t := by
      intro t x y
      refine ⟨(hb t x y).1, ?_⟩
      by_cases ht : (t : ℝ) < 1
      · have := (hb t x y).2
        rw [if_pos ht] at this
        simp only [hBdef, if_pos ht]
        exact this
      · have := (hb₂₀ t x y).2
        rw [if_neg ht] at this
        simp only [hBdef, if_neg ht]
        exact this
    have hint : IntegrableOn (fun t : ℝ => t ^ ((-(s + w₀)).re - 1) * B t) (Ioi 0) := by
      rw [Complex.neg_re]
      exact integrableOn_rpow_mul_ite (by linarith) (by linarith)
    obtain ⟨hI, hEq⟩ := hK φ₁ φ₂ Ξ₂ (-(s + w₀)) B h₁c h₂c hΞ₂c h₁.1.isLeftInvariant hA
      (fun t x y hx hy => hbB t ⟨x, hx⟩ ⟨y, hy⟩) hint
    have := isInvInvariant_haar ν hn0
    have hfun : zetaIntegrand (adelicMatrixFourier K Φ) (fun g => matrixCoeff μ φ₁ φ₂ g⁻¹) s =
        fun g => (fun h => Ξ₂ h * matrixCoeff μ φ₁ φ₂ h * detPow h (-(s + w₀))) g⁻¹ := by
      funext g
      simp only [zetaIntegrand, hΞ₂, inv_inv, detPow_inv, neg_neg, ← hw₀]
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact hI.comp_inv
    · have hconv2 : MellinConvergent J₂ (-(s + w₀)) := by
        refine mellinConvergent_of_bound hJ₂c (V := V) (fun t ht => ?_) hint
        simp only [hJ₂, dif_pos ht]
        exact norm_thetaPairing_le μ ⟨t, ht⟩ fun x y => hbB ⟨t, ht⟩ x y
      have hconv : MellinConvergent J' (s + w₀) := by
        have h := (MellinConvergent.comp_rpow (f := J₂) (s := s + w₀) (a := -1)
          (by norm_num)).2 (by
            rw [show (s + w₀) / ((-1 : ℝ) : ℂ) = -(s + w₀) by push_cast; ring]
            exact hconv2)
        unfold MellinConvergent at h ⊢
        refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
        simp only [hJ', Real.rpow_neg_one]
      show ∫ g, zetaIntegrand (adelicMatrixFourier K Φ) (fun g => matrixCoeff μ φ₁ φ₂ g⁻¹) s g ∂ν =
        (c : ℂ) * Λw' (s + w₀)
      rw [hfun, integral_comp_inv ν hn0 (fun h => Ξ₂ h * matrixCoeff μ φ₁ φ₂ h * detPow h (-(s + w₀))), hEq]
      show (c : ℂ) * mellin J₂ (-(s + w₀)) = (c : ℂ) * Λw' (s + w₀)
      rw [hΛ'eq _ hconv, hJ', mellin_comp_inv]
  · intro s
    simp only
    rw [hfe]
    congr 2
    rw [hw₀]
    push_cast
    ring

end GJGlobal

end

end GroundTheory.Automorphic
