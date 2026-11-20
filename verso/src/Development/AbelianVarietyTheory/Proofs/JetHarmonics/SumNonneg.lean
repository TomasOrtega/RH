import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselDecay

/- English proof (translation)
Conclude with `PI.PolynomialProperness.GN.gN_mul_le a b`.
-/
theorem gN_mul_le' {k r : ℕ} (a b : Mx k r) : B.gN (a * b) ≤ B.gN a * B.gN b := by
  exact PI.PolynomialProperness.GN.gN_mul_le a b

/- English proof (translation)
Conclude with `PI.PolynomialProperness.GN.gN_pos ha`.
-/
theorem gN_pos' {k r : ℕ} {a : Mx k r} (ha : a ∈ GG k r) : 0 < B.gN a := by
  exact PI.PolynomialProperness.GN.gN_pos ha

/- English proof (translation)
Apply `List.sum_nonneg` to reduce the goal to its premises. Introduce `a ha`. Take `⟨w, -, rfl⟩` from `List.mem_map.mp ha`. Conclude with `hf w`.
-/
theorem sum_nonneg' {α : Type} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (L : List α) : 0 ≤ (L.map f).sum := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp ha
  exact hf w

/- English proof (translation)
Establish `h4` using `hg.2.2.2`. Establish `: 0 ≤ AG k r` using `by unfold AG; positivity`. Establish `: 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_aOf {k r : ℕ} {h : ℝ} (hg : GapOK k r h) : 1 ≤ aOf r h := by
  have h4 := hg.2.2.2
  have : 0 ≤ AG k r := by unfold AG; positivity
  have : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith

/- English proof (translation)
Introduce `H k r ε mu h R hR hgap hok v hv`. Establish `hdec : DecInf` using `H.1.2.1`. Establish `ha` using `one_le_aOf hok`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`.

Take `⟨g, hg, v₀, hv₀, rfl⟩` from `hv`. Take `⟨C, Ws, hWs, hb⟩` from `hdec k r ε mu h R.H R.σ hR.1 hR.2 hgap hok v₀ hv₀`. Use `⟨|C| * B.gN g ^ (aOf r h - 1), Ws, hWs, fun w hw x hx => ?_⟩` and prove the remaining obligations. Take `⟨hi, hgi, hig⟩` from `Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hg`. Establish `hy : g⁻¹ * x ∈ GG k r` using `Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hi hx`.

Establish `hx' : x = g * (g⁻¹ * x)` using `by rw [← Matrix.mul_assoc, hgi, Matrix.one_mul]`. Establish `hunit` using `(Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).2`. Establish `hiso : ∀ a b, ⟪R.σ g a, R.σ g b⟫_ℂ = ⟪a, b⟫_ℂ` using `(LinearMap.norm_map_iff_inner_map_map ((R.σ g : R.H →L[ℂ] R.H) : R.H →ₗ[ℂ] R.H)).1 (hunit g hg)`. Establish `e : ⟪R.σ g v₀, R.σ x w⟫_ℂ = ⟪v₀, R.σ (g⁻¹ * x) w⟫_ℂ`. Rewrite using `[← hiso v₀]`.

Use `congr 1`. Use `conv_lhs => rw [hx', Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hR.2 hg hy]`. Both sides reduce to the same expression. Rewrite using `[e]`. Establish `h1` using `hb w hw _ hy`.

Use `set S := (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS`. Establish `hS0 : 0 ≤ S` using `sum_nonneg' _ (fun _ => norm_nonneg _) _`. Establish `pg` using `gN_pos' hg`. Establish `px` using `gN_pos' hx`. Establish `py` using `gN_pos' hy`.

Establish `hle : B.gN x ≤ B.gN g * B.gN (g⁻¹ * x)` using `by conv_lhs => rw [hx']`. Conclude with `gN_mul_le' _ _`. Establish `h2 : (B.gN g * B.gN (g⁻¹ * x)) ^ (1 - aOf r h) ≤ B.gN x ^ (1 - aOf r h)` using `Real.rpow_le_rpow_of_nonpos px hle (by linarith)`. Rewrite `h2` using `[Real.mul_rpow pg.le py.le]`. Establish `h3 : B.gN g ^ (aOf r h - 1) * B.gN g ^ (1 - aOf r h) = 1`.

Rewrite using `[← Real.rpow_add pg]`. Simplify using the standard rewrite rules. Establish `pg' : 0 < B.gN g ^ (aOf r h - 1)` using `Real.rpow_pos_of_pos pg _`. Establish `h4 : B.gN (g⁻¹ * x) ^ (1 - aOf r h) ≤ B.gN g ^ (aOf r h - 1) * B.gN x ^ (1 - aOf r h)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, h3, one_mul]`. Use `_ ≤ _ := mul_le_mul_of_nonneg_left h2 pg'.le`. Combine the equalities or inequalities in the displayed calculation. Consider the case `zero => exact ⟨0, [], by simp, fun w _ x _ => by simp⟩`. Consider the case `add u v _ _ hu hv`.

Take `⟨C, Ws, hWs, hb⟩` from `hu`. Take `⟨C', Ws', hWs', hb'⟩` from `hv`. Use `⟨|C| + |C'|, Ws ++ Ws', fun W hW => (List.mem_append.1 hW).elim (hWs W) (hWs' W), fun w hw x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `hb w hw x hx`. Establish `h2` using `hb' w hw x hx`.

Rewrite using `[List.map_append, List.sum_append, inner_add_left]`. Use `set S := (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS`. Use `set S' := (Ws'.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS'`. Establish `hS0 : 0 ≤ S` using `sum_nonneg' _ (fun _ => norm_nonneg _) _`. Establish `hS0' : 0 ≤ S'` using `sum_nonneg' _ (fun _ => norm_nonneg _) _`.

Establish `px : 0 ≤ B.gN x ^ (1 - aOf r h)` using `(Real.rpow_pos_of_pos (gN_pos' hx) _).le`. Establish `h3 : C * S + C' * S' ≤ (|C| + |C'|) * (S + S')`. Establish `a1` using `mul_le_mul_of_nonneg_right (le_abs_self C) hS0`. Establish `a2` using `mul_le_mul_of_nonneg_right (le_abs_self C') hS0'`. Establish `a3` using `mul_nonneg (abs_nonneg C) hS0'`.

Establish `a4` using `mul_nonneg (abs_nonneg C') hS0`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Consider the case `smul c v _ hv`. Take `⟨C, Ws, hWs, hb⟩` from `hv`.

Use `⟨‖c‖ * C, Ws, hWs, fun w hw x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc, mul_assoc, ← mul_assoc C]`. Conclude with `mul_le_mul_of_nonneg_left (hb w hw x hx) (norm_nonneg c)`.
-/
theorem decay_TK : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → ∀ v ∈ R.TK, ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧ ∀ w ∈ R.sm, ∀ x ∈ GG k r, ‖⟪v, R.σ x w⟫_ℂ‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum * B.gN x ^ (1 - aOf r h) := by
  intro H k r ε mu h R hR hgap hok v hv
  have hdec : DecInf := H.1.2.1
  have ha := one_le_aOf hok
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨g, hg, v₀, hv₀, rfl⟩ := hv
    obtain ⟨C, Ws, hWs, hb⟩ := hdec k r ε mu h R.H R.σ hR.1 hR.2 hgap hok v₀ hv₀
    refine ⟨|C| * B.gN g ^ (aOf r h - 1), Ws, hWs, fun w hw x hx => ?_⟩
    obtain ⟨hi, hgi, hig⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hg
    have hy : g⁻¹ * x ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hi hx
    have hx' : x = g * (g⁻¹ * x) := by rw [← Matrix.mul_assoc, hgi, Matrix.one_mul]
    have hunit := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).2
    have hiso : ∀ a b, ⟪R.σ g a, R.σ g b⟫_ℂ = ⟪a, b⟫_ℂ :=
      (LinearMap.norm_map_iff_inner_map_map ((R.σ g : R.H →L[ℂ] R.H) : R.H →ₗ[ℂ] R.H)).1 (hunit g hg)
    have e : ⟪R.σ g v₀, R.σ x w⟫_ℂ = ⟪v₀, R.σ (g⁻¹ * x) w⟫_ℂ := by
      rw [← hiso v₀]
      congr 1
      conv_lhs => rw [hx', Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hR.2 hg hy]
      rfl
    rw [e]
    have h1 := hb w hw _ hy
    set S := (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS
    have hS0 : 0 ≤ S := sum_nonneg' _ (fun _ => norm_nonneg _) _
    have pg := gN_pos' hg
    have px := gN_pos' hx
    have py := gN_pos' hy
    have hle : B.gN x ≤ B.gN g * B.gN (g⁻¹ * x) := by
      conv_lhs => rw [hx']
      exact gN_mul_le' _ _
    have h2 : (B.gN g * B.gN (g⁻¹ * x)) ^ (1 - aOf r h) ≤ B.gN x ^ (1 - aOf r h) :=
      Real.rpow_le_rpow_of_nonpos px hle (by linarith)
    rw [Real.mul_rpow pg.le py.le] at h2
    have h3 : B.gN g ^ (aOf r h - 1) * B.gN g ^ (1 - aOf r h) = 1 := by
      rw [← Real.rpow_add pg]; simp
    have pg' : 0 < B.gN g ^ (aOf r h - 1) := Real.rpow_pos_of_pos pg _
    have h4 : B.gN (g⁻¹ * x) ^ (1 - aOf r h) ≤ B.gN g ^ (aOf r h - 1) * B.gN x ^ (1 - aOf r h) := by
      calc B.gN (g⁻¹ * x) ^ (1 - aOf r h)
          = B.gN g ^ (aOf r h - 1) * (B.gN g ^ (1 - aOf r h) * B.gN (g⁻¹ * x) ^ (1 - aOf r h)) := by
            rw [← mul_assoc, h3, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 pg'.le
    calc _ ≤ C * S * B.gN (g⁻¹ * x) ^ (1 - aOf r h) := h1
      _ ≤ |C| * S * B.gN (g⁻¹ * x) ^ (1 - aOf r h) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hS0)
            (Real.rpow_pos_of_pos py _).le
      _ ≤ |C| * S * (B.gN g ^ (aOf r h - 1) * B.gN x ^ (1 - aOf r h)) :=
          mul_le_mul_of_nonneg_left h4 (mul_nonneg (abs_nonneg C) hS0)
      _ = _ := by ring
  | zero => exact ⟨0, [], by simp, fun w _ x _ => by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨C, Ws, hWs, hb⟩ := hu
    obtain ⟨C', Ws', hWs', hb'⟩ := hv
    refine ⟨|C| + |C'|, Ws ++ Ws', fun W hW => (List.mem_append.1 hW).elim (hWs W) (hWs' W),
      fun w hw x hx => ?_⟩
    have h1 := hb w hw x hx
    have h2 := hb' w hw x hx
    rw [List.map_append, List.sum_append, inner_add_left]
    set S := (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS
    set S' := (Ws'.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS'
    have hS0 : 0 ≤ S := sum_nonneg' _ (fun _ => norm_nonneg _) _
    have hS0' : 0 ≤ S' := sum_nonneg' _ (fun _ => norm_nonneg _) _
    have px : 0 ≤ B.gN x ^ (1 - aOf r h) := (Real.rpow_pos_of_pos (gN_pos' hx) _).le
    have h3 : C * S + C' * S' ≤ (|C| + |C'|) * (S + S') := by
      have a1 := mul_le_mul_of_nonneg_right (le_abs_self C) hS0
      have a2 := mul_le_mul_of_nonneg_right (le_abs_self C') hS0'
      have a3 := mul_nonneg (abs_nonneg C) hS0'
      have a4 := mul_nonneg (abs_nonneg C') hS0
      nlinarith
    calc _ ≤ ‖⟪u, R.σ x w⟫_ℂ‖ + ‖⟪v, R.σ x w⟫_ℂ‖ := norm_add_le _ _
      _ ≤ (C * S + C' * S') * B.gN x ^ (1 - aOf r h) := by rw [add_mul]; exact add_le_add h1 h2
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 px
  | smul c v _ hv =>
    obtain ⟨C, Ws, hWs, hb⟩ := hv
    refine ⟨‖c‖ * C, Ws, hWs, fun w hw x hx => ?_⟩
    rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc, mul_assoc, ← mul_assoc C]
    exact mul_le_mul_of_nonneg_left (hb w hw x hx) (norm_nonneg c)

end GlobalTheory.BesselDecay
