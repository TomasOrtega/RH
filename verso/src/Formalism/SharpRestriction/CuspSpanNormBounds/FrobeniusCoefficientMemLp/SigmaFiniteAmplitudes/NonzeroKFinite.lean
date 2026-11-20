import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothAdd

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.QuantumDeterminants

/- English proof (translation)
Introduce `hKD hKS k r ε lam H _ _ _ σ w0 Wp _ _ z c π hlam hσ hw0 l hl hnz`. Take `⟨x, hxDD, hlx⟩` from `hnz`. Establish `hxs : x ∈ PI.UpqRep.smoothVecs (k` using `k) (r := r) σ := Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hlam hσ hw0 x hxDD`. Take `⟨hadd, hsmul, -, C, Ws, hWs, hbd⟩` from `hl`. Establish `hpos : 0 < ‖l x‖` using `norm_pos_iff.mpr hlx`.

Use `set e : ℝ := ‖l x‖ / (|C| + 1) with he`. Establish `he0 : 0 < e` using `div_pos hpos (by positivity)`. Take `⟨v, hvK, hv⟩` from `hKD k r ε lam H σ hlam hσ x hxs Ws hWs e he0`. Use `⟨v, hvK, fun hlv => ?_⟩` and prove the remaining obligations. Establish `hvs : v ∈ PI.UpqRep.smoothVecs (k` using `k) (r := r) σ := hKS k r ε lam H σ hlam hσ v hvK`.

Establish `hdiff_s : x - v ∈ PI.UpqRep.smoothVecs (k` using `k) (r := r) σ := by`. Rewrite using `[sub_eq_add_neg, ← neg_one_smul ℂ v]`. Conclude with `Formalism.FourierDecayAlt.P.DDSmoothness.smooth_add hxs (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul (-1) hvs)`. Establish `hsplit : l x = l (x - v) + l v`. Use `hadd (x - v) hdiff_s v hvs` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Conclude with `this`. Rewrite `hsplit` using `[hlv, add_zero]`. Establish `hb` using `hbd (x - v) hdiff_s`. Use `set S := (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (x - v)‖).sum with hS`.

Establish `hS0 : 0 ≤ S`. Rewrite using `[hS]`. Apply `List.sum_nonneg` to reduce the goal to its premises. Introduce `y hy`. Take `⟨w, -, rfl⟩` from `List.mem_map.1 hy`.

Conclude with `norm_nonneg _`. Establish `h1 : ‖l x‖ ≤ |C| * S`. Rewrite using `[hsplit]`. Conclude with `hb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hS0)`. Establish `h2 : |C| * S ≤ |C| * e` using `mul_le_mul_of_nonneg_left hv.le (abs_nonneg C)`.

Establish `h3 : |C| * e < ‖l x‖`. Rewrite using `[he, mul_div_assoc']`. Rewrite using `[div_lt_iff₀ (by positivity)]`. Use polynomial arithmetic with `[abs_nonneg C]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nonzero_K_finite : Formalism.MainNotions.S.Pv.AmpDD.NzKF := by
  intro hKD hKS k r ε lam H _ _ _ σ w0 Wp _ _ z c π hlam hσ hw0 l hl hnz
  obtain ⟨x, hxDD, hlx⟩ := hnz
  have hxs : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hlam hσ hw0 x hxDD
  obtain ⟨hadd, hsmul, -, C, Ws, hWs, hbd⟩ := hl
  have hpos : 0 < ‖l x‖ := norm_pos_iff.mpr hlx
  set e : ℝ := ‖l x‖ / (|C| + 1) with he
  have he0 : 0 < e := div_pos hpos (by positivity)
  obtain ⟨v, hvK, hv⟩ := hKD k r ε lam H σ hlam hσ x hxs Ws hWs e he0
  refine ⟨v, hvK, fun hlv => ?_⟩
  have hvs : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := hKS k r ε lam H σ hlam hσ v hvK
  have hdiff_s : x - v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ v]
    exact Formalism.FourierDecayAlt.P.DDSmoothness.smooth_add hxs (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul (-1) hvs)
  have hsplit : l x = l (x - v) + l v := by
    have := hadd (x - v) hdiff_s v hvs
    rw [sub_add_cancel] at this
    exact this
  rw [hlv, add_zero] at hsplit
  have hb := hbd (x - v) hdiff_s
  set S := (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (x - v)‖).sum with hS
  have hS0 : 0 ≤ S := by
    rw [hS]; apply List.sum_nonneg; intro y hy
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy; exact norm_nonneg _
  have h1 : ‖l x‖ ≤ |C| * S := by
    rw [hsplit]; exact hb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hS0)
  have h2 : |C| * S ≤ |C| * e := mul_le_mul_of_nonneg_left hv.le (abs_nonneg C)
  have h3 : |C| * e < ‖l x‖ := by
    rw [he, mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

end Formalism.MainNotions.S.Pv.AmpDDPf
