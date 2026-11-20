import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsShareBound
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PShareCore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Filter Topology

noncomputable section

variable {n : ℕ} {MS : Type} [TopologicalSpace MS]

/- English proof (translation)
Introduce `p`. Take `⟨e, hp, hz, han⟩` from `hu p`. Conclude with `⟨e, hp, hz, fun x hx => (han x hx).inv (h0 _)⟩`.
-/
theorem HolomorphicAlong.inv {z : MS → (Fin n → ℂ)} {u : MS → ℂ}
    (hu : HolomorphicAlong z u) (h0 : ∀ p, u p ≠ 0) : HolomorphicAlong z (fun p => (u p)⁻¹) := by
  intro p
  obtain ⟨e, hp, hz, han⟩ := hu p
  exact ⟨e, hp, hz, fun x hx => (han x hx).inv (h0 _)⟩

/- English proof (translation)
Unfold `shareExp`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_sixteen_mul_shareExp (e : ℕ) : e ≤ 16 * shareExp e := by
  unfold shareExp; omega

/- English proof (translation)
Establish `hsc : 0 < Real.sqrt cw` using `Real.sqrt_pos.2 hcw`. Rewrite using `[le_div_iff₀ hsc]`. Establish `h1 : (Real.exp (-(rh / 4)) * Real.sqrt cw) ^ 2 = cw * Real.exp (-(rh / 2))`. Rewrite using `[mul_pow, Real.sq_sqrt hcw.le, ← Real.exp_nat_mul]`. Use `push_cast`.

Put the polynomial expressions in normal form. Establish `h2 : 0 ≤ Real.exp (-(rh / 4)) * Real.sqrt cw` using `by positivity`. Use polynomial arithmetic with `[h1, h, sq_nonneg (Real.exp (-(rh / 4)) * Real.sqrt cw - wn)]`.
-/
theorem exp_quarter_le {rh wn cw : ℝ} (hcw : 0 < cw) (hwn : 0 ≤ wn)
    (h : cw * Real.exp (-(rh / 2)) ≤ wn ^ 2) : Real.exp (-(rh / 4)) ≤ wn / Real.sqrt cw := by
  have hsc : 0 < Real.sqrt cw := Real.sqrt_pos.2 hcw
  rw [le_div_iff₀ hsc]
  have h1 : (Real.exp (-(rh / 4)) * Real.sqrt cw) ^ 2 = cw * Real.exp (-(rh / 2)) := by
    rw [mul_pow, Real.sq_sqrt hcw.le, ← Real.exp_nat_mul]
    push_cast; ring_nf
  have h2 : 0 ≤ Real.exp (-(rh / 4)) * Real.sqrt cw := by positivity
  nlinarith [h1, h, sq_nonneg (Real.exp (-(rh / 4)) * Real.sqrt cw - wn)]

/- English proof (translation)
Rewrite using `[← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]`. Establish `hae' : (e : ℝ) ≤ 16 * a` using `by exact_mod_cast hae`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exp_four_mul_le {rh K : ℝ} {a e : ℕ} (hK : -K ≤ rh) (hae : e ≤ 16 * a) :
    Real.exp (-(4 * rh)) ^ a ≤ Real.exp (K * (4 * a - e / 4)) * Real.exp (-(rh / 4)) ^ e := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
  have hae' : (e : ℝ) ≤ 16 * a := by exact_mod_cast hae
  nlinarith

/- English proof (translation)
Use `set E := Real.exp (K * (4 * a - e / 4))`. Use `set S := Real.sqrt (1 + N)`. Establish `hS : (1 + N) ^ ((e : ℝ) / 2) = S ^ e`. Simplify using `only [S]`. Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hS]`. Establish `hsc : 0 < Real.sqrt cw` using `Real.sqrt_pos.2 hcw`. Establish `hCf : 0 ≤ Cf` using `(by positivity : 0 ≤ x * hF).trans hf`.

Establish `hCθ : 0 ≤ Cθ` using `(by positivity : 0 ≤ y * hθ).trans hth`. Establish `hCτ : 0 ≤ Cτ`. Establish `: 0 ≤ Cτ * Real.exp (-(4 * rh))` using `(by positivity : 0 ≤ t * hτ).trans htau`. Conclude with `nonneg_of_mul_nonneg_left this (Real.exp_pos _)`. Establish `hprod : (x * hF) * (y * hθ) * (t * hτ) ^ a ≤ Cf * Cθ * Cτ ^ a * (E * Real.exp (-(rh / 4)) ^ e)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hq : Real.exp (-(rh / 4)) ≤ CompactFixesLatticeTheory / Real.sqrt cw * (hW * ω * S)`. Combine the equalities or inequalities in the displayed calculation. Establish `hqe : Real.exp (-(rh / 4)) ^ e ≤ (CompactFixesLatticeTheory / Real.sqrt cw) ^ e * (hW ^ e * ω ^ e * S ^ e)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hden : 0 < κ * hW ^ e * ω ^ e` using `by positivity`. Establish `hlhs : x * (y * (ω ^ e)⁻¹) * t ^ a = (x * hF) * (y * hθ) * (t * hτ) ^ a / (κ * hW ^ e * ω ^ e)`. Rewrite using `[← hbk]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hlhs, div_le_iff₀ hden]`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts.
-/
theorem share_pointwise {x y t ω N hF hθ hτ hW wn rh κ Cf Cθ Cτ cw CompactFixesLatticeTheory K : ℝ} {a e : ℕ}
    (hae : e ≤ 16 * a) (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 ≤ t) (hω : 0 < ω) (hN : 0 ≤ N)
    (hF0 : 0 < hF) (hθ0 : 0 < hθ) (hτ0 : 0 < hτ) (hW0 : 0 < hW) (hκ : 0 < κ)
    (hbk : hF * hθ * hτ ^ a = κ * hW ^ e)
    (hf : x * hF ≤ Cf) (hth : y * hθ ≤ Cθ) (htau : t * hτ ≤ Cτ * Real.exp (-(4 * rh)))
    (hcw : 0 < cw) (hwn : 0 ≤ wn) (hw : cw * Real.exp (-(rh / 2)) ≤ wn ^ 2) (hK : -K ≤ rh)
    (hfl : wn ≤ CompactFixesLatticeTheory * (hW * (ω * Real.sqrt (1 + N)))) :
    x * (y * (ω ^ e)⁻¹) * t ^ a ≤
      Cf * Cθ * Cτ ^ a * Real.exp (K * (4 * a - e / 4)) * (CompactFixesLatticeTheory / Real.sqrt cw) ^ e / κ *
        (1 + N) ^ ((e : ℝ) / 2) := by
  set E := Real.exp (K * (4 * a - e / 4))
  set S := Real.sqrt (1 + N)
  have hS : (1 + N) ^ ((e : ℝ) / 2) = S ^ e := by
    simp only [S]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1; ring
  rw [hS]
  have hsc : 0 < Real.sqrt cw := Real.sqrt_pos.2 hcw
  have hCf : 0 ≤ Cf := (by positivity : 0 ≤ x * hF).trans hf
  have hCθ : 0 ≤ Cθ := (by positivity : 0 ≤ y * hθ).trans hth
  have hCτ : 0 ≤ Cτ := by
    have : 0 ≤ Cτ * Real.exp (-(4 * rh)) := (by positivity : 0 ≤ t * hτ).trans htau
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)

  have hprod : (x * hF) * (y * hθ) * (t * hτ) ^ a ≤
      Cf * Cθ * Cτ ^ a * (E * Real.exp (-(rh / 4)) ^ e) := by
    calc (x * hF) * (y * hθ) * (t * hτ) ^ a
        ≤ Cf * Cθ * (Cτ * Real.exp (-(4 * rh))) ^ a := by
          gcongr
      _ = Cf * Cθ * Cτ ^ a * Real.exp (-(4 * rh)) ^ a := by rw [mul_pow]; ring
      _ ≤ Cf * Cθ * Cτ ^ a * (E * Real.exp (-(rh / 4)) ^ e) := by
          gcongr; exact exp_four_mul_le hK hae

  have hq : Real.exp (-(rh / 4)) ≤ CompactFixesLatticeTheory / Real.sqrt cw * (hW * ω * S) := by
    calc Real.exp (-(rh / 4)) ≤ wn / Real.sqrt cw := exp_quarter_le hcw hwn hw
      _ ≤ CompactFixesLatticeTheory * (hW * (ω * S)) / Real.sqrt cw := by gcongr
      _ = CompactFixesLatticeTheory / Real.sqrt cw * (hW * ω * S) := by ring
  have hqe : Real.exp (-(rh / 4)) ^ e ≤ (CompactFixesLatticeTheory / Real.sqrt cw) ^ e * (hW ^ e * ω ^ e * S ^ e) := by
    calc Real.exp (-(rh / 4)) ^ e ≤ (CompactFixesLatticeTheory / Real.sqrt cw * (hW * ω * S)) ^ e := by
          gcongr
      _ = (CompactFixesLatticeTheory / Real.sqrt cw) ^ e * (hW ^ e * ω ^ e * S ^ e) := by ring
  have hden : 0 < κ * hW ^ e * ω ^ e := by positivity
  have hlhs : x * (y * (ω ^ e)⁻¹) * t ^ a =
      (x * hF) * (y * hθ) * (t * hτ) ^ a / (κ * hW ^ e * ω ^ e) := by
    rw [← hbk]; field_simp; ring
  rw [hlhs, div_le_iff₀ hden]
  calc (x * hF) * (y * hθ) * (t * hτ) ^ a
      ≤ Cf * Cθ * Cτ ^ a * (E * Real.exp (-(rh / 4)) ^ e) := hprod
    _ ≤ Cf * Cθ * Cτ ^ a * (E * ((CompactFixesLatticeTheory / Real.sqrt cw) ^ e * (hW ^ e * ω ^ e * S ^ e))) := by
        gcongr
    _ = Cf * Cθ * Cτ ^ a * E * (CompactFixesLatticeTheory / Real.sqrt cw) ^ e / κ * S ^ e * (κ * hW ^ e * ω ^ e) := by
        field_simp

/- English proof (translation)
Introduce `n MS _ _ _ _ De z δ e f τ w₀ s hF hθ hτ hW wn rh κ Cf Cτ cw CompactFixesLatticeTheory K hDe hcov hf hτ hw₀ hw₀0 hs hF0 hθ0 hτ0 hW0 hκ hbk hfb hex hτne htau hcw hwn hw hK hfl`. Take `⟨θ, Cθ, hθ, hθne, hθb⟩` from `hex`. Use `set a := shareExp e`. Use `set θ' : MS → ℂ := fun p => θ p * (w₀ p ^ e)⁻¹`. Establish `hw₀e : HolomorphicAlong z (fun p => w₀ p ^ e)` using `hw₀.pow e`.

Establish `hθ' : HolomorphicAlong z θ'` using `hθ.mul (hw₀e.inv fun p => pow_ne_zero _ (hw₀0 p))`. Establish `hθ'ne : θ' ≠ 0`. Introduce `H`. Apply `hθne` to reduce the goal to its premises. Use function extensionality and compare the values at `p`.

Use `congrFun H p` as an intermediate fact. Simplify using `only [θ', Pi.zero_apply, mul_eq_zero, inv_eq_zero] at this`. Conclude with `this.resolve_right (pow_ne_zero _ (hw₀0 p))`. Establish `hbound : ∀ p, ‖f p * θ' p * τ p ^ a‖ ≤ Cf * Cθ * Cτ ^ a * Real.exp (K * (4 * a - e / 4)) * (CompactFixesLatticeTheory / Real.sqrt cw) ^ e / κ * (1 + normSq (z p)) ^ ((e : ℝ) / 2)`. Introduce `p`.

Establish `hsum : ‖w₀ p‖ ^ 2 + ∑ i, ‖s i p‖ ^ 2 = ‖w₀ p‖ ^ 2 * (1 + normSq (z p))`. Simplify using `only [hs p, norm_mul, mul_pow, normSq, ← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfl' : wn p ≤ CompactFixesLatticeTheory * (hW p * (‖w₀ p‖ * Real.sqrt (1 + normSq (z p))))`. Use `hfl p` as an intermediate fact.

Rewrite `this` using `[hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]`. Then use the resulting hypothesis. Establish `hN : 0 ≤ normSq (z p)` using `Finset.sum_nonneg fun i _ => sq_nonneg _`. Use `share_pointwise (le_sixteen_mul_shareExp e) (norm_nonneg (f p)) (norm_nonneg (θ p)) (norm_nonneg (τ p)) (norm_pos_iff.2 (hw₀0 p)) hN (hF0 p) (hθ0 p) (hτ0 p) (hW0 p) hκ (hbk p) (hfb p) (hθb p) (htau p) hcw (hwn p) (hw p) (hK p) hfl'` as an intermediate fact. Simplify `this` using `only [θ', norm_mul, norm_inv, norm_pow]`. Distinguish the cases in `H : ∀ p, z p = 0 → OrderGT z f p e`.

Use `left`. Conclude with `ShareCore.proof hNorm n MS De z δ f θ' τ _ e a hDe hcov hf hθ' hτ hθ'ne hτne hbound H`. Use `right push Not at H`. Conclude with `H`.
-/
theorem ShareBound.proof (hNorm : NormLemma.Statement) : ShareBound.Statement := by
  intro n MS _ _ _ _ De z δ e f τ w₀ s hF hθ hτ hW wn rh κ Cf Cτ cw CompactFixesLatticeTheory K hDe hcov hf hτ hw₀
    hw₀0 hs hF0 hθ0 hτ0 hW0 hκ hbk hfb hex hτne htau hcw hwn hw hK hfl
  obtain ⟨θ, Cθ, hθ, hθne, hθb⟩ := hex
  set a := shareExp e

  set θ' : MS → ℂ := fun p => θ p * (w₀ p ^ e)⁻¹
  have hw₀e : HolomorphicAlong z (fun p => w₀ p ^ e) := hw₀.pow e
  have hθ' : HolomorphicAlong z θ' := hθ.mul (hw₀e.inv fun p => pow_ne_zero _ (hw₀0 p))
  have hθ'ne : θ' ≠ 0 := by
    intro H
    apply hθne
    funext p
    have := congrFun H p
    simp only [θ', Pi.zero_apply, mul_eq_zero, inv_eq_zero] at this
    exact this.resolve_right (pow_ne_zero _ (hw₀0 p))
  have hbound : ∀ p, ‖f p * θ' p * τ p ^ a‖ ≤
      Cf * Cθ * Cτ ^ a * Real.exp (K * (4 * a - e / 4)) * (CompactFixesLatticeTheory / Real.sqrt cw) ^ e / κ *
        (1 + normSq (z p)) ^ ((e : ℝ) / 2) := by
    intro p
    have hsum : ‖w₀ p‖ ^ 2 + ∑ i, ‖s i p‖ ^ 2 = ‖w₀ p‖ ^ 2 * (1 + normSq (z p)) := by
      simp only [hs p, norm_mul, mul_pow, normSq, ← Finset.sum_mul]
      ring
    have hfl' : wn p ≤ CompactFixesLatticeTheory * (hW p * (‖w₀ p‖ * Real.sqrt (1 + normSq (z p)))) := by
      have := hfl p
      rwa [hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
    have hN : 0 ≤ normSq (z p) := Finset.sum_nonneg fun i _ => sq_nonneg _
    have := share_pointwise (le_sixteen_mul_shareExp e) (norm_nonneg (f p)) (norm_nonneg (θ p))
      (norm_nonneg (τ p)) (norm_pos_iff.2 (hw₀0 p)) hN (hF0 p) (hθ0 p) (hτ0 p) (hW0 p) hκ
      (hbk p) (hfb p) (hθb p) (htau p) hcw (hwn p) (hw p) (hK p) hfl'
    simpa only [θ', norm_mul, norm_inv, norm_pow] using this
  by_cases H : ∀ p, z p = 0 → OrderGT z f p e
  · left
    exact ShareCore.proof hNorm n MS De z δ f θ' τ _ e a hDe hcov hf hθ' hτ hθ'ne hτne hbound H
  · right
    push Not at H
    exact H

end

end GroundTheory.Heights₂.Heights.EffectiveHS
