import Formalism.PolynomialDimension.StatementNum

noncomputable section

namespace Formalism.CountingSumsFrames

open Real

/- English proof (translation)
Use the polynomial consequences of the given equalities and inequalities.
-/
lemma pII0_one_le_mul {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  nlinarith

/- English proof (translation)
Establish `h1 : r * r ≤ r * N` using `by nlinarith`. Establish `hrN : r ≤ N` using `le_of_mul_le_mul_left h1 (by linarith)`. Use `⟨hrN, by linarith, ?_⟩` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma pII0_basic (r N N₁ k : ℝ) (hr : 2 ≤ r) (hrN1 : r ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N)
    (hk : N₁ + 3 * r ≤ k) : r ≤ N ∧ 8 ≤ k ∧ N₁ + 1 ≤ 2 * r * N := by
  have h1 : r * r ≤ r * N := by nlinarith
  have hrN : r ≤ N := le_of_mul_le_mul_left h1 (by linarith)
  refine ⟨hrN, by linarith, ?_⟩
  nlinarith

/- English proof (translation)
Establish `hpos : 0 ≤ N₁ + r * k` using `by nlinarith`. Establish `hrk : 0 ≤ r * N * k` using `by positivity`. Break down `le_or_gt 0 Nₛ with hs | hs` into its components or cases. Establish `e1 : Nₛ * N₁ ≤ N₁ ^ 2` using `by nlinarith`. Establish `e2 : r * N ≤ r ^ 2 * N * k` using `by nlinarith`.

Establish `e3 : Nₛ * (r * k) ≤ 2 * N * (r * k)`. Apply `mul_le_mul_of_nonneg_right hNs2` to reduce the goal to its premises. Check the signs of the components of the expression. Establish `e4 : 2 * N * (r * k) ≤ r ^ 2 * N * k` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Establish `: Nₛ * (N₁ + r * k) ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg hs.le hpos`. Establish `: 0 ≤ 2 * r ^ 2 * N * k` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sizeBound_frame_le (r N N₁ Nₛ k : ℝ) (hr : 2 ≤ r) (hrN1 : r ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N)
    (hk8 : 8 ≤ k) (hN0 : 0 ≤ N) (hNs1 : Nₛ ≤ N₁) (hNs2 : Nₛ ≤ 2 * N) :
    Nₛ * (N₁ + r * k) ≤ 2 * r ^ 2 * N * k := by
  have hpos : 0 ≤ N₁ + r * k := by nlinarith
  have hrk : 0 ≤ r * N * k := by positivity
  rcases le_or_gt 0 Nₛ with hs | hs
  · have e1 : Nₛ * N₁ ≤ N₁ ^ 2 := by nlinarith
    have e2 : r * N ≤ r ^ 2 * N * k := by nlinarith
    have e3 : Nₛ * (r * k) ≤ 2 * N * (r * k) := by
      apply mul_le_mul_of_nonneg_right hNs2; positivity
    have e4 : 2 * N * (r * k) ≤ r ^ 2 * N * k := by nlinarith
    nlinarith
  · have : Nₛ * (N₁ + r * k) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs.le hpos
    have : 0 ≤ 2 * r ^ 2 * N * k := by positivity
    linarith

/- English proof (translation)
Establish `hrk : 16 ≤ r * k` using `by nlinarith`. Establish `e1 : c' * al ≤ c' * (1 + r * k * Q)` using `mul_le_mul_of_nonneg_left hal (by linarith)`. Establish `hcQ : 1 ≤ c' * Q` using `by nlinarith`. Establish `e2 : k * Q ≤ k * (c' * Q)` using `mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)`. Establish `e3 : 2 * k * (c' * Q) ≤ r * k * (c' * Q)` using `mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)`.

Establish `e4 : 16 * (c' * Q) ≤ r * k * (c' * Q)` using `by nlinarith`. Establish `e5 : c' ≤ c' * Q` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma sizeBound_multiplicity_le (r k Q c' al : ℝ) (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hk8 : 8 ≤ k) (hc : 1 ≤ c')
    (hal : al ≤ 1 + r * k * Q) :
    (2 * Q + 3) * c' + k * Q + c' * al + 3 * c' ≤ 3 * r * k * c' * Q := by
  have hrk : 16 ≤ r * k := by nlinarith
  have e1 : c' * al ≤ c' * (1 + r * k * Q) := mul_le_mul_of_nonneg_left hal (by linarith)
  have hcQ : 1 ≤ c' * Q := by nlinarith
  have e2 : k * Q ≤ k * (c' * Q) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
  have e3 : 2 * k * (c' * Q) ≤ r * k * (c' * Q) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
  have e4 : 16 * (c' * Q) ≤ r * k * (c' * Q) := by nlinarith
  have e5 : c' ≤ c' * Q := by nlinarith
  nlinarith

/- English proof (translation)
Break down `le_or_gt 0 Nₛ with hs | hs` into its components or cases. Establish `: Nₛ * (N₁ + 1) ≤ N₁ * (N₁ + 1)` using `mul_le_mul_of_nonneg_right hNs1 (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Establish `: Nₛ * (N₁ + 1) ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg hs.le (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma sizeBound_count_le (r N N₁ Nₛ : ℝ) (hrN1 : 2 ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N) (hNs1 : Nₛ ≤ N₁) :
    Nₛ * (N₁ + 1) ≤ 2 * r * N := by
  rcases le_or_gt 0 Nₛ with hs | hs
  · have : Nₛ * (N₁ + 1) ≤ N₁ * (N₁ + 1) := mul_le_mul_of_nonneg_right hNs1 (by linarith)
    nlinarith
  · have : Nₛ * (N₁ + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs.le (by linarith)
    nlinarith

/- English proof (translation)
Establish `hkcQ : 1 ≤ k * c' * Q ^ 2`. Establish `: 1 ≤ Q ^ 2` using `one_le_pow₀ hQ`. Establish `: 1 ≤ k * c'` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : 4 ≤ r ^ 2` using `by nlinarith`.

Establish `e1 : 2 * N ≤ r ^ 2 * N` using `by nlinarith`. Establish `e2 : r ^ 2 * N ≤ r ^ 2 * N * (k * c' * Q ^ 2)`. Establish `: 0 ≤ r ^ 2 * N` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
lemma sizeBound_card_le (r N Nₛ k Q c' : ℝ) (hr : 2 ≤ r) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hc : 1 ≤ c')
    (hN0 : 0 ≤ N) (hNs2 : Nₛ ≤ 2 * N) : Nₛ ≤ r ^ 2 * N * k * c' * Q ^ 2 := by
  have hkcQ : 1 ≤ k * c' * Q ^ 2 := by
    have : 1 ≤ Q ^ 2 := one_le_pow₀ hQ
    have : 1 ≤ k * c' := by nlinarith
    nlinarith
  have h4 : 4 ≤ r ^ 2 := by nlinarith
  have e1 : 2 * N ≤ r ^ 2 * N := by nlinarith
  have e2 : r ^ 2 * N ≤ r ^ 2 * N * (k * c' * Q ^ 2) := by
    have : 0 ≤ r ^ 2 * N := by positivity
    nlinarith
  calc Nₛ ≤ 2 * N := hNs2
    _ ≤ r ^ 2 * N := e1
    _ ≤ r ^ 2 * N * (k * c' * Q ^ 2) := e2
    _ = r ^ 2 * N * k * c' * Q ^ 2 := by ring

/- English proof (translation)
Take `⟨hrN, hk8, hN1r⟩` from `pII0_basic r N N₁ k hr hrN1 hN1 hk`. Establish `hN0 : 0 ≤ N` using `by linarith`. Use `set S := (2 * Q + 3) * c' + k * Q + c' * al + 3 * c' with hS`. Establish `hS0 : 0 ≤ S`. Establish `: 0 ≤ c' * al` using `by nlinarith`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hS3 : S ≤ 3 * r * k * c' * Q` using `sizeBound_multiplicity_le r k Q c' al hQ hr hk8 hc hal`. Establish `h1` using `sizeBound_frame_le r N N₁ Nₛ k hr hrN1 hN1 hk8 hN0 hNs1 hNs2`. Establish `h3` using `sizeBound_count_le r N N₁ Nₛ (by linarith) hN1 hNs1`. Establish `h4` using `sizeBound_card_le r N Nₛ k Q c' hr (by linarith) hQ hc hN0 hNs2`.

Use `set M := k * r ^ 2 * N * Q ^ 2 * c' with hM`. Establish `hQ2 : Q ≤ Q ^ 2` using `by nlinarith`. Establish `a1 : Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2) ≤ 2 * CE * M`. Establish `: Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2) = (CE * c' * Q ^ 2) * (Nₛ * (N₁ + r * k))` using `by ring`. Rewrite using `[this]`.

Establish `hcq : 0 ≤ CE * c' * Q ^ 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `a2 : Nₛ * ((N₁ + 1) * S) ≤ 6 * M`. Establish `e : Nₛ * ((N₁ + 1) * S) = (Nₛ * (N₁ + 1)) * S` using `by ring`. Rewrite using `[e]`.

Establish `hr0 : 0 ≤ 2 * r * N` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hM]`. Establish `: 0 ≤ k * r ^ 2 * N * c'` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Establish `a3 : Nₛ ≤ M` using `by rw [hM]; linarith [h4, show r ^ 2 * N * k * c' * Q ^ 2 = k * r ^ 2 * N * Q ^ 2 * c' by ring]`. Establish `hX : Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1) ≤ (2 * CE + 7) * M`. Establish `: Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1) = Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2) + Nₛ * ((N₁ + 1) * S) + Nₛ` using `by ring`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hB : 0 ≤ 32 * Y * k ^ 2 * Q ^ 2` using `by positivity`. Establish `hpX : p * (Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1)) ≤ Q * ((2 * CE + 7) * M)`. Establish `hX0 : 0 ≤ Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1)`. Establish `: 0 ≤ CE * c' * (N₁ + r * k) * Q ^ 2`. Establish `: 0 ≤ N₁ + r * k` using `by nlinarith`.

Check the signs of the components of the expression. Establish `: 0 ≤ (N₁ + 1) * S` using `mul_nonneg (by linarith) hS0`. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
lemma pII0_size (CE p r N N₁ Nₛ k Q c' Y al : ℝ) (hCE : 0 ≤ CE) (hp : 0 ≤ p) (hpQ : p ≤ Q)
    (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hrN1 : r ≤ N₁) (hN1 : N₁ ^ 2 ≤ r * N) (hk : N₁ + 3 * r ≤ k)
    (hNs0 : 0 ≤ Nₛ) (hNs1 : Nₛ ≤ N₁) (hNs2 : Nₛ ≤ 2 * N) (hc : 1 ≤ c') (hY : 0 ≤ Y)
    (hal0 : 0 ≤ al) (hal : al ≤ 1 + r * k * Q) :
    32 * p * Y * k ^ 2 * Nₛ * Q ^ 2 *
        (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') + 1)
      ≤ 32 * (2 * CE + 7) * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by
  obtain ⟨hrN, hk8, hN1r⟩ := pII0_basic r N N₁ k hr hrN1 hN1 hk
  have hN0 : 0 ≤ N := by linarith
  set S := (2 * Q + 3) * c' + k * Q + c' * al + 3 * c' with hS
  have hS0 : 0 ≤ S := by
    have : 0 ≤ c' * al := by nlinarith
    nlinarith
  have hS3 : S ≤ 3 * r * k * c' * Q := sizeBound_multiplicity_le r k Q c' al hQ hr hk8 hc hal
  have h1 := sizeBound_frame_le r N N₁ Nₛ k hr hrN1 hN1 hk8 hN0 hNs1 hNs2
  have h3 := sizeBound_count_le r N N₁ Nₛ (by linarith) hN1 hNs1
  have h4 := sizeBound_card_le r N Nₛ k Q c' hr (by linarith) hQ hc hN0 hNs2
  set M := k * r ^ 2 * N * Q ^ 2 * c' with hM
  have hQ2 : Q ≤ Q ^ 2 := by nlinarith
  have a1 : Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2) ≤ 2 * CE * M := by
    have : Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2) = (CE * c' * Q ^ 2) * (Nₛ * (N₁ + r * k)) := by ring
    rw [this]
    have hcq : 0 ≤ CE * c' * Q ^ 2 := by positivity
    calc (CE * c' * Q ^ 2) * (Nₛ * (N₁ + r * k)) ≤ (CE * c' * Q ^ 2) * (2 * r ^ 2 * N * k) :=
          mul_le_mul_of_nonneg_left h1 hcq
      _ = 2 * CE * M := by rw [hM]; ring
  have a2 : Nₛ * ((N₁ + 1) * S) ≤ 6 * M := by
    have e : Nₛ * ((N₁ + 1) * S) = (Nₛ * (N₁ + 1)) * S := by ring
    rw [e]
    have hr0 : 0 ≤ 2 * r * N := by positivity
    calc (Nₛ * (N₁ + 1)) * S ≤ (2 * r * N) * S := mul_le_mul_of_nonneg_right h3 hS0
      _ ≤ (2 * r * N) * (3 * r * k * c' * Q) := mul_le_mul_of_nonneg_left hS3 hr0
      _ = 6 * (k * r ^ 2 * N * Q * c') := by ring
      _ ≤ 6 * M := by
        rw [hM]
        have : 0 ≤ k * r ^ 2 * N * c' := by positivity
        nlinarith
  have a3 : Nₛ ≤ M := by rw [hM]; linarith [h4, show r ^ 2 * N * k * c' * Q ^ 2 = k * r ^ 2 * N * Q ^ 2 * c' by ring]
  have hX : Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1) ≤ (2 * CE + 7) * M := by
    have : Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1)
        = Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2) + Nₛ * ((N₁ + 1) * S) + Nₛ := by ring
    rw [this]; linarith
  have hB : 0 ≤ 32 * Y * k ^ 2 * Q ^ 2 := by positivity
  have hpX : p * (Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1)) ≤ Q * ((2 * CE + 7) * M) := by
    have hX0 : 0 ≤ Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1) := by
      have : 0 ≤ CE * c' * (N₁ + r * k) * Q ^ 2 := by
        have : 0 ≤ N₁ + r * k := by nlinarith
        positivity
      have : 0 ≤ (N₁ + 1) * S := mul_nonneg (by linarith) hS0
      positivity
    calc p * _ ≤ Q * (Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1)) :=
          mul_le_mul_of_nonneg_right hpQ hX0
      _ ≤ Q * ((2 * CE + 7) * M) := mul_le_mul_of_nonneg_left hX (by linarith)
  calc 32 * p * Y * k ^ 2 * Nₛ * Q ^ 2 * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1)
      = (32 * Y * k ^ 2 * Q ^ 2) * (p * (Nₛ * (CE * c' * (N₁ + r * k) * Q ^ 2 + (N₁ + 1) * S + 1))) := by ring
    _ ≤ (32 * Y * k ^ 2 * Q ^ 2) * (Q * ((2 * CE + 7) * M)) := mul_le_mul_of_nonneg_left hpX hB
    _ = 32 * (2 * CE + 7) * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by rw [hM]; ring

/- English proof (translation)
Establish `h0 : 0 ≤ r ^ 2 * c' * Y * k ^ 2 * Q` using `by positivity`. Establish `h1 : 1 ≤ k * N * Q ^ 4`. Establish `: 1 ≤ Q ^ 4` using `one_le_pow₀ hQ`. Establish `: 1 ≤ k * N` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma sizeBound_first_term (r N k Q c' Y : ℝ) (hr : 0 ≤ r) (hN : 1 ≤ N) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hc : 0 ≤ c') (hY : 0 ≤ Y) :
    r ^ 2 * c' * (Y * k ^ 2 * Q) ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
  have h0 : 0 ≤ r ^ 2 * c' * Y * k ^ 2 * Q := by positivity
  have h1 : 1 ≤ k * N * Q ^ 4 := by
    have : 1 ≤ Q ^ 4 := one_le_pow₀ hQ
    have : 1 ≤ k * N := by nlinarith
    nlinarith
  calc r ^ 2 * c' * (Y * k ^ 2 * Q) = (r ^ 2 * c' * Y * k ^ 2 * Q) * 1 := by ring
    _ ≤ (r ^ 2 * c' * Y * k ^ 2 * Q) * (k * N * Q ^ 4) := mul_le_mul_of_nonneg_left h1 h0
    _ = k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by ring

/- English proof (translation)
Establish `hW : 0 ≤ Y * k ^ 2 * Q` using `by positivity`. Establish `e1 : (N₁ + r) * c₀ ≤ k * c'`. Combine the equalities or inequalities in the displayed calculation. Establish `hc : 0 ≤ c'` using `le_trans hc00 hc0`. Establish `h1 : 1 ≤ r ^ 2 * N * Q ^ 4`.

Establish `: 1 ≤ Q ^ 4` using `one_le_pow₀ hQ`. Establish `: 1 ≤ r ^ 2` using `one_le_pow₀ hr`. Establish `: 1 ≤ r ^ 2 * N` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `h0 : 0 ≤ k ^ 3 * c' * Y * Q` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma sizeBound_second_term (r N N₁ k Q c' Y c₀ : ℝ) (hr : 1 ≤ r) (hN : 1 ≤ N) (hk0 : 0 ≤ k) (hQ : 1 ≤ Q)
    (hY : 0 ≤ Y) (hNk : N₁ + r ≤ k) (hc00 : 0 ≤ c₀) (hc0 : c₀ ≤ c') :
    (N₁ + r) * c₀ * (Y * k ^ 2 * Q) ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
  have hW : 0 ≤ Y * k ^ 2 * Q := by positivity
  have e1 : (N₁ + r) * c₀ ≤ k * c' := by
    calc (N₁ + r) * c₀ ≤ k * c₀ := mul_le_mul_of_nonneg_right hNk hc00
      _ ≤ k * c' := mul_le_mul_of_nonneg_left hc0 hk0
  have hc : 0 ≤ c' := le_trans hc00 hc0
  have h1 : 1 ≤ r ^ 2 * N * Q ^ 4 := by
    have : 1 ≤ Q ^ 4 := one_le_pow₀ hQ
    have : 1 ≤ r ^ 2 := one_le_pow₀ hr
    have : 1 ≤ r ^ 2 * N := by nlinarith
    nlinarith
  have h0 : 0 ≤ k ^ 3 * c' * Y * Q := by positivity
  calc (N₁ + r) * c₀ * (Y * k ^ 2 * Q) ≤ k * c' * (Y * k ^ 2 * Q) := mul_le_mul_of_nonneg_right e1 hW
    _ = (k ^ 3 * c' * Y * Q) * 1 := by ring
    _ ≤ (k ^ 3 * c' * Y * Q) * (r ^ 2 * N * Q ^ 4) := mul_le_mul_of_nonneg_left h1 h0
    _ = k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by ring

/- English proof (translation)
Establish `hS3` using `sizeBound_multiplicity_le r k Q c' al hQ hr hk8 hc hal`. Establish `hS0 : 0 ≤ (2 * Q + 3) * c' + k * Q + c' * al + 3 * c'`. Establish `: 0 ≤ c' * al` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hW : 0 ≤ Y * k ^ 2 * Q` using `by positivity`.

Establish `e1 : (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') ≤ (2 * r * N) * (3 * r * k * c' * Q)` using `mul_le_mul hN1r hS3 hS0 (by positivity)`. Establish `h1 : Q ^ 2 ≤ Q ^ 5` using `pow_le_pow_right₀ hQ (by norm_num)`. Establish `h0 : 0 ≤ 6 * r ^ 2 * N * k ^ 3 * c' * Y` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma sizeBound_third_term (r N N₁ k Q c' Y al : ℝ) (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hk8 : 8 ≤ k) (hc : 1 ≤ c')
    (hY : 0 ≤ Y) (hal0 : 0 ≤ al) (hal : al ≤ 1 + r * k * Q) (hN0 : 0 ≤ N) (hN10 : 0 ≤ N₁)
    (hN1r : N₁ + 1 ≤ 2 * r * N) :
    (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') * (Y * k ^ 2 * Q)
      ≤ 6 * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by
  have hS3 := sizeBound_multiplicity_le r k Q c' al hQ hr hk8 hc hal
  have hS0 : 0 ≤ (2 * Q + 3) * c' + k * Q + c' * al + 3 * c' := by
    have : 0 ≤ c' * al := by nlinarith
    nlinarith
  have hW : 0 ≤ Y * k ^ 2 * Q := by positivity
  have e1 : (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') ≤ (2 * r * N) * (3 * r * k * c' * Q) :=
    mul_le_mul hN1r hS3 hS0 (by positivity)
  have h1 : Q ^ 2 ≤ Q ^ 5 := pow_le_pow_right₀ hQ (by norm_num)
  have h0 : 0 ≤ 6 * r ^ 2 * N * k ^ 3 * c' * Y := by positivity
  calc (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') * (Y * k ^ 2 * Q)
      ≤ (2 * r * N) * (3 * r * k * c' * Q) * (Y * k ^ 2 * Q) := mul_le_mul_of_nonneg_right e1 hW
    _ = (6 * r ^ 2 * N * k ^ 3 * c' * Y) * Q ^ 2 := by ring
    _ ≤ (6 * r ^ 2 * N * k ^ 3 * c' * Y) * Q ^ 5 := mul_le_mul_of_nonneg_left h1 h0
    _ = 6 * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by ring

/- English proof (translation)
Establish `h` using `sizeBound_first_term r N k Q 1 Y (by linarith) hN hk hQ (by norm_num) hY`. Establish `h0 : 0 ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * Y` using `by positivity`. Establish `h1 : Y * k ^ 2 * Q ≤ r ^ 2 * 1 * (Y * k ^ 2 * Q)`. Establish `: 1 ≤ r ^ 2` using `one_le_pow₀ hr`. Establish `: 0 ≤ Y * k ^ 2 * Q` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : k ^ 3 * r ^ 2 * N * Q ^ 5 * 1 * Y ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sizeBound_fourth_term (r N k Q c' Y : ℝ) (hr : 1 ≤ r) (hN : 1 ≤ N) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hc : 1 ≤ c') (hY : 0 ≤ Y) : Y * k ^ 2 * Q ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
  have h := sizeBound_first_term r N k Q 1 Y (by linarith) hN hk hQ (by norm_num) hY
  have h0 : 0 ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * Y := by positivity
  have h1 : Y * k ^ 2 * Q ≤ r ^ 2 * 1 * (Y * k ^ 2 * Q) := by
    have : 1 ≤ r ^ 2 := one_le_pow₀ hr
    have : 0 ≤ Y * k ^ 2 * Q := by positivity
    nlinarith
  have h2 : k ^ 3 * r ^ 2 * N * Q ^ 5 * 1 * Y ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by nlinarith
  linarith

/- English proof (translation)
Take `⟨hrN, hk8, hN1r⟩` from `pII0_basic r N N₁ k hr hrN1 hN1 hk`. Establish `hN : 1 ≤ N` using `by linarith`. Establish `q1` using `sizeBound_first_term r N k Q c' Y (by linarith) hN (by linarith) hQ (by linarith) hY`. Establish `q2` using `sizeBound_second_term r N N₁ k Q c' Y c₀ (by linarith) hN (by linarith) hQ hY (by linarith) hc00 hc0`. Establish `q3` using `sizeBound_third_term r N N₁ k Q c' Y al hQ hr hk8 hc hY hal0 hal (by linarith) (by linarith) hN1r`.

Establish `q4` using `sizeBound_fourth_term r N k Q c' Y (by linarith) hN (by linarith) hQ hc hY`. Establish `hM : 0 ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y`. Establish `: 0 ≤ k` using `by linarith`. Establish `: 0 ≤ N` using `by linarith`. Establish `: 0 ≤ Q` using `by linarith`.

Establish `: 0 ≤ c'` using `by linarith`. Check the signs of the components of the expression. Establish `e : (100 * r ^ 2 * c' + 24 * (N₁ + r) * c₀ + (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') + 1) * (Y * k ^ 2 * Q) = 100 * (r ^ 2 * c' * (Y * k ^ 2 * Q)) + 24 * ((N₁ + r) * c₀ * (Y * k ^ 2 * Q)) + (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') * (Y * k ^ 2 * Q …` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma pII0_slack (r N N₁ k Q c' Y al c₀ : ℝ) (hQ : 1 ≤ Q) (hr : 2 ≤ r) (hrN1 : r ≤ N₁)
    (hN1 : N₁ ^ 2 ≤ r * N) (hk : N₁ + 3 * r ≤ k) (hc : 1 ≤ c') (hY : 0 ≤ Y)
    (hal0 : 0 ≤ al) (hal : al ≤ 1 + r * k * Q) (hc00 : 0 ≤ c₀) (hc0 : c₀ ≤ c') :
    (100 * r ^ 2 * c' + 24 * (N₁ + r) * c₀ +
        (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') + 1) * (Y * k ^ 2 * Q)
      ≤ 155 * (k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y) := by
  obtain ⟨hrN, hk8, hN1r⟩ := pII0_basic r N N₁ k hr hrN1 hN1 hk
  have hN : 1 ≤ N := by linarith
  have q1 := sizeBound_first_term r N k Q c' Y (by linarith) hN (by linarith) hQ (by linarith) hY
  have q2 := sizeBound_second_term r N N₁ k Q c' Y c₀ (by linarith) hN (by linarith) hQ hY (by linarith) hc00 hc0
  have q3 := sizeBound_third_term r N N₁ k Q c' Y al hQ hr hk8 hc hY hal0 hal (by linarith) (by linarith) hN1r
  have q4 := sizeBound_fourth_term r N k Q c' Y (by linarith) hN (by linarith) hQ hc hY
  have hM : 0 ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
    have : 0 ≤ k := by linarith
    have : 0 ≤ N := by linarith
    have : 0 ≤ Q := by linarith
    have : 0 ≤ c' := by linarith
    positivity
  have e : (100 * r ^ 2 * c' + 24 * (N₁ + r) * c₀ +
        (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') + 1) * (Y * k ^ 2 * Q)
      = 100 * (r ^ 2 * c' * (Y * k ^ 2 * Q)) + 24 * ((N₁ + r) * c₀ * (Y * k ^ 2 * Q))
        + (N₁ + 1) * ((2 * Q + 3) * c' + k * Q + c' * al + 3 * c') * (Y * k ^ 2 * Q)
        + Y * k ^ 2 * Q := by ring
  rw [e]
  linarith

/- English proof (translation)
Establish `hW : 0 < Y * k ^ 2` using `by linarith`. Establish `h1 : (L + 1) * (Y * k ^ 2) ≤ a / Q`. Rewrite using `[le_div_iff₀ hQ0]; linarith [show (L + 1) * (Y * k ^ 2) * Q = (L + 1) * (Y * k ^ 2 * Q) by ring]`. Establish `h2 : L + 1 ≤ B / (Y * k ^ 2)`. Rewrite using `[le_div_iff₀ hW]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB0 : 0 ≤ B` using `le_trans (div_nonneg ha hQ0.le) hB`. Prove the components needed by the constructor for the conclusion. Use `Int.sub_one_lt_floor (B / (Y * k ^ 2))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h3 : B / (Y * k ^ 2) ≤ B / 100` using `by gcongr`. Conclude with `le_trans (Int.floor_le _) h3`.
-/
lemma pII0_floor (L Y k Q a B : ℝ) (hQ0 : 0 < Q) (ha : 0 ≤ a) (hYk100 : 100 ≤ Y * k ^ 2)
    (h : (L + 1) * (Y * k ^ 2 * Q) ≤ a) (hB : a / Q ≤ B) :
    L ≤ ((⌊B / (Y * k ^ 2)⌋ : ℤ) : ℝ) ∧ ((⌊B / (Y * k ^ 2)⌋ : ℤ) : ℝ) ≤ B / 100 := by
  have hW : 0 < Y * k ^ 2 := by linarith
  have h1 : (L + 1) * (Y * k ^ 2) ≤ a / Q := by
    rw [le_div_iff₀ hQ0]; linarith [show (L + 1) * (Y * k ^ 2) * Q = (L + 1) * (Y * k ^ 2 * Q) by ring]
  have h2 : L + 1 ≤ B / (Y * k ^ 2) := by
    rw [le_div_iff₀ hW]; linarith
  have hB0 : 0 ≤ B := le_trans (div_nonneg ha hQ0.le) hB
  constructor
  · have := Int.sub_one_lt_floor (B / (Y * k ^ 2))
    linarith
  · have h3 : B / (Y * k ^ 2) ≤ B / 100 := by
      gcongr
    exact le_trans (Int.floor_le _) h3

/- English proof (translation)
Establish `h1 : 1 ≤ k ^ 3` using `one_le_pow₀ hk`. Establish `h2 : 1 ≤ r ^ 2` using `one_le_pow₀ hr`. Establish `h3 : 1 ≤ Q ^ 5` using `one_le_pow₀ hQ`. Conclude with `pII0_one_le_mul (pII0_one_le_mul (pII0_one_le_mul (pII0_one_le_mul (pII0_one_le_mul h1 h2) hN) h3) hc) hY`.
-/
lemma sizeBound_one_le_product (k r N Q c' Y : ℝ) (hk : 1 ≤ k) (hr : 1 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hc : 1 ≤ c') (hY : 1 ≤ Y) : 1 ≤ k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y := by
  have h1 : 1 ≤ k ^ 3 := one_le_pow₀ hk
  have h2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have h3 : 1 ≤ Q ^ 5 := one_le_pow₀ hQ
  exact pII0_one_le_mul (pII0_one_le_mul (pII0_one_le_mul (pII0_one_le_mul
    (pII0_one_le_mul h1 h2) hN) h3) hc) hY

/- English proof (translation)
Unfold `omII`. Establish `hr' : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hN' : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hrN : (1 : ℝ) ≤ r * N` using `pII0_one_le_mul hr' hN'`. Establish `hc : (0 : ℝ) ≤ c₀` using `Nat.cast_nonneg _`.

Establish `h2 : (0 : ℝ) ≤ 2 * r * n' * c''` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma pII0_om (r N n' c₀ c'' : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N) : (c₀ : ℝ) ≤ omII r N n' c₀ c'' := by
  unfold omII
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hrN : (1 : ℝ) ≤ r * N := pII0_one_le_mul hr' hN'
  have hc : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ 2 * r * n' * c'' := by positivity
  nlinarith

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `CE C₂ hCE hC₂`. Use `⟨64 * CE + 400 + C₂, by linarith, ?_⟩` and prove the remaining obligations. Introduce `p r N N₁ Nₛ J k n' L₁ G' Y a al c₀ c'' D cStar hH hal0 hal`. Take `⟨hp13, hr2, hrN1, hN1, hrY, hClog, hk, h256, hCD, hDc, hCa, hL1, hLG, hNs1, hNs2, hJ, hJr⟩` from `hH`. Establish `hr2' : (2 : ℝ) ≤ r` using `by exact_mod_cast hr2`.

Establish `hrN1' : (r : ℝ) ≤ N₁` using `by exact_mod_cast hrN1`. Establish `hN1' : (N₁ : ℝ) ^ 2 ≤ r * N` using `by exact_mod_cast hN1`. Establish `hk' : (N₁ : ℝ) + 3 * r ≤ k` using `by exact_mod_cast hk`. Establish `hNs1' : (Nₛ : ℝ) ≤ N₁` using `by exact_mod_cast hNs1`. Establish `hNs2' : (Nₛ : ℝ) ≤ 2 * N` using `by exact_mod_cast hNs2`.

Take `⟨hrN, hk8, hN1r⟩` from `pII0_basic r N N₁ k hr2' hrN1' hN1' hk'`. Establish `hNone : (1 : ℝ) ≤ N` using `by linarith`. Establish `hNone' : 1 ≤ N` using `by exact_mod_cast hNone`. Establish `hp1 : (1 : ℝ) ≤ p` using `by exact_mod_cast (show 1 ≤ p by omega)`. Establish `hQ1 : 1 ≤ QII p G'` using `one_le_pow₀ hp1`.

Establish `hpQ : (p : ℝ) ≤ QII p G'`. Unfold `QII`. Combine the equalities or inequalities in the displayed calculation. Establish `hom0 : (0 : ℝ) ≤ omII r N n' c₀ c''` using `by unfold omII; positivity`. Establish `hc1 : 1 ≤ cPrII r N n' c₀ c'' cStar`.

Unfold `cPrII`. Establish `: (8 : ℝ) ≤ cStar` using `by exact_mod_cast (show 8 ≤ cStar by omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc0le : (c₀ : ℝ) ≤ cPrII r N n' c₀ c'' cStar`. Unfold `cPrII`.

Use `pII0_om r N n' c₀ c'' (by omega) hNone'` as an intermediate fact. Establish `: (0 : ℝ) ≤ cStar` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hY1 : 1 ≤ Y` using `by linarith`. Establish `hY0 : 0 ≤ Y` using `by linarith`.

Use `set Q := QII p G' with hQdef`. Use `set c' := cPrII r N n' c₀ c'' cStar with hcdef`. Use `set M := (k : ℝ) ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y with hMdef`. Establish `hM0 : 0 ≤ M`. Establish `: 0 ≤ Q` using `by linarith`.

Establish `: 0 ≤ c'` using `by linarith`. Check the signs of the components of the expression. Establish `hCa' : (64 * CE + 400 + C₂) * M ≤ a`. Establish `: (64 * CE + 400 + C₂) * M = (64 * CE + 400 + C₂) * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * Q ^ 5 * c' * Y`. Rewrite using `[hMdef]`.

Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha0 : 0 ≤ a` using `le_trans (mul_nonneg (by linarith) hM0) hCa'`. Use `⟨?_, ?_, ?_, ?_, hY1, ?_⟩` and prove the remaining obligations. Unfold `errorTerm mStarII`.

Establish `hs` using `pII0_size CE p r N N₁ Nₛ k Q c' Y al (by linarith) (Nat.cast_nonneg _) hpQ hQ1 hr2' hrN1' hN1' hk' (Nat.cast_nonneg _) hNs1' hNs2' hc1 hY0 hal0 hal`. Establish `: 32 * (2 * CE + 7) * M ≤ (64 * CE + 400 + C₂) * M` using `mul_le_mul_of_nonneg_right (by linarith) hM0`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `B hB`. Unfold `slII mStarII`.

Establish `hs` using `pII0_slack r N N₁ k Q c' Y al c₀ hQ1 hr2' hrN1' hN1' hk' hc1 hY0 hal0 hal (Nat.cast_nonneg _) hc0le`. Establish `h155 : 155 * M ≤ (64 * CE + 400 + C₂) * M` using `mul_le_mul_of_nonneg_right (by linarith) hM0`. Establish `hYk : 100 ≤ Y * (k : ℝ) ^ 2`. Establish `: (64 : ℝ) ≤ (k : ℝ) ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `pII0_floor _ Y k Q a B (by linarith) ha0 hYk (by linarith) hB`. Establish `: (0 : ℝ) ≤ (k : ℝ) ^ 2 * Y ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Break down `le_or_gt 0 (Real.log a) with hl | hl` into its components or cases. Establish `hsq : (Nₛ : ℝ) ^ 2 ≤ (N₁ : ℝ) ^ 2` using `pow_le_pow_left₀ (Nat.cast_nonneg _) hNs1' 2`.

Establish `e1 : C₂ * (Nₛ : ℝ) ^ 2 ≤ (64 * CE + 400 + C₂) * (N₁ : ℝ) ^ 2` using `mul_le_mul (by linarith) hsq (by positivity) (by linarith)`. Establish `e2` using `mul_le_mul_of_nonneg_right e1 hl`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: C₂ * (Nₛ : ℝ) ^ 2 * Real.log a ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos (by positivity) hl.le`. Establish `: (0 : ℝ) ≤ k` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion. Use linear arithmetic over natural numbers and integers.
-/
theorem secondParameterSizeBounds_holds : ParamsII0 := by
  intro CE C₂ hCE hC₂
  refine ⟨64 * CE + 400 + C₂, by linarith, ?_⟩
  intro p r N N₁ Nₛ J k n' L₁ G' Y a al c₀ c'' D cStar hH hal0 hal
  obtain ⟨hp13, hr2, hrN1, hN1, hrY, hClog, hk, h256, hCD, hDc, hCa, hL1, hLG, hNs1, hNs2,
    hJ, hJr⟩ := hH
  have hr2' : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have hrN1' : (r : ℝ) ≤ N₁ := by exact_mod_cast hrN1
  have hN1' : (N₁ : ℝ) ^ 2 ≤ r * N := by exact_mod_cast hN1
  have hk' : (N₁ : ℝ) + 3 * r ≤ k := by exact_mod_cast hk
  have hNs1' : (Nₛ : ℝ) ≤ N₁ := by exact_mod_cast hNs1
  have hNs2' : (Nₛ : ℝ) ≤ 2 * N := by exact_mod_cast hNs2
  obtain ⟨hrN, hk8, hN1r⟩ := pII0_basic r N N₁ k hr2' hrN1' hN1' hk'
  have hNone : (1 : ℝ) ≤ N := by linarith
  have hNone' : 1 ≤ N := by exact_mod_cast hNone
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hQ1 : 1 ≤ QII p G' := one_le_pow₀ hp1
  have hpQ : (p : ℝ) ≤ QII p G' := by
    unfold QII
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ G' := pow_le_pow_right₀ hp1 (by omega)
  have hom0 : (0 : ℝ) ≤ omII r N n' c₀ c'' := by unfold omII; positivity
  have hc1 : 1 ≤ cPrII r N n' c₀ c'' cStar := by
    unfold cPrII
    have : (8 : ℝ) ≤ cStar := by exact_mod_cast (show 8 ≤ cStar by omega)
    linarith
  have hc0le : (c₀ : ℝ) ≤ cPrII r N n' c₀ c'' cStar := by
    unfold cPrII
    have := pII0_om r N n' c₀ c'' (by omega) hNone'
    have : (0 : ℝ) ≤ cStar := Nat.cast_nonneg _
    linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 ≤ Y := by linarith
  set Q := QII p G' with hQdef
  set c' := cPrII r N n' c₀ c'' cStar with hcdef
  set M := (k : ℝ) ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y with hMdef
  have hM0 : 0 ≤ M := by
    have : 0 ≤ Q := by linarith
    have : 0 ≤ c' := by linarith
    positivity
  have hCa' : (64 * CE + 400 + C₂) * M ≤ a := by
    have : (64 * CE + 400 + C₂) * M
        = (64 * CE + 400 + C₂) * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * Q ^ 5 * c' * Y := by
      rw [hMdef]; ring
    linarith
  have ha0 : 0 ≤ a := le_trans (mul_nonneg (by linarith) hM0) hCa'
  refine ⟨?_, ?_, ?_, ?_, hY1, ?_⟩
  · unfold errorTerm mStarII
    have hs := pII0_size CE p r N N₁ Nₛ k Q c' Y al (by linarith) (Nat.cast_nonneg _) hpQ hQ1
      hr2' hrN1' hN1' hk' (Nat.cast_nonneg _) hNs1' hNs2' hc1 hY0 hal0 hal
    have : 32 * (2 * CE + 7) * M ≤ (64 * CE + 400 + C₂) * M :=
      mul_le_mul_of_nonneg_right (by linarith) hM0
    linarith
  · intro B hB
    unfold slII mStarII
    have hs := pII0_slack r N N₁ k Q c' Y al c₀ hQ1 hr2' hrN1' hN1' hk' hc1 hY0 hal0 hal
      (Nat.cast_nonneg _) hc0le
    have h155 : 155 * M ≤ (64 * CE + 400 + C₂) * M :=
      mul_le_mul_of_nonneg_right (by linarith) hM0
    have hYk : 100 ≤ Y * (k : ℝ) ^ 2 := by
      have : (64 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      nlinarith
    exact pII0_floor _ Y k Q a B (by linarith) ha0 hYk (by linarith) hB
  · have : (0 : ℝ) ≤ (k : ℝ) ^ 2 * Y ^ 2 := by positivity
    nlinarith
  · rcases le_or_gt 0 (Real.log a) with hl | hl
    · have hsq : (Nₛ : ℝ) ^ 2 ≤ (N₁ : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hNs1' 2
      have e1 : C₂ * (Nₛ : ℝ) ^ 2 ≤ (64 * CE + 400 + C₂) * (N₁ : ℝ) ^ 2 :=
        mul_le_mul (by linarith) hsq (by positivity) (by linarith)
      have e2 := mul_le_mul_of_nonneg_right e1 hl
      linarith
    · have : C₂ * (Nₛ : ℝ) ^ 2 * Real.log a ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hl.le
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      linarith
  · omega

end Formalism.CountingSumsFrames
