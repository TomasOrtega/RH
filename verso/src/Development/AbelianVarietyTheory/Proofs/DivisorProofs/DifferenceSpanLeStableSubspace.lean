import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BallIndicatorSmallerBallsSumStatement

noncomputable section

open ValuativeRel

namespace GlobalTheory.PrinTwo.DiffSpan

open GlobalTheory.PrinTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `ha : valuation k (a : k) ≠ 0` using `by simp`. Rewrite `h` using `[map_mul, map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[inv_mul_cancel_left₀ ha]`. Use `_ ≤ (valuation k (a : k))⁻¹ * (valuation k (a : k) * valuation k u) := by gcongr`. Use `_ = valuation k u := by rw [inv_mul_cancel_left₀ ha]`. Introduce `h`. Rewrite using `[map_mul, map_mul]`.

Use `gcongr`.
-/
theorem val_mul_le_val_mul_iff (a : kˣ) (w u : k) :
    valuation k ((a : k) * w) ≤ valuation k ((a : k) * u) ↔ valuation k w ≤ valuation k u := by
  constructor
  · intro h
    have ha : valuation k (a : k) ≠ 0 := by simp
    rw [map_mul, map_mul] at h
    calc valuation k w = (valuation k (a : k))⁻¹ * (valuation k (a : k) * valuation k w) := by
          rw [inv_mul_cancel_left₀ ha]
      _ ≤ (valuation k (a : k))⁻¹ * (valuation k (a : k) * valuation k u) := by gcongr
      _ = valuation k u := by rw [inv_mul_cancel_left₀ ha]
  · intro h
    rw [map_mul, map_mul]; gcongr

/- English proof (translation)
Take `⟨n, hn⟩` from `MulArchimedean.arch (valuation k z / valuation k (s : k)) ht`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hs : valuation k (s : k) ≠ 0` using `by simp`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[div_mul_cancel₀ _ hs]`. Use `_ ≤ valuation k (t : k) ^ n * valuation k (s : k) := by gcongr`.
-/
theorem exists_pow (t : kˣ) (ht : 1 < valuation k (t : k)) (z : k) (s : kˣ) :
    ∃ n : ℕ, valuation k z ≤ valuation k (((t ^ n * s : kˣ)) : k) := by
  obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation k z / valuation k (s : k)) ht
  refine ⟨n, ?_⟩
  have hs : valuation k (s : k) ≠ 0 := by simp
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  calc valuation k z = valuation k z / valuation k (s : k) * valuation k (s : k) := by
        rw [div_mul_cancel₀ _ hs]
    _ ≤ valuation k (t : k) ^ n * valuation k (s : k) := by gcongr

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_ball_iff {c x : k} {r : kˣ} :
    x ∈ ball c r ↔ valuation k (x - c) ≤ valuation k (r : k) := Iff.rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem elemDiff_apply (c c' : k) (r : kˣ) (x : k) :
    elemDiff c c' r x = (ball c r).indicator 1 x - (ball c' r).indicator 1 x := rfl

/- English proof (translation)
Simplify using `only [Set.indicator_apply, mem_ball_iff, Pi.one_apply]`. Rewrite using `[show x + y - c = x - (c - y) by ring]`.
-/
theorem indicator_ball_shift (c y x : k) (r : kˣ) :
    (ball c r).indicator (1 : k → ℂ) (x + y) = (ball (c - y) r).indicator 1 x := by
  classical
  simp only [Set.indicator_apply, mem_ball_iff, Pi.one_apply]
  rw [show x + y - c = x - (c - y) by ring]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [elemDiff_apply, indicator_ball_shift]`.
-/
theorem elemDiff_shift (c c' y : k) (r : kˣ) :
    (fun x => elemDiff c c' r (x + y)) = elemDiff (c - y) (c' - y) r := by
  funext x; simp only [elemDiff_apply, indicator_ball_shift]

/- English proof (translation)
Simplify using `only [Set.indicator_apply, mem_ball_iff, Pi.one_apply]`. Establish `h1 : (a : k) * x - c = (a : k) * (x - ((a⁻¹ : kˣ) : k) * c)`. Rewrite using `[mul_sub, ← mul_assoc, Units.mul_inv, one_mul]`. Establish `h2 : (r : k) = (a : k) * ((a⁻¹ * r : kˣ) : k)`. Rewrite using `[Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]`.

Establish `key : valuation k ((a : k) * x - c) ≤ valuation k (r : k) ↔ valuation k (x - ((a⁻¹ : kˣ) : k) * c) ≤ valuation k ((a⁻¹ * r : kˣ) : k)`. Rewrite using `[h1, h2, val_mul_le_val_mul_iff]`. Simplify using `only [key]`.
-/
theorem indicator_ball_dilate (c x : k) (r a : kˣ) :
    (ball c r).indicator (1 : k → ℂ) ((a : k) * x) =
      (ball (((a⁻¹ : kˣ) : k) * c) (a⁻¹ * r)).indicator 1 x := by
  classical
  simp only [Set.indicator_apply, mem_ball_iff, Pi.one_apply]
  have h1 : (a : k) * x - c = (a : k) * (x - ((a⁻¹ : kˣ) : k) * c) := by
    rw [mul_sub, ← mul_assoc, Units.mul_inv, one_mul]
  have h2 : (r : k) = (a : k) * ((a⁻¹ * r : kˣ) : k) := by
    rw [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
  have key : valuation k ((a : k) * x - c) ≤ valuation k (r : k) ↔
      valuation k (x - ((a⁻¹ : kˣ) : k) * c) ≤ valuation k ((a⁻¹ * r : kˣ) : k) := by
    rw [h1, h2, val_mul_le_val_mul_iff]
  simp only [key]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [elemDiff_apply, indicator_ball_dilate]`.
-/
theorem elemDiff_dilate (c c' : k) (r a : kˣ) :
    (fun x => elemDiff c c' r ((a : k) * x)) =
      elemDiff (((a⁻¹ : kˣ) : k) * c) (((a⁻¹ : kˣ) : k) * c') (a⁻¹ * r) := by
  funext x; simp only [elemDiff_apply, indicator_ball_dilate]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [mem_ball_iff, h]`.
-/
theorem ball_congr (c : k) {r r' : kˣ} (h : valuation k (r : k) = valuation k (r' : k)) :
    ball c r = ball c r' := by
  ext x; simp only [mem_ball_iff, h]

/- English proof (translation)
Simplify using `only [elemDiff, ball_congr c h, ball_congr c' h]`.
-/
theorem elemDiff_congr (c c' : k) {r r' : kˣ} (h : valuation k (r : k) = valuation k (r' : k)) :
    elemDiff c c' r = elemDiff c c' r' := by
  simp only [elemDiff, ball_congr c h, ball_congr c' h]

/- English proof (translation)
Establish `hb : ball c r = ball c' r`. Use extensionality with `x`. Simplify using `only [mem_ball_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Rewrite using `[show x - c' = (x - c) - (c' - c) by ring]`. Conclude with `(valuation k).map_sub_le hx h`. Introduce `hx`. Rewrite using `[show x - c = (x - c') + (c' - c) by ring]`. Conclude with `(valuation k).map_add_le hx h`.

Simplify using `[elemDiff, hb]`.
-/
theorem elemDiff_eq_zero {c c' : k} {r : kˣ} (h : valuation k (c' - c) ≤ valuation k (r : k)) :
    elemDiff c c' r = 0 := by
  have hb : ball c r = ball c' r := by
    ext x
    simp only [mem_ball_iff]
    constructor
    · intro hx
      rw [show x - c' = (x - c) - (c' - c) by ring]
      exact (valuation k).map_sub_le hx h
    · intro hx
      rw [show x - c = (x - c') + (c' - c) by ring]
      exact (valuation k).map_add_le hx h
  simp [elemDiff, hb]

/- English proof (translation)
The claim follows from `GlobalTheory.T.ball_indicator_smaller_balls_sum k s S h`.
-/
theorem decomp (s S : kˣ) (h : valuation k (s : k) ≤ valuation k (S : k)) :
    ∃ T : Finset k, T.Nonempty ∧ (∀ t ∈ T, valuation k t ≤ valuation k (S : k)) ∧
      ∀ c x : k, (ball c S).indicator (1 : k → ℂ) x = ∑ t ∈ T, (ball (c + t) s).indicator 1 x :=
  GlobalTheory.T.ball_indicator_smaller_balls_sum k s S h

/- English proof (translation)
Introduce `k _ _ _ _ W hT hD y r c hc hry hW`. Establish `shift : ∀ (e e' : k) (s : kˣ) (y' : k), elemDiff e e' s ∈ W → elemDiff (e - y') (e' - y') s ∈ W`. Introduce `e e' s y' h`. Rewrite using `[← elemDiff_shift]`. Conclude with `hT _ h y'`.

Establish `dil : ∀ (e e' : k) (s a : kˣ), elemDiff e e' s ∈ W → elemDiff (((a⁻¹ : kˣ) : k) * e) (((a⁻¹ : kˣ) : k) * e') (a⁻¹ * s) ∈ W`. Introduce `e e' s a h`. Rewrite using `[← elemDiff_dilate]`. Conclude with `hD _ h a`. Establish `hy : elemDiff 0 y r ∈ W`.

Use `W.smul_mem c⁻¹ hW` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis. Establish `add : ∀ (s : kˣ) (z z' : k), elemDiff 0 z s ∈ W → elemDiff 0 z' s ∈ W → elemDiff 0 (z + z') s ∈ W`. Introduce `s z z' h h'`. Establish `h2` using `shift 0 z' s (-z) h'`.

Simplify using `only [zero_sub, neg_neg, sub_neg_eq_add, zero_add] at h2`. Establish `: elemDiff 0 (z + z') s = elemDiff 0 z s + elemDiff z (z' + z) s`. Use function extensionality and compare the values at `x`. Simplify using `only [elemDiff_apply, Pi.add_apply, add_comm z' z]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `W.add_mem h h2`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hry`.

Use `set t : kˣ := Units.mk0 y hy0 * r⁻¹ with ht_def`. Establish `ht_val : (t : k) = y * (r : k)⁻¹` using `by simp [t]`. Establish `hty : y = (t : k) * (r : k)` using `by rw [ht_val]; field_simp`. Establish `ht1 : 1 < valuation k (t : k)`. Assume the negation of the conclusion as `hle`.

Use `push_neg at hle`. Establish `: valuation k y ≤ valuation k (r : k)`. Rewrite using `[hty, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `absurd hry (not_lt.mpr this)`.

Establish `sphere : ∀ z : k, valuation k z = valuation k y → elemDiff 0 z r ∈ W`. Introduce `z hz`. Establish `hz0 : z ≠ 0` using `by rintro rfl; rw [map_zero] at hz; exact hy0 ((map_eq_zero _).mp hz.symm)`. Use `set a : kˣ := Units.mk0 y hy0 * (Units.mk0 z hz0)⁻¹`. Establish `h` using `dil 0 y r a hy`.

Establish `ha1 : ((a⁻¹ : kˣ) : k) * y = z` using `by simp [a]; field_simp`. Establish `hva : valuation k ((a⁻¹ * r : kˣ) : k) = valuation k (r : k)`. Simplify using `only [a, Units.val_mul, map_mul, mul_inv_rev, inv_inv, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, hz]`. Rewrite using `[mul_inv_cancel₀ (by simpa using hy0), one_mul]`. Rewrite `h` using `[mul_zero, ha1, elemDiff_congr 0 z hva]`. Then use the resulting hypothesis.

Establish `G1 : ∀ z : k, valuation k z ≤ valuation k y → elemDiff 0 z r ∈ W`. Introduce `z hz`. Break down `hz.lt_or_eq with hlt | heq` into its components or cases. Establish `h1 : valuation k (z - y) = valuation k y` using `(valuation k).map_sub_eq_of_lt_right hlt`. Use `add r (z - y) y (sphere _ h1) hy` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Conclude with `sphere z heq`. Establish `G2 : ∀ (s : kˣ) (w : k), valuation k w ≤ valuation k ((t * s : kˣ) : k) → elemDiff 0 w s ∈ W`. Introduce `s w hw`. Use `set a : kˣ := r * s⁻¹`.

Establish `hay : (a : k) * ((t * s : kˣ) : k) = y`. Simplify using `only [a, Units.val_mul, Units.val_inv_eq_inv_val, ht_val]`. Clear the denominators using the available nonvanishing facts. Establish `hz : valuation k ((a : k) * w) ≤ valuation k y`. Rewrite using `[← hay, val_mul_le_val_mul_iff]`.

Conclude with `hw`. Establish `h` using `dil 0 ((a : k) * w) r a (G1 _ hz)`. Establish `har : a⁻¹ * r = s` using `by simp [a]`. Rewrite `h` using `[mul_zero, ← mul_assoc, Units.inv_mul, one_mul, har]`. Then use the resulting hypothesis. Establish `G3 : ∀ (s : kˣ) (z : k), elemDiff 0 z (t * s) ∈ W → elemDiff 0 z s ∈ W`.

Introduce `s z hz`. Establish `hsS : valuation k (s : k) ≤ valuation k ((t * s : kˣ) : k)`. Rewrite using `[Units.val_mul, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨T, hTne, hTv, hdec⟩` from `decomp s (t * s) hsS`.

Establish `hE : ∀ u ∈ T, elemDiff u (z + u) s - elemDiff 0 z s ∈ W`. Introduce `u hu`. Establish `h1` using `G2 s u (hTv u hu)`. Establish `h2` using `shift 0 u s (-z) h1`. Simplify using `only [zero_sub, neg_neg, sub_neg_eq_add, zero_add] at h2`.

Establish `: elemDiff u (z + u) s - elemDiff 0 z s = elemDiff z (u + z) s - elemDiff 0 u s`. Use function extensionality and compare the values at `x`. Simplify using `only [elemDiff_apply, Pi.sub_apply, add_comm u z]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `W.sub_mem h2 h1`. Establish `hsum : elemDiff 0 z (t * s) = ∑ u ∈ T, elemDiff u (z + u) s`. Use function extensionality and compare the values at `x`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [elemDiff_apply]`.

Rewrite using `[hdec 0 x, hdec z x, ← Finset.sum_sub_distrib]`. Simplify using `only [zero_add]`. Establish `hcard : T.card • elemDiff 0 z s ∈ W`. Establish `: T.card • elemDiff 0 z s = ∑ u ∈ T, elemDiff u (z + u) s - ∑ u ∈ T, (elemDiff u (z + u) s - elemDiff 0 z s)`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this, ← hsum]`. Conclude with `W.sub_mem hz (W.sum_mem hE)`. Establish `hc0 : (T.card : ℂ) ≠ 0` using `by exact_mod_cast hTne.card_pos.ne'`. Rewrite `hcard` using `[← Nat.cast_smul_eq_nsmul ℂ]`.

Use `W.smul_mem (T.card : ℂ)⁻¹ hcard` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Then use the resulting hypothesis. Establish `G4 : ∀ (n : ℕ) (s : kˣ) (z : k), elemDiff 0 z (t ^ n * s) ∈ W → elemDiff 0 z s ∈ W`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro s z h`. Simplify using `using h`. Consider the case `succ n ih`. Introduce `s z h`. Rewrite `h` using `[pow_succ, mul_assoc]`.

Conclude with `G3 s z (ih (t * s) z h)`. Establish `G5 : ∀ (z : k) (s : kˣ), elemDiff 0 z s ∈ W`. Introduce `z s`. Take `⟨n, hn⟩` from `exists_pow t ht1 z s`. Use `G4 n s z ?_` and prove the remaining obligations.

Rewrite using `[elemDiff_eq_zero (by simpa using hn)]`. Conclude with `W.zero_mem`. Rewrite using `[elemSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨⟨e, e', s⟩, rfl⟩`. Use `shift 0 (e' - e) s (-e) (G5 _ _)` as an intermediate fact.

Apply the tactic sequence `have he : elemDiff e e' s = elemDiff (0 - -e) (e' - e - -e) s := by congr 1 <;> ring`. Use `show elemDiff e e' s ∈ W`. Rewrite using `[he]`. Conclude with `this`.
-/
theorem elemSpan_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (W : Submodule ℂ (k → ℂ)),
    (∀ Φ ∈ W, ∀ y : k, (fun x => Φ (x + y)) ∈ W) → (∀ Φ ∈ W, ∀ a : kˣ, (fun x => Φ (a * x)) ∈ W) →
    ∀ (y : k) (r : kˣ) (c : ℂ), c ≠ 0 → ValuativeRel.valuation k (r : k) < ValuativeRel.valuation k y →
    c • GlobalTheory.PrinTwo.elemDiff 0 y r ∈ W → GlobalTheory.PrinTwo.elemSpan k ≤ W := by
  intro k _ _ _ _ W hT hD y r c hc hry hW
  have shift : ∀ (e e' : k) (s : kˣ) (y' : k), elemDiff e e' s ∈ W →
      elemDiff (e - y') (e' - y') s ∈ W := by
    intro e e' s y' h; rw [← elemDiff_shift]; exact hT _ h y'
  have dil : ∀ (e e' : k) (s a : kˣ), elemDiff e e' s ∈ W →
      elemDiff (((a⁻¹ : kˣ) : k) * e) (((a⁻¹ : kˣ) : k) * e') (a⁻¹ * s) ∈ W := by
    intro e e' s a h; rw [← elemDiff_dilate]; exact hD _ h a
  have hy : elemDiff 0 y r ∈ W := by
    have := W.smul_mem c⁻¹ hW
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have add : ∀ (s : kˣ) (z z' : k), elemDiff 0 z s ∈ W → elemDiff 0 z' s ∈ W →
      elemDiff 0 (z + z') s ∈ W := by
    intro s z z' h h'
    have h2 := shift 0 z' s (-z) h'
    simp only [zero_sub, neg_neg, sub_neg_eq_add, zero_add] at h2
    have : elemDiff 0 (z + z') s = elemDiff 0 z s + elemDiff z (z' + z) s := by
      funext x; simp only [elemDiff_apply, Pi.add_apply, add_comm z' z]; ring
    rw [this]; exact W.add_mem h h2
  have hy0 : y ≠ 0 := by
    rintro rfl; simp at hry
  set t : kˣ := Units.mk0 y hy0 * r⁻¹ with ht_def
  have ht_val : (t : k) = y * (r : k)⁻¹ := by simp [t]
  have hty : y = (t : k) * (r : k) := by rw [ht_val]; field_simp
  have ht1 : 1 < valuation k (t : k) := by
    by_contra hle
    push_neg at hle
    have : valuation k y ≤ valuation k (r : k) := by
      rw [hty, map_mul]
      calc valuation k (t : k) * valuation k (r : k) ≤ 1 * valuation k (r : k) := by gcongr
        _ = valuation k (r : k) := one_mul _
    exact absurd hry (not_lt.mpr this)

  have sphere : ∀ z : k, valuation k z = valuation k y → elemDiff 0 z r ∈ W := by
    intro z hz
    have hz0 : z ≠ 0 := by rintro rfl; rw [map_zero] at hz; exact hy0 ((map_eq_zero _).mp hz.symm)
    set a : kˣ := Units.mk0 y hy0 * (Units.mk0 z hz0)⁻¹
    have h := dil 0 y r a hy
    have ha1 : ((a⁻¹ : kˣ) : k) * y = z := by simp [a]; field_simp
    have hva : valuation k ((a⁻¹ * r : kˣ) : k) = valuation k (r : k) := by
      simp only [a, Units.val_mul, map_mul, mul_inv_rev, inv_inv, Units.val_inv_eq_inv_val,
        Units.val_mk0, map_inv₀, hz]
      rw [mul_inv_cancel₀ (by simpa using hy0), one_mul]
    rwa [mul_zero, ha1, elemDiff_congr 0 z hva] at h
  have G1 : ∀ z : k, valuation k z ≤ valuation k y → elemDiff 0 z r ∈ W := by
    intro z hz
    rcases hz.lt_or_eq with hlt | heq
    · have h1 : valuation k (z - y) = valuation k y := (valuation k).map_sub_eq_of_lt_right hlt
      have := add r (z - y) y (sphere _ h1) hy
      rwa [sub_add_cancel] at this
    · exact sphere z heq
  have G2 : ∀ (s : kˣ) (w : k), valuation k w ≤ valuation k ((t * s : kˣ) : k) →
      elemDiff 0 w s ∈ W := by
    intro s w hw
    set a : kˣ := r * s⁻¹
    have hay : (a : k) * ((t * s : kˣ) : k) = y := by
      simp only [a, Units.val_mul, Units.val_inv_eq_inv_val, ht_val]; field_simp
    have hz : valuation k ((a : k) * w) ≤ valuation k y := by
      rw [← hay, val_mul_le_val_mul_iff]; exact hw
    have h := dil 0 ((a : k) * w) r a (G1 _ hz)
    have har : a⁻¹ * r = s := by simp [a]
    rwa [mul_zero, ← mul_assoc, Units.inv_mul, one_mul, har] at h
  have G3 : ∀ (s : kˣ) (z : k), elemDiff 0 z (t * s) ∈ W → elemDiff 0 z s ∈ W := by
    intro s z hz
    have hsS : valuation k (s : k) ≤ valuation k ((t * s : kˣ) : k) := by
      rw [Units.val_mul, map_mul]
      calc valuation k (s : k) = 1 * valuation k (s : k) := (one_mul _).symm
        _ ≤ valuation k (t : k) * valuation k (s : k) := by gcongr
    obtain ⟨T, hTne, hTv, hdec⟩ := decomp s (t * s) hsS
    have hE : ∀ u ∈ T, elemDiff u (z + u) s - elemDiff 0 z s ∈ W := by
      intro u hu
      have h1 := G2 s u (hTv u hu)
      have h2 := shift 0 u s (-z) h1
      simp only [zero_sub, neg_neg, sub_neg_eq_add, zero_add] at h2
      have : elemDiff u (z + u) s - elemDiff 0 z s = elemDiff z (u + z) s - elemDiff 0 u s := by
        funext x; simp only [elemDiff_apply, Pi.sub_apply, add_comm u z]; ring
      rw [this]; exact W.sub_mem h2 h1
    have hsum : elemDiff 0 z (t * s) = ∑ u ∈ T, elemDiff u (z + u) s := by
      funext x
      rw [Finset.sum_apply]
      simp only [elemDiff_apply]
      rw [hdec 0 x, hdec z x, ← Finset.sum_sub_distrib]
      simp only [zero_add]
    have hcard : T.card • elemDiff 0 z s ∈ W := by
      have : T.card • elemDiff 0 z s = ∑ u ∈ T, elemDiff u (z + u) s -
          ∑ u ∈ T, (elemDiff u (z + u) s - elemDiff 0 z s) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const]; abel
      rw [this, ← hsum]
      exact W.sub_mem hz (W.sum_mem hE)
    have hc0 : (T.card : ℂ) ≠ 0 := by exact_mod_cast hTne.card_pos.ne'
    rw [← Nat.cast_smul_eq_nsmul ℂ] at hcard
    have := W.smul_mem (T.card : ℂ)⁻¹ hcard
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  have G4 : ∀ (n : ℕ) (s : kˣ) (z : k), elemDiff 0 z (t ^ n * s) ∈ W → elemDiff 0 z s ∈ W := by
    intro n
    induction n with
    | zero => intro s z h; simpa using h
    | succ n ih =>
      intro s z h
      rw [pow_succ, mul_assoc] at h
      exact G3 s z (ih (t * s) z h)
  have G5 : ∀ (z : k) (s : kˣ), elemDiff 0 z s ∈ W := by
    intro z s
    obtain ⟨n, hn⟩ := exists_pow t ht1 z s
    refine G4 n s z ?_
    rw [elemDiff_eq_zero (by simpa using hn)]
    exact W.zero_mem
  rw [elemSpan, Submodule.span_le]
  rintro _ ⟨⟨e, e', s⟩, rfl⟩
  have := shift 0 (e' - e) s (-e) (G5 _ _)
  have he : elemDiff e e' s = elemDiff (0 - -e) (e' - e - -e) s := by congr 1 <;> ring
  show elemDiff e e' s ∈ W
  rw [he]
  exact this

end GlobalTheory.PrinTwo.DiffSpan
