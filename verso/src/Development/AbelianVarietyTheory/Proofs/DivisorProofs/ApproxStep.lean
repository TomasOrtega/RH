import Mathlib

namespace GlobalTheory.FixedPointApproximation

noncomputable def approx {B : Type} [CommRing B] (q : B) (σ : B →+* B) (w : B) : ℕ → B
  | 0 => 0
  | n + 1 => -w + q * σ (approx q σ w n)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Take `⟨t, ht⟩` from `ih`. Use `⟨σ t, ?_⟩` and prove the remaining obligations.

Establish `e : approx q σ w (n + 1 + 1) - approx q σ w (n + 1) = q * σ (approx q σ w (n + 1) - approx q σ w n)`. Rewrite using `[map_sub]`. Use `show -w + q * σ (approx q σ w (n + 1)) - (-w + q * σ (approx q σ w n)) = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ht, map_mul, map_pow, hq]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem approx_step {B : Type} [CommRing B] (q : B) (σ : B →+* B) (hq : σ q = q) (w : B) (n : ℕ) :
    q ^ n ∣ approx q σ w (n + 1) - approx q σ w n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨σ t, ?_⟩
    have e : approx q σ w (n + 1 + 1) - approx q σ w (n + 1) =
        q * σ (approx q σ w (n + 1) - approx q σ w n) := by
      rw [map_sub]
      show -w + q * σ (approx q σ w (n + 1)) - (-w + q * σ (approx q σ w n)) = _
      ring
    rw [e, ht, map_mul, map_pow, hq]
    ring

/- English proof (translation)
Proceed by induction on `n, h using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`. Establish `h2 : q ^ m ∣ approx q σ w (n + 1) - approx q σ w n` using `(pow_dvd_pow q hmn).trans (approx_step q σ hq w n)`. Establish `e : approx q σ w m - approx q σ w (n + 1) = (approx q σ w m - approx q σ w n) - (approx q σ w (n + 1) - approx q σ w n)` using `by ring`.

Rewrite using `[e]`. Conclude with `dvd_sub ih h2`.
-/
theorem approx_dvd {B : Type} [CommRing B] (q : B) (σ : B →+* B) (hq : σ q = q) (w : B)
    (m n : ℕ) (h : m ≤ n) : q ^ m ∣ approx q σ w m - approx q σ w n := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have h2 : q ^ m ∣ approx q σ w (n + 1) - approx q σ w n :=
      (pow_dvd_pow q hmn).trans (approx_step q σ hq w n)
    have e : approx q σ w m - approx q σ w (n + 1) =
        (approx q σ w m - approx q σ w n) - (approx q σ w (n + 1) - approx q σ w n) := by ring
    rw [e]
    exact dvd_sub ih h2

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.
-/
theorem smodEq_iff {B : Type} [CommRing B] (q : B) (n : ℕ) (x y : B) :
    x ≡ y [SMOD ((Ideal.span {q}) ^ n • ⊤ : Submodule B B)] ↔ q ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

/- English proof (translation)
Take `⟨c, hc⟩` from `h.toIsPrecomplete.prec (f := approx q σ w) fun {m n} hmn => (smodEq_iff q m _ _).mpr (approx_dvd q σ hq w m n hmn)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hd : ∀ n, q ^ n ∣ c - (-w + q * σ c)`. Introduce `n`. Establish `h1 : q ^ n ∣ approx q σ w n - c` using `(smodEq_iff q n _ _).mp (hc n)`.

Establish `h2 : q ^ (n + 1) ∣ approx q σ w (n + 1) - c` using `(smodEq_iff q (n + 1) _ _).mp (hc (n + 1))`. Take `⟨t, ht⟩` from `h1`. Establish `e : c - (-w + q * σ c) = -(approx q σ w (n + 1) - c) + q * σ (approx q σ w n - c)`. Rewrite using `[map_sub]`. Use `show _ = -((-w + q * σ (approx q σ w n)) - c) + q * (σ (approx q σ w n) - σ c)`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ht, map_mul, map_pow, hq]`. Conclude with `dvd_add (dvd_neg.mpr ((pow_dvd_pow q (Nat.le_succ n)).trans h2)) ⟨q * σ t, by ring⟩`. Establish `h0` using `h.toIsHausdorff.haus (c - (-w + q * σ c)) fun n => (smodEq_iff q n _ _).mpr (by simpa using hd n)`. Conclude with `sub_eq_zero.mp h0`.
-/
theorem exists_fixed {B : Type} [inst : CommRing B] (q : B)
    [h : IsAdicComplete (Ideal.span {q}) B] (σ : B →+* B) (hq : σ q = q) (w : B) :
    ∃ c : B, c = -w + q * σ c := by
  obtain ⟨c, hc⟩ := h.toIsPrecomplete.prec (f := approx q σ w) fun {m n} hmn =>
    (smodEq_iff q m _ _).mpr (approx_dvd q σ hq w m n hmn)
  refine ⟨c, ?_⟩
  have hd : ∀ n, q ^ n ∣ c - (-w + q * σ c) := by
    intro n
    have h1 : q ^ n ∣ approx q σ w n - c := (smodEq_iff q n _ _).mp (hc n)
    have h2 : q ^ (n + 1) ∣ approx q σ w (n + 1) - c := (smodEq_iff q (n + 1) _ _).mp (hc (n + 1))
    obtain ⟨t, ht⟩ := h1
    have e : c - (-w + q * σ c) = -(approx q σ w (n + 1) - c) + q * σ (approx q σ w n - c) := by
      rw [map_sub]
      show _ = -((-w + q * σ (approx q σ w n)) - c) + q * (σ (approx q σ w n) - σ c)
      ring
    rw [e, ht, map_mul, map_pow, hq]
    exact dvd_add (dvd_neg.mpr ((pow_dvd_pow q (Nat.le_succ n)).trans h2)) ⟨q * σ t, by ring⟩
  have h0 := h.toIsHausdorff.haus (c - (-w + q * σ c)) fun n =>
    (smodEq_iff q n _ _).mpr (by simpa using hd n)
  exact sub_eq_zero.mp h0

end GlobalTheory.FixedPointApproximation
