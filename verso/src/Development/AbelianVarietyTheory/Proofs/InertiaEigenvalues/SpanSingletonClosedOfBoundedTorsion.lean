import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

namespace GlobalTheory.BSP

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ' _ (k + 1)]`. Use `(Ideal.mul_mono_right ih).trans ?_` and prove the remaining obligations.

Rewrite using `[Ideal.mul_sup, Ideal.sup_mul, Ideal.sup_mul]`. Use `sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_mul_span_singleton, ← pow_succ']`. Conclude with `le_sup_left`. Use `le_sup_of_le_right (Ideal.mul_mono_right ?_)` and prove the remaining obligations.

Rewrite using `[← Ideal.span_singleton_pow]`. Conclude with `Ideal.pow_right_mono le_sup_left _`. Use `le_sup_of_le_right ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, pow_succ' _ k]`. Conclude with `Ideal.mul_mono_right (Ideal.mul_mono_left le_sup_left)`.

Use `le_sup_of_le_right ?_` and prove the remaining obligations. Rewrite using `[pow_succ' _ k]`. Conclude with `Ideal.mul_mono_right (Ideal.mul_mono_left le_sup_right)`.
-/
private theorem span_sup_span_pow_succ_le {A : Type} [CommRing A] (p d : A) (k : ℕ) :
    (Ideal.span {p} ⊔ Ideal.span {d}) ^ (k + 1) ≤
      Ideal.span {p ^ (k + 1)} ⊔ Ideal.span {d} * (Ideal.span {p} ⊔ Ideal.span {d}) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' _ (k + 1)]
    refine (Ideal.mul_mono_right ih).trans ?_
    rw [Ideal.mul_sup, Ideal.sup_mul, Ideal.sup_mul]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    ·
      rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ']
      exact le_sup_left
    ·
      refine le_sup_of_le_right (Ideal.mul_mono_right ?_)
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_right_mono le_sup_left _
    · refine le_sup_of_le_right ?_
      rw [mul_left_comm, pow_succ' _ k]
      exact Ideal.mul_mono_right (Ideal.mul_mono_left le_sup_left)
    · refine le_sup_of_le_right ?_
      rw [pow_succ' _ k]
      exact Ideal.mul_mono_right (Ideal.mul_mono_left le_sup_right)

/- English proof (translation)
Establish `h1` using `span_sup_span_pow_succ_le p d (2 * (n + N + 1) - 1)`. Establish `e : 2 * (n + N + 1) - 1 + 1 = 2 * (n + N + 1)` using `by omega`. Rewrite `h1` using `[e]`. Take `⟨y1, hy1, y2, hy2, hsum⟩` from `Submodule.mem_sup.1 (h1 hz)`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hy1`.

Take `⟨w, hw, rfl⟩` from `Ideal.mem_span_singleton_mul.1 hy2`. Establish `key : p ^ (2 * (n + N + 1)) * a ∈ Ideal.span {d}`. Rewrite using `[Ideal.mem_span_singleton']`. Conclude with `⟨z - w, by linear_combination (-1 : A) * hsum⟩`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 (ht a _ key)`.

Establish `hp : p ^ (2 * (n + N + 1)) = p ^ (2 * (n + N + 1) - N) * p ^ N`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hz' : z = w + p ^ (2 * (n + N + 1) - N) * b`.

Establish `h0 : d * (z - (w + p ^ (2 * (n + N + 1) - N) * b)) = 0`. Take the linear combination `(-1 : A) * hsum + a * hp - p ^ (2 * (n + N + 1) - N) * hb`. Conclude with `sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff hd).1 h0)`. Rewrite using `[hz']`. Use `Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) hw) (Ideal.mul_mem_right _ _ ?_)` and prove the remaining obligations.

Conclude with `Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self p)) _)`.
-/
private theorem div_cont {A : Type} [CommRing A] (p d : A) (N : ℕ) (hd : d ∈ nonZeroDivisors A)
    (ht : ∀ (x : A) (m : ℕ), p ^ m * x ∈ Ideal.span {d} → p ^ N * x ∈ Ideal.span {d})
    (n : ℕ) (z : A) (hz : d * z ∈ (Ideal.span {p} ⊔ Ideal.span {d}) ^ (2 * (n + N + 1))) :
    z ∈ (Ideal.span {p} ⊔ Ideal.span {d}) ^ n := by

  have h1 := span_sup_span_pow_succ_le p d (2 * (n + N + 1) - 1)
  have e : 2 * (n + N + 1) - 1 + 1 = 2 * (n + N + 1) := by omega
  rw [e] at h1
  obtain ⟨y1, hy1, y2, hy2, hsum⟩ := Submodule.mem_sup.1 (h1 hz)
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy1
  obtain ⟨w, hw, rfl⟩ := Ideal.mem_span_singleton_mul.1 hy2

  have key : p ^ (2 * (n + N + 1)) * a ∈ Ideal.span {d} := by
    rw [Ideal.mem_span_singleton']
    exact ⟨z - w, by linear_combination (-1 : A) * hsum⟩
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (ht a _ key)
  have hp : p ^ (2 * (n + N + 1)) = p ^ (2 * (n + N + 1) - N) * p ^ N := by
    rw [← pow_add]; congr 1; omega

  have hz' : z = w + p ^ (2 * (n + N + 1) - N) * b := by
    have h0 : d * (z - (w + p ^ (2 * (n + N + 1) - N) * b)) = 0 := by
      linear_combination (-1 : A) * hsum + a * hp - p ^ (2 * (n + N + 1) - N) * hb
    exact sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff hd).1 h0)
  rw [hz']
  refine Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) hw) (Ideal.mul_mem_right _ _ ?_)
  exact Ideal.pow_le_pow_right (by omega)
    (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self p)) _)

/- English proof (translation)
Establish `hsm : ∀ n : ℕ, ((Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n • ⊤ : Submodule A A) = (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n` using `fun n => by`. Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top]`. Use `choose z hz using hx`. Establish `hcau : ∀ {m k : ℕ}, m ≤ k → z (2 * (m + N + 1)) - z (2 * (k + N + 1)) ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ m`. Introduce `m k hmk`.

Apply `div_cont (l : A) d N hd ht m` to reduce the goal to its premises. Establish `h1` using `hz (2 * (m + N + 1))`. Establish `h2` using `Ideal.pow_le_pow_right (I := Ideal.span {(l : A)} ⊔ Ideal.span {d}) (show 2 * (m + N + 1) ≤ 2 * (k + N + 1) by omega) (hz (2 * (k + N + 1)))`. Establish `e : d * (z (2 * (m + N + 1)) - z (2 * (k + N + 1))) = (x - d * z (2 * (k + N + 1))) - (x - d * z (2 * (m + N + 1)))` using `by ring`. Rewrite using `[e]`.

Conclude with `Ideal.sub_mem _ h2 h1`. Take `⟨L, hL⟩` from `hc.toIsPrecomplete.prec' (fun n => z (2 * (n + N + 1))) (fun {m k} hmk => by rw [SModEq.sub_mem, hsm]; exact hcau hmk)`. Establish `h0 : x - d * L = 0`. Apply `hc.toIsHausdorff.haus'` to reduce the goal to its premises. Introduce `n`.

Rewrite using `[SModEq.sub_mem, sub_zero, hsm]`. Establish `h2 : z (2 * (n + N + 1)) - L ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n`. Establish `h3` using `hL n`. Rewrite `h3` using `[SModEq.sub_mem, hsm]`. Conclude with `h3`.

Establish `e : x - d * L = (x - d * z (2 * (n + N + 1))) + d * (z (2 * (n + N + 1)) - L)` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) (hz _)) (Ideal.mul_mem_left _ _ h2)`. Rewrite using `[sub_eq_zero.1 h0]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self d)`.
-/
theorem span_singleton_closed_of_bounded_torsion (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A]
    (d : A) (N : ℕ) (hd : d ∈ nonZeroDivisors A)
    (ht : ∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d})
    (hc : IsAdicComplete (Ideal.span {(l : A)} ⊔ Ideal.span {d}) A) (x : A)
    (hx : ∀ n : ℕ, ∃ z, x - d * z ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n) :
    x ∈ Ideal.span {d} := by
  have hsm : ∀ n : ℕ, ((Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n • ⊤ : Submodule A A) =
      (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n := fun n => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  choose z hz using hx

  have hcau : ∀ {m k : ℕ}, m ≤ k → z (2 * (m + N + 1)) - z (2 * (k + N + 1)) ∈
      (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ m := by
    intro m k hmk
    apply div_cont (l : A) d N hd ht m
    have h1 := hz (2 * (m + N + 1))
    have h2 := Ideal.pow_le_pow_right (I := Ideal.span {(l : A)} ⊔ Ideal.span {d})
      (show 2 * (m + N + 1) ≤ 2 * (k + N + 1) by omega) (hz (2 * (k + N + 1)))
    have e : d * (z (2 * (m + N + 1)) - z (2 * (k + N + 1))) =
        (x - d * z (2 * (k + N + 1))) - (x - d * z (2 * (m + N + 1))) := by ring
    rw [e]
    exact Ideal.sub_mem _ h2 h1
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec' (fun n => z (2 * (n + N + 1)))
    (fun {m k} hmk => by rw [SModEq.sub_mem, hsm]; exact hcau hmk)

  have h0 : x - d * L = 0 := by
    apply hc.toIsHausdorff.haus'
    intro n
    rw [SModEq.sub_mem, sub_zero, hsm]
    have h2 : z (2 * (n + N + 1)) - L ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n := by
      have h3 := hL n
      rw [SModEq.sub_mem, hsm] at h3
      exact h3
    have e : x - d * L = (x - d * z (2 * (n + N + 1))) + d * (z (2 * (n + N + 1)) - L) := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) (hz _)) (Ideal.mul_mem_left _ _ h2)
  rw [sub_eq_zero.1 h0]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self d)

end GlobalTheory.BSP
