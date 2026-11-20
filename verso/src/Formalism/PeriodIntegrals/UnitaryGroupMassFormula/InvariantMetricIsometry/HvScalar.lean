import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.VnuMapZero

noncomputable section

open Matrix Classical

namespace PI.IsoInvMetricW

open PI.IsoInvMetric

/- English proof (translation)
Introduce `i`. Take `⟨n, hn⟩` from `i`. Proceed by induction on `n with`. Consider the case `zero => exact Nat.zero_le _`. Consider the case `succ n ih`.

Establish `h1` using `ih (by omega)`. Establish `h2 : J ⟨n, by omega⟩ < J ⟨n + 1, hn⟩` using `J.lt_iff_lt.mpr (Fin.mk_lt_mk.mpr (Nat.lt_succ_self n))`. Rewrite `h2` using `[Fin.lt_def]`. Simplify using `only at h1 ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem oe_ge {h N : ℕ} (J : Fin h ↪o Fin N) : ∀ i : Fin h, (i : ℕ) ≤ (J i : ℕ) := by
  intro i
  obtain ⟨n, hn⟩ := i
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 : J ⟨n, by omega⟩ < J ⟨n + 1, hn⟩ :=
      J.lt_iff_lt.mpr (Fin.mk_lt_mk.mpr (Nat.lt_succ_self n))
    rw [Fin.lt_def] at h2
    simp only at h1 ⊢
    omega

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular]`. Both sides reduce to the same expression. Introduce `i j hij`. Simplify using `only [id] at hij`. Simplify using `only [Matrix.of_apply]`.

Apply `hw` to reduce the goal to its premises. Establish `h1` using `oe_ge J i`. Establish `h2` using `Fin.lt_def.mp hij`. Use linear arithmetic over natural numbers and integers.
-/
theorem det_tri {h N : ℕ} (J : Fin h ↪o Fin N) (w : Fin N → ℕ → ℂ)
    (hw : ∀ (a : Fin N) (j : ℕ), j < a → w a j = 0) :
    Matrix.det (Matrix.of fun i j : Fin h => w (J i) (j : ℕ)) = ∏ i : Fin h, w (J i) i := by
  rw [Matrix.det_of_upperTriangular]
  · rfl
  · intro i j hij
    simp only [id] at hij
    simp only [Matrix.of_apply]
    apply hw
    have h1 := oe_ge J i
    have h2 := Fin.lt_def.mp hij
    omega

def dg {Lt : Type} {N : ℕ} (w : Lt → Fin N → ℕ → ℂ) (s : Lt) (i : ℕ) : ℂ :=
  if h : i < N then w s ⟨i, h⟩ i else 0

/- English proof (translation)
Establish `e : hvC N nu w J = ∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), w s (J s c i) i`. Unfold `hvC minY`. Conclude with `Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => det_tri (J s c) (w s) (hw s)`. Rewrite using `[e]`. Use `split_ifs with hstd`.

Use `Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hi : (i : ℕ) < N`. Use `(J s c i).2` as an intermediate fact. Rewrite `this` using `[hstd s c i]`. Conclude with `this`.

Establish `: J s c i = ⟨i, hi⟩` using `Fin.ext (hstd s c i)`. Simplify using `only [dg, hi, dite_true, this]`. Use `push_neg at hstd`. Take `⟨s, c, i, hne⟩` from `hstd`. Apply `Finset.prod_eq_zero (Finset.mem_univ s)` to reduce the goal to its premises.

Apply `Finset.prod_eq_zero (Finset.mem_univ c)` to reduce the goal to its premises. Apply `Finset.prod_eq_zero (Finset.mem_univ i)` to reduce the goal to its premises. Apply `hw` to reduce the goal to its premises. Use `oe_ge (J s c) i` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem hv_tri {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} (nu : Lt → YoungDiagram)
    (w : Lt → Fin N → ℕ → ℂ) (hw : ∀ s (a : Fin N) (j : ℕ), j < a → w s a j = 0)
    (J : ColChoice N nu) :
    hvC N nu w J = if (∀ s c i, (J s c i : ℕ) = i) then
      ∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), dg w s i else 0 := by
  have e : hvC N nu w J =
      ∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), w s (J s c i) i := by
    unfold hvC minY
    exact Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ =>
      det_tri (J s c) (w s) (hw s)
  rw [e]
  split_ifs with hstd
  · refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ =>
      Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℕ) < N := by
      have := (J s c i).2
      rw [hstd s c i] at this
      exact this
    have : J s c i = ⟨i, hi⟩ := Fin.ext (hstd s c i)
    simp only [dg, hi, dite_true, this]
  · push_neg at hstd
    obtain ⟨s, c, i, hne⟩ := hstd
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply hw
    have := oe_ge (J s c) i
    omega

/- English proof (translation)
Establish `h1 : ∀ s (a : Fin N) (j : ℕ), j < a → (fun _ : Lt => colsOf (1 : Matrix (Fin N) (Fin N) ℂ)) s a j = 0`. Introduce `s a j hja`. Simplify using `only [colsOf]`. Use `split_ifs with hj`. Rewrite using `[Matrix.one_apply_ne]`.

Introduce `h`. Rewrite `hja` using `[h]`. Simplify using `at hja`. Both sides reduce to the same expression. Use function extensionality and compare the values at `J`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, u0, hv_tri nu w hw J, hv_tri nu _ h1 J]`. Use `split_ifs with hstd`. Establish `: ∀ s (c : Fin ((nu s).rowLen 0)) (i : Fin ((nu s).colLen c)), dg (fun _ : Lt => colsOf (1 : Matrix (Fin N) (Fin N) ℂ)) s i = 1`. Introduce `s c i`. Establish `hi : (i : ℕ) < N`.

Use `(J s c i).2` as an intermediate fact. Rewrite `this` using `[hstd s c i]`. Conclude with `this`. Simplify using `[dg, hi, colsOf]`. Simplify using `[this]`.

Simplify using the standard rewrite rules.
-/
theorem hv_scalar {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} (nu : Lt → YoungDiagram)
    (w : Lt → Fin N → ℕ → ℂ) (hw : ∀ s (a : Fin N) (j : ℕ), j < a → w s a j = 0) :
    hvC N nu w =
      (∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), dg w s i) • u0 N nu := by
  have h1 : ∀ s (a : Fin N) (j : ℕ), j < a →
      (fun _ : Lt => colsOf (1 : Matrix (Fin N) (Fin N) ℂ)) s a j = 0 := by
    intro s a j hja
    simp only [colsOf]
    split_ifs with hj
    · rw [Matrix.one_apply_ne]
      intro h
      rw [h] at hja
      simp at hja
    · rfl
  funext J
  rw [Pi.smul_apply, smul_eq_mul, u0, hv_tri nu w hw J, hv_tri nu _ h1 J]
  split_ifs with hstd
  · have : ∀ s (c : Fin ((nu s).rowLen 0)) (i : Fin ((nu s).colLen c)),
        dg (fun _ : Lt => colsOf (1 : Matrix (Fin N) (Fin N) ℂ)) s i = 1 := by
      intro s c i
      have hi : (i : ℕ) < N := by
        have := (J s c i).2
        rw [hstd s c i] at this
        exact this
      simp [dg, hi, colsOf]
    simp [this]
  · simp

/- English proof (translation)
Introduce `Lt _ _ N nu x`. Establish `hq` using `fun s => hQ N (Matrix.of fun a (j : Fin N) => x s a j)`. Use `choose k hk htri using hq`. Use `⟨k, hk, ?_⟩` and prove the remaining obligations. Set `y` to `fr (fun s => star (k s)) x`.

Establish `hxy : x = fr k y`. Use function extensionality and compare the values at `s a j`. Establish `hkk : k s * star (k s) = 1` using `Matrix.mem_unitaryGroup_iff.mp (hk s)`. Use `show x s a j = ∑ b, k s a b * ∑ c, star (k s) b c * x s c j`. Simplify using `only [Finset.mul_sum, ← mul_assoc]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_mul]`. Establish `: ∀ c, ∑ b, k s a b * star (k s) b c = if a = c then 1 else 0` using `fun c => by`. Rewrite using `[← Matrix.one_apply, ← hkk, Matrix.mul_apply]`. Simplify using `only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Establish `ytri : ∀ s (a : Fin N) (j : ℕ), j < a → y s a j = 0`. Introduce `s a j hja`. Establish `hjN : j < N` using `lt_trans hja a.2`. Use `htri s a ⟨j, hjN⟩ (Fin.lt_def.mpr hja)` as an intermediate fact. Simplify `this` using `[y, fr, Matrix.mul_apply]`.

Use `⟨∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), dg y s i, ?_⟩` and prove the remaining obligations. Rewrite using `[hxy, ← hM Lt N nu k y, hv_scalar nu y ytri, vnuMap_smul, ← hvCols_of hM Lt N nu k]`.
-/
theorem gen_of (hQ : QR) (hM : HvMap) : Gen := by
  intro Lt _ _ N nu x
  have hq := fun s => hQ N (Matrix.of fun a (j : Fin N) => x s a j)
  choose k hk htri using hq
  refine ⟨k, hk, ?_⟩
  let y := fr (fun s => star (k s)) x
  have hxy : x = fr k y := by
    funext s a j
    have hkk : k s * star (k s) = 1 := Matrix.mem_unitaryGroup_iff.mp (hk s)
    show x s a j = ∑ b, k s a b * ∑ c, star (k s) b c * x s c j
    simp only [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    have : ∀ c, ∑ b, k s a b * star (k s) b c = if a = c then 1 else 0 := fun c => by
      rw [← Matrix.one_apply, ← hkk, Matrix.mul_apply]
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have ytri : ∀ s (a : Fin N) (j : ℕ), j < a → y s a j = 0 := by
    intro s a j hja
    have hjN : j < N := lt_trans hja a.2
    have := htri s a ⟨j, hjN⟩ (Fin.lt_def.mpr hja)
    simpa [y, fr, Matrix.mul_apply] using this
  refine ⟨∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), dg y s i, ?_⟩
  rw [hxy, ← hM Lt N nu k y, hv_scalar nu y ytri, vnuMap_smul, ← hvCols_of hM Lt N nu k]

end PI.IsoInvMetricW
