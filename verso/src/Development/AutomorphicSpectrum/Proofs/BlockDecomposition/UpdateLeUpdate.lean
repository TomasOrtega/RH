import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape

noncomputable section

open Polynomial
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open PositivityTheory.Rg.Rs.An

namespace GlobalTheory.CompanionTheory.AnBoot

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Unfold `sr`. Rewrite using `[dif_neg h]`.
-/
theorem sr_eq_zero (x : Fin n → ℝ) {r : ℕ} (h : ¬ (0 < r ∧ r < n)) : sr x r = 0 := by
  unfold sr
  rw [dif_neg h]

/- English proof (translation)
Introduce `ω hω hB t₀ Q hQ`. Take `⟨C, hC⟩` from `h ω hω hB t₀ Q hQ`. Use `⟨max C 0 * Real.exp (∑ r ∈ Finset.range n, (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)), ?_⟩` and prove the remaining obligations. Introduce `b hb x hx q hq`. Establish `h1` using `hC b hb x hx q hq`.

Establish `hs : ∑ r ∈ Finset.range n, m r * sr x r ≤ (∑ r ∈ Finset.range n, (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) + ∑ r ∈ Finset.range n, m' r * sr x r`. Rewrite using `[← Finset.sum_add_distrib]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `r _`. Distinguish the cases in `hr : 0 < r ∧ r < n`.

Rewrite using `[if_pos hr]`. Use `mul_le_mul_of_nonneg_left (hx r) (sub_nonneg.2 (hm r hr.1 hr.2))` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[if_neg hr, sr_eq_zero x hr]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.exp_add, mul_assoc]`.
-/
theorem bnd_mono {φ : AdelicGLn.AdelicGL K n → ℂ} {m m' : ℕ → ℝ}
    (hm : ∀ r, 0 < r → r < n → m r ≤ m' r) (h : Bnd φ m) : Bnd φ m' := by
  intro ω hω hB t₀ Q hQ
  obtain ⟨C, hC⟩ := h ω hω hB t₀ Q hQ
  refine ⟨max C 0 * Real.exp (∑ r ∈ Finset.range n,
    (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)), ?_⟩
  intro b hb x hx q hq
  have h1 := hC b hb x hx q hq
  have hs : ∑ r ∈ Finset.range n, m r * sr x r ≤
      (∑ r ∈ Finset.range n, (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) +
        ∑ r ∈ Finset.range n, m' r * sr x r := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    by_cases hr : 0 < r ∧ r < n
    · rw [if_pos hr]
      have := mul_le_mul_of_nonneg_left (hx r) (sub_nonneg.2 (hm r hr.1 hr.2))
      nlinarith
    · rw [if_neg hr, sr_eq_zero x hr]
      simp
  calc ‖φ (b * tor K x * q)‖ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) := h1
    _ ≤ max C 0 * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp ((∑ r ∈ Finset.range n,
          (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) +
            ∑ r ∈ Finset.range n, m' r * sr x r) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hs) (le_max_right _ _)
    _ = max C 0 * Real.exp (∑ r ∈ Finset.range n,
          (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) *
            Real.exp (∑ r ∈ Finset.range n, m' r * sr x r) := by
        rw [Real.exp_add, mul_assoc]

/- English proof (translation)
Introduce `ω hω hB t₀ Q hQ`. Take `⟨C, hC⟩` from `hf ω hω hB t₀ Q hQ`. Take `⟨D, hD⟩` from `hg ω hω hB t₀ Q hQ`. Use `⟨C + D, fun b hb x hx q hq => ?_⟩` and prove the remaining obligations. Establish `h1` using `hC b hb x hx q hq`.

Establish `h2` using `hD b hb x hx q hq`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem bnd_add {f g : AdelicGLn.AdelicGL K n → ℂ} {m : ℕ → ℝ} (hf : Bnd f m) (hg : Bnd g m) :
    Bnd (fun y => f y + g y) m := by
  intro ω hω hB t₀ Q hQ
  obtain ⟨C, hC⟩ := hf ω hω hB t₀ Q hQ
  obtain ⟨D, hD⟩ := hg ω hω hB t₀ Q hQ
  refine ⟨C + D, fun b hb x hx q hq => ?_⟩
  have h1 := hC b hb x hx q hq
  have h2 := hD b hb x hx q hq
  calc ‖f (b * tor K x * q) + g (b * tor K x * q)‖
      ≤ ‖f (b * tor K x * q)‖ + ‖g (b * tor K x * q)‖ := norm_add_le _ _
    _ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) +
          D * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) := add_le_add h1 h2
    _ = (C + D) * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) := by ring

/- English proof (translation)
Distinguish the cases in `hs : s = r`. Substitute `hs` using the available equality. Simplify using `using h`. Simplify using `[Function.update_of_ne hs]`.
-/
theorem update_le_update (m : ℕ → ℝ) (r : ℕ) {a b : ℝ} (h : a ≤ b) (s : ℕ) :
    Function.update m r a s ≤ Function.update m r b s := by
  by_cases hs : s = r
  · subst hs
    simpa using h
  · simp [Function.update_of_ne hs]

/- English proof (translation)
Establish `a : Bnd (fun g => φ g - ctn r φ g) (Function.update m r (max (m r - 1) κ))` using `bnd_mono (fun s _ _ => update_le_update m r (le_max_left _ _) s) (hD K n φ m r h0 h1 hφ h)`. Establish `b : Bnd (ctn r φ) (Function.update m r (max (m r - 1) κ))` using `bnd_mono (fun s _ _ => update_le_update m r (le_max_right _ _) s) (hC K n φ m r p κ h0 h1 hφ h hp hk hz)`. Establish `c` using `bnd_add a b`. Simplify using `using c`.
-/
theorem bnd_step (hD : DiffStep) (hC : CtStep) {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Nice φ)
    {r : ℕ} (h0 : 0 < r) (h1 : r < n) {p : ℂ[X]} {κ : ℝ} (hp : p.Monic) (hk : Kill r φ p)
    (hz : ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) {m : ℕ → ℝ} (h : Bnd φ m) :
    Bnd φ (Function.update m r (max (m r - 1) κ)) := by
  have a : Bnd (fun g => φ g - ctn r φ g) (Function.update m r (max (m r - 1) κ)) :=
    bnd_mono (fun s _ _ => update_le_update m r (le_max_left _ _) s) (hD K n φ m r h0 h1 hφ h)
  have b : Bnd (ctn r φ) (Function.update m r (max (m r - 1) κ)) :=
    bnd_mono (fun s _ _ => update_le_update m r (le_max_right _ _) s)
      (hC K n φ m r p κ h0 h1 hφ h hp hk hz)
  have c := bnd_add a b
  simpa using c

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Use `bnd_mono (fun s _ _ => ?_) h` and prove the remaining obligations. Distinguish the cases in `hs : s = r`. Substitute `hs` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hs]`. Consider the case `succ k ih`. Use `bnd_step hD hC hφ h0 h1 hp hk hz ih` as an intermediate fact. Rewrite `this` using `[Function.update_self, Function.update_idem]`.

Use `bnd_mono (fun s _ _ => update_le_update m r ?_ s) this` and prove the remaining obligations. Use `push_cast`. Use `max_le ?_ (le_max_right _ _)` and prove the remaining obligations. Break down `le_total (m r - k) κ with h' | h'` into its components or cases. Rewrite using `[max_eq_right h']`.

Conclude with `le_trans (by linarith) (le_max_right _ _)`. Rewrite using `[max_eq_left h']`. Conclude with `le_trans (by linarith) (le_max_left _ _)`.
-/
theorem bnd_iter (hD : DiffStep) (hC : CtStep) {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Nice φ)
    {r : ℕ} (h0 : 0 < r) (h1 : r < n) {p : ℂ[X]} {κ : ℝ} (hp : p.Monic) (hk : Kill r φ p)
    (hz : ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) {m : ℕ → ℝ} (h : Bnd φ m) (k : ℕ) :
    Bnd φ (Function.update m r (max (m r - k) κ)) := by
  induction k with
  | zero =>
    refine bnd_mono (fun s _ _ => ?_) h
    by_cases hs : s = r
    · subst hs
      simp
    · simp [Function.update_of_ne hs]
  | succ k ih =>
    have := bnd_step hD hC hφ h0 h1 hp hk hz ih
    rw [Function.update_self, Function.update_idem] at this
    refine bnd_mono (fun s _ _ => update_le_update m r ?_ s) this
    push_cast
    refine max_le ?_ (le_max_right _ _)
    rcases le_total (m r - k) κ with h' | h'
    · rw [max_eq_right h']
      exact le_trans (by linarith) (le_max_right _ _)
    · rw [max_eq_left h']
      exact le_trans (by linarith) (le_max_left _ _)

/- English proof (translation)
Take `⟨k, hk'⟩` from `exists_nat_ge (m r - κ)`. Use `bnd_iter hD hC hφ h0 h1 hp hk hz h k` as an intermediate fact. Rewrite `this` using `[max_eq_right (by linarith)]`. Then use the resulting hypothesis.
-/
theorem bnd_one (hD : DiffStep) (hC : CtStep) {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Nice φ)
    {r : ℕ} (h0 : 0 < r) (h1 : r < n) {p : ℂ[X]} {κ : ℝ} (hp : p.Monic) (hk : Kill r φ p)
    (hz : ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) {m : ℕ → ℝ} (h : Bnd φ m) :
    Bnd φ (Function.update m r κ) := by
  obtain ⟨k, hk'⟩ := exists_nat_ge (m r - κ)
  have := bnd_iter hD hC hφ h0 h1 hp hk hz h k
  rwa [max_eq_right (by linarith)] at this

/- English proof (translation)
Introduce `hD hC K _ _ n φ M κ hφ hM hp`. Establish `key : ∀ s : Finset ℕ, (∀ r ∈ s, 0 < r ∧ r < n) → Bnd φ (fun r => if r ∈ s then κ r else M)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Introduce `_`. Simplify using `using hM`. Consider the case `insert a s ha ih`. Introduce `hs`. Establish `h'` using `ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))`.

Take `⟨h0, h1⟩` from `hs a (Finset.mem_insert_self a s)`. Take `⟨p, hpm, hpk, hpz⟩` from `hp a h0 h1`. Use `bnd_one hD hC hφ h0 h1 hpm hpk hpz h'` as an intermediate fact. Use `bnd_mono (fun r _ _ => le_of_eq ?_) this` and prove the remaining obligations. Distinguish the cases in `hr : r = a`.

Substitute `hr` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hr, Finset.mem_insert, hr]`. Use `bnd_mono (fun r h0 h1 => le_of_eq ?_) (key (Finset.Ioo 0 n) (fun r hr => Finset.mem_Ioo.1 hr))` and prove the remaining obligations. Simplify using `[h0, h1]`.
-/
theorem bootGlue : BootGlue := by
  intro hD hC K _ _ n φ M κ hφ hM hp
  have key : ∀ s : Finset ℕ, (∀ r ∈ s, 0 < r ∧ r < n) →
      Bnd φ (fun r => if r ∈ s then κ r else M) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using hM
    | insert a s ha ih =>
      intro hs
      have h' := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
      obtain ⟨h0, h1⟩ := hs a (Finset.mem_insert_self a s)
      obtain ⟨p, hpm, hpk, hpz⟩ := hp a h0 h1
      have := bnd_one hD hC hφ h0 h1 hpm hpk hpz h'
      refine bnd_mono (fun r _ _ => le_of_eq ?_) this
      by_cases hr : r = a
      · subst hr
        simp
      · simp [Function.update_of_ne hr, Finset.mem_insert, hr]
  refine bnd_mono (fun r h0 h1 => le_of_eq ?_) (key (Finset.Ioo 0 n) (fun r hr => Finset.mem_Ioo.1 hr))
  simp [h0, h1]

end GlobalTheory.CompanionTheory.AnBoot

end
