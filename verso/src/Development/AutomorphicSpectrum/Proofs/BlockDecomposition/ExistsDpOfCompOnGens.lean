import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIdealLifts.NilpotentDividedPowerTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersOfGenerators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowerEvalTwoVarsRingHom

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA PositivityTheory.JLift

namespace GlobalTheory.CompanionTheory.JLiftDP

section Comp

open MvPolynomial Finset

def dpBas2 (p : ℕ × ℕ) : MvPolynomial (Fin 2) ℚ :=
  ((p.1.factorial : ℚ)⁻¹ • X 0 ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • X 1 ^ p.2)

/- English proof (translation)
Use `h.mul n 0 0 J.zero_mem` as an intermediate fact. Rewrite `this` using `[mul_zero, zero_pow hn, zero_mul]`. Then use the resulting hypothesis.
-/
theorem preDP_eval_zero {B : Type} [CommRing B] {J : Ideal B} {γ : ℕ → B → B} (h : IsPreDP J γ)
    {n : ℕ} (hn : n ≠ 0) : γ n 0 = 0 := by
  have := h.mul n 0 0 J.zero_mem
  rwa [mul_zero, zero_pow hn, zero_mul] at this

/- English proof (translation)
Use `set D := Submodule.span ℤ (Set.range dpBas2) with hD`. Take `⟨φ, hφb, hφ2, hφz⟩ : ∃ φ : MvPolynomial (Fin 2) ℚ → B, (∀ a c : ℕ, φ (dpBas2 (a, c)) = γ a x * γ c y) ∧ (∀ d ∈ D, ∀ e ∈ D, φ (d + e) = φ d + φ e ∧ d * e ∈ D ∧ φ (d * e) = φ d * φ e) ∧ (∀ z : ℤ, ∀ d ∈ D, φ (z • d) = z • φ d)` from `GlobalTheory.dpEval_two B (fun a ↦ γ a x) (fun c ↦ γ c y) (h.zero x hx) (h.zero y hy) (fun a b ↦ h.mul_dpow a b x hx) (fun a b ↦ h.mul_dpow a b y hy)`. Set `Γ : DividedPowers (⊤ : Ideal (MvPolynomial (Fin 2) ℚ))` to `RatAlgebra.dividedPowers ⊤`. Establish `top : ∀ q : MvPolynomial (Fin 2) ℚ, q ∈ (⊤ : Ideal _)` using `fun _ ↦ Submodule.mem_top`. Establish `hΓ : ∀ (k : ℕ) (q : MvPolynomial (Fin 2) ℚ), Γ.dpow k q = (k.factorial : ℚ)⁻¹ • q ^ k` using `fun k q ↦ by`.

Rewrite using `[RatAlgebra.dpow_eq_inv_fact_smul _ Γ (top q), Ring.inverse_eq_inv']`. Establish `hbasΓ : ∀ p : ℕ × ℕ, dpBas2 p = Γ.dpow p.1 (X 0) * Γ.dpow p.2 (X 1)` using `fun p ↦ by`. Rewrite using `[dpBas2, hΓ, hΓ]`. Establish `hX0 : ∀ a, Γ.dpow a (X 0) = dpBas2 (a, 0)` using `fun a ↦ by`. Rewrite using `[hbasΓ, Γ.dpow_zero (top _), mul_one]`.

Establish `hX1 : ∀ c, Γ.dpow c (X 1) = dpBas2 (0, c)` using `fun c ↦ by`. Rewrite using `[hbasΓ, Γ.dpow_zero (top _), one_mul]`. Establish `hbasΓ' : ∀ a c, dpBas2 (a, c) = Γ.dpow a (X 0) * Γ.dpow c (X 1)` using `fun a c ↦ hbasΓ (a, c)`. Establish `hDb : ∀ p, dpBas2 p ∈ D` using `fun p ↦ Submodule.subset_span ⟨p, rfl⟩`. Establish `hone : dpBas2 (0, 0) = 1` using `by simp [dpBas2]`.

Establish `hφ1 : φ 1 = 1` using `by rw [← hone, hφb, h.zero x hx, h.zero y hy, one_mul]`. Establish `hD1 : (1 : MvPolynomial (Fin 2) ℚ) ∈ D` using `hone ▸ hDb _`. Establish `hφ0 : φ 0 = 0`. Use `(hφ2 0 D.zero_mem 0 D.zero_mem).1` as an intermediate fact. Rewrite `this` using `[add_zero]`.

Conclude with `left_eq_add.mp this`. Establish `hpow : ∀ d ∈ D, ∀ k : ℕ, d ^ k ∈ D ∧ φ (d ^ k) = φ d ^ k`. Introduce `d hd k`. Proceed by induction on `k with`. Consider the case `zero => simpa using ⟨hD1, hφ1⟩`.

Consider the case `succ k ih`. Take `⟨_, h2, h3⟩` from `hφ2 _ ih.1 d hd`. Rewrite using `[pow_succ, pow_succ, h3, ih.2]`. Conclude with `⟨h2, rfl⟩`. Establish `hsum : ∀ (t : Finset (ℕ × ℕ)) (f : ℕ × ℕ → MvPolynomial (Fin 2) ℚ), (∀ i ∈ t, f i ∈ D) → (∑ i ∈ t, f i) ∈ D ∧ φ (∑ i ∈ t, f i) = ∑ i ∈ t, φ (f i)`.

Introduce `t f hf`. Proceed by induction on `t using Finset.induction with`. Consider the case `empty => simp [hφ0]`. Consider the case `insert i t hi ih`. Establish `ih'` using `ih fun j hj ↦ hf j (mem_insert_of_mem hj)`.

Establish `hfi` using `hf i (mem_insert_self i t)`. Rewrite using `[sum_insert hi, sum_insert hi, (hφ2 _ hfi _ ih'.1).1, ih'.2]`. Conclude with `⟨add_mem hfi ih'.1, rfl⟩`. Establish `hnat : ∀ (N : ℕ), ∀ d ∈ D, (N : MvPolynomial (Fin 2) ℚ) * d ∈ D ∧ φ ((N : MvPolynomial (Fin 2) ℚ) * d) = N * φ d`. Introduce `N d hd`.

Establish `e1 : (N : MvPolynomial (Fin 2) ℚ) * d = (N : ℤ) • d` using `by rw [zsmul_eq_mul, Int.cast_natCast]`. Use `⟨by rw [e1]; exact Submodule.smul_mem _ _ hd, ?_⟩` and prove the remaining obligations. Rewrite using `[e1, hφz _ _ hd, zsmul_eq_mul, Int.cast_natCast]`. Establish `hsX : ∀ N : ℕ, Γ.dpow N (X 0 + X 1) ∈ D ∧ φ (Γ.dpow N (X 0 + X 1)) = γ N (x + y)`. Introduce `N`.

Establish `e1 : Γ.dpow N (X 0 + X 1) = ∑ p ∈ antidiagonal N, dpBas2 p`. Rewrite using `[Γ.dpow_add (top _) (top _)]`. Conclude with `sum_congr rfl fun p _ ↦ (hbasΓ p).symm`. Rewrite using `[e1, (hsum _ _ fun p _ ↦ hDb p).2, h.add N x hx y hy]`. Conclude with `⟨(hsum _ _ fun p _ ↦ hDb p).1, sum_congr rfl fun p _ ↦ hφb p.1 p.2⟩`.

Use `set Dp := Submodule.span ℤ (dpBas2 '' {p | p ≠ 0}) with hDp`. Establish `T : ∀ d ∈ Dp, d ∈ D ∧ φ d ∈ J ∧ ∀ k, Γ.dpow k d ∈ D ∧ γ k (φ d) = φ (Γ.dpow k d)`. Introduce `d hd`. Proceed by induction on `hd using Submodule.span_induction with`. Consider the case `mem d hd`.

Take `⟨⟨a, c⟩, hac, rfl⟩` from `hd`. Use `⟨hDb _, ?_, fun k ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[hφb]`. Distinguish the cases in `ha : a = 0`. Establish `hc : c ≠ 0` using `by rintro rfl; exact hac (by simp [ha])`.

Conclude with `J.mul_mem_left _ (h.mem c hc y hy)`. Conclude with `J.mul_mem_right _ (h.mem a ha x hx)`. Use `show Γ.dpow k (dpBas2 (a, c)) ∈ D ∧ γ k (φ (dpBas2 (a, c))) = φ (Γ.dpow k (dpBas2 (a, c)))`. Rewrite using `[hφb a c]`. Distinguish the cases in `ha : a = 0`.

Substitute `ha` using the available equality. Establish `hc : c ≠ 0` using `by rintro rfl; exact hac rfl`. Establish `e : Γ.dpow k (dpBas2 (0, c)) = ((k.uniformBell c : ℕ) : MvPolynomial (Fin 2) ℚ) * dpBas2 (0, k * c)`. Rewrite using `[← hX1 c, Γ.dpow_comp hc (top _), hX1 (k * c)]`. Take `⟨h1, h2⟩` from `hnat (k.uniformBell c) _ (hDb (0, k * c))`.

Rewrite using `[e]`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, hφb, h.zero x hx, one_mul, one_mul, Py k c hc]`. Establish `e : Γ.dpow k (dpBas2 (a, c)) = ((k.uniformBell a : ℕ) : MvPolynomial (Fin 2) ℚ) * dpBas2 (k * a, 0) * dpBas2 (0, c) ^ k`. Rewrite using `[hbasΓ' a c, Γ.dpow_mul_right (top _), Γ.dpow_comp ha (top _), hX0 (k * a), hX1 c]`.

Take `⟨h1, h2⟩` from `hnat (k.uniformBell a) _ (hDb (k * a, 0))`. Take `⟨h3, h4⟩` from `hpow _ (hDb (0, c)) k`. Take `⟨_, h5, h6⟩` from `hφ2 _ h1 _ h3`. Rewrite using `[e]`. Use `⟨h5, ?_⟩` and prove the remaining obligations.

Rewrite using `[h6, h2, h4, hφb, hφb, h.zero x hx, h.zero y hy, mul_comm (γ a x), h.mul k _ _ (h.mem a ha x hx), Px k a ha]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero`. Use `⟨D.zero_mem, hφ0 ▸ J.zero_mem, fun k ↦ ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : k = 0`.

Substitute `hk` using the available equality. Rewrite using `[Γ.dpow_zero (top _), hφ0, h.zero 0 J.zero_mem, hφ1]`. Conclude with `⟨hD1, rfl⟩`. Rewrite using `[Γ.dpow_eval_zero hk, hφ0, preDP_eval_zero h hk]`. Conclude with `⟨D.zero_mem, rfl⟩`.

Consider the case `add d e _ _ hd he`. Take `⟨dD, dJ, dk⟩` from `hd`. Take `⟨eD, eJ, ek⟩` from `he`. Take `⟨hde, -, -⟩` from `hφ2 d dD e eD`. Use `⟨add_mem dD eD, hde ▸ add_mem dJ eJ, fun k ↦ ?_⟩` and prove the remaining obligations.

Establish `hm : ∀ p ∈ antidiagonal k, Γ.dpow p.1 d * Γ.dpow p.2 e ∈ D` using `fun p _ ↦ (hφ2 _ (dk p.1).1 _ (ek p.2).1).2.1`. Rewrite using `[Γ.dpow_add (top _) (top _), hde, h.add k _ dJ _ eJ, (hsum _ _ hm).2]`. Use `⟨(hsum _ _ hm).1, sum_congr rfl fun p _ ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[(dk p.1).2, (ek p.2).2, (hφ2 _ (dk p.1).1 _ (ek p.2).1).2.2]`. Consider the case `smul z d _ hd`.

Take `⟨dD, dJ, dk⟩` from `hd`. Use `⟨Submodule.smul_mem _ _ dD, (hφz z d dD) ▸ zsmul_mem dJ z, fun k ↦ ?_⟩` and prove the remaining obligations. Establish `e1 : Γ.dpow k (z • d) = (z ^ k) • Γ.dpow k d`. Rewrite using `[zsmul_eq_mul, Γ.dpow_mul (top _), zsmul_eq_mul, Int.cast_pow]`. Use `⟨by rw [e1]; exact Submodule.smul_mem _ _ (dk k).1, ?_⟩` and prove the remaining obligations.

Rewrite using `[e1, hφz _ _ dD, hφz _ _ (dk k).1, zsmul_eq_mul, h.mul k _ _ dJ, (dk k).2, zsmul_eq_mul, Int.cast_pow]`. Establish `hmem : Γ.dpow n (X 0 + X 1) ∈ Dp`. Rewrite using `[Γ.dpow_add (top _) (top _)]`. Use `Submodule.sum_mem _ fun p hp ↦ ?_` and prove the remaining obligations. Rewrite using `[← hbasΓ]`.

Use `Submodule.subset_span ⟨p, fun h0 ↦ hn ?_, rfl⟩` and prove the remaining obligations. Rewrite `hp` using `[HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[← hp, h0]`. Both sides reduce to the same expression. Take `⟨_, _, hk⟩` from `T _ hmem`.

Rewrite using `[← (hsX n).2, (hk m).2, Γ.dpow_comp hn (top _), (hnat _ _ (hsX _).1).2, (hsX _).2]`.
-/
theorem preDP_comp_add {B : Type} [CommRing B] {J : Ideal B} {γ : ℕ → B → B} (h : IsPreDP J γ)
    {x y : B} (hx : x ∈ J) (hy : y ∈ J)
    (Px : ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x)
    (Py : ∀ m n : ℕ, n ≠ 0 → γ m (γ n y) = (m.uniformBell n : B) * γ (m * n) y)
    (m n : ℕ) (hn : n ≠ 0) : γ m (γ n (x + y)) = (m.uniformBell n : B) * γ (m * n) (x + y) := by
  classical
  set D := Submodule.span ℤ (Set.range dpBas2) with hD
  obtain ⟨φ, hφb, hφ2, hφz⟩ : ∃ φ : MvPolynomial (Fin 2) ℚ → B,
      (∀ a c : ℕ, φ (dpBas2 (a, c)) = γ a x * γ c y) ∧
      (∀ d ∈ D, ∀ e ∈ D, φ (d + e) = φ d + φ e ∧ d * e ∈ D ∧ φ (d * e) = φ d * φ e) ∧
      (∀ z : ℤ, ∀ d ∈ D, φ (z • d) = z • φ d) :=
    GlobalTheory.dpEval_two B (fun a ↦ γ a x) (fun c ↦ γ c y) (h.zero x hx) (h.zero y hy)
      (fun a b ↦ h.mul_dpow a b x hx) (fun a b ↦ h.mul_dpow a b y hy)
  let Γ : DividedPowers (⊤ : Ideal (MvPolynomial (Fin 2) ℚ)) := RatAlgebra.dividedPowers ⊤
  have top : ∀ q : MvPolynomial (Fin 2) ℚ, q ∈ (⊤ : Ideal _) := fun _ ↦ Submodule.mem_top
  have hΓ : ∀ (k : ℕ) (q : MvPolynomial (Fin 2) ℚ), Γ.dpow k q = (k.factorial : ℚ)⁻¹ • q ^ k := fun k q ↦ by
    rw [RatAlgebra.dpow_eq_inv_fact_smul _ Γ (top q), Ring.inverse_eq_inv']
  have hbasΓ : ∀ p : ℕ × ℕ, dpBas2 p = Γ.dpow p.1 (X 0) * Γ.dpow p.2 (X 1) := fun p ↦ by
    rw [dpBas2, hΓ, hΓ]
  have hX0 : ∀ a, Γ.dpow a (X 0) = dpBas2 (a, 0) := fun a ↦ by
    rw [hbasΓ, Γ.dpow_zero (top _), mul_one]
  have hX1 : ∀ c, Γ.dpow c (X 1) = dpBas2 (0, c) := fun c ↦ by
    rw [hbasΓ, Γ.dpow_zero (top _), one_mul]
  have hbasΓ' : ∀ a c, dpBas2 (a, c) = Γ.dpow a (X 0) * Γ.dpow c (X 1) := fun a c ↦ hbasΓ (a, c)
  have hDb : ∀ p, dpBas2 p ∈ D := fun p ↦ Submodule.subset_span ⟨p, rfl⟩
  have hone : dpBas2 (0, 0) = 1 := by simp [dpBas2]
  have hφ1 : φ 1 = 1 := by rw [← hone, hφb, h.zero x hx, h.zero y hy, one_mul]
  have hD1 : (1 : MvPolynomial (Fin 2) ℚ) ∈ D := hone ▸ hDb _
  have hφ0 : φ 0 = 0 := by
    have := (hφ2 0 D.zero_mem 0 D.zero_mem).1
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hpow : ∀ d ∈ D, ∀ k : ℕ, d ^ k ∈ D ∧ φ (d ^ k) = φ d ^ k := by
    intro d hd k
    induction k with
    | zero => simpa using ⟨hD1, hφ1⟩
    | succ k ih =>
      obtain ⟨_, h2, h3⟩ := hφ2 _ ih.1 d hd
      rw [pow_succ, pow_succ, h3, ih.2]
      exact ⟨h2, rfl⟩
  have hsum : ∀ (t : Finset (ℕ × ℕ)) (f : ℕ × ℕ → MvPolynomial (Fin 2) ℚ), (∀ i ∈ t, f i ∈ D) →
      (∑ i ∈ t, f i) ∈ D ∧ φ (∑ i ∈ t, f i) = ∑ i ∈ t, φ (f i) := by
    intro t f hf
    induction t using Finset.induction with
    | empty => simp [hφ0]
    | insert i t hi ih =>
      have ih' := ih fun j hj ↦ hf j (mem_insert_of_mem hj)
      have hfi := hf i (mem_insert_self i t)
      rw [sum_insert hi, sum_insert hi, (hφ2 _ hfi _ ih'.1).1, ih'.2]
      exact ⟨add_mem hfi ih'.1, rfl⟩
  have hnat : ∀ (N : ℕ), ∀ d ∈ D, (N : MvPolynomial (Fin 2) ℚ) * d ∈ D ∧ φ ((N : MvPolynomial (Fin 2) ℚ) * d) = N * φ d := by
    intro N d hd
    have e1 : (N : MvPolynomial (Fin 2) ℚ) * d = (N : ℤ) • d := by rw [zsmul_eq_mul, Int.cast_natCast]
    refine ⟨by rw [e1]; exact Submodule.smul_mem _ _ hd, ?_⟩
    rw [e1, hφz _ _ hd, zsmul_eq_mul, Int.cast_natCast]
  have hsX : ∀ N : ℕ, Γ.dpow N (X 0 + X 1) ∈ D ∧ φ (Γ.dpow N (X 0 + X 1)) = γ N (x + y) := by
    intro N
    have e1 : Γ.dpow N (X 0 + X 1) = ∑ p ∈ antidiagonal N, dpBas2 p := by
      rw [Γ.dpow_add (top _) (top _)]
      exact sum_congr rfl fun p _ ↦ (hbasΓ p).symm
    rw [e1, (hsum _ _ fun p _ ↦ hDb p).2, h.add N x hx y hy]
    exact ⟨(hsum _ _ fun p _ ↦ hDb p).1, sum_congr rfl fun p _ ↦ hφb p.1 p.2⟩
  set Dp := Submodule.span ℤ (dpBas2 '' {p | p ≠ 0}) with hDp
  have T : ∀ d ∈ Dp, d ∈ D ∧ φ d ∈ J ∧ ∀ k, Γ.dpow k d ∈ D ∧ γ k (φ d) = φ (Γ.dpow k d) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨⟨a, c⟩, hac, rfl⟩ := hd
      refine ⟨hDb _, ?_, fun k ↦ ?_⟩
      · rw [hφb]
        by_cases ha : a = 0
        · have hc : c ≠ 0 := by rintro rfl; exact hac (by simp [ha])
          exact J.mul_mem_left _ (h.mem c hc y hy)
        · exact J.mul_mem_right _ (h.mem a ha x hx)
      show Γ.dpow k (dpBas2 (a, c)) ∈ D ∧ γ k (φ (dpBas2 (a, c))) = φ (Γ.dpow k (dpBas2 (a, c)))
      rw [hφb a c]
      by_cases ha : a = 0
      · subst ha
        have hc : c ≠ 0 := by rintro rfl; exact hac rfl
        have e : Γ.dpow k (dpBas2 (0, c)) = ((k.uniformBell c : ℕ) : MvPolynomial (Fin 2) ℚ) * dpBas2 (0, k * c) := by
          rw [← hX1 c, Γ.dpow_comp hc (top _), hX1 (k * c)]
        obtain ⟨h1, h2⟩ := hnat (k.uniformBell c) _ (hDb (0, k * c))
        rw [e]
        refine ⟨h1, ?_⟩
        rw [h2, hφb, h.zero x hx, one_mul, one_mul, Py k c hc]
      · have e : Γ.dpow k (dpBas2 (a, c)) =
            ((k.uniformBell a : ℕ) : MvPolynomial (Fin 2) ℚ) * dpBas2 (k * a, 0) * dpBas2 (0, c) ^ k := by
          rw [hbasΓ' a c, Γ.dpow_mul_right (top _), Γ.dpow_comp ha (top _), hX0 (k * a), hX1 c]
        obtain ⟨h1, h2⟩ := hnat (k.uniformBell a) _ (hDb (k * a, 0))
        obtain ⟨h3, h4⟩ := hpow _ (hDb (0, c)) k
        obtain ⟨_, h5, h6⟩ := hφ2 _ h1 _ h3
        rw [e]
        refine ⟨h5, ?_⟩
        rw [h6, h2, h4, hφb, hφb, h.zero x hx, h.zero y hy, mul_comm (γ a x), h.mul k _ _ (h.mem a ha x hx),
          Px k a ha]
        ring
    | zero =>
      refine ⟨D.zero_mem, hφ0 ▸ J.zero_mem, fun k ↦ ?_⟩
      by_cases hk : k = 0
      · subst hk
        rw [Γ.dpow_zero (top _), hφ0, h.zero 0 J.zero_mem, hφ1]
        exact ⟨hD1, rfl⟩
      · rw [Γ.dpow_eval_zero hk, hφ0, preDP_eval_zero h hk]
        exact ⟨D.zero_mem, rfl⟩
    | add d e _ _ hd he =>
      obtain ⟨dD, dJ, dk⟩ := hd
      obtain ⟨eD, eJ, ek⟩ := he
      obtain ⟨hde, -, -⟩ := hφ2 d dD e eD
      refine ⟨add_mem dD eD, hde ▸ add_mem dJ eJ, fun k ↦ ?_⟩
      have hm : ∀ p ∈ antidiagonal k, Γ.dpow p.1 d * Γ.dpow p.2 e ∈ D := fun p _ ↦
        (hφ2 _ (dk p.1).1 _ (ek p.2).1).2.1
      rw [Γ.dpow_add (top _) (top _), hde, h.add k _ dJ _ eJ, (hsum _ _ hm).2]
      refine ⟨(hsum _ _ hm).1, sum_congr rfl fun p _ ↦ ?_⟩
      rw [(dk p.1).2, (ek p.2).2, (hφ2 _ (dk p.1).1 _ (ek p.2).1).2.2]
    | smul z d _ hd =>
      obtain ⟨dD, dJ, dk⟩ := hd
      refine ⟨Submodule.smul_mem _ _ dD, (hφz z d dD) ▸ zsmul_mem dJ z, fun k ↦ ?_⟩
      have e1 : Γ.dpow k (z • d) = (z ^ k) • Γ.dpow k d := by
        rw [zsmul_eq_mul, Γ.dpow_mul (top _), zsmul_eq_mul, Int.cast_pow]
      refine ⟨by rw [e1]; exact Submodule.smul_mem _ _ (dk k).1, ?_⟩
      rw [e1, hφz _ _ dD, hφz _ _ (dk k).1, zsmul_eq_mul, h.mul k _ _ dJ, (dk k).2, zsmul_eq_mul, Int.cast_pow]
  have hmem : Γ.dpow n (X 0 + X 1) ∈ Dp := by
    rw [Γ.dpow_add (top _) (top _)]
    refine Submodule.sum_mem _ fun p hp ↦ ?_
    rw [← hbasΓ]
    refine Submodule.subset_span ⟨p, fun h0 ↦ hn ?_, rfl⟩
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    rw [← hp, h0]; rfl
  obtain ⟨_, _, hk⟩ := T _ hmem
  rw [← (hsX n).2, (hk m).2, Γ.dpow_comp hn (top _), (hnat _ _ (hsX _).1).2, (hsX _).2]

/- English proof (translation)
Introduce `B _ J γ s h hJ hs`. Establish `key : ∀ x ∈ J, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x`. Introduce `x hx`. Substitute `hJ` using the available equality. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hxs => exact hs x hxs`. Consider the case `zero`. Introduce `m n hn`. Rewrite using `[preDP_eval_zero h hn]`. Distinguish the cases in `hm : m = 0`.

Substitute `hm` using the available equality. Rewrite using `[Nat.uniformBell_zero_left, zero_mul, h.zero 0 (Submodule.zero_mem _), Nat.cast_one, one_mul]`. Rewrite using `[preDP_eval_zero h hm, preDP_eval_zero h (mul_ne_zero hm hn), mul_zero]`. Consider the case `add x y hx hy Px Py => exact fun m n hn ↦ preDP_comp_add h hx hy Px Py m n hn`. Consider the case `smul a x hx Px`.

Introduce `m n hn`. Rewrite using `[smul_eq_mul, h.mul n a x hx, h.mul m _ _ (h.mem n hn x hx), Px m n hn, h.mul (m * n) a x hx, ← pow_mul, mul_comm n m]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨{ dpow := γ dpow_null := fun hx ↦ h.null _ _ hx dpow_zero := fun hx ↦ h.zero _ hx dpow_one := fun hx ↦ h.one _ hx dpow_mem := fun hn hx ↦ h.mem _ hn _ hx dpow_add := fun hx hy ↦ h.add _ _ hx _ hy dpow_mul := fun hx ↦ h.mul _ _ _ hx mul_dpow := fun hx ↦ h.mul_dpow _ _ _ hx dpow_c …`.
-/
theorem exists_dp_of_comp_on_gens :
    ∀ (B : Type) [CommRing B] (J : Ideal B) (γ : ℕ → B → B) (s : Set B), IsPreDP J γ → J = Ideal.span s →
      (∀ x ∈ s, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) →
      ∃ δ : DividedPowers J, δ.dpow = γ := by
  intro B _ J γ s h hJ hs
  have key : ∀ x ∈ J, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x := by
    intro x hx
    subst hJ
    induction hx using Submodule.span_induction with
    | mem x hxs => exact hs x hxs
    | zero =>
      intro m n hn
      rw [preDP_eval_zero h hn]
      by_cases hm : m = 0
      · subst hm
        rw [Nat.uniformBell_zero_left, zero_mul, h.zero 0 (Submodule.zero_mem _), Nat.cast_one, one_mul]
      · rw [preDP_eval_zero h hm, preDP_eval_zero h (mul_ne_zero hm hn), mul_zero]
    | add x y hx hy Px Py => exact fun m n hn ↦ preDP_comp_add h hx hy Px Py m n hn
    | smul a x hx Px =>
      intro m n hn
      rw [smul_eq_mul, h.mul n a x hx, h.mul m _ _ (h.mem n hn x hx), Px m n hn, h.mul (m * n) a x hx, ← pow_mul,
        mul_comm n m]
      ring
  exact ⟨{ dpow := γ
           dpow_null := fun hx ↦ h.null _ _ hx
           dpow_zero := fun hx ↦ h.zero _ hx
           dpow_one := fun hx ↦ h.one _ hx
           dpow_mem := fun hn hx ↦ h.mem _ hn _ hx
           dpow_add := fun hx hy ↦ h.add _ _ hx _ hy
           dpow_mul := fun hx ↦ h.mul _ _ _ hx
           mul_dpow := fun hx ↦ h.mul_dpow _ _ _ hx
           dpow_comp := fun hn hx ↦ key _ hx _ _ hn }, rfl⟩

end Comp

section Flat

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R} (κ : DividedPowers I)

def expS (z : R) (y : A) : PowerSeries A :=
  PowerSeries.mk fun n ↦ y ^ n * algebraMap R A (κ.dpow n z)

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul]`. Establish `h : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, y ^ p.1 * algebraMap R A (κ.dpow p.1 z) * (y' ^ p.2 * algebraMap R A (κ.dpow p.2 z)) = y ^ p.1 * y' ^ p.2 * (n.choose p.1 : A) * algebraMap R A (κ.dpow n z)`. Introduce `p hp`. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Establish `h` using `κ.mul_dpow (m := p.1) (n := p.2) hz`. Rewrite `h` using `[hp]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = _ := by rw [h, map_mul, map_natCast]; ring`. Rewrite using `[Finset.sum_congr rfl h, ← Finset.sum_mul, add_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`.
-/
theorem expS_add_right {z : R} (hz : z ∈ I) (y y' : A) :
    expS κ z (y + y') = expS κ z y * expS κ z y' := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  have h : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, y ^ p.1 * algebraMap R A (κ.dpow p.1 z) *
      (y' ^ p.2 * algebraMap R A (κ.dpow p.2 z)) =
      y ^ p.1 * y' ^ p.2 * (n.choose p.1 : A) * algebraMap R A (κ.dpow n z) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h := κ.mul_dpow (m := p.1) (n := p.2) hz
    rw [hp] at h
    calc _ = y ^ p.1 * y' ^ p.2 * algebraMap R A (κ.dpow p.1 z * κ.dpow p.2 z) := by
            rw [map_mul]; ring
      _ = _ := by rw [h, map_mul, map_natCast]; ring
  rw [Finset.sum_congr rfl h, ← Finset.sum_mul, add_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul, κ.dpow_add hz hz', map_sum, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun p hp ↦ ?_` and prove the remaining obligations. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[← hp, pow_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem expS_add_left {z z' : R} (hz : z ∈ I) (hz' : z' ∈ I) (y : A) :
    expS κ (z + z') y = expS κ z y * expS κ z' y := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul, κ.dpow_add hz hz', map_sum, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, pow_add]; ring

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [expS, PowerSeries.coeff_mk, κ.dpow_mul hz, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem expS_smul {z : R} (hz : z ∈ I) (a : R) (y : A) :
    expS κ z (algebraMap R A a * y) = expS κ (a * z) y := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, κ.dpow_mul hz, map_mul, map_pow]
  ring

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[κ.dpow_zero I.zero_mem]`. Simplify using `[κ.dpow_eval_zero hn, hn]`.
-/
theorem expS_zero_left (y : A) : expS κ 0 y = 1 := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ.dpow_zero I.zero_mem]
  · simp [κ.dpow_eval_zero hn, hn]

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[κ.dpow_zero hz]`. Simplify using `[hn]`.
-/
theorem expS_zero_right (z : R) (hz : z ∈ I) : expS κ z (0 : A) = 1 := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ.dpow_zero hz]
  · simp [hn]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [expS_zero_right κ z hz]`. Consider the case `insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, expS_add_right κ hz, ih]`.
-/
theorem expS_sum_right {z : R} (hz : z ∈ I) {K : Type} (s : Finset K) (f : K → A) :
    expS κ z (∑ k ∈ s, f k) = ∏ k ∈ s, expS κ z (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero_right κ z hz]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, expS_add_right κ hz, ih]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [expS_zero_left κ y]`. Consider the case `insert k s hk ih`. Rewrite using `[Finset.sum_insert hk, Finset.prod_insert hk, expS_add_left κ (hf k (Finset.mem_insert_self k s)) (Ideal.sum_mem _ fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)), ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)]`.
-/
theorem expS_sum_left {K : Type} (s : Finset K) (f : K → R) (hf : ∀ k ∈ s, f k ∈ I) (y : A) :
    expS κ (∑ k ∈ s, f k) y = ∏ k ∈ s, expS κ (f k) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero_left κ y]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk,
      expS_add_left κ (hf k (Finset.mem_insert_self k s))
        (Ideal.sum_mem _ fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)]

/- English proof (translation)
Establish `h : ∑ i : ↥c.support, ((i : I) : R) • (c (i : I) : A) = (0 : A)`. Rewrite using `[Finset.sum_coe_sort c.support (fun i : I ↦ ((i : R)) • (c i : A)), ← hc, Finsupp.sum]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`. Take `⟨k, a, y, hx, ha⟩` from `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := A) h`.

Simplify using `only at hx ha`. Express the relevant statement in the definitionally equal form `(∏ i ∈ c.support, expS κ (i : R) (c i)) = 1`. Rewrite using `[← Finset.prod_coe_sort]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_congr rfl fun i _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[hx i, expS_sum_right κ (i.1 : I).2]`. Use `Finset.prod_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, expS_smul κ (i.1 : I).2]`. Use `_ = ∏ j, ∏ i : c.support, expS κ (a i j * ((i.1 : I) : R)) (y j) := Finset.prod_comm`. Use `_ = ∏ j, expS κ (∑ i : c.support, a i j * ((i.1 : I) : R)) (y j) := by`.

Use `Finset.prod_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[expS_sum_left κ _ _ fun i _ ↦ I.mul_mem_left _ (i.1 : I).2]`. Use `_ = 1 := by`. Use `Finset.prod_eq_one fun j _ ↦ ?_` and prove the remaining obligations. Establish `: ∑ i : c.support, a i j * ((i.1 : I) : R) = 0`.

Rewrite using `[← ha j]`. Conclude with `Finset.sum_congr rfl fun i _ ↦ mul_comm _ _`. Rewrite using `[this, expS_zero_left]`.
-/
theorem prod_expS_eq_one [Module.Flat R A] (c : I →₀ A)
    (hc : (c.sum fun i a ↦ a * algebraMap R A i) = 0) :
    (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * algebraMap R A (κ.dpow n i)) = 1 := by
  have h : ∑ i : ↥c.support, ((i : I) : R) • (c (i : I) : A) = (0 : A) := by
    rw [Finset.sum_coe_sort c.support (fun i : I ↦ ((i : R)) • (c i : A)), ← hc, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, mul_comm]
  obtain ⟨k, a, y, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := A) h
  simp only at hx ha
  change (∏ i ∈ c.support, expS κ (i : R) (c i)) = 1
  rw [← Finset.prod_coe_sort]
  calc ∏ i : c.support, expS κ ((i.1 : I) : R) (c i.1)
      = ∏ i : c.support, ∏ j, expS κ (a i j * ((i.1 : I) : R)) (y j) := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [hx i, expS_sum_right κ (i.1 : I).2]
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [Algebra.smul_def, expS_smul κ (i.1 : I).2]
    _ = ∏ j, ∏ i : c.support, expS κ (a i j * ((i.1 : I) : R)) (y j) := Finset.prod_comm
    _ = ∏ j, expS κ (∑ i : c.support, a i j * ((i.1 : I) : R)) (y j) := by
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [expS_sum_left κ _ _ fun i _ ↦ I.mul_mem_left _ (i.1 : I).2]
    _ = 1 := by
        refine Finset.prod_eq_one fun j _ ↦ ?_
        have : ∑ i : c.support, a i j * ((i.1 : I) : R) = 0 := by
          rw [← ha j]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
        rw [this, expS_zero_left]

/- English proof (translation)
Introduce `R A _ _ _ _ I κ`. Set `x : I → A` to `fun i ↦ algebraMap R A i`. Establish `hspan : Ideal.span (Set.range x) = I.map (algebraMap R A)`. Rewrite using `[Ideal.map]`. Use `congr 1`.

Use extensionality with `b`. Simplify using `[x]`. Take `⟨γ, hγ, hγx⟩` from `GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ A I x (fun i n ↦ algebraMap R A (κ.dpow n i)) (fun i ↦ by simp [κ.dpow_zero i.2]) (fun i ↦ by simp [x, κ.dpow_one i.2]) (fun i n hn ↦ Ideal.subset_span ⟨⟨κ.dpow n i, κ.dpow_mem hn i.2⟩, rfl⟩) (fun i m n ↦ by rw [← map_mul, …`. Rewrite `hγ` using `[hspan]`. Take `⟨δ, hδ⟩` from `exists_dp_of_comp_on_gens A _ γ (Set.range x) hγ hspan.symm (by`.

Introduce and unpack `_ ⟨i, rfl⟩ m n hn`. Rewrite using `[hγx, show algebraMap R A (κ.dpow n i) = x ⟨κ.dpow n i, κ.dpow_mem hn i.2⟩ from rfl, hγx]`. Simplify using `only [κ.dpow_comp hn i.2, map_mul, map_natCast]`. Rewrite using `[← hγx])`. Conclude with `⟨δ, ⟨le_rfl, fun a ha ↦ by rw [hδ]; exact hγx ⟨a, ha⟩ _⟩⟩`.
-/
theorem dpFlat : DPFlat := by
  intro R A _ _ _ _ I κ
  let x : I → A := fun i ↦ algebraMap R A i
  have hspan : Ideal.span (Set.range x) = I.map (algebraMap R A) := by
    rw [Ideal.map]; congr 1; ext b; simp [x]
  obtain ⟨γ, hγ, hγx⟩ := GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ A I x (fun i n ↦ algebraMap R A (κ.dpow n i))
    (fun i ↦ by simp [κ.dpow_zero i.2]) (fun i ↦ by simp [x, κ.dpow_one i.2])
    (fun i n hn ↦ Ideal.subset_span ⟨⟨κ.dpow n i, κ.dpow_mem hn i.2⟩, rfl⟩)
    (fun i m n ↦ by rw [← map_mul, κ.mul_dpow i.2, map_mul, map_natCast])
    (prod_expS_eq_one κ)
  rw [hspan] at hγ
  obtain ⟨δ, hδ⟩ := exists_dp_of_comp_on_gens A _ γ (Set.range x) hγ hspan.symm (by
    rintro _ ⟨i, rfl⟩ m n hn
    rw [hγx, show algebraMap R A (κ.dpow n i) = x ⟨κ.dpow n i, κ.dpow_mem hn i.2⟩ from rfl, hγx]
    simp only [κ.dpow_comp hn i.2, map_mul, map_natCast]
    rw [← hγx])
  exact ⟨δ, ⟨le_rfl, fun a ha ↦ by rw [hδ]; exact hγx ⟨a, ha⟩ _⟩⟩

end Flat

end GlobalTheory.CompanionTheory.JLiftDP
