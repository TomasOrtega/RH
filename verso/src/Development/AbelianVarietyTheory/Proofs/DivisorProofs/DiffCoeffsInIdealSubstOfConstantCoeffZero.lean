import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.SubstDiff

variable {τ B : Type} [CommRing B]

def euler (j : τ) (g : MvPowerSeries τ B) : MvPowerSeries τ B :=
  fun γ => (γ j : B) * coeff γ g

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_euler (j : τ) (g : MvPowerSeries τ B) (γ : τ →₀ ℕ) :
    coeff γ (euler j g) = (γ j : B) * coeff γ g := rfl

/- English proof (translation)
Use extensionality with `γ`. Rewrite using `[coeff_euler, map_add, coeff_mul, coeff_mul, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun q hq => ?_` and prove the remaining obligations. Establish `hq' : q.1 + q.2 = γ` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hq`. Rewrite using `[coeff_euler, coeff_euler, ← hq', Finsupp.add_apply]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem euler_mul (j : τ) (x y : MvPowerSeries τ B) :
    euler j (x * y) = euler j x * y + x * euler j y := by
  classical
  ext γ
  rw [coeff_euler, map_add, coeff_mul, coeff_mul, coeff_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q.1 + q.2 = γ := Finset.HasAntidiagonal.mem_antidiagonal.1 hq
  rw [coeff_euler, coeff_euler, ← hq', Finsupp.add_apply]
  push_cast
  ring

/- English proof (translation)
Use extensionality with `γ`. Rewrite using `[coeff_euler, coeff_one, map_zero]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem euler_one (j : τ) : euler j (1 : MvPowerSeries τ B) = 0 := by
  classical
  ext γ
  rw [coeff_euler, coeff_one, map_zero]
  split_ifs with h
  · subst h; simp
  · simp

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ x (n + 1), euler_mul, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem euler_pow (j : τ) (x : MvPowerSeries τ B) (n : ℕ) :
    euler j (x ^ (n + 1)) = ((n + 1 : ℕ) : MvPowerSeries τ B) * x ^ n * euler j x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ x (n + 1), euler_mul, ih]
    push_cast
    ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, euler_one]`. Conclude with `Ideal.zero_mem _`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, euler_mul]`.

Use `Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_left _ _ ih)` and prove the remaining obligations. Break down `h : α a with _ | n` into its components or cases. Rewrite using `[pow_zero, euler_one]`. Conclude with `Ideal.zero_mem _`. Rewrite using `[euler_pow]`.

Use `Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, ?_⟩))` and prove the remaining obligations. Simplify using `only [h]`.
-/
theorem euler_prod_mem {σ : Type} (j : τ) (u : σ → MvPowerSeries τ B) (α : σ → ℕ)
    (s : Finset σ) :
    euler j (∏ i ∈ s, u i ^ α i) ∈
      Ideal.span (Set.range fun i => ((α i : ℕ) : MvPowerSeries τ B)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, euler_one]; exact Ideal.zero_mem _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, euler_mul]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_left _ _ ih)
    rcases h : α a with _ | n
    · rw [pow_zero, euler_one]; exact Ideal.zero_mem _
    · rw [euler_pow]
      refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, ?_⟩))
      simp only [h]

variable {Q : Type} [CommRing Q] [Algebra B Q]

/- English proof (translation)
Proceed by induction on `hh using Submodule.span_induction with`. Consider the case `mem x hx => classical`. Take `⟨i, rfl⟩` from `hx`. Introduce `e`. Simplify using `only`.

Rewrite using `[← map_natCast (C (σ := τ) (R := B)), coeff_C]`. Use `split_ifs`. Rewrite using `[Algebra.smul_def, map_natCast]`. Conclude with `hc i`. Rewrite using `[zero_smul]`.

Conclude with `N.zero_mem`. Consider the case `zero => intro e`. Rewrite using `[map_zero, zero_smul]`. Conclude with `N.zero_mem`. Consider the case `add x y _ _ hx hy => intro e`.

Rewrite using `[map_add, add_smul]`. Conclude with `N.add_mem (hx e) (hy e)`. Consider the case `smul r x _ hx => classical`. Introduce `e`. Rewrite using `[smul_eq_mul, coeff_mul, Finset.sum_smul]`.

Use `N.sum_mem fun q _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `N.smul_mem _ (hx q.2)`.
-/
theorem smul_mem_of_mem_span {σ : Type} (N : Submodule B Q) (α : σ → ℕ) (c : Q)
    (hc : ∀ i, (α i : Q) * c ∈ N) (h : MvPowerSeries τ B)
    (hh : h ∈ Ideal.span (Set.range fun i => ((α i : ℕ) : MvPowerSeries τ B))) :
    ∀ e, coeff e h • c ∈ N := by
  induction hh using Submodule.span_induction with
  | mem x hx =>
    classical
    obtain ⟨i, rfl⟩ := hx
    intro e
    dsimp only
    rw [← map_natCast (C (σ := τ) (R := B)), coeff_C]
    split_ifs
    · rw [Algebra.smul_def, map_natCast]; exact hc i
    · rw [zero_smul]; exact N.zero_mem
  | zero => intro e; rw [map_zero, zero_smul]; exact N.zero_mem
  | add x y _ _ hx hy => intro e; rw [map_add, add_smul]; exact N.add_mem (hx e) (hy e)
  | smul r x _ hx =>
    classical
    intro e
    rw [smul_eq_mul, coeff_mul, Finset.sum_smul]
    refine N.sum_mem fun q _ => ?_
    rw [mul_smul]
    exact N.smul_mem _ (hx q.2)

end GlobalTheory.QLog.SubstDiff

open GlobalTheory.QLog.SubstDiff in
/- English proof (translation)
Introduce `p _ B O Q _ _ _ _ θ _ σ τ _ N f u hD hu`. Use `set NQ : Submodule B Q := Submodule.map (Algebra.linearMap B Q) N with hNQ`. Establish `memNQ : ∀ q : Q, q ∈ NQ ↔ ∃ b ∈ N, q = algebraMap B Q b`. Introduce `q`. Rewrite using `[hNQ, Submodule.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, rfl⟩`. Conclude with `⟨b, hb, rfl⟩`. Introduce and unpack `⟨b, hb, rfl⟩`. Conclude with `⟨b, hb, rfl⟩`.

Establish `ha : HasSubst (up Q u)` using `hasSubst_of_constantCoeff_zero fun i => by`. Simplify using `only [up]`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu i, map_zero]`. Establish `hprod : ∀ d : σ →₀ ℕ, (d.prod fun s e => (up Q u s) ^ e) = map (algebraMap B Q) (∏ i, u i ^ d i)`. Introduce `d`.

Rewrite using `[Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod]`. Simplify using `only [up, map_pow]`. Establish `hcoeff : ∀ e, coeff e (subst (up Q u) f) = ∑ d ∈ (coeff_subst_finite ha f e).toFinset, algebraMap B Q (coeff e (∏ i, u i ^ d i)) * coeff d f`. Introduce `e`. Rewrite using `[coeff_subst ha, finsum_eq_sum _ (coeff_subst_finite ha f e)]`.

Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[hprod, coeff_map, smul_eq_mul, mul_comm]`. Use `⟨fun e j => ?_, fun hI e => ?_⟩` and prove the remaining obligations. Rewrite using `[← memNQ, hcoeff, Finset.mul_sum]`. Use `NQ.sum_mem fun d _ => ?_` and prove the remaining obligations.

Establish `key` using `smul_mem_of_mem_span NQ (fun i => d i) (coeff d f) (fun i => (memNQ _).2 (by obtain ⟨b, hb, h⟩ := hD d i; exact ⟨b, hb, h⟩)) _ (euler_prod_mem j u (fun i => d i) Finset.univ) e`. Use `key using 1` and compare the differences between its conclusion and the goal. Rewrite using `[coeff_euler, Algebra.smul_def, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← memNQ, hcoeff]`.

Use `NQ.sum_mem fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.smul_def]`. Conclude with `NQ.smul_mem _ ((memNQ _).2 (by obtain ⟨b, hb, h⟩ := hI d; exact ⟨b, hb, h⟩))`.
-/
theorem GlobalTheory.QLog.dIn_subst_up : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → DIn N (subst (up Q u) f) ∧ (In N f → In N (subst (up Q u) f)) := by
  intro p _ B O Q _ _ _ _ θ _ σ τ _ N f u hD hu
  set NQ : Submodule B Q := Submodule.map (Algebra.linearMap B Q) N with hNQ
  have memNQ : ∀ q : Q, q ∈ NQ ↔ ∃ b ∈ N, q = algebraMap B Q b := by
    intro q
    rw [hNQ, Submodule.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
  have ha : HasSubst (up Q u) :=
    hasSubst_of_constantCoeff_zero fun i => by
      simp only [up]
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu i,
        map_zero]

  have hprod : ∀ d : σ →₀ ℕ, (d.prod fun s e => (up Q u s) ^ e) =
      map (algebraMap B Q) (∏ i, u i ^ d i) := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod]
    simp only [up, map_pow]
  have hcoeff : ∀ e, coeff e (subst (up Q u) f) =
      ∑ d ∈ (coeff_subst_finite ha f e).toFinset,
        algebraMap B Q (coeff e (∏ i, u i ^ d i)) * coeff d f := by
    intro e
    rw [coeff_subst ha, finsum_eq_sum _ (coeff_subst_finite ha f e)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hprod, coeff_map, smul_eq_mul, mul_comm]
  refine ⟨fun e j => ?_, fun hI e => ?_⟩
  · rw [← memNQ, hcoeff, Finset.mul_sum]
    refine NQ.sum_mem fun d _ => ?_
    have key := smul_mem_of_mem_span NQ (fun i => d i) (coeff d f)
      (fun i => (memNQ _).2 (by obtain ⟨b, hb, h⟩ := hD d i; exact ⟨b, hb, h⟩))
      _ (euler_prod_mem j u (fun i => d i) Finset.univ) e
    convert key using 1
    rw [coeff_euler, Algebra.smul_def, map_mul, map_natCast]
    ring
  · rw [← memNQ, hcoeff]
    refine NQ.sum_mem fun d _ => ?_
    rw [← Algebra.smul_def]
    exact NQ.smul_mem _ ((memNQ _).2 (by obtain ⟨b, hb, h⟩ := hI d; exact ⟨b, hb, h⟩))
