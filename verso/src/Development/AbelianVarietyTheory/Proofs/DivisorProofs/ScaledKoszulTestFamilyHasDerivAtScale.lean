import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

noncomputable section

namespace GlobalTheory.PsCo.HomotDeriv

/- English proof (translation)
Simplify using `only [rP, rM, map_sum, map_mul, ev, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]`. Use `push_cast`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ev_rP {n : ℕ} (ε : Fin n → Bool) (g : Mat n) : ev g (rP ε) = ((rM ε g : ℝ) : ℂ) := by
  simp only [rP, rM, map_sum, map_mul, ev, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/- English proof (translation)
Establish `hc : ∀ m : ℕ, ContDiff ℝ m G` using `fun m => hG.of_le (by exact_mod_cast le_top)`. Establish `e : ∀ (m : ℕ) (s : ℝ), iteratedDeriv m (fun y => G (s * y)) r = s ^ m * iteratedDeriv m G (s * r)` using `fun m s => congrFun (iteratedDeriv_comp_const_mul (hc m) s) r`. Simplify using `only [e]`. Establish `hD : HasDerivAt (iteratedDeriv k G) (iteratedDeriv (k + 1) G (t * r)) (t * r)`. Rewrite using `[iteratedDeriv_succ]`.

Conclude with `((hc (k + 1)).differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)).differentiableAt.hasDerivAt`. Establish `h1 : HasDerivAt (fun s : ℝ => s * r) r t` using `by simpa using (hasDerivAt_id t).mul_const r`. Establish `h2 : HasDerivAt (fun s : ℝ => s ^ k * iteratedDeriv k G (s * r)) (k * t ^ (k - 1) * iteratedDeriv k G (t * r) + t ^ k * (iteratedDeriv (k + 1) G (t * r) * r)) t`. Establish `h3` using `(hasDerivAt_pow k t).mul (hD.comp t h1)`. Conclude with `h3`.

Use `h2.congr_deriv ?_` and prove the remaining obligations. Break down `k with _ | k` into its components or cases. Simplify using `only [Nat.cast_zero, zero_mul, zero_add, pow_zero, pow_one]`. Clear the denominators using the available nonvanishing facts. Simplify using `only [Nat.add_sub_cancel]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_scale (G : ℝ → ℝ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (k : ℕ) (r t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => iteratedDeriv k (fun y => G (s * y)) r)
      (t⁻¹ * (k * iteratedDeriv k (fun y => G (t * y)) r + r * iteratedDeriv (k + 1) (fun y => G (t * y)) r)) t := by
  have hc : ∀ m : ℕ, ContDiff ℝ m G := fun m => hG.of_le (by exact_mod_cast le_top)
  have e : ∀ (m : ℕ) (s : ℝ), iteratedDeriv m (fun y => G (s * y)) r = s ^ m * iteratedDeriv m G (s * r) :=
    fun m s => congrFun (iteratedDeriv_comp_const_mul (hc m) s) r
  simp only [e]
  have hD : HasDerivAt (iteratedDeriv k G) (iteratedDeriv (k + 1) G (t * r)) (t * r) := by
    rw [iteratedDeriv_succ]
    exact ((hc (k + 1)).differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => s * r) r t := by simpa using (hasDerivAt_id t).mul_const r
  have h2 : HasDerivAt (fun s : ℝ => s ^ k * iteratedDeriv k G (s * r))
      (k * t ^ (k - 1) * iteratedDeriv k G (t * r) + t ^ k * (iteratedDeriv (k + 1) G (t * r) * r)) t :=
    by
    have h3 := (hasDerivAt_pow k t).mul (hD.comp t h1)
    exact h3
  refine h2.congr_deriv ?_
  rcases k with _ | k
  · simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, pow_one]
    field_simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

/- English proof (translation)
Establish `h1 : ∑ k ∈ Finset.range (N + 1), (k : ℂ) * a k * e k = ∑ k ∈ Finset.range (N + 1), a (k + 1) * (((k : ℂ) + 1) * e (k + 1))`. Rewrite using `[Finset.sum_range_succ', Finset.sum_range_succ (n := N), he]`. Simplify using `only [Nat.cast_zero, zero_mul, mul_zero, add_zero]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [add_mul (_ * a _), mul_add (a _), Finset.sum_add_distrib, h1]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem sum_shift (N : ℕ) (a e : ℕ → ℂ) (r : ℂ) (he : e (N + 1) = 0) :
    ∑ k ∈ Finset.range (N + 1), ((k : ℂ) * a k + r * a (k + 1)) * e k =
      ∑ k ∈ Finset.range (N + 1), a (k + 1) * (((k : ℂ) + 1) * e (k + 1) + r * e k) := by
  have h1 : ∑ k ∈ Finset.range (N + 1), (k : ℂ) * a k * e k =
      ∑ k ∈ Finset.range (N + 1), a (k + 1) * (((k : ℂ) + 1) * e (k + 1)) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ (n := N), he]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  simp only [add_mul (_ * a _), mul_add (a _), Finset.sum_add_distrib, h1]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Rewrite using `[Finset.sum_range_succ', Finset.sum_range_succ (n := N), hq]`. Simplify using `[prev]`.
-/
theorem sum_prev {n : ℕ} (g : Mat n) (N : ℕ) (a : ℕ → ℂ) (q : ℕ → Poly n) (hq : q N = 0) (R : ℂ) :
    ∑ k ∈ Finset.range (N + 1), a (k + 1) * (R * ev g (prev q k)) =
      ∑ k ∈ Finset.range (N + 1), a (k + 1 + 1) * (R * ev g (q k)) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ (n := N), hq]
  simp [prev]

/- English proof (translation)
Introduce `n ε G p q hG hK t ht g`. Take `⟨hrec, hp, hq⟩` from `hK`. Set `a : ℕ → ℂ` to `fun j => ((iteratedDeriv j (fun y => G (t * y)) (rM ε g) : ℝ) : ℂ)`. Establish `hd : ∀ k ∈ Finset.range (nMode ε + 1), HasDerivAt (fun s : ℝ => bas ε (iteratedDeriv k fun x => G (s * x)) (p k) g) (((t⁻¹ : ℝ) : ℂ) * (((k : ℂ) * a k + (rM ε g : ℂ) * a (k + 1)) * ev g (p k))) t`. Introduce `k _`.

Use `(((hasDerivAt_scale G hG k (rM ε g) t ht.ne').ofReal_comp).mul_const (ev g (p k))).congr_deriv ?_` and prove the remaining obligations. Simplify using `only [a]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `(HasDerivAt.fun_sum hd).congr_deriv ?_` and prove the remaining obligations.

Rewrite using `[← Finset.mul_sum]`. Use `congr 1`. Establish `hA : ∀ (x : Mode ε) (j : ℕ), adBas ε (Matrix.single x.1.2 x.1.1 1) (iteratedDeriv (j + 1) (fun y => G (t * y))) (q x j) g = a (j + 1) * ev g (dM ε x (q x j)) + a (j + 1 + 1) * (ev g (dM ε x (rP ε)) * ev g (q x j))`. Introduce `x j`. Simplify using `only [adBas, bas, dM, ← iteratedDeriv_succ, map_mul, a]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hR : ∀ j : ℕ, ((j : ℂ) + 1) * ev g (p (j + 1)) + (rM ε g : ℂ) * ev g (p j) = ∑ x, (ev g (dM ε x (q x j)) + ev g (dM ε x (rP ε)) * ev g (prev (q x) j))`. Introduce `j`. Use `congrArg (ev g) (hrec j)` as an intermediate fact. Simplify `this` using `only [map_sum, map_add, map_mul, ev_rP, map_natCast, map_one]`.

Rewrite using `[sum_shift (nMode ε) a (fun k => ev g (p k)) (rM ε g : ℂ) (by simp [hp (nMode ε + 1) (Nat.lt_succ_self _)])]`. Simplify using `only [hA, hR, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `only [mul_add, Finset.sum_add_distrib]`.

Rewrite using `[sum_prev g (nMode ε) a (q x) (hq x _ le_rfl)]`.
-/
theorem famF_hasDerivAt : ∀ {n : ℕ} (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → GlobalTheory.PsCo.Pc1.Poly n) (q : GlobalTheory.PsCo.Pc1.Mode ε → ℕ → GlobalTheory.PsCo.Pc1.Poly n), ContDiff ℝ (⊤ : ℕ∞) G → GlobalTheory.PsCo.Pc1.IsKoszul ε p q → ∀ t : ℝ, 0 < t → ∀ g : GlobalTheory.PsCo.Pc1.Mat n, HasDerivAt (fun s : ℝ => GlobalTheory.PsCo.Pc1.famF ε G p s g) (((t⁻¹ : ℝ) : ℂ) * ∑ x : GlobalTheory.PsCo.Pc1.Mode ε, ∑ j ∈ Finset.range (GlobalTheory.PsCo.Pc1.nMode ε + 1), GlobalTheory.PsCo.Pc1.adBas ε (Matrix.single x.1.2 x.1.1 1) (iteratedDeriv (j + 1) (fun y => G (t * y))) (q x j) g) t := by
  intro n ε G p q hG hK t ht g
  obtain ⟨hrec, hp, hq⟩ := hK
  let a : ℕ → ℂ := fun j => ((iteratedDeriv j (fun y => G (t * y)) (rM ε g) : ℝ) : ℂ)
  have hd : ∀ k ∈ Finset.range (nMode ε + 1),
      HasDerivAt (fun s : ℝ => bas ε (iteratedDeriv k fun x => G (s * x)) (p k) g)
        (((t⁻¹ : ℝ) : ℂ) * (((k : ℂ) * a k + (rM ε g : ℂ) * a (k + 1)) * ev g (p k))) t := by
    intro k _
    refine (((hasDerivAt_scale G hG k (rM ε g) t ht.ne').ofReal_comp).mul_const (ev g (p k))).congr_deriv ?_
    simp only [a]
    push_cast
    ring
  refine (HasDerivAt.fun_sum hd).congr_deriv ?_
  rw [← Finset.mul_sum]
  congr 1
  have hA : ∀ (x : Mode ε) (j : ℕ),
      adBas ε (Matrix.single x.1.2 x.1.1 1) (iteratedDeriv (j + 1) (fun y => G (t * y))) (q x j) g =
        a (j + 1) * ev g (dM ε x (q x j)) + a (j + 1 + 1) * (ev g (dM ε x (rP ε)) * ev g (q x j)) := by
    intro x j
    simp only [adBas, bas, dM, ← iteratedDeriv_succ, map_mul, a]
    ring
  have hR : ∀ j : ℕ, ((j : ℂ) + 1) * ev g (p (j + 1)) + (rM ε g : ℂ) * ev g (p j) =
      ∑ x, (ev g (dM ε x (q x j)) + ev g (dM ε x (rP ε)) * ev g (prev (q x) j)) := by
    intro j
    have := congrArg (ev g) (hrec j)
    simpa only [map_sum, map_add, map_mul, ev_rP, map_natCast, map_one] using this
  rw [sum_shift (nMode ε) a (fun k => ev g (p k)) (rM ε g : ℂ) (by simp [hp (nMode ε + 1) (Nat.lt_succ_self _)])]
  simp only [hA, hR, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [mul_add, Finset.sum_add_distrib]
  rw [sum_prev g (nMode ε) a (q x) (hq x _ le_rfl)]

end GlobalTheory.PsCo.HomotDeriv
