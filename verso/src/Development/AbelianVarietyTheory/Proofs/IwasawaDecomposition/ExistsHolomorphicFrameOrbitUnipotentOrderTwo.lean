import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MajorantHarnackHolomorphicHalfPlaneStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped Matrix

namespace GlobalTheory.ShFam.OrbitUnip

def LinGrowth {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ v w : Fin N → ℂ, w ≠ 0 → ∃ L : (Fin N → ℂ) →ₗ[ℂ] ℂ, L w ≠ 0 ∧ ∃ C : ℝ, ∀ k : ℕ, ‖L (A ^ k *ᵥ v)‖ ≤ C * (1 + k)

/- English proof (translation)
Establish `h1 : μ ∈ spectrum ℂ A` using `Matrix.mem_spectrum_iff_isRoot_charpoly.2 hμ`. Establish `h2 : Module.End.HasEigenvalue (Matrix.toLin' A) μ`. Rewrite using `[Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']`. Conclude with `h1`. Take `⟨v, hv⟩` from `h2.exists_hasEigenvector`.

Establish `hAv : A *ᵥ v = μ • v` using `by simpa using hv.apply_eq_smul`. Establish `hk : ∀ k : ℕ, A ^ k *ᵥ v = μ ^ k • v`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]`. Take `⟨L, hL, C, hC⟩` from `h v v hv.2`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Establish `hpos : 0 < ‖L v‖` using `norm_pos_iff.2 hL`.

Establish `t0` using `tendsto_pow_const_div_const_pow_of_one_lt 0 hlt`. Establish `t1` using `tendsto_pow_const_div_const_pow_of_one_lt 1 hlt`. Establish `t2` using `(t0.add t1).const_mul C`. Simplify using `only [add_zero, mul_zero] at t2`. Establish `hle : ∀ k : ℕ, ‖L v‖ ≤ C * ((k : ℝ) ^ 0 / ‖μ‖ ^ k + (k : ℝ) ^ 1 / ‖μ‖ ^ k)`.

Introduce `k`. Use `hC k` as an intermediate fact. Rewrite `this` using `[hk, map_smul, norm_smul, norm_pow]`. Establish `hp : 0 < ‖μ‖ ^ k` using `pow_pos (by linarith) k`. Rewrite using `[← add_div, ← mul_div_assoc, le_div_iff₀ hp, pow_zero, pow_one]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `ge_of_tendsto' t2 hle` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem LinGrowth.norm_le_one {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (h : LinGrowth A) {μ : ℂ}
    (hμ : A.charpoly.IsRoot μ) : ‖μ‖ ≤ 1 := by
  have h1 : μ ∈ spectrum ℂ A := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hμ
  have h2 : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']; exact h1
  obtain ⟨v, hv⟩ := h2.exists_hasEigenvector
  have hAv : A *ᵥ v = μ • v := by simpa using hv.apply_eq_smul
  have hk : ∀ k : ℕ, A ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  obtain ⟨L, hL, C, hC⟩ := h v v hv.2
  by_contra hlt
  push Not at hlt
  have hpos : 0 < ‖L v‖ := norm_pos_iff.2 hL
  have t0 := tendsto_pow_const_div_const_pow_of_one_lt 0 hlt
  have t1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hlt
  have t2 := (t0.add t1).const_mul C
  simp only [add_zero, mul_zero] at t2
  have hle : ∀ k : ℕ, ‖L v‖ ≤ C * ((k : ℝ) ^ 0 / ‖μ‖ ^ k + (k : ℝ) ^ 1 / ‖μ‖ ^ k) := by
    intro k
    have := hC k
    rw [hk, map_smul, norm_smul, norm_pow] at this
    have hp : 0 < ‖μ‖ ^ k := pow_pos (by linarith) k
    rw [← add_div, ← mul_div_assoc, le_div_iff₀ hp, pow_zero, pow_one]
    linarith
  have := ge_of_tendsto' t2 hle
  linarith

/- English proof (translation)
Establish `key : ∀ v : Fin N → ℂ, n ^ 3 *ᵥ v = 0 → n ^ 2 *ᵥ v = 0`. Introduce `v hv`. Assume the negation of the conclusion as `hw`. Take `⟨L, hL, C, hC⟩` from `h v _ hw`. Establish `hk : ∀ k : ℕ, (1 + n) ^ k *ᵥ v = v + (k : ℂ) • (n *ᵥ v) + ((k : ℂ) * (k - 1) / 2) • (n ^ 2 *ᵥ v)`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e2 : n *ᵥ (n *ᵥ v) = n ^ 2 *ᵥ v` using `by rw [Matrix.mulVec_mulVec, sq]`.

Establish `e3 : n *ᵥ (n ^ 2 *ᵥ v) = 0` using `by rw [Matrix.mulVec_mulVec, ← pow_succ', hv]`. Rewrite using `[pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, e2, e3]`. Use `push_cast`. Use `module`. Use `set a := ‖L v‖`.

Use `set b := ‖L (n *ᵥ v)‖`. Use `set c := ‖L (n ^ 2 *ᵥ v)‖`. Establish `hc : 0 < c` using `norm_pos_iff.2 hL`. Establish `ha : 0 ≤ a` using `norm_nonneg _`. Establish `hb : 0 ≤ b` using `norm_nonneg _`.

Establish `hle : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * (k - 1) / 2 * c ≤ C * (1 + k) + a + k * b`. Introduce `k hk1`. Establish `h1` using `hC k`. Establish `e : ((k : ℂ) * (k - 1) / 2) * L (n ^ 2 *ᵥ v) = L ((1 + n) ^ k *ᵥ v) - L v - k * L (n *ᵥ v)`. Rewrite using `[hk]`.

Simplify using `only [map_add, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk1`. Establish `e' : ‖((k : ℂ) * (k - 1) / 2)‖ = (k : ℝ) * (k - 1) / 2`. Rewrite using `[show ((k : ℂ) * (k - 1) / 2) = (((k : ℝ) * (k - 1) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by have : (0 : ℝ) ≤ k - 1 := by linarith positivity)]`.

Establish `h2` using `congrArg norm e`. Rewrite `h2` using `[norm_mul, e']`. Establish `h3 : ‖L ((1 + n) ^ k *ᵥ v) - L v - k * L (n *ᵥ v)‖ ≤ ‖L ((1 + n) ^ k *ᵥ v)‖ + a + k * b`. Use `(norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_natCast]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC0 : 0 ≤ C`. Use `(norm_nonneg _).trans (hC 0)` as an intermediate fact. Simplify using `using this`. Take `⟨k, hk⟩` from `exists_nat_gt (2 * (2 * C + a + b) / c + 1)`.

Establish `hq : 0 ≤ 2 * (2 * C + a + b) / c` using `by positivity`. Establish `hk1 : (1 : ℝ) < k` using `by linarith`. Establish `h4` using `hle k (by exact_mod_cast hk1.le)`. Establish `h5 : 2 * (2 * C + a + b) < (k - 1) * c`. Rewrite using `[← div_lt_iff₀ hc]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h6 : (k : ℝ) * (2 * (2 * C + a + b)) < k * ((k - 1) * c)` using `mul_lt_mul_of_pos_left h5 (by linarith)`. Use polynomial arithmetic with `[mul_nonneg hC0 (sub_nonneg.2 hk1.le), mul_nonneg ha (sub_nonneg.2 hk1.le)]`. Establish `step : ∀ j : ℕ, n ^ (j + 2) = 0 → n ^ 2 = 0`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Introduce `hj`. Apply `ih` to reduce the goal to its premises.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Use `key (n ^ j *ᵥ u) (by rw [Matrix.mulVec_mulVec, ← pow_add, add_comm, show j + 3 = j + 1 + 2 by ring, hj]; simp)` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, ← pow_add, add_comm]`. Rewrite using `[Matrix.toLin'_apply, this, map_zero, LinearMap.zero_apply]`.

Take `⟨j, hj⟩` from `hn`. Conclude with `step j (by rw [pow_add, hj, zero_mul])`.
-/
theorem LinGrowth.sq_eq_zero {N : ℕ} {n : Matrix (Fin N) (Fin N) ℂ} (h : LinGrowth (1 + n)) (hn : IsNilpotent n) :
    n ^ 2 = 0 := by
  have key : ∀ v : Fin N → ℂ, n ^ 3 *ᵥ v = 0 → n ^ 2 *ᵥ v = 0 := by
    intro v hv
    by_contra hw
    obtain ⟨L, hL, C, hC⟩ := h v _ hw
    have hk : ∀ k : ℕ, (1 + n) ^ k *ᵥ v = v + (k : ℂ) • (n *ᵥ v) + ((k : ℂ) * (k - 1) / 2) • (n ^ 2 *ᵥ v) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have e2 : n *ᵥ (n *ᵥ v) = n ^ 2 *ᵥ v := by rw [Matrix.mulVec_mulVec, sq]
        have e3 : n *ᵥ (n ^ 2 *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec, ← pow_succ', hv]
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_add,
          Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, e2, e3]
        push_cast
        module
    set a := ‖L v‖
    set b := ‖L (n *ᵥ v)‖
    set c := ‖L (n ^ 2 *ᵥ v)‖
    have hc : 0 < c := norm_pos_iff.2 hL
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    have hle : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * (k - 1) / 2 * c ≤ C * (1 + k) + a + k * b := by
      intro k hk1
      have h1 := hC k
      have e : ((k : ℂ) * (k - 1) / 2) * L (n ^ 2 *ᵥ v) = L ((1 + n) ^ k *ᵥ v) - L v - k * L (n *ᵥ v) := by
        rw [hk]; simp only [map_add, map_smul, smul_eq_mul]; ring
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have e' : ‖((k : ℂ) * (k - 1) / 2)‖ = (k : ℝ) * (k - 1) / 2 := by
        rw [show ((k : ℂ) * (k - 1) / 2) = (((k : ℝ) * (k - 1) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by have : (0 : ℝ) ≤ k - 1 := by linarith
                                  positivity)]
      have h2 := congrArg norm e
      rw [norm_mul, e'] at h2
      have h3 : ‖L ((1 + n) ^ k *ᵥ v) - L v - k * L (n *ᵥ v)‖ ≤ ‖L ((1 + n) ^ k *ᵥ v)‖ + a + k * b := by
        refine (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)
        rw [norm_mul, Complex.norm_natCast]
      linarith
    have hC0 : 0 ≤ C := by
      have := (norm_nonneg _).trans (hC 0)
      simpa using this
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * (2 * C + a + b) / c + 1)
    have hq : 0 ≤ 2 * (2 * C + a + b) / c := by positivity
    have hk1 : (1 : ℝ) < k := by linarith
    have h4 := hle k (by exact_mod_cast hk1.le)
    have h5 : 2 * (2 * C + a + b) < (k - 1) * c := by
      rw [← div_lt_iff₀ hc]; linarith
    have h6 : (k : ℝ) * (2 * (2 * C + a + b)) < k * ((k - 1) * c) := mul_lt_mul_of_pos_left h5 (by linarith)
    nlinarith [mul_nonneg hC0 (sub_nonneg.2 hk1.le), mul_nonneg ha (sub_nonneg.2 hk1.le)]
  have step : ∀ j : ℕ, n ^ (j + 2) = 0 → n ^ 2 = 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      apply ih
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun u => ?_
      have := key (n ^ j *ᵥ u) (by rw [Matrix.mulVec_mulVec, ← pow_add, add_comm, show j + 3 = j + 1 + 2 by ring, hj]; simp)
      rw [Matrix.mulVec_mulVec, ← pow_add, add_comm] at this
      rw [Matrix.toLin'_apply, this, map_zero, LinearMap.zero_apply]
  obtain ⟨j, hj⟩ := hn
  exact step j (by rw [pow_add, hj, zero_mul])

/- English proof (translation)
Introduce `v w hw`. Take `⟨L, hL, C, hC⟩` from `h v w hw`. Establish `hC0 : 0 ≤ C`. Use `(norm_nonneg _).trans (hC 0)` as an intermediate fact. Simplify using `using this`.

Use `⟨L, hL, C * (1 + m), fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_mul]`. Use `(hC _).trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Use `mul_le_mul_of_nonneg_left ?_ hC0` and prove the remaining obligations.

Use `push_cast`. Establish `: (0 : ℝ) ≤ m` using `m.cast_nonneg`. Establish `: (0 : ℝ) ≤ k` using `k.cast_nonneg`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem LinGrowth.pow {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (h : LinGrowth A) (m : ℕ) : LinGrowth (A ^ m) := by
  intro v w hw
  obtain ⟨L, hL, C, hC⟩ := h v w hw
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0)
    simpa using this
  refine ⟨L, hL, C * (1 + m), fun k => ?_⟩
  rw [← pow_mul]
  refine (hC _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC0
  push_cast
  have : (0 : ℝ) ≤ m := m.cast_nonneg
  have : (0 : ℝ) ≤ k := k.cast_nonneg
  nlinarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} {X : Data E N} {T : ℝ} {M : ℕ}
  {γ : GL (Fin N) E} {x : ℂ → Frame X.Ψ N}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use `⟨fun _ => (1 : Matrix (Fin N) (Fin N) ℂ), fun τ => ⟨?_, fun a c h => Matrix.one_apply_ne h.ne'⟩, fun _ i => Matrix.one_apply_eq i, ?_⟩` and prove the remaining obligations. Use `show (1 : Matrix (Fin N) (Fin N) ℂ).det ≠ 0`. Simplify using the standard rewrite rules.

Use function extensionality and compare the values at `τ`. Rewrite using `[zero_mul, Nat.cast_zero, add_zero]`. Use `show mat (x w) τ = ((γ ^ 0 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 * mat (x w) τ * 1`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Take `⟨b, hb, hb1, e⟩` from `ih`. Take `⟨b', hb', hb1', e'⟩` from `h.2.2.2.2 (w + (n * M : ℕ)) (by simpa using hw)`. Establish `tb : ∀ τ, (mat b τ).BlockTriangular id` using `fun τ a c hac => (hb τ).2 a c hac`. Establish `tb' : ∀ τ, (mat b' τ).BlockTriangular id` using `fun τ a c hac => (hb' τ).2 a c hac`. Use `⟨rmul b b', fun τ => ⟨?_, fun a c hac => (tb τ).mul (tb' τ) hac⟩, fun τ i => ?_, ?_⟩` and prove the remaining obligations.

Use `show (mat b τ * mat b' τ).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero (hb τ).1 (hb' τ).1`. Use `show (mat b τ * mat b' τ) i i = 1`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`.

Use `show b τ i i * b' τ i i = 1`. Rewrite using `[hb1, hb1', one_mul]`. Introduce `j _ hj`. Break down `lt_or_gt_of_ne hj with hj | hj` into its components or cases. Rewrite using `[tb τ hj, zero_mul]`.

Rewrite using `[tb' τ hj, mul_zero]`. Simplify using the standard rewrite rules. Rewrite using `[show w + (((n + 1) * M : ℕ) : ℂ) = w + (n * M : ℕ) + M by push_cast; ring, e', e]`. Use function extensionality and compare the values at `τ`. Use `show (γ : Matrix (Fin N) (Fin N) E).map τ.1 * (((γ ^ n : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 * mat (x w) τ * mat b τ) * mat b' τ = ((γ ^ (n + 1) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 * mat (x w) τ * (mat b τ * mat b' τ)`.

Rewrite using `[pow_succ', Units.val_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem shift_pow (h : IsOrbit X T M γ x) (n : ℕ) (w : ℂ) (hw : T < w.im) :
    ∃ b ∈ Bor X.Ψ N, (∀ τ i, b τ i i = 1) ∧ x (w + (n * M : ℕ)) = rmul (lact (γ ^ n) (x w)) b := by
  induction n with
  | zero =>
    refine ⟨fun _ => (1 : Matrix (Fin N) (Fin N) ℂ), fun τ => ⟨?_, fun a c h => Matrix.one_apply_ne h.ne'⟩,
      fun _ i => Matrix.one_apply_eq i, ?_⟩
    · show (1 : Matrix (Fin N) (Fin N) ℂ).det ≠ 0
      simp
    · funext τ
      rw [zero_mul, Nat.cast_zero, add_zero]
      show mat (x w) τ = ((γ ^ 0 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 * mat (x w) τ * 1
      simp
  | succ n ih =>
    obtain ⟨b, hb, hb1, e⟩ := ih
    obtain ⟨b', hb', hb1', e'⟩ := h.2.2.2.2 (w + (n * M : ℕ)) (by simpa using hw)
    have tb : ∀ τ, (mat b τ).BlockTriangular id := fun τ a c hac => (hb τ).2 a c hac
    have tb' : ∀ τ, (mat b' τ).BlockTriangular id := fun τ a c hac => (hb' τ).2 a c hac
    refine ⟨rmul b b', fun τ => ⟨?_, fun a c hac => (tb τ).mul (tb' τ) hac⟩, fun τ i => ?_, ?_⟩
    · show (mat b τ * mat b' τ).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero (hb τ).1 (hb' τ).1
    · show (mat b τ * mat b' τ) i i = 1
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · show b τ i i * b' τ i i = 1
        rw [hb1, hb1', one_mul]
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with hj | hj
        · rw [tb τ hj, zero_mul]
        · rw [tb' τ hj, mul_zero]
      · simp
    · rw [show w + (((n + 1) * M : ℕ) : ℂ) = w + (n * M : ℕ) + M by push_cast; ring, e', e]
      funext τ
      show (γ : Matrix (Fin N) (Fin N) E).map τ.1 *
          (((γ ^ n : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 * mat (x w) τ * mat b τ) * mat b' τ =
        ((γ ^ (n + 1) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 * mat (x w) τ * (mat b τ * mat b' τ)
      rw [pow_succ', Units.val_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Nat.mul_pos hn h.1, pow_mem h.2.1 n, h.2.2.1, h.2.2.2.1, fun w hw => shift_pow h n w hw⟩`.
-/
theorem isOrbit_pow (h : IsOrbit X T M γ x) {n : ℕ} (hn : 0 < n) : IsOrbit X T (n * M) (γ ^ n) x :=
  ⟨Nat.mul_pos hn h.1, pow_mem h.2.1 n, h.2.2.1, h.2.2.2.1, fun w hw => shift_pow h n w hw⟩

/- English proof (translation)
Introduce `v u hu`. Use `set w : ℂ := ((T + 1 : ℝ) : ℂ) * Complex.I with hwdef`. Establish `hwi : w.im = T + 1` using `by simp [hwdef]`. Establish `hw : T < w.im` using `by rw [hwi]; linarith`. Establish `hx` using `h.2.2.2.1 w hw`.

Set `L : (Fin N → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun p => X.Hf (x w) τ p u map_add' := fun p q => by`. Use `ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.Hf_sub_left X (x w) τ (p + q) q u` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.

Use the proof step `map_smul' := fun k p => ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.Hf_smul_left X (x w) τ k p u }`. Establish `hu0` using `X.maj_pos hx τ hu`. Establish `hv0` using `ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ v`. Use `⟨L, ?_, Real.sqrt ((2 + M ^ 2) * X.maj (x w) τ v * X.maj (x w) τ u), fun k => ?_⟩` and prove the remaining obligations. Use `show X.Hf (x w) τ u u ≠ 0`.

Rewrite using `[X.Hf_self hx τ u]`. Conclude with `hu0.ne'` after adjusting the coercions. Take `⟨b, hb, -, e⟩` from `shift_pow h k w hw`. Establish `hst` using `X.Γ_stab _ (pow_mem h.2.1 k)`. Establish `hpow : ((γ ^ k : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 = ((γ : Matrix (Fin N) (Fin N) E).map τ.1) ^ k`.

Rewrite using `[Units.val_pow_eq_pow_val]`. Conclude with `map_pow (τ.1.mapMatrix) _ k`. Establish `h1 : X.maj (x (w + (k * M : ℕ))) τ (((γ : Matrix (Fin N) (Fin N) E).map τ.1) ^ k *ᵥ v) = X.maj (x w) τ v`. Rewrite using `[e, MajInv.maj_rmul X (MajInv.lact_mem_dom X hst hx) hb, ← hpow]`. Conclude with `MajInv.maj_lact X hst _ τ v`.

Establish `h2` using `GlobalTheory.T.majorant_harnack_holomorphic_half_plane E N X T x h.2.2.1 h.2.2.2.1 (w + (k * M : ℕ)) w (by simpa using hw) hw τ (((γ : Matrix (Fin N) (Fin N) E).map τ.1) ^ k *ᵥ v)`. Rewrite `h2` using `[h1, add_sub_cancel_left, Complex.norm_natCast, Complex.add_im, Complex.natCast_im, hwi]`. Establish `h3` using `ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.cs X hx τ (((γ : Matrix (Fin N) (Fin N) E).map τ.1) ^ k *ᵥ v) u`. Establish `hk : (0 : ℝ) ≤ k` using `k.cast_nonneg`. Establish `hM : (0 : ℝ) ≤ M` using `M.cast_nonneg`.

Establish `h4 : (2 + ((k * M : ℕ) : ℝ) ^ 2 / ((T + 1 + 0 - T) * (T + 1 - T))) ≤ (2 + M ^ 2) * (1 + k) ^ 2`. Rewrite using `[show (T + 1 + 0 - T) * (T + 1 - T) = 1 by ring]`. Use `push_cast`. Use polynomial arithmetic with `[mul_nonneg hk (sq_nonneg (M : ℝ)), sq_nonneg (k : ℝ), sq_nonneg (M : ℝ)]`. Use `le_of_sq_le_sq ?_ (by positivity)` and prove the remaining obligations.

Rewrite using `[mul_pow, Real.sq_sqrt (by positivity)]`. Use `h3.trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem linGrowth (h : IsOrbit X T M γ x) (τ : X.Ψ) : LinGrowth ((γ : Matrix (Fin N) (Fin N) E).map τ.1) := by
  intro v u hu
  set w : ℂ := ((T + 1 : ℝ) : ℂ) * Complex.I with hwdef
  have hwi : w.im = T + 1 := by simp [hwdef]
  have hw : T < w.im := by rw [hwi]; linarith
  have hx := h.2.2.2.1 w hw
  let L : (Fin N → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun p => X.Hf (x w) τ p u
      map_add' := fun p q => by
        have := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.Hf_sub_left X (x w) τ (p + q) q u
        rw [add_sub_cancel_right] at this
        rw [this]; ring
      map_smul' := fun k p => ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.Hf_smul_left X (x w) τ k p u }
  have hu0 := X.maj_pos hx τ hu
  have hv0 := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ v
  refine ⟨L, ?_, Real.sqrt ((2 + M ^ 2) * X.maj (x w) τ v * X.maj (x w) τ u), fun k => ?_⟩
  · show X.Hf (x w) τ u u ≠ 0
    rw [X.Hf_self hx τ u]
    exact_mod_cast hu0.ne'
  obtain ⟨b, hb, -, e⟩ := shift_pow h k w hw
  have hst := X.Γ_stab _ (pow_mem h.2.1 k)
  have hpow : ((γ ^ k : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 =
      ((γ : Matrix (Fin N) (Fin N) E).map τ.1) ^ k := by
    rw [Units.val_pow_eq_pow_val]
    exact map_pow (τ.1.mapMatrix) _ k
  have h1 : X.maj (x (w + (k * M : ℕ))) τ (((γ : Matrix (Fin N) (Fin N) E).map τ.1) ^ k *ᵥ v) = X.maj (x w) τ v := by
    rw [e, MajInv.maj_rmul X (MajInv.lact_mem_dom X hst hx) hb, ← hpow]
    exact MajInv.maj_lact X hst _ τ v
  have h2 := GlobalTheory.T.majorant_harnack_holomorphic_half_plane E N X T x h.2.2.1 h.2.2.2.1 (w + (k * M : ℕ)) w (by simpa using hw) hw τ
    (((γ : Matrix (Fin N) (Fin N) E).map τ.1) ^ k *ᵥ v)
  rw [h1, add_sub_cancel_left, Complex.norm_natCast, Complex.add_im, Complex.natCast_im, hwi] at h2
  have h3 := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.cs X hx τ (((γ : Matrix (Fin N) (Fin N) E).map τ.1) ^ k *ᵥ v) u
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have hM : (0 : ℝ) ≤ M := M.cast_nonneg
  have h4 : (2 + ((k * M : ℕ) : ℝ) ^ 2 / ((T + 1 + 0 - T) * (T + 1 - T))) ≤ (2 + M ^ 2) * (1 + k) ^ 2 := by
    rw [show (T + 1 + 0 - T) * (T + 1 - T) = 1 by ring]
    push_cast
    nlinarith [mul_nonneg hk (sq_nonneg (M : ℝ)), sq_nonneg (k : ℝ), sq_nonneg (M : ℝ)]
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  refine h3.trans ?_
  calc _ ≤ (2 + M ^ 2) * (1 + k) ^ 2 * X.maj (x w) τ v * X.maj (x w) τ u :=
        mul_le_mul_of_nonneg_right (h2.trans (mul_le_mul_of_nonneg_right h4 hv0)) hu0.le
    _ = _ := by ring

open Polynomial in

/- English proof (translation)
Establish `: Module.Finite (𝓞 E) Λ` using `Module.Finite.iff_fg.2 hfg`. Set `f : Module.End (𝓞 E) Λ` to `((Matrix.toLin' A).restrictScalars (𝓞 E)).restrict (fun v hv => hA v hv)`. Take `⟨q, hq, hq0⟩` from `LinearMap.exists_monic_and_aeval_eq_zero (𝓞 E) f`. Establish `hpow : ∀ (n : ℕ) (v : Λ), (((f ^ n) v : Λ) : Fin N → E) = A ^ n *ᵥ (v : Fin N → E)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => intro v`. Rewrite using `[pow_succ, Module.End.mul_apply, ih, pow_succ, ← Matrix.mulVec_mulVec]`. Both sides reduce to the same expression.

Establish `hae : ∀ (p : (𝓞 E)[X]) (v : Λ), ((aeval f p v : Λ) : Fin N → E) = aeval A p *ᵥ (v : Fin N → E)`. Introduce `p v`. Rewrite using `[aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum, Matrix.sum_mulVec]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, Submodule.coe_smul, hpow]`.

Conclude with `(Matrix.smul_mulVec (algebraMap (𝓞 E) E (p.coeff i)) (A ^ i) v).symm`. Use `⟨q, hq, Matrix.toLin'.injective (LinearMap.ext_on hsp fun v hv => ?_)⟩` and prove the remaining obligations. Use `hae q ⟨v, hv⟩` as an intermediate fact. Rewrite `this` using `[hq0]`. Simplify using `using this.symm`.
-/
theorem exists_monic (Λ : Submodule (𝓞 E) (Fin N → E)) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin N → E)) = ⊤)
    (A : Matrix (Fin N) (Fin N) E) (hA : ∀ v ∈ Λ, A *ᵥ v ∈ Λ) : ∃ q : (𝓞 E)[X], q.Monic ∧ aeval A q = 0 := by
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  let f : Module.End (𝓞 E) Λ := ((Matrix.toLin' A).restrictScalars (𝓞 E)).restrict (fun v hv => hA v hv)
  obtain ⟨q, hq, hq0⟩ := LinearMap.exists_monic_and_aeval_eq_zero (𝓞 E) f
  have hpow : ∀ (n : ℕ) (v : Λ), (((f ^ n) v : Λ) : Fin N → E) = A ^ n *ᵥ (v : Fin N → E) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro v; rw [pow_succ, Module.End.mul_apply, ih, pow_succ, ← Matrix.mulVec_mulVec]; rfl
  have hae : ∀ (p : (𝓞 E)[X]) (v : Λ), ((aeval f p v : Λ) : Fin N → E) = aeval A p *ᵥ (v : Fin N → E) := by
    intro p v
    rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, hpow]
    exact (Matrix.smul_mulVec (algebraMap (𝓞 E) E (p.coeff i)) (A ^ i) v).symm
  refine ⟨q, hq, Matrix.toLin'.injective (LinearMap.ext_on hsp fun v hv => ?_)⟩
  have := hae q ⟨v, hv⟩
  rw [hq0] at this
  simpa using this.symm

open Polynomial in
/- English proof (translation)
Use `set A : Matrix (Fin N) (Fin N) E := γ.val with hA`. Take `⟨q, hq, hq0⟩` from `exists_monic X.Λ X.Λ_fg X.Λ_span A fun v hv => ((X.Γ_stab _ h.2.1).2 v).1 hv`. Use `set p := minpoly E A with hp`. Establish `hint : IsIntegral E A` using `Algebra.IsIntegral.isIntegral A`. Establish `hpm : p.Monic` using `minpoly.monic hint`.

Establish `hpq : p ∣ q.map (algebraMap (𝓞 E) E)` using `minpoly.dvd E A (by rw [aeval_map_algebraMap, hq0])`. Establish `hpc : p ∣ A.charpoly` using `Matrix.minpoly_dvd_charpoly A`. Set `K` to `p.SplittingField`. Establish `: NumberField K` using `NumberField.of_module_finite E K`. Establish `hroot : ∀ a : K, aeval a p = 0 → ∃ n : ℕ, 0 < n ∧ a ^ n = 1`.

Introduce `a ha`. Establish `hc : aeval a A.charpoly = 0` using `aeval_eq_zero_of_dvd_aeval_eq_zero hpc ha`. Establish `hi : IsIntegral (𝓞 E) a`. Use `⟨q, hq, ?_⟩` and prove the remaining obligations. Use `aeval_eq_zero_of_dvd_aeval_eq_zero hpq ha` as an intermediate fact.

Rewrite `this` using `[aeval_map_algebraMap]`. Then use the resulting hypothesis. Establish `hi' : IsIntegral ℤ a` using `isIntegral_trans a hi`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Establish `h0 : A.charpoly.coeff 0 = 0`.

Rewrite `hc` using `[aeval_def, eval₂_at_zero]`. Conclude with `(map_eq_zero _).1 hc`. Establish `hd` using `Matrix.det_eq_sign_charpoly_coeff A`. Rewrite `hd` using `[h0, mul_zero]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero hd`.

Establish `hgood : ∀ φ : K →+* ℂ, φ.comp (algebraMap E K) ∈ X.Ψ → ‖φ a‖ ≤ 1`. Introduce `φ hφ`. Use `(linGrowth h ⟨_, hφ⟩).norm_le_one ?_` and prove the remaining obligations. Rewrite using `[Matrix.charpoly_map, IsRoot, Polynomial.eval_map, ← hom_eval₂, ← aeval_def, hc, map_zero]`. Take `⟨n, hn, hn1⟩` from `NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ ha0 hi' (fun φ => by`.

Distinguish the cases in `hφ : φ.comp (algebraMap E K) ∈ X.Ψ`. Conclude with `hgood φ hφ`. Establish `h2 : ComplexEmbedding.conjugate (φ.comp (algebraMap E K)) ∈ X.Ψ`. Assume the negation of the conclusion as `h3`. Conclude with `hφ ((X.cmType _).2 h3)`.

Use `hgood (ComplexEmbedding.conjugate φ) h2` as an intermediate fact. Simplify using `using this)`. Conclude with `⟨n, hn, hn1⟩`. Use `choose! n hn hn1 using hroot`. Use `set s := (p.map (algebraMap E K)).roots with hs`.

Establish `hmem : ∀ a ∈ s, aeval a p = 0` using `fun a ha => by`. Use `(mem_roots'.1 ha).2` as an intermediate fact. Rewrite `this` using `[IsRoot, eval_map_algebraMap]`. Then use the resulting hypothesis. Use `⟨∏ a ∈ s.toFinset, n a, Finset.prod_pos fun a ha => hn a (hmem a (Multiset.mem_toFinset.1 ha)), ?_⟩` and prove the remaining obligations. Use `set m := ∏ a ∈ s.toFinset, n a`.

Establish `hm : ∀ a ∈ s, a ^ m = 1` using `fun a ha => by`. Take `⟨c, hc⟩ : n a ∣ m` from `Finset.dvd_prod_of_mem _ (Multiset.mem_toFinset.2 ha)`. Rewrite using `[hc, pow_mul, hn1 a (hmem a ha), one_pow]`. Establish `hsplit : p.map (algebraMap E K) = (s.map fun a => Polynomial.X - C a).prod` using `(SplittingField.splits p).eq_prod_roots_of_monic (hpm.map _)`. Establish `hdvd : ∀ t : Multiset K, (∀ a ∈ t, a ^ m = 1) → (t.map fun a => Polynomial.X - C a).prod ∣ (Polynomial.X ^ m - 1 : K[X]) ^ t.card`.

Introduce `t`. Proceed by induction on `t using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a t ih`. Introduce `ht`.

Rewrite using `[Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']`. Use `mul_dvd_mul (dvd_iff_isRoot.2 ?_) (ih fun b hb => ht b (Multiset.mem_cons_of_mem hb))` and prove the remaining obligations. Simplify using `[ht a (Multiset.mem_cons_self a t)]`. Establish `hd : p ∣ (Polynomial.X ^ m - 1 : E[X]) ^ s.card`. Rewrite using `[← map_dvd_map' (algebraMap E K), hsplit]`.

Simplify using `using hdvd s hm`. Use `⟨s.card, ?_⟩` and prove the remaining obligations. Use `aeval_eq_zero_of_dvd_aeval_eq_zero hd (minpoly.aeval E A)` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_pow_nilpotent (h : IsOrbit X T M γ x) :
    ∃ m : ℕ, 0 < m ∧ IsNilpotent ((γ : Matrix (Fin N) (Fin N) E) ^ m - 1) := by
  classical
  set A : Matrix (Fin N) (Fin N) E := γ.val with hA
  obtain ⟨q, hq, hq0⟩ := exists_monic X.Λ X.Λ_fg X.Λ_span A fun v hv => ((X.Γ_stab _ h.2.1).2 v).1 hv
  set p := minpoly E A with hp
  have hint : IsIntegral E A := Algebra.IsIntegral.isIntegral A
  have hpm : p.Monic := minpoly.monic hint
  have hpq : p ∣ q.map (algebraMap (𝓞 E) E) := minpoly.dvd E A (by rw [aeval_map_algebraMap, hq0])
  have hpc : p ∣ A.charpoly := Matrix.minpoly_dvd_charpoly A
  let K := p.SplittingField
  have : NumberField K := NumberField.of_module_finite E K
  have hroot : ∀ a : K, aeval a p = 0 → ∃ n : ℕ, 0 < n ∧ a ^ n = 1 := by
    intro a ha
    have hc : aeval a A.charpoly = 0 := aeval_eq_zero_of_dvd_aeval_eq_zero hpc ha
    have hi : IsIntegral (𝓞 E) a := by
      refine ⟨q, hq, ?_⟩
      have := aeval_eq_zero_of_dvd_aeval_eq_zero hpq ha
      rwa [aeval_map_algebraMap] at this
    have hi' : IsIntegral ℤ a := isIntegral_trans a hi
    have ha0 : a ≠ 0 := by
      rintro rfl
      have h0 : A.charpoly.coeff 0 = 0 := by
        rw [aeval_def, eval₂_at_zero] at hc
        exact (map_eq_zero _).1 hc
      have hd := Matrix.det_eq_sign_charpoly_coeff A
      rw [h0, mul_zero] at hd
      exact ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero hd
    have hgood : ∀ φ : K →+* ℂ, φ.comp (algebraMap E K) ∈ X.Ψ → ‖φ a‖ ≤ 1 := by
      intro φ hφ
      refine (linGrowth h ⟨_, hφ⟩).norm_le_one ?_
      rw [Matrix.charpoly_map, IsRoot, Polynomial.eval_map, ← hom_eval₂, ← aeval_def, hc, map_zero]
    obtain ⟨n, hn, hn1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ ha0 hi' (fun φ => by
      by_cases hφ : φ.comp (algebraMap E K) ∈ X.Ψ
      · exact hgood φ hφ
      · have h2 : ComplexEmbedding.conjugate (φ.comp (algebraMap E K)) ∈ X.Ψ := by
          by_contra h3
          exact hφ ((X.cmType _).2 h3)
        have := hgood (ComplexEmbedding.conjugate φ) h2
        simpa using this)
    exact ⟨n, hn, hn1⟩
  choose! n hn hn1 using hroot
  set s := (p.map (algebraMap E K)).roots with hs
  have hmem : ∀ a ∈ s, aeval a p = 0 := fun a ha => by
    have := (mem_roots'.1 ha).2
    rwa [IsRoot, eval_map_algebraMap] at this
  refine ⟨∏ a ∈ s.toFinset, n a, Finset.prod_pos fun a ha => hn a (hmem a (Multiset.mem_toFinset.1 ha)), ?_⟩
  set m := ∏ a ∈ s.toFinset, n a
  have hm : ∀ a ∈ s, a ^ m = 1 := fun a ha => by
    obtain ⟨c, hc⟩ : n a ∣ m := Finset.dvd_prod_of_mem _ (Multiset.mem_toFinset.2 ha)
    rw [hc, pow_mul, hn1 a (hmem a ha), one_pow]
  have hsplit : p.map (algebraMap E K) = (s.map fun a => Polynomial.X - C a).prod :=
    (SplittingField.splits p).eq_prod_roots_of_monic (hpm.map _)
  have hdvd : ∀ t : Multiset K, (∀ a ∈ t, a ^ m = 1) →
      (t.map fun a => Polynomial.X - C a).prod ∣ (Polynomial.X ^ m - 1 : K[X]) ^ t.card := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      intro ht
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
      refine mul_dvd_mul (dvd_iff_isRoot.2 ?_) (ih fun b hb => ht b (Multiset.mem_cons_of_mem hb))
      simp [ht a (Multiset.mem_cons_self a t)]
  have hd : p ∣ (Polynomial.X ^ m - 1 : E[X]) ^ s.card := by
    rw [← map_dvd_map' (algebraMap E K), hsplit]
    simpa using hdvd s hm
  refine ⟨s.card, ?_⟩
  have := aeval_eq_zero_of_dvd_aeval_eq_zero hd (minpoly.aeval E A)
  simpa using this

/- English proof (translation)
Introduce `E _ _ _ N X T M γ x h`. Take `⟨m, hm, hnil⟩` from `exists_pow_nilpotent h`. Use `⟨m * M, γ ^ m, isOrbit_pow h hm, ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Conclude with `hne φ ((X.cmType φ).2 (hne _))`. Establish `hg` using `(linGrowth h ⟨τ, hτ⟩).pow m`. Set `F : Matrix (Fin N) (Fin N) E →+* Matrix (Fin N) (Fin N) ℂ` to `τ.mapMatrix`.

Establish `e : ((γ : Matrix (Fin N) (Fin N) E).map τ) ^ m = 1 + F ((γ : Matrix (Fin N) (Fin N) E) ^ m - 1)`. Rewrite using `[map_sub, map_one, map_pow, add_sub_cancel]`. Both sides reduce to the same expression. Rewrite `hg` using `[e]`. Establish `h2` using `hg.sq_eq_zero (hnil.map F)`.

Rewrite `h2` using `[← map_pow]`. Rewrite using `[Units.val_pow_eq_pow_val]`. Use extensionality with `i j`. Conclude with `(map_eq_zero τ).1 (congrFun (congrFun h2 i) j)`.
-/
theorem exists_isOrbit_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N), IsOrbit X T M γ x → ∃ (M' : ℕ) (γ' : GL (Fin N) E), IsOrbit X T M' γ' x ∧ ((γ' : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 := by
  intro E _ _ _ N X T M γ x h
  obtain ⟨m, hm, hnil⟩ := exists_pow_nilpotent h
  refine ⟨m * M, γ ^ m, isOrbit_pow h hm, ?_⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_contra hne
    push Not at hne
    exact hne φ ((X.cmType φ).2 (hne _))
  have hg := (linGrowth h ⟨τ, hτ⟩).pow m
  let F : Matrix (Fin N) (Fin N) E →+* Matrix (Fin N) (Fin N) ℂ := τ.mapMatrix
  have e : ((γ : Matrix (Fin N) (Fin N) E).map τ) ^ m = 1 + F ((γ : Matrix (Fin N) (Fin N) E) ^ m - 1) := by
    rw [map_sub, map_one, map_pow, add_sub_cancel]; rfl
  rw [e] at hg
  have h2 := hg.sq_eq_zero (hnil.map F)
  rw [← map_pow] at h2
  rw [Units.val_pow_eq_pow_val]
  ext i j
  exact (map_eq_zero τ).1 (congrFun (congrFun h2 i) j)

end GlobalTheory.ShFam.OrbitUnip
