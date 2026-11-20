import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandauSummableOfExpDirichletSeriesEntire
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasSumLogZetaSqMul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EulerProductNeZeroOneOfEntire

open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Establish `hZ' : Differentiable ℂ (fun s => starRingEnd ℂ (Z (starRingEnd ℂ s)))`. Introduce `s`. Use `(hZ (starRingEnd ℂ s)).conj_conj` as an intermediate fact. Rewrite `this` using `[Complex.conj_conj]`. Conclude with `this`.

Establish `hev : (fun s => starRingEnd ℂ (Z (starRingEnd ℂ s))) =ᶠ[nhds (2 : ℂ)] Z`. Establish `ho : IsOpen {s : ℂ | 1 < s.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Use `filter_upwards [ho.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs`. Conclude with `h s hs`. Use `AnalyticOnNhd.eq_of_eventuallyEq (hZ'.differentiableOn.analyticOnNhd isOpen_univ) (hZ.differentiableOn.analyticOnNhd isOpen_univ) hev` as an intermediate fact.

Conclude with `congrFun this s`.
-/
theorem conj_apply_conj_of_entire (Z : ℂ → ℂ) (hZ : Differentiable ℂ Z)
    (h : ∀ s : ℂ, 1 < s.re → starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s) (s : ℂ) :
    starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s := by
  have hZ' : Differentiable ℂ (fun s => starRingEnd ℂ (Z (starRingEnd ℂ s))) := by
    intro s
    have := (hZ (starRingEnd ℂ s)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  have hev : (fun s => starRingEnd ℂ (Z (starRingEnd ℂ s))) =ᶠ[nhds (2 : ℂ)] Z := by
    have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
    exact h s hs
  have := AnalyticOnNhd.eq_of_eventuallyEq
    (hZ'.differentiableOn.analyticOnNhd isOpen_univ)
    (hZ.differentiableOn.analyticOnNhd isOpen_univ) hev
  exact congrFun this s

/- English proof (translation)
Introduce `ι N hN hsum hne Z hZ hZs t ht ha`. Take `⟨i₀⟩` from `hne`. Establish `hpos : ∀ i, 0 < N i` using `fun i => by have := hN i; omega`. Establish `hN0 : ∀ i, ((N i : ℕ) : ℂ) ≠ 0` using `fun i => by exact_mod_cast (hpos i).ne'`. Establish `hconj : ∀ s, starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s`.

Use `conj_apply_conj_of_entire Z hZ fun s hs => ?_` and prove the remaining obligations. Establish `hs' : 1 < (starRingEnd ℂ s).re` using `by simpa using hs`. Rewrite using `[hZs _ hs', hZs s hs, map_mul, map_sub, Complex.conj_conj, map_one, ← Complex.exp_conj, Complex.conj_tsum]`. Simplify using `only [conj_neg_log_euler_factor _ (hN _) 1 (by simp) s hs, map_one]`. Use `set u : ℂ := (t : ℂ) * Complex.I with hu`.

Establish `hu0 : u ≠ 0` using `mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero`. Establish `hure : u.re = 0` using `by simp [hu]`. Establish `huc : starRingEnd ℂ u = -u` using `by simp [hu]`. Establish `hb : Z (1 - u) = 0`. Rewrite using `[← hconj, map_sub, map_one, huc, sub_neg_eq_add, ha, map_zero]`.

Establish `hds : ∀ (f : ℂ → ℂ) (a : ℂ), Differentiable ℂ f → Differentiable ℂ (dslope f a)`. Introduce `f a hf`. Rewrite using `[← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]`. Conclude with `hf.differentiableOn`. Establish `hmul : ∀ (f : ℂ → ℂ) (a : ℂ), f a = 0 → ∀ s, (s - a) * dslope f a s = f s`.

Introduce `f a h0 s`. Use `sub_smul_dslope f a s` as an intermediate fact. Rewrite `this` using `[smul_eq_mul, h0, sub_zero]`. Conclude with `this`. Establish `hD1` using `hds Z (1 + u) hZ`.

Establish `hD2` using `hds Z (1 - u) hZ`. Establish `hG` using `hds _ (1 - u) hD1`. Establish `hD1b : dslope Z (1 + u) (1 - u) = 0`. Use `hmul Z (1 + u) ha (1 - u)` as an intermediate fact. Rewrite `this` using `[hb, mul_eq_zero]`.

Use `this.resolve_left fun h => hu0 ?_` and prove the remaining obligations. Take the linear combination `(-1 / 2 : ℂ) * h`. Use `set c : ι → ℂ := fun i => ((N i : ℕ) : ℂ) ^ (-u) with hcdef`. Establish `hc : ∀ i, ‖c i‖ ≤ 1` using `fun i => by`. Simplify using `only [hcdef]`.

Rewrite using `[Complex.norm_natCast_cpow_of_pos (hpos i), Complex.neg_re, hure]`. Simplify using the standard rewrite rules. Establish `hcc : ∀ i, starRingEnd ℂ (c i) = ((N i : ℕ) : ℂ) ^ u` using `fun i => by`. Establish `harg' : ((N i : ℕ) : ℂ).arg ≠ Real.pi`. Rewrite using `[Complex.natCast_arg]`.

Conclude with `Real.pi_ne_zero.symm`. Use `Complex.cpow_conj ((N i : ℕ) : ℂ) (-u) harg'` as an intermediate fact. Rewrite `this` using `[map_neg, huc, neg_neg, map_natCast]`. Conclude with `this.symm`. Establish `key` using `GlobalTheory.landau_exp_summable (ι × ℕ) (fun p => (2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1)) (fun p => ((p.2 : ℝ) + 1) * Real.log (N p.1)) (fun s => Z s * dslope (dslope Z (1 + u)) (1 - u) s * dslope Z (1 + u) (s + u) * dslope Z (1 - u) (s - u)) (fun p => by`.

Establish `hw : ‖c p.1 ^ (p.2 + 1)‖ ≤ 1`. Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) (hc _)`. Establish `h1` using `Complex.abs_re_le_norm (c p.1 ^ (p.2 + 1))`. Establish `h2` using `neg_abs_le (c p.1 ^ (p.2 + 1)).re`.

Apply `div_nonneg (by linarith) (by positivity))` to reduce the goal to its premises. Use the proof step `(fun p => mul_nonneg (by positivity) (Real.log_natCast_nonneg _))`. Use the proof step `(((hZ.mul hG).mul (hD1.comp (differentiable_id.add_const u))).mul (hD2.comp (differentiable_id.sub_const u)))`. Use the proof step `(fun s hs => by`. Use `⟨_, GlobalTheory.LogEulerSeries.hasSum_log_zeta_sq_mul ι N c hN hc hsum s hs, ?_⟩` and prove the remaining obligations.

Establish `e1 : ∀ i, c i * ((N i : ℕ) : ℂ) ^ (-s) = 1 * ((N i : ℕ) : ℂ) ^ (-(s + u))`. Introduce `i`. Simplify using `only [hcdef]`. Rewrite using `[one_mul, ← Complex.cpow_add _ _ (hN0 i)]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∀ i, starRingEnd ℂ (c i) * ((N i : ℕ) : ℂ) ^ (-s) = 1 * ((N i : ℕ) : ℂ) ^ (-(s - u))`. Introduce `i`. Rewrite using `[hcc, one_mul, ← Complex.cpow_add _ _ (hN0 i)]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e1, e2]`. Rewrite using `[Complex.exp_add, Complex.exp_add, two_mul, Complex.exp_add]`. Establish `h0` using `hZs s hs`. Establish `h1` using `hZs (s + u) (by simpa [hure] using hs)`.

Establish `h2` using `hZs (s - u) (by simpa [hure] using hs)`. Establish `g0` using `hmul Z (1 + u) ha s`. Establish `g0'` using `hmul _ (1 - u) hD1b s`. Establish `g1` using `hmul Z (1 + u) ha (s + u)`. Establish `g2` using `hmul Z (1 - u) hb (s - u)`.

Establish `n1 : s - 1 ≠ 0` using `fun h => by`. Use `congrArg Complex.re h` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `n2 : s - (1 + u) ≠ 0` using `fun h => by`.

Use `congrArg Complex.re h` as an intermediate fact. Simplify using `[hure] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `n3 : s - (1 - u) ≠ 0` using `fun h => by`. Use `congrArg Complex.re h` as an intermediate fact.

Simplify using `[hure] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Generalize the expression as in `Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s))) = E at *`. Generalize the expression as in `Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-(s + u)))) = E1 at *`. Generalize the expression as in `Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-(s - u)))) = E2 at *`.

Generalize the expression as in `dslope (dslope Z (1 + u)) (1 - u) s = G at *`. Generalize the expression as in `dslope Z (1 + u) (s + u) = A at *`. Generalize the expression as in `dslope Z (1 - u) (s - u) = B at *`. Establish `k0 : (s - (1 + u)) * (s - (1 - u)) * G = (s - 1) * E`. Rewrite using `[← h0, ← g0, ← g0']`.

Expand and normalize the polynomial expressions, which then agree. Establish `k1 : (s - 1) * A = (s - (1 - u)) * E1`. Take the linear combination `g1 + h1`. Establish `k2 : (s - 1) * B = (s - (1 + u)) * E2`. Take the linear combination `g2 + h2`.

Apply `mul_left_cancel₀ (mul_ne_zero (mul_ne_zero n1 n2) n3)` to reduce the goal to its premises. Rewrite using `[h0]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `not_summable_two_add_two_re_pow_div (c i₀) (hc i₀) (key.prod_factor i₀)`.
-/
theorem zetaEulerProduct_ne_zero_one_add_mul_I : ∀ (ι : Type) (N : ι → ℕ), (∀ i, 2 ≤ N i) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → Nonempty ι → ∀ Z : ℂ → ℂ, Differentiable ℂ Z → (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s)))) → ∀ t : ℝ, t ≠ 0 → Z (1 + (t : ℂ) * Complex.I) ≠ 0 := by
  intro ι N hN hsum hne Z hZ hZs t ht ha
  obtain ⟨i₀⟩ := hne
  have hpos : ∀ i, 0 < N i := fun i => by have := hN i; omega
  have hN0 : ∀ i, ((N i : ℕ) : ℂ) ≠ 0 := fun i => by exact_mod_cast (hpos i).ne'
  have hconj : ∀ s, starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s := by
    refine conj_apply_conj_of_entire Z hZ fun s hs => ?_
    have hs' : 1 < (starRingEnd ℂ s).re := by simpa using hs
    rw [hZs _ hs', hZs s hs, map_mul, map_sub, Complex.conj_conj, map_one, ← Complex.exp_conj,
      Complex.conj_tsum]
    simp only [conj_neg_log_euler_factor _ (hN _) 1 (by simp) s hs, map_one]
  set u : ℂ := (t : ℂ) * Complex.I with hu
  have hu0 : u ≠ 0 := mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
  have hure : u.re = 0 := by simp [hu]
  have huc : starRingEnd ℂ u = -u := by simp [hu]
  have hb : Z (1 - u) = 0 := by
    rw [← hconj, map_sub, map_one, huc, sub_neg_eq_add, ha, map_zero]
  have hds : ∀ (f : ℂ → ℂ) (a : ℂ), Differentiable ℂ f → Differentiable ℂ (dslope f a) := by
    intro f a hf
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact hf.differentiableOn
  have hmul : ∀ (f : ℂ → ℂ) (a : ℂ), f a = 0 → ∀ s, (s - a) * dslope f a s = f s := by
    intro f a h0 s
    have := sub_smul_dslope f a s
    rw [smul_eq_mul, h0, sub_zero] at this
    exact this
  have hD1 := hds Z (1 + u) hZ
  have hD2 := hds Z (1 - u) hZ
  have hG := hds _ (1 - u) hD1
  have hD1b : dslope Z (1 + u) (1 - u) = 0 := by
    have := hmul Z (1 + u) ha (1 - u)
    rw [hb, mul_eq_zero] at this
    refine this.resolve_left fun h => hu0 ?_
    linear_combination (-1 / 2 : ℂ) * h
  set c : ι → ℂ := fun i => ((N i : ℕ) : ℂ) ^ (-u) with hcdef
  have hc : ∀ i, ‖c i‖ ≤ 1 := fun i => by
    simp only [hcdef]
    rw [Complex.norm_natCast_cpow_of_pos (hpos i), Complex.neg_re, hure]
    simp
  have hcc : ∀ i, starRingEnd ℂ (c i) = ((N i : ℕ) : ℂ) ^ u := fun i => by
    have harg' : ((N i : ℕ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
    have := Complex.cpow_conj ((N i : ℕ) : ℂ) (-u) harg'
    rw [map_neg, huc, neg_neg, map_natCast] at this
    exact this.symm
  have key := GlobalTheory.landau_exp_summable (ι × ℕ)
    (fun p => (2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1))
    (fun p => ((p.2 : ℝ) + 1) * Real.log (N p.1))
    (fun s => Z s * dslope (dslope Z (1 + u)) (1 - u) s * dslope Z (1 + u) (s + u) *
      dslope Z (1 - u) (s - u))
    (fun p => by
      have hw : ‖c p.1 ^ (p.2 + 1)‖ ≤ 1 := by
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hc _)
      have h1 := Complex.abs_re_le_norm (c p.1 ^ (p.2 + 1))
      have h2 := neg_abs_le (c p.1 ^ (p.2 + 1)).re
      apply div_nonneg (by linarith) (by positivity))
    (fun p => mul_nonneg (by positivity) (Real.log_natCast_nonneg _))
    (((hZ.mul hG).mul (hD1.comp (differentiable_id.add_const u))).mul
      (hD2.comp (differentiable_id.sub_const u)))
    (fun s hs => by
      refine ⟨_, GlobalTheory.LogEulerSeries.hasSum_log_zeta_sq_mul ι N c hN hc hsum s hs, ?_⟩
      have e1 : ∀ i, c i * ((N i : ℕ) : ℂ) ^ (-s) = 1 * ((N i : ℕ) : ℂ) ^ (-(s + u)) := by
        intro i
        simp only [hcdef]
        rw [one_mul, ← Complex.cpow_add _ _ (hN0 i)]
        congr 1; ring
      have e2 : ∀ i, starRingEnd ℂ (c i) * ((N i : ℕ) : ℂ) ^ (-s) =
          1 * ((N i : ℕ) : ℂ) ^ (-(s - u)) := by
        intro i
        rw [hcc, one_mul, ← Complex.cpow_add _ _ (hN0 i)]
        congr 1; ring
      simp only [e1, e2]
      rw [Complex.exp_add, Complex.exp_add, two_mul, Complex.exp_add]
      have h0 := hZs s hs
      have h1 := hZs (s + u) (by simpa [hure] using hs)
      have h2 := hZs (s - u) (by simpa [hure] using hs)
      have g0 := hmul Z (1 + u) ha s
      have g0' := hmul _ (1 - u) hD1b s
      have g1 := hmul Z (1 + u) ha (s + u)
      have g2 := hmul Z (1 - u) hb (s - u)
      have n1 : s - 1 ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp at this; linarith
      have n2 : s - (1 + u) ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp [hure] at this; linarith
      have n3 : s - (1 - u) ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp [hure] at this; linarith
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s))) = E at *
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-(s + u)))) = E1 at *
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-(s - u)))) = E2 at *
      generalize dslope (dslope Z (1 + u)) (1 - u) s = G at *
      generalize dslope Z (1 + u) (s + u) = A at *
      generalize dslope Z (1 - u) (s - u) = B at *
      have k0 : (s - (1 + u)) * (s - (1 - u)) * G = (s - 1) * E := by
        rw [← h0, ← g0, ← g0']; ring
      have k1 : (s - 1) * A = (s - (1 - u)) * E1 := by
        linear_combination g1 + h1
      have k2 : (s - 1) * B = (s - (1 + u)) * E2 := by
        linear_combination g2 + h2
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero n1 n2) n3)
      rw [h0]
      calc (s - 1) * (s - (1 + u)) * (s - (1 - u)) * ((s - 1) * E * G * A * B)
          = E * ((s - (1 + u)) * (s - (1 - u)) * G) * ((s - 1) * A) * ((s - 1) * B) := by ring
        _ = _ := by rw [k0, k1, k2]; ring)
  exact not_summable_two_add_two_re_pow_div (c i₀) (hc i₀) (key.prod_factor i₀)

end GlobalTheory
