import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet.UnitaryFlow

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Establish `h1 : HasDerivAt (fun t => U (t - s) a) b s`. Establish `h' : HasDerivAt (fun t => U t a) b (s - s)` using `by rw [sub_self]; exact h`. Conclude with `h'.comp_sub_const s s`. Establish `h2 : HasDerivAt (fun t => U s (U (t - s) a)) (U s b) s` using `((U s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1`. Establish `h3 : (fun t => U s (U (t - s) a)) = fun t => U t a`.

Use function extensionality and compare the values at `t`. Establish `e` using `hadd s (t - s)`. Rewrite `e` using `[show s + (t - s) = t by ring]`. Rewrite using `[e]`. Both sides reduce to the same expression.

Rewrite `h2` using `[h3]`. Then use the resulting hypothesis.
-/
theorem hasDerivAt_orbit (U : ℝ → (H →L[ℂ] H)) (hadd : ∀ s t, U (s + t) = U s * U t)
    (a b : H) (h : HasDerivAt (fun t => U t a) b 0) (s : ℝ) :
    HasDerivAt (fun t => U t a) (U s b) s := by
  have h1 : HasDerivAt (fun t => U (t - s) a) b s := by
    have h' : HasDerivAt (fun t => U t a) b (s - s) := by rw [sub_self]; exact h
    exact h'.comp_sub_const s s
  have h2 : HasDerivAt (fun t => U s (U (t - s) a)) (U s b) s :=
    ((U s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
  have h3 : (fun t => U s (U (t - s) a)) = fun t => U t a := by
    funext t
    have e := hadd s (t - s)
    rw [show s + (t - s) = t by ring] at e
    rw [e]
    rfl
  rwa [h3] at h2

/- English proof (translation)
Establish `hconst : ∀ t, ⟪U t (x i), U t (x k)⟫_ℂ = ⟪x i, x k⟫_ℂ`. Introduce `t`. Set `L : H →ₗᵢ[ℂ] H` to `⟨(U t).toLinearMap, hn t⟩`. Conclude with `L.inner_map_map (x i) (x k)`. Establish `hder` using `(hd i).inner ℂ (hd k)`.

Simplify using `only [hconst, h0, ContinuousLinearMap.one_apply] at hder`. Establish `h2` using `hder.unique (hasDerivAt_const (0 : ℝ) ⟪x i, x k⟫_ℂ)`. Take the linear combination `h2`.
-/
theorem inner_skew (U : ℝ → (H →L[ℂ] H)) (x : ℕ → H) (h0 : U 0 = 1)
    (hn : ∀ t v, ‖U t v‖ = ‖v‖)
    (hd : ∀ m, HasDerivAt (fun t => U t (x m)) (x (m + 1)) 0) (i k : ℕ) :
    ⟪x (i + 1), x k⟫_ℂ = -⟪x i, x (k + 1)⟫_ℂ := by
  have hconst : ∀ t, ⟪U t (x i), U t (x k)⟫_ℂ = ⟪x i, x k⟫_ℂ := by
    intro t
    let L : H →ₗᵢ[ℂ] H := ⟨(U t).toLinearMap, hn t⟩
    exact L.inner_map_map (x i) (x k)
  have hder := (hd i).inner ℂ (hd k)
  simp only [hconst, h0, ContinuousLinearMap.one_apply] at hder
  have h2 := hder.unique (hasDerivAt_const (0 : ℝ) ⟪x i, x k⟫_ℂ)
  linear_combination h2

/- English proof (translation)
Proceed by induction on `i generalizing k with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[h n k, norm_neg, ih (k + 1), show n + (k + 1) = n + 1 + k by omega]`.
-/
theorem norm_inner_shift (x : ℕ → H)
    (h : ∀ i k, ⟪x (i + 1), x k⟫_ℂ = -⟪x i, x (k + 1)⟫_ℂ) (i k : ℕ) :
    ‖⟪x i, x k⟫_ℂ‖ = ‖⟪x 0, x (i + k)⟫_ℂ‖ := by
  induction i generalizing k with
  | zero => simp
  | succ n ih =>
    rw [h n k, norm_neg, ih (k + 1), show n + (k + 1) = n + 1 + k by omega]

/- English proof (translation)
Establish `h1 : (2 * m).choose m * m.factorial * m.factorial = (2 * m).factorial`. Establish `e` using `Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)`. Rewrite `e` using `[show 2 * m - m = m by omega]`. Then use the resulting hypothesis. Establish `h2 : (2 * m).choose m ≤ 2 ^ (2 * m)` using `Nat.choose_le_two_pow _ _`. Establish `h3 : (2 * m).factorial ≤ 2 ^ (2 * m) * m.factorial ^ 2`.

Rewrite using `[← h1, sq, ← mul_assoc]`. Conclude with `Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2)`. Conclude with `h3` after adjusting the coercions.
-/
theorem factorial_two_mul_le (m : ℕ) :
    (((2 * m).factorial : ℕ) : ℝ) ≤ 2 ^ (2 * m) * (m.factorial : ℝ) ^ 2 := by
  have h1 : (2 * m).choose m * m.factorial * m.factorial = (2 * m).factorial := by
    have e := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    rwa [show 2 * m - m = m by omega] at e
  have h2 : (2 * m).choose m ≤ 2 ^ (2 * m) := Nat.choose_le_two_pow _ _
  have h3 : (2 * m).factorial ≤ 2 ^ (2 * m) * m.factorial ^ 2 := by
    rw [← h1, sq, ← mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2)
  exact_mod_cast h3

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[iteratedDeriv_succ, ih]`. Use function extensionality and compare the values at `t`.

Conclude with `(hg n t).deriv`.
-/
theorem iteratedDeriv_chain (g : ℕ → ℝ → ℂ)
    (hg : ∀ m t, HasDerivAt (g m) (g (m + 1) t) t) (m : ℕ) :
    iteratedDeriv m (g 0) = g m := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hg n t).deriv

/- English proof (translation)
Establish `hf0 : AnalyticAt ℝ f 0` using `hf 0 (Set.mem_univ _)`. Establish `hg0 : AnalyticAt ℝ g 0` using `hg 0 (Set.mem_univ _)`. Establish `hz : ∀ n, iteratedDeriv n (f - g) 0 = 0`. Introduce `n`. Rewrite using `[iteratedDeriv_sub hf0.contDiffAt hg0.contDiffAt, h n, sub_self]`.

Establish `htop : analyticOrderAt (f - g) 0 = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨k, hk⟩` from `ENat.ne_top_iff_exists.mp hne`. Establish `hle` using `(natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf0.sub hg0) (n := k + 1)).mpr (fun i _ => hz i)`. Rewrite `hle` using `[← hk]`.

Normalize the coercions in `at hle`. Use linear arithmetic over natural numbers and integers. Establish `hev : f =ᶠ[𝓝 0] g` using `by filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz`. Simplify `hz` using `[sub_eq_zero]`. Conclude with `congrFun (AnalyticOnNhd.eq_of_eventuallyEq hf hg hev) t`.
-/
theorem eq_of_iteratedDeriv_eq (f g : ℝ → ℂ) (hf : AnalyticOnNhd ℝ f Set.univ)
    (hg : AnalyticOnNhd ℝ g Set.univ) (h : ∀ m, iteratedDeriv m f 0 = iteratedDeriv m g 0)
    (t : ℝ) : f t = g t := by
  have hf0 : AnalyticAt ℝ f 0 := hf 0 (Set.mem_univ _)
  have hg0 : AnalyticAt ℝ g 0 := hg 0 (Set.mem_univ _)
  have hz : ∀ n, iteratedDeriv n (f - g) 0 = 0 := by
    intro n
    rw [iteratedDeriv_sub hf0.contDiffAt hg0.contDiffAt, h n, sub_self]
  have htop : analyticOrderAt (f - g) 0 = ⊤ := by
    by_contra hne
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
    have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf0.sub hg0)
      (n := k + 1)).mpr (fun i _ => hz i)
    rw [← hk] at hle
    norm_cast at hle
    omega
  have hev : f =ᶠ[𝓝 0] g := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    simpa [sub_eq_zero] using hz
  exact congrFun (AnalyticOnNhd.eq_of_eventuallyEq hf hg hev) t

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `m t _`. Simplify using `using hM m t`.

Consider the case `succ n ih`. Introduce `m t ht`. Establish `hsum : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.range (n + 1), (s ^ k / (k.factorial : ℝ)) • V (m + k) 0) (∑ k ∈ Finset.range n, (s ^ k / (k.factorial : ℝ)) • V (m + 1 + k) 0) s`. Introduce `s`. Establish `e : (fun s : ℝ => ∑ k ∈ Finset.range (n + 1), (s ^ k / (k.factorial : ℝ)) • V (m + k) 0) = fun s : ℝ => (∑ k ∈ Finset.range n, (s ^ (k + 1) / ((k + 1).factorial : ℝ)) • V (m + 1 + k) 0) + V m 0`.

Use function extensionality and compare the values at `s`. Rewrite using `[Finset.sum_range_succ']`. Simplify using `only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_smul, add_zero]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[show m + (k + 1) = m + 1 + k by omega]`. Rewrite using `[e]`. Establish `hterm : ∀ k ∈ Finset.range n, HasDerivAt (fun s : ℝ => (s ^ (k + 1) / ((k + 1).factorial : ℝ)) • V (m + 1 + k) 0) ((s ^ k / (k.factorial : ℝ)) • V (m + 1 + k) 0) s`. Introduce `k _`. Establish `hc : ((k + 1 : ℕ) : ℝ) * s ^ (k + 1 - 1) / ((k + 1).factorial : ℝ) = s ^ k / (k.factorial : ℝ)`.

Rewrite using `[Nat.add_sub_cancel, Nat.factorial_succ]`. Establish `hk : (k.factorial : ℝ) ≠ 0` using `by positivity`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`.

Conclude with `(((hasDerivAt_pow (k + 1) s).div_const ((k + 1).factorial : ℝ)).smul_const (V (m + 1 + k) 0)).congr_deriv (by rw [hc])`. Conclude with `(HasDerivAt.fun_sum hterm).add_const (V m 0)`. Establish `hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => V m s - ∑ k ∈ Finset.range (n + 1), (s ^ k / (k.factorial : ℝ)) • V (m + k) 0) (V (m + 1) s - ∑ k ∈ Finset.range n, (s ^ k / (k.factorial : ℝ)) • V (m + 1 + k) 0) s` using `fun s => (hV m s).sub (hsum s)`. Establish `hB : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s ^ (n + 1) / ((n + 1).factorial : ℝ) * M (m + 1 + n)) (s ^ n / (n.factorial : ℝ) * M (m + 1 + n)) s`. Introduce `s`.

Establish `hc : ((n + 1 : ℕ) : ℝ) * s ^ (n + 1 - 1) / ((n + 1).factorial : ℝ) = s ^ n / (n.factorial : ℝ)`. Rewrite using `[Nat.add_sub_cancel, Nat.factorial_succ]`. Establish `hk : (n.factorial : ℝ) ≠ 0` using `by positivity`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `try ring`. Conclude with `(((hasDerivAt_pow (n + 1) s).div_const ((n + 1).factorial : ℝ)).mul_const (M (m + 1 + n))).congr_deriv (by rw [hc])`. Establish `key` using `image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := t) (fun s _ => (hderiv s).continuousAt.continuousWithinAt) (fun s _ => (hderiv s).hasDerivWithinAt) (by simp [Finset.sum_range_succ']) hB (fun s hs => ih (m + 1) s hs.1) (show t ∈ Set.Icc (0 : ℝ) t from ⟨ht, le_rf …`. Rewrite using `[show m + (n + 1) = m + 1 + n by omega]`. Conclude with `key`.
-/
private theorem norm_sub_taylor_sum_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : ℕ → ℝ → E) (M : ℕ → ℝ)
    (hV : ∀ m s, HasDerivAt (V m) (V (m + 1) s) s) (hM : ∀ m s, ‖V m s‖ ≤ M m) :
    ∀ (n m : ℕ) (t : ℝ), 0 ≤ t →
      ‖V m t - ∑ k ∈ Finset.range n, (t ^ k / (k.factorial : ℝ)) • V (m + k) 0‖ ≤
        t ^ n / (n.factorial : ℝ) * M (m + n) := by
  intro n
  induction n with
  | zero =>
    intro m t _
    simpa using hM m t
  | succ n ih =>
    intro m t ht
    have hsum : ∀ s : ℝ, HasDerivAt
        (fun s : ℝ => ∑ k ∈ Finset.range (n + 1), (s ^ k / (k.factorial : ℝ)) • V (m + k) 0)
        (∑ k ∈ Finset.range n, (s ^ k / (k.factorial : ℝ)) • V (m + 1 + k) 0) s := by
      intro s
      have e : (fun s : ℝ => ∑ k ∈ Finset.range (n + 1), (s ^ k / (k.factorial : ℝ)) • V (m + k) 0) =
          fun s : ℝ => (∑ k ∈ Finset.range n,
            (s ^ (k + 1) / ((k + 1).factorial : ℝ)) • V (m + 1 + k) 0) + V m 0 := by
        funext s
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_smul, add_zero]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show m + (k + 1) = m + 1 + k by omega]
      rw [e]
      have hterm : ∀ k ∈ Finset.range n, HasDerivAt
          (fun s : ℝ => (s ^ (k + 1) / ((k + 1).factorial : ℝ)) • V (m + 1 + k) 0)
          ((s ^ k / (k.factorial : ℝ)) • V (m + 1 + k) 0) s := by
        intro k _
        have hc : ((k + 1 : ℕ) : ℝ) * s ^ (k + 1 - 1) / ((k + 1).factorial : ℝ) =
            s ^ k / (k.factorial : ℝ) := by
          rw [Nat.add_sub_cancel, Nat.factorial_succ]
          have hk : (k.factorial : ℝ) ≠ 0 := by positivity
          push_cast
          field_simp
          try ring
        exact (((hasDerivAt_pow (k + 1) s).div_const ((k + 1).factorial : ℝ)).smul_const
          (V (m + 1 + k) 0)).congr_deriv (by rw [hc])
      exact (HasDerivAt.fun_sum hterm).add_const (V m 0)
    have hderiv : ∀ s : ℝ, HasDerivAt
        (fun s : ℝ => V m s - ∑ k ∈ Finset.range (n + 1), (s ^ k / (k.factorial : ℝ)) • V (m + k) 0)
        (V (m + 1) s - ∑ k ∈ Finset.range n, (s ^ k / (k.factorial : ℝ)) • V (m + 1 + k) 0) s :=
      fun s => (hV m s).sub (hsum s)
    have hB : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s ^ (n + 1) / ((n + 1).factorial : ℝ) * M (m + 1 + n))
        (s ^ n / (n.factorial : ℝ) * M (m + 1 + n)) s := by
      intro s
      have hc : ((n + 1 : ℕ) : ℝ) * s ^ (n + 1 - 1) / ((n + 1).factorial : ℝ) =
          s ^ n / (n.factorial : ℝ) := by
        rw [Nat.add_sub_cancel, Nat.factorial_succ]
        have hk : (n.factorial : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp
        try ring
      exact (((hasDerivAt_pow (n + 1) s).div_const ((n + 1).factorial : ℝ)).mul_const
        (M (m + 1 + n))).congr_deriv (by rw [hc])
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := t)
      (fun s _ => (hderiv s).continuousAt.continuousWithinAt)
      (fun s _ => (hderiv s).hasDerivWithinAt) (by simp [Finset.sum_range_succ']) hB
      (fun s hs => ih (m + 1) s hs.1) (show t ∈ Set.Icc (0 : ℝ) t from ⟨ht, le_rfl⟩)
    rw [show m + (n + 1) = m + 1 + n by omega]
    exact key

/- English proof (translation)
The claim follows from `|t| ^ n / (n.factorial : ℝ) * ‖x n‖ := by have horb : ∀ m s, HasDerivAt (fun t => U t (x m)) (U s (x (m + 1))) s := fun m s => UnitaryFlow.hasDerivAt_orbit U hadd (x m) (x (m + 1)) (hd m) s rcases le_or_gt 0 t with ht | ht · have e := norm_sub_taylor_sum_le (fun m s => U s (x m)) …`.
-/
private theorem norm_unitary_sub_taylor_le {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : ℝ → (H →L[ℂ] H)) (x : ℕ → H) (h0 : U 0 = 1) (hadd : ∀ s t, U (s + t) = U s * U t)
    (hn : ∀ t v, ‖U t v‖ = ‖v‖) (hd : ∀ m, HasDerivAt (fun t => U t (x m)) (x (m + 1)) 0)
    (n : ℕ) (t : ℝ) :
    ‖U t (x 0) - ∑ k ∈ Finset.range n, (t ^ k / (k.factorial : ℝ)) • x k‖ ≤
      |t| ^ n / (n.factorial : ℝ) * ‖x n‖ := by
  have horb : ∀ m s, HasDerivAt (fun t => U t (x m)) (U s (x (m + 1))) s :=
    fun m s => UnitaryFlow.hasDerivAt_orbit U hadd (x m) (x (m + 1)) (hd m) s
  rcases le_or_gt 0 t with ht | ht
  · have e := norm_sub_taylor_sum_le (fun m s => U s (x m)) (fun m => ‖x m‖) horb
      (fun m s => (hn s (x m)).le) n 0 t ht
    simpa [h0, abs_of_nonneg ht] using e
  · have hV : ∀ m s, HasDerivAt (fun s : ℝ => ((-1 : ℝ) ^ m) • U (-s) (x m))
        (((-1 : ℝ) ^ (m + 1)) • U (-s) (x (m + 1))) s := by
      intro m s
      have e1 := (HasDerivAt.scomp s (horb m (-s)) (hasDerivAt_neg (x := s))).const_smul ((-1 : ℝ) ^ m)
      have e3 : HasDerivAt (fun s : ℝ => ((-1 : ℝ) ^ m) • U (-s) (x m))
          (((-1 : ℝ) ^ m) • ((-1 : ℝ) • U (-s) (x (m + 1)))) s := e1
      exact e3.congr_deriv (by rw [smul_smul, ← pow_succ])
    have e := norm_sub_taylor_sum_le (fun m s => ((-1 : ℝ) ^ m) • U (-s) (x m)) (fun m => ‖x m‖) hV
      (fun m s => by simp [norm_smul, hn]) n 0 (-t) (by linarith)
    have hs : ∀ k, ((-t) ^ k / (k.factorial : ℝ)) • ((-1 : ℝ) ^ k • U 0 (x k)) =
        (t ^ k / (k.factorial : ℝ)) • x k := by
      intro k
      have hm : (-t) ^ k * (-1 : ℝ) ^ k = t ^ k := by
        rw [← mul_pow]
        norm_num
      rw [h0, ContinuousLinearMap.one_apply, smul_smul, div_mul_eq_mul_div, hm]
    simp only [zero_add, neg_zero, hs, pow_zero, one_smul, neg_neg] at e
    rwa [abs_of_neg ht]

end GlobalTheory.SphJet.UnitaryFlow

namespace GlobalTheory.SphJet
open UnitaryFlow

/- English proof (translation)
Introduce `H _ _ U x y φ φ₀ h0 hadd hn hd hφ hφ₀ hφd hφ₀d t`. Establish `hskew` using `fun i k => UnitaryFlow.inner_skew U x h0 hn hd i k`. Establish `hshift` using `UnitaryFlow.norm_inner_shift x hskew`. Take `⟨p, r, hp⟩` from `hφ₀`. Take `⟨ρ, hρ0, hρr⟩` from `ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos`.

Take `⟨C, hC, hCb⟩` from `p.norm_mul_pow_le_of_lt_radius (hρr.trans_le hp.r_le)`. Establish `hρpos : (0 : ℝ) < ρ` using `NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hρ0)`. Establish `hdiag : ∀ n, ‖⟪x 0, x n⟫_ℂ‖ * (ρ : ℝ) ^ n ≤ n.factorial * C`. Introduce `n`. Establish `e2 : ⟪x 0, x n⟫_ℂ = (n.factorial : ℂ) * p n (fun _ => 1)`.

Rewrite using `[← hφ₀d n, ← nsmul_eq_mul, hp.factorial_smul 1 n]`. Apply the tactic sequence `try rfl`. Establish `e3 : ‖p n (fun _ => 1)‖ ≤ ‖p n‖`. Simplify using `using (p n).le_opNorm (fun _ => (1 : ℝ))`. Rewrite using `[e2, norm_mul, Complex.norm_natCast]`.

Establish `hf : (0 : ℝ) ≤ n.factorial` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc]`. Use `gcongr`. Use `_ ≤ n.factorial * C := by gcongr; exact hCb n`.

Use `set ρ2 : NNReal := ρ / 2 with hρ2def`. Establish `hρ2 : (ρ2 : ℝ) = ρ / 2` using `by simp [hρ2def]`. Establish `hρ2pos : (0 : ℝ) < ρ2` using `by rw [hρ2]; positivity`. Establish `hxb : ∀ m, ‖x m‖ * (ρ2 : ℝ) ^ m ≤ m.factorial * Real.sqrt C`. Introduce `m`.

Establish `hsq : ‖x m‖ ^ 2 = ‖⟪x 0, x (m + m)⟫_ℂ‖`. Rewrite using `[← hshift m m, inner_self_eq_norm_sq_to_K]`. Simplify using the standard rewrite rules. Establish `h3 : (‖x m‖ * (ρ : ℝ) ^ m) ^ 2 ≤ (2 ^ m * m.factorial) ^ 2 * C`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_pow, hsq, ← pow_mul, show m * 2 = m + m by ring]`. Use `_ ≤ (m + m).factorial * C := hdiag (m + m)`. Use `_ ≤ 2 ^ (2 * m) * m.factorial ^ 2 * C := by`. Rewrite using `[← two_mul]`. Conclude with `mul_le_mul_of_nonneg_right (UnitaryFlow.factorial_two_mul_le m) hC.le`.

Use `_ = (2 ^ m * m.factorial) ^ 2 * C := by ring`. Establish `h4 : ‖x m‖ * (ρ : ℝ) ^ m ≤ 2 ^ m * m.factorial * Real.sqrt C`. Rewrite using `[← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 ^ m * m.factorial), ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 ^ m * m.factorial) ^ 2) C]`. Conclude with `(le_abs_self _).trans (Real.abs_le_sqrt h3)`. Establish `h5 : (0 : ℝ) < 2 ^ m` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hρ2, div_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 2 ^ m * m.factorial * Real.sqrt C / 2 ^ m := by gcongr`. Use `_ = m.factorial * Real.sqrt C := by`.

Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Establish `hkey : ∀ n (s : ℝ), |s| ^ n / (n.factorial : ℝ) * ‖x n‖ ≤ Real.sqrt C * (|s| / ρ2) ^ n`. Introduce `n s`. Establish `hf : (0 : ℝ) < n.factorial` using `by positivity`.

Establish `hr : (0 : ℝ) < (ρ2 : ℝ) ^ n` using `by positivity`. Establish `hr' : (ρ2 : ℝ) ≠ 0` using `hρ2pos.ne'`. Establish `hf' : (n.factorial : ℝ) ≠ 0` using `hf.ne'`. Establish `h` using `hxb n`. Combine the equalities or inequalities in the displayed calculation.

Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Use `_ ≤ |s| ^ n * (n.factorial * Real.sqrt C) / (n.factorial * (ρ2 : ℝ) ^ n) := by gcongr`. Use `_ = Real.sqrt C * (|s| / ρ2) ^ n := by`. Rewrite using `[div_pow]`.

Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Set `P : FormalMultilinearSeries ℝ ℝ H` to `fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (((n.factorial : ℝ))⁻¹ • x n)`. Establish `hPn : ∀ n, ‖P n‖ = ‖x n‖ / n.factorial`. Introduce `n`.

Simplify using `[P, ContinuousMultilinearMap.norm_mkPiRing, norm_smul, div_eq_inv_mul]`. Establish `hPb : ∀ n, ‖P n‖ * (ρ2 : ℝ) ^ n ≤ Real.sqrt C`. Introduce `n`. Establish `hf : (0 : ℝ) < n.factorial` using `by positivity`. Rewrite using `[hPn, div_mul_eq_mul_div, div_le_iff₀ hf]`.

Combine the linear relations using `[hxb n]`. Establish `hterm : ∀ n (s : ℝ), P n (fun _ => s) = (s ^ n / (n.factorial : ℝ)) • x n`. Introduce `n s`. Simplify using `[P, ContinuousMultilinearMap.mkPiRing_apply, smul_smul, div_eq_mul_inv]`. Establish `hser : HasFPowerSeriesOnBall (fun t => U t (x 0)) P 0 ρ2`.

Use `⟨P.le_radius_of_bound _ hPb, ENNReal.coe_pos.mpr (NNReal.coe_pos.mp hρ2pos), fun {s} hs => ?_⟩` and prove the remaining obligations. Establish `hs' : |s| < ρ2`. Rewrite `hs` using `[Metric.mem_eball, edist_lt_coe, ← NNReal.coe_lt_coe, coe_nndist, Real.dist_eq, sub_zero]`. Conclude with `hs`. Establish `hq0 : 0 ≤ |s| / ρ2` using `by positivity`.

Establish `hq : |s| / ρ2 < 1` using `(div_lt_one hρ2pos).mpr hs'`. Establish `hnb : ∀ n, ‖(s ^ n / (n.factorial : ℝ)) • x n‖ ≤ Real.sqrt C * (|s| / ρ2) ^ n`. Introduce `n`. Rewrite using `[norm_smul, norm_div, norm_pow, Real.norm_natCast, Real.norm_eq_abs]`. Conclude with `hkey n s`.

Simplify using `only [hterm, zero_add]`. Rewrite using `[hasSum_iff_tendsto_nat_of_summable_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnb ((summable_geometric_of_lt_one hq0 hq).mul_left _)), tendsto_iff_norm_sub_tendsto_zero]`. Establish `hlim : Tendsto (fun n : ℕ => Real.sqrt C * (|s| / ρ2) ^ n) atTop (𝓝 0)`. Simplify using `using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul (Real.sqrt C)`. Use `squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim` and prove the remaining obligations.

Conclude with `(norm_sub_rev _ _).trans_le ((UnitaryFlow.norm_unitary_sub_taylor_le U x h0 hadd hn hd n s).trans (hkey n s))`. Establish `hψ : AnalyticOnNhd ℝ (fun t => ⟪y, U t (x 0)⟫_ℂ) Set.univ`. Introduce `s _`. Establish `h1` using `hser.comp_sub s`. Establish `h2` using `(((innerSL ℂ y).comp (U s)).restrictScalars ℝ).comp_hasFPowerSeriesOnBall h1`.

Establish `h3` using `h2.analyticAt`. Rewrite `h3` using `[zero_add]`. Use `h3.congr (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Use `show ⟪y, U s (U (z - s) (x 0))⟫_ℂ = ⟪y, U z (x 0)⟫_ℂ`. Establish `e` using `hadd s (z - s)`.

Rewrite `e` using `[show s + (z - s) = z by ring]`. Rewrite using `[e]`. Both sides reduce to the same expression. Establish `hg : ∀ m s, HasDerivAt (fun t => ⟪y, U t (x m)⟫_ℂ) ⟪y, U s (x (m + 1))⟫_ℂ s`. Introduce `m s`.

Establish `e` using `(hasDerivAt_const s y).inner ℂ (UnitaryFlow.hasDerivAt_orbit U hadd (x m) (x (m + 1)) (hd m) s)`. Simplify using `using e`. Establish `hderivs : ∀ m, iteratedDeriv m φ 0 = iteratedDeriv m (fun t => ⟪y, U t (x 0)⟫_ℂ) 0`. Introduce `m`. Establish `hc : iteratedDeriv m (fun t => ⟪y, U t (x 0)⟫_ℂ) = fun t => ⟪y, U t (x m)⟫_ℂ` using `UnitaryFlow.iteratedDeriv_chain (fun m t => ⟪y, U t (x m)⟫_ℂ) hg m`.

Rewrite using `[hφd m, hc]`. Simplify using `[h0]`. Conclude with `UnitaryFlow.eq_of_iteratedDeriv_eq φ _ hφ hψ hderivs t`.
-/
theorem unitaryFlow_coeff_eq_of_taylor : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (U : ℝ → (H →L[ℂ] H)) (x : ℕ → H) (y : H) (φ φ₀ : ℝ → ℂ), U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ t v, ‖U t v‖ = ‖v‖) → (∀ m, HasDerivAt (fun t => U t (x m)) (x (m + 1)) 0) → AnalyticOnNhd ℝ φ Set.univ → AnalyticAt ℝ φ₀ 0 → (∀ m, iteratedDeriv m φ 0 = ⟪y, x m⟫_ℂ) → (∀ m, iteratedDeriv m φ₀ 0 = ⟪x 0, x m⟫_ℂ) → ∀ t, φ t = ⟪y, U t (x 0)⟫_ℂ := by
  intro H _ _ U x y φ φ₀ h0 hadd hn hd hφ hφ₀ hφd hφ₀d t
  have hskew := fun i k => UnitaryFlow.inner_skew U x h0 hn hd i k
  have hshift := UnitaryFlow.norm_inner_shift x hskew
  obtain ⟨p, r, hp⟩ := hφ₀
  obtain ⟨ρ, hρ0, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  obtain ⟨C, hC, hCb⟩ := p.norm_mul_pow_le_of_lt_radius (hρr.trans_le hp.r_le)
  have hρpos : (0 : ℝ) < ρ := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hρ0)
  have hdiag : ∀ n, ‖⟪x 0, x n⟫_ℂ‖ * (ρ : ℝ) ^ n ≤ n.factorial * C := by
    intro n
    have e2 : ⟪x 0, x n⟫_ℂ = (n.factorial : ℂ) * p n (fun _ => 1) := by
      rw [← hφ₀d n, ← nsmul_eq_mul, hp.factorial_smul 1 n]
      try rfl
    have e3 : ‖p n (fun _ => 1)‖ ≤ ‖p n‖ := by
      simpa using (p n).le_opNorm (fun _ => (1 : ℝ))
    rw [e2, norm_mul, Complex.norm_natCast]
    have hf : (0 : ℝ) ≤ n.factorial := by positivity
    calc (n.factorial : ℝ) * ‖p n fun _ => 1‖ * (ρ : ℝ) ^ n
        ≤ n.factorial * (‖p n‖ * (ρ : ℝ) ^ n) := by
          rw [mul_assoc]
          gcongr
      _ ≤ n.factorial * C := by gcongr; exact hCb n
  set ρ2 : NNReal := ρ / 2 with hρ2def
  have hρ2 : (ρ2 : ℝ) = ρ / 2 := by simp [hρ2def]
  have hρ2pos : (0 : ℝ) < ρ2 := by rw [hρ2]; positivity
  have hxb : ∀ m, ‖x m‖ * (ρ2 : ℝ) ^ m ≤ m.factorial * Real.sqrt C := by
    intro m
    have hsq : ‖x m‖ ^ 2 = ‖⟪x 0, x (m + m)⟫_ℂ‖ := by
      rw [← hshift m m, inner_self_eq_norm_sq_to_K]
      simp
    have h3 : (‖x m‖ * (ρ : ℝ) ^ m) ^ 2 ≤ (2 ^ m * m.factorial) ^ 2 * C := by
      calc (‖x m‖ * (ρ : ℝ) ^ m) ^ 2 = ‖⟪x 0, x (m + m)⟫_ℂ‖ * (ρ : ℝ) ^ (m + m) := by
            rw [mul_pow, hsq, ← pow_mul, show m * 2 = m + m by ring]
        _ ≤ (m + m).factorial * C := hdiag (m + m)
        _ ≤ 2 ^ (2 * m) * m.factorial ^ 2 * C := by
            rw [← two_mul]
            exact mul_le_mul_of_nonneg_right (UnitaryFlow.factorial_two_mul_le m) hC.le
        _ = (2 ^ m * m.factorial) ^ 2 * C := by ring
    have h4 : ‖x m‖ * (ρ : ℝ) ^ m ≤ 2 ^ m * m.factorial * Real.sqrt C := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 ^ m * m.factorial),
        ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 ^ m * m.factorial) ^ 2) C]
      exact (le_abs_self _).trans (Real.abs_le_sqrt h3)
    have h5 : (0 : ℝ) < 2 ^ m := by positivity
    calc ‖x m‖ * (ρ2 : ℝ) ^ m = ‖x m‖ * (ρ : ℝ) ^ m / 2 ^ m := by
          rw [hρ2, div_pow]
          ring
      _ ≤ 2 ^ m * m.factorial * Real.sqrt C / 2 ^ m := by gcongr
      _ = m.factorial * Real.sqrt C := by
          field_simp
          try ring
  have hkey : ∀ n (s : ℝ), |s| ^ n / (n.factorial : ℝ) * ‖x n‖ ≤
      Real.sqrt C * (|s| / ρ2) ^ n := by
    intro n s
    have hf : (0 : ℝ) < n.factorial := by positivity
    have hr : (0 : ℝ) < (ρ2 : ℝ) ^ n := by positivity
    have hr' : (ρ2 : ℝ) ≠ 0 := hρ2pos.ne'
    have hf' : (n.factorial : ℝ) ≠ 0 := hf.ne'
    have h := hxb n
    calc |s| ^ n / (n.factorial : ℝ) * ‖x n‖
        = |s| ^ n * (‖x n‖ * (ρ2 : ℝ) ^ n) / (n.factorial * (ρ2 : ℝ) ^ n) := by
          field_simp
          try ring
      _ ≤ |s| ^ n * (n.factorial * Real.sqrt C) / (n.factorial * (ρ2 : ℝ) ^ n) := by gcongr
      _ = Real.sqrt C * (|s| / ρ2) ^ n := by
          rw [div_pow]
          field_simp
          try ring
  let P : FormalMultilinearSeries ℝ ℝ H := fun n =>
    ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (((n.factorial : ℝ))⁻¹ • x n)
  have hPn : ∀ n, ‖P n‖ = ‖x n‖ / n.factorial := by
    intro n
    simp [P, ContinuousMultilinearMap.norm_mkPiRing, norm_smul, div_eq_inv_mul]
  have hPb : ∀ n, ‖P n‖ * (ρ2 : ℝ) ^ n ≤ Real.sqrt C := by
    intro n
    have hf : (0 : ℝ) < n.factorial := by positivity
    rw [hPn, div_mul_eq_mul_div, div_le_iff₀ hf]
    linarith [hxb n]
  have hterm : ∀ n (s : ℝ), P n (fun _ => s) = (s ^ n / (n.factorial : ℝ)) • x n := by
    intro n s
    simp [P, ContinuousMultilinearMap.mkPiRing_apply, smul_smul, div_eq_mul_inv]
  have hser : HasFPowerSeriesOnBall (fun t => U t (x 0)) P 0 ρ2 := by
    refine ⟨P.le_radius_of_bound _ hPb, ENNReal.coe_pos.mpr (NNReal.coe_pos.mp hρ2pos),
      fun {s} hs => ?_⟩
    have hs' : |s| < ρ2 := by
      rw [Metric.mem_eball, edist_lt_coe, ← NNReal.coe_lt_coe, coe_nndist, Real.dist_eq,
        sub_zero] at hs
      exact hs
    have hq0 : 0 ≤ |s| / ρ2 := by positivity
    have hq : |s| / ρ2 < 1 := (div_lt_one hρ2pos).mpr hs'
    have hnb : ∀ n, ‖(s ^ n / (n.factorial : ℝ)) • x n‖ ≤ Real.sqrt C * (|s| / ρ2) ^ n := by
      intro n
      rw [norm_smul, norm_div, norm_pow, Real.norm_natCast, Real.norm_eq_abs]
      exact hkey n s
    simp only [hterm, zero_add]
    rw [hasSum_iff_tendsto_nat_of_summable_norm (Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _) hnb ((summable_geometric_of_lt_one hq0 hq).mul_left _)),
      tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => Real.sqrt C * (|s| / ρ2) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul (Real.sqrt C)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
    exact (norm_sub_rev _ _).trans_le ((UnitaryFlow.norm_unitary_sub_taylor_le U x h0 hadd hn hd n s).trans (hkey n s))
  have hψ : AnalyticOnNhd ℝ (fun t => ⟪y, U t (x 0)⟫_ℂ) Set.univ := by
    intro s _
    have h1 := hser.comp_sub s
    have h2 := (((innerSL ℂ y).comp (U s)).restrictScalars ℝ).comp_hasFPowerSeriesOnBall h1
    have h3 := h2.analyticAt
    rw [zero_add] at h3
    refine h3.congr (Filter.Eventually.of_forall fun z => ?_)
    show ⟪y, U s (U (z - s) (x 0))⟫_ℂ = ⟪y, U z (x 0)⟫_ℂ
    have e := hadd s (z - s)
    rw [show s + (z - s) = z by ring] at e
    rw [e]
    rfl
  have hg : ∀ m s, HasDerivAt (fun t => ⟪y, U t (x m)⟫_ℂ) ⟪y, U s (x (m + 1))⟫_ℂ s := by
    intro m s
    have e := (hasDerivAt_const s y).inner ℂ
      (UnitaryFlow.hasDerivAt_orbit U hadd (x m) (x (m + 1)) (hd m) s)
    simpa using e
  have hderivs : ∀ m, iteratedDeriv m φ 0 = iteratedDeriv m (fun t => ⟪y, U t (x 0)⟫_ℂ) 0 := by
    intro m
    have hc : iteratedDeriv m (fun t => ⟪y, U t (x 0)⟫_ℂ) = fun t => ⟪y, U t (x m)⟫_ℂ :=
      UnitaryFlow.iteratedDeriv_chain (fun m t => ⟪y, U t (x m)⟫_ℂ) hg m
    rw [hφd m, hc]
    simp [h0]
  exact UnitaryFlow.eq_of_iteratedDeriv_eq φ _ hφ hψ hderivs t

end GlobalTheory.SphJet
