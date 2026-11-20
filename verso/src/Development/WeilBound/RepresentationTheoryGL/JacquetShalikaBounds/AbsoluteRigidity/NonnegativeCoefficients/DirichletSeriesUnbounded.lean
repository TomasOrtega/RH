import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow

noncomputable section

open scoped ComplexConjugate

namespace PositivityTheory.RgJS

namespace DirichletSeriesUnbounded₂

variable {W X : Type} (q : W → ℕ) {d : X → ℕ} (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (x : ι → X)

def PP (p : W × ℕ) : ℂ := ∑ i, ∑ a, A (x i) p.1 a ^ (p.2 + 1)

def cc (p : W × ℕ) : ℝ := ‖PP A x p‖ ^ 2 / ((p.2 : ℝ) + 1)

def ll (p : W × ℕ) : ℝ := ((p.2 : ℝ) + 1) * Real.log (q p.1)

/- English proof (translation)
Unfold `cc`. Check the signs of the components of the expression.
-/
theorem cc_nonneg (p : W × ℕ) : 0 ≤ cc A x p := by
  unfold cc; positivity

/- English proof (translation)
Establish `h1 : (q p.1 : ℂ) = ((q p.1 : ℝ) : ℂ)` using `by push_cast; rfl`. Establish `h2 : (-(σ : ℂ)) = ((-σ : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[h1, h2, ← Complex.ofReal_cpow (hq p.1).le, ← Complex.ofReal_pow, Real.rpow_def_of_pos (hq p.1), ← Real.exp_nat_mul]`. Use `congr 2`. Simplify using `only [ll]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cpow_pow (hq : ∀ w, (0 : ℝ) < q w) (σ : ℝ) (p : W × ℕ) :
    ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) = ((Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
  have h1 : (q p.1 : ℂ) = ((q p.1 : ℝ) : ℂ) := by push_cast; rfl
  have h2 : (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, ← Complex.ofReal_cpow (hq p.1).le, ← Complex.ofReal_pow, Real.rpow_def_of_pos (hq p.1),
    ← Real.exp_nat_mul]
  congr 2
  simp only [ll]
  push_cast
  ring

/- English proof (translation)
Use `set s : ι → ℂ := fun i => ∑ a, A (x i) p.1 a ^ (p.2 + 1) with hs`. Use `set z : ℂ := ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / ((p.2 : ℂ) + 1) with hz`. Establish `e1 : ∀ i j, lterm q (A (x i)) (A (x j)) σ p = s i * conj (s j) * z`. Introduce `i j`. Simplify using `only [lterm, hs, hz]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e1]`. Establish `e2 : ∑ i, ∑ j, s i * conj (s j) * z = (∑ i, s i) * conj (∑ j, s j) * z`. Rewrite using `[map_sum, Finset.sum_mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_mul]`. Rewrite using `[e2, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz, cpow_pow q hq σ p]`. Simplify using `only [cc, PP, hs]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_lterm (hq : ∀ w, (0 : ℝ) < q w) (σ : ℝ) (p : W × ℕ) :
    ∑ i, ∑ j, lterm q (A (x i)) (A (x j)) σ p = ((cc A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
  set s : ι → ℂ := fun i => ∑ a, A (x i) p.1 a ^ (p.2 + 1) with hs
  set z : ℂ := ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / ((p.2 : ℂ) + 1) with hz
  have e1 : ∀ i j, lterm q (A (x i)) (A (x j)) σ p = s i * conj (s j) * z := by
    intro i j
    simp only [lterm, hs, hz]
    ring
  simp only [e1]
  have e2 : ∑ i, ∑ j, s i * conj (s j) * z = (∑ i, s i) * conj (∑ j, s j) * z := by
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  rw [e2, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz, cpow_pow q hq σ p]
  simp only [cc, PP, hs]
  push_cast
  ring

end DirichletSeriesUnbounded₂

open DirichletSeriesUnbounded₂ in
/- English proof (translation)
Introduce `hL hN hE hR hC W q X d A hS ι _ _ x hMex`. Take `⟨M, hM⟩` from `hMex`. Use `set c : W × ℕ → ℝ := cc A x with hc`. Use `set l : W × ℕ → ℝ := ll q with hl`. Establish `hq : ∀ w, (0 : ℝ) < q w` using `fun w => by`.

Use `hS.primes.two w` as an intermediate fact. Conclude with `(by omega : 0 < q w)` after adjusting the coercions. Establish `hq1 : ∀ w, (1 : ℝ) ≤ q w` using `fun w => by`. Use `hS.primes.two w` as an intermediate fact. Conclude with `(by omega : 1 ≤ q w)` after adjusting the coercions.

Establish `hc0 : ∀ p, 0 ≤ c p` using `fun p => cc_nonneg A x p`. Establish `hl0 : ∀ p, 0 ≤ l p` using `fun p => mul_nonneg (by positivity) (Real.log_nonneg (hq1 p.1))`. Establish `hpt : ∀ (σ : ℝ) p, ∑ i, ∑ j, lterm q (A (x i)) (A (x j)) σ p = ((c p * Real.exp (-(l p * σ)) : ℝ) : ℂ)` using `fun σ p => sum_lterm q A x hq σ p`. Establish `hsum : ∀ σ : ℝ, 1 < σ → Summable fun p => c p * Real.exp (-(l p * σ))`. Introduce `σ hσ`.

Establish `h1 : ∀ i j, Summable fun p => ‖lterm q (A (x i)) (A (x j)) σ p‖` using `fun i j => (hC W q X d A hS (x i) (x j)).1 σ hσ`. Use `Summable.of_nonneg_of_le (fun p => mul_nonneg (hc0 p) (Real.exp_pos _).le) (fun p => ?_) (summable_sum (s := Finset.univ) fun i _ => summable_sum (s := Finset.univ) fun j _ => h1 i j)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (hc0 p) (Real.exp_pos _).le)]`. Use `_ = ‖∑ i, ∑ j, lterm q (A (x i)) (A (x j)) σ p‖ := by rw [hpt σ p]`.

Use `_ ≤ ∑ i, ∑ j, ‖lterm q (A (x i)) (A (x j)) σ p‖ := (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)`. Establish `htsum : ∀ σ : ℝ, 1 < σ → ∑ i, ∑ j, ∑' p, lterm q (A (x i)) (A (x j)) σ p = ((∑' p, c p * Real.exp (-(l p * σ)) : ℝ) : ℂ)`. Introduce `σ hσ`. Establish `hs : ∀ i j, Summable fun p => lterm q (A (x i)) (A (x j)) σ p` using `fun i j => ((hC W q X d A hS (x i) (x j)).1 σ hσ).of_norm`. Rewrite using `[Complex.ofReal_tsum]`.

Repeatedly rewrite using `[← hpt σ]`. Rewrite using `[Summable.tsum_finsetSum (fun i _ => summable_sum (s := Finset.univ) fun j _ => hs i j)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Summable.tsum_finsetSum (fun j _ => hs i j)]`. Establish `hT : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∑' p, c p * Real.exp (-(l p * σ)) ≤ M`.

Introduce `σ h1 h2`. Use `hM σ h1 h2` as an intermediate fact. Rewrite `this` using `[htsum σ h1, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `(le_abs_self _).trans this`. Use `choose F σ0 hFa hFe using fun ij : ι × ι => hS.rs (x ij.1) (x ij.2)`.

Use `set G : ℂ → ℂ := fun s => ∏ ij : ι × ι, F ij s with hG`. Establish `hGa : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ G σ` using `fun σ hσ => by`. Use `Finset.analyticAt_prod (𝕜 := ℂ) (f := F) (c := (σ : ℂ)) Finset.univ (fun ij _ => hFa ij σ hσ)` as an intermediate fact. Establish `e : G = ∏ ij ∈ Finset.univ, F ij`. Use function extensionality and compare the values at `s`.

Simplify using `[hG, Finset.prod_apply]`. Rewrite using `[e]`. Conclude with `this`. Use `set B : ℝ := 2 + ∑ ij, |σ0 ij| with hBd`. Establish `hB : ∀ ij, σ0 ij ≤ B` using `fun ij => by`.

Use `Finset.single_le_sum (f := fun ij => |σ0 ij|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ij)` as an intermediate fact. Use `le_abs_self (σ0 ij)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB2 : (2 : ℝ) ≤ B`. Use `Finset.sum_nonneg (s := Finset.univ) (f := fun ij : ι × ι => |σ0 ij|) (fun _ _ => abs_nonneg _)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set r : ℕ := (Finset.univ.filter fun ij : ι × ι => x ij.1 = x ij.2).card with hr`. Use `set SC : ℂ → ℂ := fun s => ∑' p, (c p : ℂ) * Complex.exp (-((l p : ℂ) * s)) with hSCd`. Establish `hSC : ∀ σ : ℝ, SC σ = ((∑' p, c p * Real.exp (-(l p * σ)) : ℝ) : ℂ)`. Introduce `σ`.

Rewrite using `[Complex.ofReal_tsum]`. Use `tsum_congr fun p => ?_` and prove the remaining obligations. Rewrite using `[Complex.ofReal_mul, Complex.ofReal_exp]`. Use `push_cast`. Put the polynomial expressions in normal form.

Establish `hSCa : ∀ σ : ℝ, 1 < σ → AnalyticAt ℂ SC σ`. Introduce `σ hσ`. Use `set σ' : ℝ := (1 + σ) / 2 with hσ'`. Establish `hU : IsOpen {s : ℂ | σ' < s.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hd : DifferentiableOn ℂ SC {s : ℂ | σ' < s.re}`.

Use `Complex.differentiableOn_tsum_of_summable_norm (hsum σ' (by linarith)) (fun p => ?_) hU (fun p s hs => ?_)` and prove the remaining obligations. Conclude with `(Differentiable.differentiableOn (by fun_prop))`. Rewrite using `[norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (hc0 p)]`. Use `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hc0 p)` and prove the remaining obligations. Establish `hs' : σ' < s.re` using `hs`.

Simplify using `only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]`. Use polynomial arithmetic with `[hl0 p]`. Conclude with `hd.analyticAt (hU.mem_nhds (by simp only [Set.mem_ofPred_eq, Complex.ofReal_re]; linarith))`. Establish `hEq : ∀ σ : ℝ, B < σ → G σ = ((σ : ℂ) - 1) ^ r * Complex.exp (SC σ)`. Introduce `σ hσ`.

Establish `h2 : (2 : ℝ) < σ` using `by linarith`. Establish `e0 : G σ = ∏ ij : ι × ι, ((if x ij.1 = x ij.2 then (σ : ℂ) - 1 else 1) * eul q (A (x ij.1)) (A (x ij.2)) σ)` using `Finset.prod_congr rfl fun ij _ => hFe ij σ (lt_of_le_of_lt (hB ij) hσ)`. Rewrite using `[e0, Finset.prod_mul_distrib]`. Use `congr 1`. Rewrite using `[Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]`.

Rewrite using `[hSC σ, ← htsum σ (by linarith), ← Fintype.sum_prod_type', Complex.exp_sum]`. Use `Finset.prod_congr rfl fun ij _ => ?_` and prove the remaining obligations. Conclude with `(hE W q (Fin (d (x ij.1))) (Fin (d (x ij.2))) (A (x ij.1)) (A (x ij.2)) σ hS.primes (hS.bd _) (hS.bd _) (by simpa using h2)).2.1`. Establish `ha1 : AnalyticOnNhd ℝ (fun t : ℝ => G t) (Set.Ioi 1)` using `fun t ht => by`. Establish `h1 : AnalyticAt ℝ G (t : ℂ)` using `(hGa t (by linarith [Set.mem_Ioi.1 ht])).restrictScalars`.

Conclude with `h1.comp (Complex.ofRealCLM.analyticAt t)`. Establish `ha2 : AnalyticOnNhd ℝ (fun t : ℝ => ((t : ℂ) - 1) ^ r * Complex.exp (SC t)) (Set.Ioi 1)` using `fun t ht => by`. Establish `h : AnalyticAt ℂ (fun s => (s - 1) ^ r * Complex.exp (SC s)) (t : ℂ)` using `((analyticAt_id.sub analyticAt_const).pow r).mul (hSCa t (Set.mem_Ioi.1 ht)).cexp`. Establish `h1 : AnalyticAt ℝ (fun s => (s - 1) ^ r * Complex.exp (SC s)) (t : ℂ)` using `h.restrictScalars`. Conclude with `h1.comp (Complex.ofRealCLM.analyticAt t)`.

Establish `hid : Set.EqOn (fun t : ℝ => G t) (fun t : ℝ => ((t : ℂ) - 1) ^ r * Complex.exp (SC t)) (Set.Ioi 1)` using `ha1.eqOn_of_preconnected_of_eventuallyEq ha2 isPreconnected_Ioi (z₀ := B + 1) (Set.mem_Ioi.2 (by linarith)) (by filter_upwards [Ioi_mem_nhds (show B < B + 1 by linarith)] with t ht`. Conclude with `hEq t ht)`. Establish `hGb : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖G σ‖ ≤ Real.exp M * (σ - 1) ^ r`. Introduce `σ h1 h2`. Establish `e` using `hid (Set.mem_Ioi.2 h1)`.

Simplify using `only at e`. Establish `hn : ‖(σ : ℂ) - 1‖ = σ - 1`. Rewrite using `[← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]`. Rewrite using `[e, norm_mul, norm_pow, hn, hSC, Complex.norm_exp_ofReal, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hT σ h1 h2)) (pow_nonneg (by linarith) _)`.

Take `⟨G', hG'a, hG'e⟩` from `hR G r (Real.exp M) hGa hGb`. Establish `hG'v : ∀ σ : ℝ, 1 < σ → G' σ = ((Real.exp (∑' p, c p * Real.exp (-(l p * σ))) : ℝ) : ℂ)`. Introduce `σ hσ`. Establish `e1` using `hid (Set.mem_Ioi.2 hσ)`. Simplify using `only at e1`.

Establish `e2` using `hG'e σ hσ`. Establish `hne : ((σ : ℂ) - 1) ^ r ≠ 0` using `pow_ne_zero _ (sub_ne_zero.2 (by exact_mod_cast hσ.ne'))`. Rewrite `e2` using `[e1]`. Establish `e3` using `mul_left_cancel₀ hne e2`. Rewrite using `[← e3, hSC, Complex.ofReal_exp]`.

Establish `hLand` using `hL (W × ℕ) c l 0 1 G' hc0 hl0 (fun σ hσ => hG'a σ hσ) hsum (fun σ hσ => hG'v σ hσ)`. Use `set N : ℕ := ∑ i, d (x i) with hNd`. Establish `hN1 : 1 ≤ N`. Take `⟨i⟩` from `‹Nonempty ι›`. Conclude with `le_trans (hS.pos (x i)) (Finset.single_le_sum (f := fun i => d (x i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))`.

Establish `hNpos : (0 : ℝ) < N` using `by exact_mod_cast hN1`. Establish `hs0` using `hLand (1 / N) (by positivity)`. Take `⟨c0, hc0pos, hc0le⟩` from `hN N hN1`. Establish `hlow : ∀ w, c0 / N * (q w : ℝ)⁻¹ ≤ ∑ k ∈ Finset.range N, c (w, k) * Real.exp (-(l (w, k) * (1 / N)))`. Introduce `w`.

Establish `hnew` using `hc0le (Σ i : ι, Fin (d (x i))) (fun ib => A (x ib.1) w ib.2) (by rw [Fintype.card_sigma]; simp [hNd]) (by`. Rewrite using `[Fintype.prod_sigma, norm_prod]`. Conclude with `Finset.prod_eq_one fun i _ => hS.det (x i) w)`. Establish `hPk : ∀ k, (∑ ib : Σ i : ι, Fin (d (x i)), A (x ib.1) w ib.2 ^ (k + 1)) = PP A x (w, k)` using `fun k => by`. Rewrite using `[Fintype.sum_sigma]`.

Both sides reduce to the same expression. Simplify using `only [hPk] at hnew`. Establish `hterm : ∀ k ∈ Finset.range N, ‖PP A x (w, k)‖ ^ 2 / N * (q w : ℝ)⁻¹ ≤ c (w, k) * Real.exp (-(l (w, k) * (1 / N)))`. Introduce `k hk`. Establish `hk' : (k : ℝ) + 1 ≤ N` using `by exact_mod_cast Finset.mem_range.1 hk`.

Establish `hlog : 0 ≤ Real.log (q w)` using `Real.log_nonneg (hq1 w)`. Establish `he : (q w : ℝ)⁻¹ ≤ Real.exp (-(l (w, k) * (1 / N)))`. Rewrite using `[← Real.exp_log (hq w), ← Real.exp_neg]`. Use `Real.exp_le_exp.2 (neg_le_neg ?_)` and prove the remaining obligations. Simplify using `only [hl, ll]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hc' : ‖PP A x (w, k)‖ ^ 2 / N ≤ c (w, k)`. Simplify using `only [hc, cc]`. Conclude with `div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hk'`. Conclude with `mul_le_mul hc' he (by positivity) (hc0 _)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_div, Finset.sum_mul]`. Use `_ ≤ _ := Finset.sum_le_sum hterm`. Establish `hsw : Summable fun w => ∑ k ∈ Finset.range N, c (w, k) * Real.exp (-(l (w, k) * (1 / N)))` using `summable_sum (s := Finset.range N) fun k _ => hs0.comp_injective (fun a b h => (Prod.mk.inj h).1)`. Establish `h2 : Summable fun w => c0 / N * (q w : ℝ)⁻¹` using `Summable.of_nonneg_of_le (fun w => by have := hq w; positivity) hlow hsw`.

Establish `h3 : Summable fun w => (q w : ℝ)⁻¹`. Use `h2.mul_left (N / c0)` as an intermediate fact. Use `this.congr fun w => ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Conclude with `hS.primes.div h3`.
-/
theorem dirichlet_series_unbounded : LandauL → NewtonLow → EulerLog → Remov → Conv1 → Unb := by
  intro hL hN hE hR hC W q X d A hS ι _ _ x hMex
  obtain ⟨M, hM⟩ := hMex
  classical
  set c : W × ℕ → ℝ := cc A x with hc
  set l : W × ℕ → ℝ := ll q with hl
  have hq : ∀ w, (0 : ℝ) < q w := fun w => by
    have := hS.primes.two w
    exact_mod_cast (by omega : 0 < q w)
  have hq1 : ∀ w, (1 : ℝ) ≤ q w := fun w => by
    have := hS.primes.two w
    exact_mod_cast (by omega : 1 ≤ q w)
  have hc0 : ∀ p, 0 ≤ c p := fun p => cc_nonneg A x p
  have hl0 : ∀ p, 0 ≤ l p := fun p => mul_nonneg (by positivity) (Real.log_nonneg (hq1 p.1))
  have hpt : ∀ (σ : ℝ) p, ∑ i, ∑ j, lterm q (A (x i)) (A (x j)) σ p = ((c p * Real.exp (-(l p * σ)) : ℝ) : ℂ) :=
    fun σ p => sum_lterm q A x hq σ p
  have hsum : ∀ σ : ℝ, 1 < σ → Summable fun p => c p * Real.exp (-(l p * σ)) := by
    intro σ hσ
    have h1 : ∀ i j, Summable fun p => ‖lterm q (A (x i)) (A (x j)) σ p‖ := fun i j =>
      (hC W q X d A hS (x i) (x j)).1 σ hσ
    refine Summable.of_nonneg_of_le (fun p => mul_nonneg (hc0 p) (Real.exp_pos _).le) (fun p => ?_)
      (summable_sum (s := Finset.univ) fun i _ => summable_sum (s := Finset.univ) fun j _ => h1 i j)
    calc c p * Real.exp (-(l p * σ)) = ‖((c p * Real.exp (-(l p * σ)) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (hc0 p) (Real.exp_pos _).le)]
      _ = ‖∑ i, ∑ j, lterm q (A (x i)) (A (x j)) σ p‖ := by rw [hpt σ p]
      _ ≤ ∑ i, ∑ j, ‖lterm q (A (x i)) (A (x j)) σ p‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
  have htsum : ∀ σ : ℝ, 1 < σ → ∑ i, ∑ j, ∑' p, lterm q (A (x i)) (A (x j)) σ p =
      ((∑' p, c p * Real.exp (-(l p * σ)) : ℝ) : ℂ) := by
    intro σ hσ
    have hs : ∀ i j, Summable fun p => lterm q (A (x i)) (A (x j)) σ p := fun i j =>
      ((hC W q X d A hS (x i) (x j)).1 σ hσ).of_norm
    rw [Complex.ofReal_tsum]
    simp_rw [← hpt σ]
    rw [Summable.tsum_finsetSum (fun i _ => summable_sum (s := Finset.univ) fun j _ => hs i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  have hT : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∑' p, c p * Real.exp (-(l p * σ)) ≤ M := by
    intro σ h1 h2
    have := hM σ h1 h2
    rw [htsum σ h1, Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  choose F σ0 hFa hFe using fun ij : ι × ι => hS.rs (x ij.1) (x ij.2)
  set G : ℂ → ℂ := fun s => ∏ ij : ι × ι, F ij s with hG
  have hGa : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ G σ := fun σ hσ => by
    have := Finset.analyticAt_prod (𝕜 := ℂ) (f := F) (c := (σ : ℂ)) Finset.univ (fun ij _ => hFa ij σ hσ)
    have e : G = ∏ ij ∈ Finset.univ, F ij := by
      funext s
      simp [hG, Finset.prod_apply]
    rw [e]
    exact this
  set B : ℝ := 2 + ∑ ij, |σ0 ij| with hBd
  have hB : ∀ ij, σ0 ij ≤ B := fun ij => by
    have := Finset.single_le_sum (f := fun ij => |σ0 ij|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ij)
    have := le_abs_self (σ0 ij)
    linarith
  have hB2 : (2 : ℝ) ≤ B := by
    have := Finset.sum_nonneg (s := Finset.univ) (f := fun ij : ι × ι => |σ0 ij|) (fun _ _ => abs_nonneg _)
    linarith
  set r : ℕ := (Finset.univ.filter fun ij : ι × ι => x ij.1 = x ij.2).card with hr
  set SC : ℂ → ℂ := fun s => ∑' p, (c p : ℂ) * Complex.exp (-((l p : ℂ) * s)) with hSCd
  have hSC : ∀ σ : ℝ, SC σ = ((∑' p, c p * Real.exp (-(l p * σ)) : ℝ) : ℂ) := by
    intro σ
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun p => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    ring_nf
  have hSCa : ∀ σ : ℝ, 1 < σ → AnalyticAt ℂ SC σ := by
    intro σ hσ
    set σ' : ℝ := (1 + σ) / 2 with hσ'
    have hU : IsOpen {s : ℂ | σ' < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hd : DifferentiableOn ℂ SC {s : ℂ | σ' < s.re} := by
      refine Complex.differentiableOn_tsum_of_summable_norm (hsum σ' (by linarith)) (fun p => ?_) hU (fun p s hs => ?_)
      · exact (Differentiable.differentiableOn (by fun_prop))
      · rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (hc0 p)]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hc0 p)
        have hs' : σ' < s.re := hs
        simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        nlinarith [hl0 p]
    exact hd.analyticAt (hU.mem_nhds (by simp only [Set.mem_ofPred_eq, Complex.ofReal_re]; linarith))
  have hEq : ∀ σ : ℝ, B < σ → G σ = ((σ : ℂ) - 1) ^ r * Complex.exp (SC σ) := by
    intro σ hσ
    have h2 : (2 : ℝ) < σ := by linarith
    have e0 : G σ = ∏ ij : ι × ι, ((if x ij.1 = x ij.2 then (σ : ℂ) - 1 else 1) *
        eul q (A (x ij.1)) (A (x ij.2)) σ) :=
      Finset.prod_congr rfl fun ij _ => hFe ij σ (lt_of_le_of_lt (hB ij) hσ)
    rw [e0, Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    · rw [hSC σ, ← htsum σ (by linarith), ← Fintype.sum_prod_type', Complex.exp_sum]
      refine Finset.prod_congr rfl fun ij _ => ?_
      exact (hE W q (Fin (d (x ij.1))) (Fin (d (x ij.2))) (A (x ij.1)) (A (x ij.2)) σ hS.primes (hS.bd _) (hS.bd _)
        (by simpa using h2)).2.1
  have ha1 : AnalyticOnNhd ℝ (fun t : ℝ => G t) (Set.Ioi 1) := fun t ht => by
    have h1 : AnalyticAt ℝ G (t : ℂ) := (hGa t (by linarith [Set.mem_Ioi.1 ht])).restrictScalars
    exact h1.comp (Complex.ofRealCLM.analyticAt t)
  have ha2 : AnalyticOnNhd ℝ (fun t : ℝ => ((t : ℂ) - 1) ^ r * Complex.exp (SC t)) (Set.Ioi 1) := fun t ht => by
    have h : AnalyticAt ℂ (fun s => (s - 1) ^ r * Complex.exp (SC s)) (t : ℂ) :=
      ((analyticAt_id.sub analyticAt_const).pow r).mul (hSCa t (Set.mem_Ioi.1 ht)).cexp
    have h1 : AnalyticAt ℝ (fun s => (s - 1) ^ r * Complex.exp (SC s)) (t : ℂ) := h.restrictScalars
    exact h1.comp (Complex.ofRealCLM.analyticAt t)
  have hid : Set.EqOn (fun t : ℝ => G t) (fun t : ℝ => ((t : ℂ) - 1) ^ r * Complex.exp (SC t)) (Set.Ioi 1) :=
    ha1.eqOn_of_preconnected_of_eventuallyEq ha2 isPreconnected_Ioi (z₀ := B + 1)
      (Set.mem_Ioi.2 (by linarith)) (by
        filter_upwards [Ioi_mem_nhds (show B < B + 1 by linarith)] with t ht
        exact hEq t ht)
  have hGb : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖G σ‖ ≤ Real.exp M * (σ - 1) ^ r := by
    intro σ h1 h2
    have e := hid (Set.mem_Ioi.2 h1)
    simp only at e
    have hn : ‖(σ : ℂ) - 1‖ = σ - 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [e, norm_mul, norm_pow, hn, hSC, Complex.norm_exp_ofReal, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hT σ h1 h2)) (pow_nonneg (by linarith) _)
  obtain ⟨G', hG'a, hG'e⟩ := hR G r (Real.exp M) hGa hGb
  have hG'v : ∀ σ : ℝ, 1 < σ → G' σ = ((Real.exp (∑' p, c p * Real.exp (-(l p * σ))) : ℝ) : ℂ) := by
    intro σ hσ
    have e1 := hid (Set.mem_Ioi.2 hσ)
    simp only at e1
    have e2 := hG'e σ hσ
    have hne : ((σ : ℂ) - 1) ^ r ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 (by exact_mod_cast hσ.ne'))
    rw [e1] at e2
    have e3 := mul_left_cancel₀ hne e2
    rw [← e3, hSC, Complex.ofReal_exp]
  have hLand := hL (W × ℕ) c l 0 1 G' hc0 hl0 (fun σ hσ => hG'a σ hσ) hsum (fun σ hσ => hG'v σ hσ)
  set N : ℕ := ∑ i, d (x i) with hNd
  have hN1 : 1 ≤ N := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact le_trans (hS.pos (x i)) (Finset.single_le_sum (f := fun i => d (x i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hs0 := hLand (1 / N) (by positivity)
  obtain ⟨c0, hc0pos, hc0le⟩ := hN N hN1
  have hlow : ∀ w, c0 / N * (q w : ℝ)⁻¹ ≤ ∑ k ∈ Finset.range N, c (w, k) * Real.exp (-(l (w, k) * (1 / N))) := by
    intro w
    have hnew := hc0le (Σ i : ι, Fin (d (x i))) (fun ib => A (x ib.1) w ib.2)
      (by rw [Fintype.card_sigma]; simp [hNd]) (by
        rw [Fintype.prod_sigma, norm_prod]
        exact Finset.prod_eq_one fun i _ => hS.det (x i) w)
    have hPk : ∀ k, (∑ ib : Σ i : ι, Fin (d (x i)), A (x ib.1) w ib.2 ^ (k + 1)) = PP A x (w, k) := fun k => by
      rw [Fintype.sum_sigma]; rfl
    simp only [hPk] at hnew
    have hterm : ∀ k ∈ Finset.range N, ‖PP A x (w, k)‖ ^ 2 / N * (q w : ℝ)⁻¹ ≤ c (w, k) * Real.exp (-(l (w, k) * (1 / N))) := by
      intro k hk
      have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hk
      have hlog : 0 ≤ Real.log (q w) := Real.log_nonneg (hq1 w)
      have he : (q w : ℝ)⁻¹ ≤ Real.exp (-(l (w, k) * (1 / N))) := by
        rw [← Real.exp_log (hq w), ← Real.exp_neg]
        refine Real.exp_le_exp.2 (neg_le_neg ?_)
        simp only [hl, ll]
        calc ((k : ℝ) + 1) * Real.log (q w) * (1 / N) = ((k + 1) / N) * Real.log (q w) := by ring
          _ ≤ 1 * Real.log (q w) := mul_le_mul_of_nonneg_right ((div_le_one hNpos).2 hk') hlog
          _ = Real.log (q w) := one_mul _
      have hc' : ‖PP A x (w, k)‖ ^ 2 / N ≤ c (w, k) := by
        simp only [hc, cc]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hk'
      exact mul_le_mul hc' he (by positivity) (hc0 _)
    calc c0 / N * (q w : ℝ)⁻¹ ≤ (∑ k ∈ Finset.range N, ‖PP A x (w, k)‖ ^ 2) / N * (q w : ℝ)⁻¹ := by
          gcongr
      _ = ∑ k ∈ Finset.range N, ‖PP A x (w, k)‖ ^ 2 / N * (q w : ℝ)⁻¹ := by
          rw [Finset.sum_div, Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum hterm
  have hsw : Summable fun w => ∑ k ∈ Finset.range N, c (w, k) * Real.exp (-(l (w, k) * (1 / N))) :=
    summable_sum (s := Finset.range N) fun k _ => hs0.comp_injective (fun a b h => (Prod.mk.inj h).1)
  have h2 : Summable fun w => c0 / N * (q w : ℝ)⁻¹ :=
    Summable.of_nonneg_of_le (fun w => by have := hq w; positivity) hlow hsw
  have h3 : Summable fun w => (q w : ℝ)⁻¹ := by
    have := h2.mul_left (N / c0)
    refine this.congr fun w => ?_
    field_simp
  exact hS.primes.div h3

end PositivityTheory.RgJS
