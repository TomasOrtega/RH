import Formalism.SharpRestriction.InertJacobiLevels.RayPrimes

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField

section Norm

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Establish `h1` using `H.gal_sqd H.conj`. Establish `h2 : H.gal H.conj = R.cc` using `H.galE_conjE`. Rewrite `h1` using `[h2]`. Simplify `h1` using `[Formalism.HC.Frame.cc, c0]`.
-/
theorem conj_bE : H.conj (H.sqd) = - H.sqd := by
  have h1 := H.gal_sqd H.conj
  have h2 : H.gal H.conj = R.cc := H.galE_conjE
  rw [h2] at h1
  simpa [Formalism.HC.Frame.cc, c0] using h1

/- English proof (translation)
Conclude with `H.sqd_sq`.
-/
theorem bE_sq : H.sqd ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

/- English proof (translation)
Use `⟨Polynomial.X ^ 2 + Polynomial.C (H.d : ℤ), by monicity!, ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]`. Simplify using `only [eq_intCast, Int.cast_natCast]`. Take the linear combination `bE_sq H`.
-/
theorem bE_integral : IsIntegral ℤ (H.sqd) := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (H.d : ℤ), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  simp only [eq_intCast, Int.cast_natCast]
  linear_combination bE_sq H

def bO : 𝓞 H.E := ⟨H.sqd, bE_integral H⟩

/- English proof (translation)
Establish `hbc : ((bO H : 𝓞 H.E) : H.E) = H.sqd` using `rfl`. Establish `hco : (((1 + (M : 𝓞 H.E) * ((x : 𝓞 H.E) + (y : 𝓞 H.E) * bO H) : 𝓞 H.E)) : H.E) = 1 + (M : H.E) * ((x : H.E) + (y : H.E) * H.sqd)`. Rewrite using `[← hbc]`. Use `push_cast`. Both sides reduce to the same expression.

Use `⟨1 + (M : 𝓞 H.E) * ((x : 𝓞 H.E) + (y : 𝓞 H.E) * bO H), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hco]`. Establish `hb : H.sqd ∈ H.K` using `IntermediateField.mem_adjoin_simple_self ℚ _`. Conclude with `add_mem (one_mem _) (mul_mem (natCast_mem _ _) (add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) hb)))`. Rewrite using `[hco]`.

Establish `hT' : (T : H.E) = (1 + M * x) ^ 2 + H.d * (M * y) ^ 2` using `by exact_mod_cast congrArg (Int.cast : ℤ → H.E) hT`. Simplify using `only [map_add, map_mul, map_one, map_natCast, map_intCast, conj_bE]`. Rewrite using `[hT']`. Take the linear combination `(-(M : H.E) ^ 2 * (y : H.E) ^ 2) * bE_sq H`. Rewrite using `[← hM, Ideal.mem_span_singleton]`.

Conclude with `⟨(x : 𝓞 H.E) + (y : 𝓞 H.E) * bO H, by ring⟩`.
-/
theorem tnorm_of (x y : ℤ) (T M : ℕ) (hT : (T : ℤ) = (1 + M * x) ^ 2 + H.d * (M * y) ^ 2)
    (hM : M = H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2) : TNorm H T := by
  have hbc : ((bO H : 𝓞 H.E) : H.E) = H.sqd := rfl
  have hco : (((1 + (M : 𝓞 H.E) * ((x : 𝓞 H.E) + (y : 𝓞 H.E) * bO H) : 𝓞 H.E)) : H.E) =
      1 + (M : H.E) * ((x : H.E) + (y : H.E) * H.sqd) := by
    rw [← hbc]; push_cast; rfl
  refine ⟨1 + (M : 𝓞 H.E) * ((x : 𝓞 H.E) + (y : 𝓞 H.E) * bO H), ?_, ?_, ?_⟩
  · rw [hco]
    have hb : H.sqd ∈ H.K := IntermediateField.mem_adjoin_simple_self ℚ _
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ _) (add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) hb)))
  · rw [hco]
    have hT' : (T : H.E) = (1 + M * x) ^ 2 + H.d * (M * y) ^ 2 := by exact_mod_cast congrArg (Int.cast : ℤ → H.E) hT
    simp only [map_add, map_mul, map_one, map_natCast, map_intCast, conj_bE]
    rw [hT']
    linear_combination (-(M : H.E) ^ 2 * (y : H.E) ^ 2) * bE_sq H
  · rw [← hM, Ideal.mem_span_singleton]
    exact ⟨(x : 𝓞 H.E) + (y : 𝓞 H.E) * bO H, by ring⟩

end Norm

/- English proof (translation)
Establish `hM : 0 < 2 ^ (2 + 2) * A.q * A.d * (A.g0 * A.g1) ^ 2`. Use `A.hyp.1.pos` as an intermediate fact. Use `A.hyp.2.1.pos` as an intermediate fact. Use `A.first_prime_isPrime.pos` as an intermediate fact. Use `A.second_prime_isPrime.pos` as an intermediate fact.

Check the signs of the components of the expression. Take `⟨x, y, T, hN, hp, hT⟩` from `h A.d _ N A.hyp.2.1 hM`. Conclude with `⟨T, hN, hp, fun u0 T' Lw => tnorm_of (hostOf A u0 T' Lw) x y T _ hT rfl⟩`.
-/
theorem exists_strictHenselian_absolutely_closed_local_ring (h : RayPrimes) {s B : ℕ} (A : Arith B (4 * (2 * s + 15) * 9 + 1)) (N : ℕ) :
    ∃ T : ℕ, N < T ∧ T.Prime ∧ ∀ (u0 : (Rt s).A) (T' Lw : ℕ), TNorm (hostOf A u0 T' Lw) T := by
  have hM : 0 < 2 ^ (2 + 2) * A.q * A.d * (A.g0 * A.g1) ^ 2 := by
    have := A.hyp.1.pos; have := A.hyp.2.1.pos; have := A.first_prime_isPrime.pos; have := A.second_prime_isPrime.pos
    positivity
  obtain ⟨x, y, T, hN, hp, hT⟩ := h A.d _ N A.hyp.2.1 hM
  exact ⟨T, hN, hp, fun u0 T' Lw => tnorm_of (hostOf A u0 T' Lw) x y T _ hT rfl⟩

/- English proof (translation)
Establish `hx : 0 < sc.x` using `by linarith [sc.one_lt_alt]`. Establish `hb : 0 < sc.b` using `Real.exp_pos _`. Establish `hX : 1 ≤ sc.X'` using `Real.one_le_exp (by positivity)`. Establish `hn' : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `e : sc.w'' n = sc.b / (n * sc.X')`.

Simplify using `only [Scale.w'', Scale.b', Scale.a]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Use `⟨by positivity, ?_⟩` and prove the remaining obligations. Rewrite using `[div_le_iff₀ (by positivity)]`.

Establish `h1 : (1 : ℝ) ≤ n * sc.X'` using `one_le_mul_of_one_le_of_one_le hn' hX`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem scale_w''_bounds (sc : Scale) (n : ℕ) (hn : 1 ≤ n) : 0 ≤ sc.w'' n ∧ sc.w'' n ≤ sc.b := by
  have hx : 0 < sc.x := by linarith [sc.one_lt_alt]
  have hb : 0 < sc.b := Real.exp_pos _
  have hX : 1 ≤ sc.X' := Real.one_le_exp (by positivity)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have e : sc.w'' n = sc.b / (n * sc.X') := by
    simp only [Scale.w'', Scale.b', Scale.a]
    field_simp
  rw [e]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have h1 : (1 : ℝ) ≤ n * sc.X' := one_le_mul_of_one_le_of_one_le hn' hX
  nlinarith

def sizeDataOfAjZero (D : D7) (sc : Scale)
    (hTT : D.host.TT = ∅)
    (hAj : ∀ j w, D.what₂.Aj j w = 0)
    (hTu : ∀ u, sc.b ^ ((D.R.m : ℝ) / 2) ≤ ((D.mem u).A.T : ℝ))
    (hb : ∀ τ j, (((D.hc τ).b j : ℚ) : ℝ) ≤ sc.b ^ 2)
    (hsplit : ⌊sc.x ^ (sc.ez / 5)⌋₊ ≤ D.host.splitBound)
    (ho : (D.R.o : ℝ) ≤ sc.x ^ (sc.eps / 100))
    (hQS : (D.host.QS : ℝ) ≤ 4 * D.R.n * sc.x ^ (sc.eps / 100))
    (j0 : ℕ) (hj0 : Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ j0)
    (hLw : 10 * j0 + 20 ≤ D.host.Lw)
    (η Cc : ℝ) (hη : 0 < η)
    (hthick : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ,
      (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces →
      sc.b ≤ wj D j τ ∧ wj D j τ ≤ sc.b + η + 1)
    (hthin : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) →
      sc.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ sc.w'' D.R.n + η)
    (hcg : ∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
      (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) ≤ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ∧
      (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ Cc * ((D.R.k : ℝ) * (4 * (D.s.Del : ℝ))))
    (hcv : ∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧
      (((D.hc τ).v i : ℚ) : ℝ) ≤ (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)))
    (hcu : ∀ u τ (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k →
      0 ≤ (((D.hcW u τ).u i : ℚ) : ℝ) ∧ (((D.hcW u τ).u i : ℚ) : ℝ) ≤ (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)))
    (hbe : ∀ τ (i j : Fin D.R.m), |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| ≤ η)
    (hSc : 0 < (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)))
    (Ct : ℝ) (htw : 1 ≤ (D.R.t : ℝ) ∧ (D.R.t : ℝ) ≤ sc.x ^ Ct)
    (CGam : ℝ) (hCG : 0 < CGam)
    (hGam : ∀ u, Real.log (D.mem u).A.GamP = CGam * (D.R.m : ℝ) ^ 5 * D.R.f * sc.L)
    (LaG : ℝ) (hT2 : D.host.T2.card = 1) : SizeData₂ D where
  sc := sc
  aT := fun _ => 0
  aT_win := fun t => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  bT := fun _ => 0
  bT_ge := fun t => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  top_u := fun _ t _ _ => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  top_b := fun _ t _ _ => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  supp := ∅
  gain := fun _ _ => 0
  F := fun _ _ => 0
  E := fun _ _ _ => 0
  tau := fun _ => 0
  io := fun _ => 0
  gain_supp := fun _ _ _ => rfl
  F_supp := fun _ _ _ => rfl
  E_supp := fun _ _ _ _ => rfl
  tau_supp := fun _ _ => rfl
  io_supp := fun _ _ => rfl
  gain_g := fun _ _ _ => rfl
  b_le := hb
  untwisted := fun w _ j _ _ => ⟨hAj j w, rfl⟩
  not_inert := fun _ _ _ => ⟨fun _ => rfl, rfl, rfl⟩
  drop := ∅
  drop_alt := fun _ => Set.notMem_empty _
  F_conj := fun _ _ => rfl
  F_above := by intros; rfl
  j0 := j0
  logFiveDepth_le := hj0
  weightLength_ge_depth := hLw
  logDerivativeAtOne := dlogL D 1
  logDerivative_at_one_eq := rfl
  split_tie := hsplit
  o_tie := ho
  QS_tie := hQS
  NuLat := fun _ => ⊤
  de2 := (D.host.T2.card : ℝ) / D.R.n
  thickDensity_pos := by
    have : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.toFrame.ord_pos
    rw [hT2]; positivity
  thickDensity_le_one := by
    have : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.toFrame.ord_pos
    rw [hT2, div_le_one (by linarith)]; simpa using this
  typeDensity_eq_card_div := rfl
  LaG := LaG
  Sc := (D.R.k : ℝ) * (4 * (D.s.Del : ℝ))
  etaSz := η
  Cc := Cc
  win_thick := hthick
  win_top := fun _ _ _ _ t _ => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  win_thin := hthin
  cloud_gap := hcg
  cloud_v := hcv
  cloud_u := hcu
  be_close := hbe
  Sc_pos := hSc
  Sc_eq := rfl
  etaSz_pos := hη
  TTw := fun _ => Finset.univ
  TTw_full := fun _ _ => rfl
  Ct := Ct
  t_win := htw
  CGam := CGam
  CGam_pos := hCG
  Gam_eq := hGam
  wPart := fun _ _ _ _ => 1
  wPart_ge := fun _ _ _ _ => le_rfl
  lenMN := fun _ _ => 0

/- English proof (translation)
Use `⟨⌈(L - 15) / 2⌉₊, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `Nat.le_ceil ((L - 15) / 2)`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h` using `Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ (L - 15) / 2)`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_odd (L : ℝ) (hL : 20 < L) : ∃ s : ℕ, L ≤ ((2 * s + 15 : ℕ) : ℝ) ∧ ((2 * s + 15 : ℕ) : ℝ) < L + 2 := by
  refine ⟨⌈(L - 15) / 2⌉₊, ?_, ?_⟩
  · have h := Nat.le_ceil ((L - 15) / 2)
    push_cast
    linarith
  · have h := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ (L - 15) / 2)
    push_cast
    linarith

/- English proof (translation)
Introduce `eps he0 he1`. Establish `hx1 : (1 : ℝ) < (30 : ℝ) ^ (1 / eps)` using `Real.one_lt_rpow (by norm_num) (by positivity)`. Use `⟨(30 : ℝ) ^ (1 / eps), hx1, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx0 : 1 < x` using `hx1.trans hx`. Establish `hL : 30 < x ^ eps`.

Establish `h1 : ((30 : ℝ) ^ (1 / eps)) ^ eps < x ^ eps` using `Real.rpow_lt_rpow (by positivity) hx he0`. Rewrite `h1` using `[← Real.rpow_mul (by norm_num), one_div_mul_cancel he0.ne', Real.rpow_one]`. Then use the resulting hypothesis. Take `⟨s, hs1, hs2⟩` from `exists_odd (x ^ eps - 2) (by linarith)`. Use `set sc : Scale := ⟨x, eps, hx0, he0, he1, 1, le_rfl⟩ with hsc`. Establish `hscL : sc.L = x ^ eps` using `rfl`.

Establish `hscb : sc.b = Real.exp (x ^ eps)` using `rfl`. Establish `hb0 : 0 < sc.b` using `Real.exp_pos _`. Establish `hbL : x ^ eps + 1 ≤ sc.b` using `Real.add_one_le_exp _`. Establish `hβ1 : sc.b ≤ (⌈sc.b⌉₊ : ℝ)` using `Nat.le_ceil _`. Establish `hβ2 : (⌈sc.b⌉₊ : ℝ) < sc.b + 1` using `Nat.ceil_lt_add_one hb0.le`.

Establish `hs2' : 2 * (s : ℝ) + 15 < x ^ eps + 2` using `by push_cast at hs2; linarith`. Establish `hs0 : (0 : ℝ) ≤ s` using `Nat.cast_nonneg s`. Establish `hbsq : 21 * sc.b ≤ sc.b ^ 2` using `by nlinarith`. Use `⟨s, ⌊x ^ (eps / 5)⌋₊, 10 * ⌈Real.logb 5 (((Rt s).n : ℝ) * (Rt s).N (Rt s).m / (Rt s).m)⌉₊ + 20, ⌈sc.b⌉₊, Real.exp (256 * x ^ eps), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Nat.one_le_ceil_iff.2 hb0`.

Conclude with `Real.one_lt_exp_iff.2 (by linarith)`. Introduce `lb D A u0 T Tstar hT hF`. Establish `hR : D.R = Rt s` using `congrArg Sigma.fst hF.host_eq`. Establish `hTT : D.host.TT = ∅` using `(congrArg (fun p : Σ R : Ranks, Host R => p.2.TT = ∅) hF.host_eq).mpr rfl`. Establish `hLw : D.host.Lw = _` using `congrArg (fun p : Σ R : Ranks, Host R => p.2.Lw) hF.host_eq`.

Establish `hsb : D.host.splitBound = _` using `congrArg (fun p : Σ R : Ranks, Host R => p.2.splitBound) hF.host_eq`. Establish `hQS : D.host.QS = 16` using `congrArg (fun p : Σ R : Ranks, Host R => p.2.QS) hF.host_eq`. Establish `hone : (1 : ℝ) ≤ sc.x ^ (sc.eps / 100)` using `Real.one_le_rpow hx0.le (by positivity)`. Establish `hk : D.R.k = 8` using `by rw [hR]; rfl`. Establish `hm : D.R.m = 2` using `by rw [hR]; rfl`.

Establish `hn : D.R.n = 4` using `by rw [hR]; rfl`. Establish `hf : D.R.f = 8` using `by rw [hR]; rfl`. Establish `ht : D.R.t = 2 * s + 15` using `by rw [hR]; rfl`. Establish `hSc : (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) = 32` using `by rw [hk, hF.Del_eq]; norm_num`. Establish `hw` using `scale_w''_bounds sc D.R.n (by omega)`.

Establish `hwj : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, sc.b ≤ wj D j τ ∧ wj D j τ ≤ sc.b + 1 + 3 * ((s : ℝ) + 9)`. Introduce `j h1 h2 τ`. Establish `h : j - 1 < D.R.m` using `by omega`. Unfold `wj`. Rewrite using `[dif_pos h, hF.he]`.

Take `h3 | h3 : j - 1 = 0 ∨ j - 1 = 1` from `by omega`. Use `all_goals`. Simplify using `only [h3]`. Use `push_cast`. Apply the tactic sequence `constructor <;> linarith`.

Use `⟨sizeDataOfAjZero D sc hTT hF.Aj_eq ?_ ?_ ?_ ?_ ?_ ⌈Real.logb 5 (((Rt s).n : ℝ) * (Rt s).N (Rt s).m / (Rt s).m)⌉₊ ?_ ?_ (2 * sc.b + 4 * ((s : ℝ) + 9) + 2) 2 (by positivity) ?_ ?_ ?_ ?_ ?_ ?_ (by rw [hSc]; norm_num) eps ?_ 1 one_pos ?_ (x ^ eps) (congrArg (fun p : Σ R : Ranks, Hos …` and prove the remaining obligations. Introduce `u`. Rewrite using `[hm, hF.T_eq]`. Evaluate the numerical expressions. Conclude with `hT`.

Introduce `τ j`. Rewrite using `[hF.hb]`. Take `h3 | h3 : (j : ℕ) = 0 ∨ (j : ℕ) = 1` from `by omega`. Use `all_goals`. Rewrite using `[h3]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hsb] show ⌊x ^ (eps / 1 / 5)⌋₊ ≤ ⌊x ^ (eps / 5)⌋₊`. Rewrite using `[div_one]`. Establish `h1 : D.R.o = 1` using `by rw [hR]; exact Formalism.HC.cyclicFrame_index 2`.

Rewrite using `[h1, Nat.cast_one]`. Conclude with `hone`. Rewrite using `[hQS, hn]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hR]`. Conclude with `Nat.le_ceil _`. Rewrite using `[hLw]`. Use `show _ ≤ _ + 20 + 4`. Use linear arithmetic over natural numbers and integers.

Introduce `j h1 h2 τ _`. Take `⟨a1, a2⟩` from `hwj j h1 h2 τ`. Apply the tactic sequence `constructor <;> linarith`. Introduce `j h1 h2 τ _`. Take `⟨a1, a2⟩` from `hwj j h1 h2 τ`.

Apply the tactic sequence `constructor <;> linarith [hw.1, hw.2]`. Introduce `τ h0 _`. Rewrite using `[hSc, hF.hu0, hF.hv]`. Evaluate the numerical expressions. Introduce `τ i`.

Rewrite using `[hSc, hF.hv]`. Establish `h3 : ((i : ℕ) : ℝ) ≤ 6` using `by exact_mod_cast (by omega : (i : ℕ) ≤ 6)`. Establish `h4 : (0 : ℝ) ≤ ((i : ℕ) : ℝ)` using `by positivity`. Use `push_cast`. Apply the tactic sequence `constructor <;> linarith`.

Introduce `u τ i h1 h2`. Rewrite using `[hSc, hF.hu u τ i h1 h2]`. Establish `h3 : ((i : ℕ) : ℝ) ≤ 6` using `by exact_mod_cast (by omega : (i : ℕ) ≤ 6)`. Establish `h4 : (1 : ℝ) ≤ ((i : ℕ) : ℝ)` using `by exact_mod_cast h1`. Use `push_cast`.

Apply the tactic sequence `constructor <;> linarith`. Introduce `τ i j`. Rewrite using `[hF.hb, hF.he]`. Take `h3 | h3 : (i : ℕ) = 0 ∨ (i : ℕ) = 1` from `by omega`. Use `all_goals`.

Take `h4 | h4 : (j : ℕ) = 0 ∨ (j : ℕ) = 1` from `by omega`. Use `all_goals`. Rewrite using `[h3, h4]`. Use `push_cast`. Rewrite using `[abs_le]`.

Apply the tactic sequence `constructor <;> linarith`. Rewrite using `[ht] show 1 ≤ _ ∧ _ ≤ x ^ eps`. Move the coercions through the operations in `at hs1 hs2 ⊢`. Apply the tactic sequence `constructor <;> linarith`. Introduce `u`.

Rewrite using `[hF.Gam_eq, Real.log_exp, hm, hf, hscL]`. Evaluate the numerical expressions.
-/
theorem sizeDataAt : SizeDataAt := by
  intro eps he0 he1
  have hx1 : (1 : ℝ) < (30 : ℝ) ^ (1 / eps) := Real.one_lt_rpow (by norm_num) (by positivity)
  refine ⟨(30 : ℝ) ^ (1 / eps), hx1, fun x hx => ?_⟩
  have hx0 : 1 < x := hx1.trans hx
  have hL : 30 < x ^ eps := by
    have h1 : ((30 : ℝ) ^ (1 / eps)) ^ eps < x ^ eps := Real.rpow_lt_rpow (by positivity) hx he0
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel he0.ne', Real.rpow_one] at h1
  obtain ⟨s, hs1, hs2⟩ := exists_odd (x ^ eps - 2) (by linarith)
  set sc : Scale := ⟨x, eps, hx0, he0, he1, 1, le_rfl⟩ with hsc
  have hscL : sc.L = x ^ eps := rfl
  have hscb : sc.b = Real.exp (x ^ eps) := rfl
  have hb0 : 0 < sc.b := Real.exp_pos _
  have hbL : x ^ eps + 1 ≤ sc.b := Real.add_one_le_exp _
  have hβ1 : sc.b ≤ (⌈sc.b⌉₊ : ℝ) := Nat.le_ceil _
  have hβ2 : (⌈sc.b⌉₊ : ℝ) < sc.b + 1 := Nat.ceil_lt_add_one hb0.le
  have hs2' : 2 * (s : ℝ) + 15 < x ^ eps + 2 := by push_cast at hs2; linarith
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hbsq : 21 * sc.b ≤ sc.b ^ 2 := by nlinarith
  refine ⟨s, ⌊x ^ (eps / 5)⌋₊,
    10 * ⌈Real.logb 5 (((Rt s).n : ℝ) * (Rt s).N (Rt s).m / (Rt s).m)⌉₊ + 20, ⌈sc.b⌉₊,
    Real.exp (256 * x ^ eps), ?_, ?_, ?_⟩
  · exact Nat.one_le_ceil_iff.2 hb0
  · exact Real.one_lt_exp_iff.2 (by linarith)
  intro lb D A u0 T Tstar hT hF
  have hR : D.R = Rt s := congrArg Sigma.fst hF.host_eq
  have hTT : D.host.TT = ∅ :=
    (congrArg (fun p : Σ R : Ranks, Host R => p.2.TT = ∅) hF.host_eq).mpr rfl
  have hLw : D.host.Lw = _ := congrArg (fun p : Σ R : Ranks, Host R => p.2.Lw) hF.host_eq
  have hsb : D.host.splitBound = _ := congrArg (fun p : Σ R : Ranks, Host R => p.2.splitBound) hF.host_eq
  have hQS : D.host.QS = 16 := congrArg (fun p : Σ R : Ranks, Host R => p.2.QS) hF.host_eq
  have hone : (1 : ℝ) ≤ sc.x ^ (sc.eps / 100) := Real.one_le_rpow hx0.le (by positivity)
  have hk : D.R.k = 8 := by rw [hR]; rfl
  have hm : D.R.m = 2 := by rw [hR]; rfl
  have hn : D.R.n = 4 := by rw [hR]; rfl
  have hf : D.R.f = 8 := by rw [hR]; rfl
  have ht : D.R.t = 2 * s + 15 := by rw [hR]; rfl
  have hSc : (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) = 32 := by rw [hk, hF.Del_eq]; norm_num
  have hw := scale_w''_bounds sc D.R.n (by omega)
  have hwj : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, sc.b ≤ wj D j τ ∧ wj D j τ ≤ sc.b + 1 + 3 * ((s : ℝ) + 9) := by
    intro j h1 h2 τ
    have h : j - 1 < D.R.m := by omega
    unfold wj
    rw [dif_pos h, hF.he]
    obtain h3 | h3 : j - 1 = 0 ∨ j - 1 = 1 := by omega
    all_goals
      simp only [h3]
      push_cast
      constructor <;> linarith
  refine ⟨sizeDataOfAjZero D sc hTT hF.Aj_eq ?_ ?_ ?_ ?_ ?_ ⌈Real.logb 5 (((Rt s).n : ℝ) * (Rt s).N (Rt s).m / (Rt s).m)⌉₊ ?_ ?_
    (2 * sc.b + 4 * ((s : ℝ) + 9) + 2) 2 (by positivity) ?_ ?_ ?_ ?_ ?_ ?_ (by rw [hSc]; norm_num)
    eps ?_ 1 one_pos ?_ (x ^ eps) (congrArg (fun p : Σ R : Ranks, Host R => p.2.T2.card) hF.host_eq), rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro u
    rw [hm, hF.T_eq]
    norm_num
    exact hT
  · intro τ j
    rw [hF.hb]
    obtain h3 | h3 : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
    all_goals
      rw [h3]
      push_cast
      linarith
  · rw [hsb]
    show ⌊x ^ (eps / 1 / 5)⌋₊ ≤ ⌊x ^ (eps / 5)⌋₊
    rw [div_one]
  · have h1 : D.R.o = 1 := by rw [hR]; exact Formalism.HC.cyclicFrame_index 2
    rw [h1, Nat.cast_one]
    exact hone
  · rw [hQS, hn]
    push_cast
    linarith
  · rw [hR]; exact Nat.le_ceil _
  · rw [hLw]; show _ ≤ _ + 20 + 4; omega
  · intro j h1 h2 τ _
    obtain ⟨a1, a2⟩ := hwj j h1 h2 τ
    constructor <;> linarith
  · intro j h1 h2 τ _
    obtain ⟨a1, a2⟩ := hwj j h1 h2 τ
    constructor <;> linarith [hw.1, hw.2]
  · intro τ h0 _
    rw [hSc, hF.hu0, hF.hv]
    norm_num
  · intro τ i
    rw [hSc, hF.hv]
    have h3 : ((i : ℕ) : ℝ) ≤ 6 := by exact_mod_cast (by omega : (i : ℕ) ≤ 6)
    have h4 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := by positivity
    push_cast
    constructor <;> linarith
  · intro u τ i h1 h2
    rw [hSc, hF.hu u τ i h1 h2]
    have h3 : ((i : ℕ) : ℝ) ≤ 6 := by exact_mod_cast (by omega : (i : ℕ) ≤ 6)
    have h4 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast
    constructor <;> linarith
  · intro τ i j
    rw [hF.hb, hF.he]
    obtain h3 | h3 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
    all_goals
      obtain h4 | h4 : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
      all_goals
        rw [h3, h4]
        push_cast
        rw [abs_le]
        constructor <;> linarith
  · rw [ht]
    show 1 ≤ _ ∧ _ ≤ x ^ eps
    push_cast at hs1 hs2 ⊢
    constructor <;> linarith
  · intro u
    rw [hF.Gam_eq, Real.log_exp, hm, hf, hscL]
    norm_num

end Formalism.MainNotions.Inhab

end
