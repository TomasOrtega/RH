import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.TwoRelations

open Filter Topology

noncomputable def mult (l : ℕ) (s : ℂ) : ℂ := (l : ℂ) ^ (1 - s)

noncomputable def efac (l h : ℕ) (s : ℂ) : ℂ := mult l s ^ h - 1

noncomputable def wsum {G : Type} (T : G → ℂ → ℂ) (l : ℕ) (τ : Equiv.Perm G) (h : ℕ)
    (c : G) (s : ℂ) : ℂ :=
  ∑ e ∈ Finset.range h, mult l s ^ e * T ((τ ^ e) c) s

/- English proof (translation)
Introduce `s`. Establish `h0 : (l : ℂ) ≠ 0` using `by exact_mod_cast hl.ne_zero`. Conclude with `((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl h0)`.
-/
lemma mult_differentiable {l : ℕ} (hl : l.Prime) : Differentiable ℂ (mult l) := by
  intro s
  have h0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl h0)

/- English proof (translation)
Introduce `s`. Conclude with `(((mult_differentiable hl) s).pow h).sub (differentiableAt_const _)`.
-/
lemma efac_differentiable {l : ℕ} (hl : l.Prime) (h : ℕ) : Differentiable ℂ (efac l h) := by
  intro s
  exact (((mult_differentiable hl) s).pow h).sub (differentiableAt_const _)

/- English proof (translation)
Introduce `s`. Unfold `wsum`. Use `DifferentiableAt.fun_sum fun e _ => ?_` and prove the remaining obligations. Conclude with `(((mult_differentiable hl) s).pow e).mul (hT _ s)`.
-/
lemma wsum_differentiable {G : Type} {T : G → ℂ → ℂ} {l : ℕ} (hl : l.Prime)
    (hT : ∀ c, Differentiable ℂ (T c)) (τ : Equiv.Perm G) (h : ℕ) (c : G) :
    Differentiable ℂ (wsum T l τ h c) := by
  intro s
  unfold wsum
  refine DifferentiableAt.fun_sum fun e _ => ?_
  exact (((mult_differentiable hl) s).pow e).mul (hT _ s)

/- English proof (translation)
Unfold `mult`. Rewrite using `[Complex.norm_natCast_cpow_of_pos hl.pos]`. Apply `Real.rpow_lt_one_of_one_lt_of_neg` to reduce the goal to its premises. Conclude with `hl.one_lt` after adjusting the coercions. Simplify using `only [Complex.sub_re, Complex.one_re]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma norm_mult_lt_one {l : ℕ} (hl : l.Prime) {s : ℂ} (hs : 1 < s.re) : ‖mult l s‖ < 1 := by
  unfold mult
  rw [Complex.norm_natCast_cpow_of_pos hl.pos]
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hl.one_lt
  · simp only [Complex.sub_re, Complex.one_re]; linarith

/- English proof (translation)
Introduce `h0`. Establish `h1 : mult l s ^ h = 1` using `sub_eq_zero.mp h0`. Establish `h2 : ‖mult l s‖ ^ h = 1` using `by rw [← norm_pow, h1, norm_one]`. Establish `h3` using `pow_lt_one₀ (norm_nonneg _) (norm_mult_lt_one hl hs) hh`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma efac_ne_zero {l h : ℕ} (hl : l.Prime) (hh : h ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    efac l h s ≠ 0 := by
  intro h0
  have h1 : mult l s ^ h = 1 := sub_eq_zero.mp h0
  have h2 : ‖mult l s‖ ^ h = 1 := by rw [← norm_pow, h1, norm_one]
  have h3 := pow_lt_one₀ (norm_nonneg _) (norm_mult_lt_one hl hs) hh
  linarith

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [wsum]`. Consider the case `succ n ih`. Establish `ih' : ∑ e ∈ Finset.range n, mult l s ^ e * T ((τ ^ e) c) s = mult l s ^ n * D ((τ ^ n) c) s - D c s` using `ih`. Establish `hstep : (τ ^ (n + 1)) c = τ ((τ ^ n) c)`.

Rewrite using `[pow_succ', Equiv.Perm.mul_apply]`. Unfold `wsum`. Rewrite using `[Finset.sum_range_succ, ih', ← hrel ((τ ^ n) c), hstep]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma telescope {G : Type} {D T : G → ℂ → ℂ} {l : ℕ} {τ : Equiv.Perm G} {s : ℂ}
    (hrel : ∀ c, mult l s * D (τ c) s - D c s = T c s) (c : G) (n : ℕ) :
    wsum T l τ n c s = mult l s ^ n * D ((τ ^ n) c) s - D c s := by
  induction n with
  | zero => simp [wsum]
  | succ n ih =>
    have ih' : ∑ e ∈ Finset.range n, mult l s ^ e * T ((τ ^ e) c) s
        = mult l s ^ n * D ((τ ^ n) c) s - D c s := ih
    have hstep : (τ ^ (n + 1)) c = τ ((τ ^ n) c) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    unfold wsum
    rw [Finset.sum_range_succ, ih', ← hrel ((τ ^ n) c), hstep]
    ring

/- English proof (translation)
Rewrite using `[telescope hrel c, pow_orderOf_eq_one]`. Simplify using `only [efac, Equiv.Perm.coe_one, id_eq]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma efac_mul_eq {G : Type} [Fintype G] {D T : G → ℂ → ℂ} {l : ℕ} {τ : Equiv.Perm G} {s : ℂ}
    (hrel : ∀ c, mult l s * D (τ c) s - D c s = T c s) (c : G) :
    efac l (orderOf τ) s * D c s = wsum T l τ (orderOf τ) c s := by
  rw [telescope hrel c, pow_orderOf_eq_one]
  simp only [efac, Equiv.Perm.coe_one, id_eq]
  ring

/- English proof (translation)
Establish `hexp : ∀ {p : ℕ}, p.Prime → ∀ m : ℕ, mult p s ^ m = Complex.exp ((m : ℂ) * (((Real.log p : ℝ) : ℂ) * (1 - s)))`. Introduce `p hp m`. Establish `hp0 : (p : ℂ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Rewrite using `[Complex.exp_nat_mul, mult, Complex.cpow_def_of_ne_zero hp0, Complex.natCast_log]`. Establish `hu : (1 - s) ≠ 0` using `sub_ne_zero.mpr (Ne.symm hs)`.

Establish `hL : 0 < Real.log l` using `Real.log_pos (by exact_mod_cast hl.one_lt)`. Establish `hL' : 0 < Real.log l'` using `Real.log_pos (by exact_mod_cast hl'.one_lt)`. Establish `e1 : Complex.exp ((h : ℂ) * (((Real.log l : ℝ) : ℂ) * (1 - s))) = 1`. Rewrite using `[← hexp hl]`. Conclude with `sub_eq_zero.mp h1`.

Establish `e2 : Complex.exp ((h' : ℂ) * (((Real.log l' : ℝ) : ℂ) * (1 - s))) = 1`. Rewrite using `[← hexp hl']`. Conclude with `sub_eq_zero.mp h2`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.mp e1`. Take `⟨n', hn'⟩` from `Complex.exp_eq_one_iff.mp e2`.

Establish `hLc : ((Real.log l : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hL.ne'`. Establish `hLc' : ((Real.log l' : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hL'.ne'`. Establish `hhc : (h : ℂ) ≠ 0` using `by exact_mod_cast hh`. Establish `hhc' : (h' : ℂ) ≠ 0` using `by exact_mod_cast hh'`. Establish `hn0 : n ≠ 0`.

Introduce and unpack `rfl`. Establish `: (h : ℂ) * (((Real.log l : ℝ) : ℂ) * (1 - s)) ≠ 0` using `mul_ne_zero hhc (mul_ne_zero hLc hu)`. Apply `this` to reduce the goal to its premises. Rewrite using `[hn]`. Simplify using the standard rewrite rules.

Establish `hn0' : n' ≠ 0`. Introduce and unpack `rfl`. Establish `: (h' : ℂ) * (((Real.log l' : ℝ) : ℂ) * (1 - s)) ≠ 0` using `mul_ne_zero hhc' (mul_ne_zero hLc' hu)`. Apply `this` to reduce the goal to its premises. Rewrite using `[hn']`.

Simplify using the standard rewrite rules. Establish `hcross : ((n' : ℂ) * h * ((Real.log l : ℝ) : ℂ)) = (n : ℂ) * h' * ((Real.log l' : ℝ) : ℂ)`. Apply `mul_right_cancel₀ hu` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hn, hn']`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = (n : ℂ) * h' * ((Real.log l' : ℝ) : ℂ) * (1 - s) := by ring`. Establish `hreal : (n' : ℝ) * h * Real.log l = (n : ℝ) * h' * Real.log l'`. Conclude with `hcross` after adjusting the coercions. Establish `habs : (n'.natAbs : ℝ) * h * Real.log l = (n.natAbs : ℝ) * h' * Real.log l'`.

Use `congrArg abs hreal` as an intermediate fact. Simplify using `only [abs_mul, Nat.abs_cast, abs_of_pos hL, abs_of_pos hL'] at this`. Rewrite using `[Nat.cast_natAbs, Nat.cast_natAbs]`. Use `push_cast`. Conclude with `this`.

Establish `hlog : Real.log ((l : ℝ) ^ (n'.natAbs * h)) = Real.log ((l' : ℝ) ^ (n.natAbs * h'))`. Rewrite using `[Real.log_pow, Real.log_pow]`. Use `push_cast`. Conclude with `habs`. Establish `hpos : (0 : ℝ) < (l : ℝ) ^ (n'.natAbs * h)`.

Establish `: (0 : ℝ) < l` using `by exact_mod_cast hl.pos`. Check the signs of the components of the expression. Establish `hpos' : (0 : ℝ) < (l' : ℝ) ^ (n.natAbs * h')`. Establish `: (0 : ℝ) < l'` using `by exact_mod_cast hl'.pos`. Check the signs of the components of the expression.

Establish `heq` using `Real.log_injOn_pos (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr hpos') hlog`. Establish `hnat : l ^ (n'.natAbs * h) = l' ^ (n.natAbs * h')` using `by exact_mod_cast heq`. Establish `hexp0 : n'.natAbs * h ≠ 0` using `Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hn0') hh`. Establish `hdvd : l ∣ l' ^ (n.natAbs * h')`. Rewrite using `[← hnat]`.

Conclude with `dvd_pow_self l hexp0`. Conclude with `hne ((Nat.prime_dvd_prime_iff_eq hl hl').mp (hl.dvd_of_dvd_pow hdvd))`.
-/
lemma no_common_zero {l l' h h' : ℕ} (hl : l.Prime) (hl' : l'.Prime) (hne : l ≠ l')
    (hh : h ≠ 0) (hh' : h' ≠ 0) {s : ℂ} (hs : s ≠ 1)
    (h1 : efac l h s = 0) (h2 : efac l' h' s = 0) : False := by
  have hexp : ∀ {p : ℕ}, p.Prime → ∀ m : ℕ, mult p s ^ m
      = Complex.exp ((m : ℂ) * (((Real.log p : ℝ) : ℂ) * (1 - s))) := by
    intro p hp m
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [Complex.exp_nat_mul, mult, Complex.cpow_def_of_ne_zero hp0, Complex.natCast_log]
  have hu : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hL : 0 < Real.log l := Real.log_pos (by exact_mod_cast hl.one_lt)
  have hL' : 0 < Real.log l' := Real.log_pos (by exact_mod_cast hl'.one_lt)
  have e1 : Complex.exp ((h : ℂ) * (((Real.log l : ℝ) : ℂ) * (1 - s))) = 1 := by
    rw [← hexp hl]; exact sub_eq_zero.mp h1
  have e2 : Complex.exp ((h' : ℂ) * (((Real.log l' : ℝ) : ℂ) * (1 - s))) = 1 := by
    rw [← hexp hl']; exact sub_eq_zero.mp h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp e1
  obtain ⟨n', hn'⟩ := Complex.exp_eq_one_iff.mp e2
  have hLc : ((Real.log l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLc' : ((Real.log l' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL'.ne'
  have hhc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hhc' : (h' : ℂ) ≠ 0 := by exact_mod_cast hh'
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : (h : ℂ) * (((Real.log l : ℝ) : ℂ) * (1 - s)) ≠ 0 :=
      mul_ne_zero hhc (mul_ne_zero hLc hu)
    apply this; rw [hn]; simp
  have hn0' : n' ≠ 0 := by
    rintro rfl
    have : (h' : ℂ) * (((Real.log l' : ℝ) : ℂ) * (1 - s)) ≠ 0 :=
      mul_ne_zero hhc' (mul_ne_zero hLc' hu)
    apply this; rw [hn']; simp
  have hcross : ((n' : ℂ) * h * ((Real.log l : ℝ) : ℂ)) = (n : ℂ) * h' * ((Real.log l' : ℝ) : ℂ) := by
    apply mul_right_cancel₀ hu
    calc (n' : ℂ) * h * ((Real.log l : ℝ) : ℂ) * (1 - s)
        = (n' : ℂ) * ((h : ℂ) * (((Real.log l : ℝ) : ℂ) * (1 - s))) := by ring
      _ = (n : ℂ) * ((h' : ℂ) * (((Real.log l' : ℝ) : ℂ) * (1 - s))) := by
          rw [hn, hn']; ring
      _ = (n : ℂ) * h' * ((Real.log l' : ℝ) : ℂ) * (1 - s) := by ring
  have hreal : (n' : ℝ) * h * Real.log l = (n : ℝ) * h' * Real.log l' := by
    exact_mod_cast hcross
  have habs : (n'.natAbs : ℝ) * h * Real.log l = (n.natAbs : ℝ) * h' * Real.log l' := by
    have := congrArg abs hreal
    simp only [abs_mul, Nat.abs_cast, abs_of_pos hL, abs_of_pos hL'] at this
    rw [Nat.cast_natAbs, Nat.cast_natAbs]
    push_cast
    exact this
  have hlog : Real.log ((l : ℝ) ^ (n'.natAbs * h)) = Real.log ((l' : ℝ) ^ (n.natAbs * h')) := by
    rw [Real.log_pow, Real.log_pow]
    push_cast
    exact habs
  have hpos : (0 : ℝ) < (l : ℝ) ^ (n'.natAbs * h) := by
    have : (0 : ℝ) < l := by exact_mod_cast hl.pos
    positivity
  have hpos' : (0 : ℝ) < (l' : ℝ) ^ (n.natAbs * h') := by
    have : (0 : ℝ) < l' := by exact_mod_cast hl'.pos
    positivity
  have heq := Real.log_injOn_pos (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr hpos') hlog
  have hnat : l ^ (n'.natAbs * h) = l' ^ (n.natAbs * h') := by exact_mod_cast heq
  have hexp0 : n'.natAbs * h ≠ 0 := Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hn0') hh
  have hdvd : l ∣ l' ^ (n.natAbs * h') := by
    rw [← hnat]; exact dvd_pow_self l hexp0
  exact hne ((Nat.prime_dvd_prime_iff_eq hl hl').mp (hl.dvd_of_dvd_pow hdvd))

/- English proof (translation)
Establish `hfa : AnalyticOnNhd ℂ f Set.univ` using `fun z _ => hf.analyticAt z`. Establish `hga : AnalyticOnNhd ℂ g Set.univ` using `fun z _ => hg.analyticAt z`. Establish `hopen : IsOpen {s : ℂ | 1 < s.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ)` using `hopen.mem_nhds (by simp)`. Use `hfa.eq_of_eventuallyEq hga (z₀ := 2) ?_` and prove the remaining obligations.

Use `filter_upwards [hmem] with s hs using hfg s hs`.
-/
lemma entire_eq_of_halfplane {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfg : ∀ s : ℂ, 1 < s.re → f s = g s) : f = g := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) := hopen.mem_nhds (by simp)
  refine hfa.eq_of_eventuallyEq hga (z₀ := 2) ?_
  filter_upwards [hmem] with s hs using hfg s hs

/- English proof (translation)
Distinguish the cases in `h : E s ≠ 0`. Establish `hev : ∀ᶠ t in 𝓝 s, E t ≠ 0` using `hE.continuous.continuousAt.eventually_ne h`. Use `((hW s).div (hE s) h).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hev] with t ht`. Simplify using `[ht]`.

Establish `h' : E' s ≠ 0` using `hs.resolve_left h`. Establish `hev : ∀ᶠ t in 𝓝 s, E' t ≠ 0` using `hE'.continuous.continuousAt.eventually_ne h'`. Use `((hW' s).div (hE' s) h').congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hev] with t ht`. Rewrite using `[Pi.div_apply]`.

Distinguish the cases in `h0 : E t ≠ 0`. Rewrite using `[if_pos h0, div_eq_div_iff h0 ht]`. Conclude with `hcross t`. Rewrite using `[if_neg h0]`.
-/
lemma glue_differentiableAt {E E' W W' : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hE' : Differentiable ℂ E') (hW : Differentiable ℂ W) (hW' : Differentiable ℂ W')
    (hcross : ∀ s, W s * E' s = W' s * E s) {s : ℂ} (hs : E s ≠ 0 ∨ E' s ≠ 0) :
    DifferentiableAt ℂ (fun t => if E t ≠ 0 then W t / E t else W' t / E' t) s := by
  by_cases h : E s ≠ 0
  · have hev : ∀ᶠ t in 𝓝 s, E t ≠ 0 := hE.continuous.continuousAt.eventually_ne h
    refine ((hW s).div (hE s) h).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    simp [ht]
  · have h' : E' s ≠ 0 := hs.resolve_left h
    have hev : ∀ᶠ t in 𝓝 s, E' t ≠ 0 := hE'.continuous.continuousAt.eventually_ne h'
    refine ((hW' s).div (hE' s) h').congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [Pi.div_apply]
    by_cases h0 : E t ≠ 0
    · rw [if_pos h0, div_eq_div_iff h0 ht]
      exact hcross t
    · rw [if_neg h0]

/- English proof (translation)
Simplify using `[mult]`.
-/
lemma mult_at_neg {l k : ℕ} : mult l (1 - (k : ℂ)) = ((l ^ k : ℕ) : ℂ) := by
  simp [mult]

/- English proof (translation)
Introduce `G _ D T T' l l' τ τ' hl hl' hne hT hT' hrel hrel'`. Establish `hh : orderOf τ ≠ 0` using `(orderOf_pos τ).ne'`. Establish `hh' : orderOf τ' ≠ 0` using `(orderOf_pos τ').ne'`. Establish `hED : ∀ c s, 1 < s.re → efac l (orderOf τ) s * D c s = wsum T l τ (orderOf τ) c s` using `fun c s hs => efac_mul_eq (fun c => hrel c s hs) c`. Establish `hED' : ∀ c s, 1 < s.re → efac l' (orderOf τ') s * D c s = wsum T' l' τ' (orderOf τ') c s` using `fun c s hs => efac_mul_eq (fun c => hrel' c s hs) c`.

Establish `hEd` using `efac_differentiable hl (orderOf τ)`. Establish `hEd'` using `efac_differentiable hl' (orderOf τ')`. Establish `hWd` using `fun c => wsum_differentiable hl hT τ (orderOf τ) c`. Establish `hWd'` using `fun c => wsum_differentiable hl' hT' τ' (orderOf τ') c`. Establish `hcross : ∀ c s, wsum T l τ (orderOf τ) c s * efac l' (orderOf τ') s = wsum T' l' τ' (orderOf τ') c s * efac l (orderOf τ) s`.

Introduce `c s`. Use `entire_eq_of_halfplane (f := fun s => wsum T l τ (orderOf τ) c s * efac l' (orderOf τ') s) (g := fun s => wsum T' l' τ' (orderOf τ') c s * efac l (orderOf τ) s) ((hWd c).mul hEd') ((hWd' c).mul hEd) (fun s hs => by show wsum T l τ (orderOf τ) c s * efac l' (orderOf τ') s = wsum T …` as an intermediate fact. Rewrite using `[← hED c s hs, ← hED' c s hs]`. Use the proof step `ring)`. Conclude with `congrFun this s`.

Use `⟨fun c t => if efac l (orderOf τ) t ≠ 0 then wsum T l τ (orderOf τ) c t / efac l (orderOf τ) t else wsum T' l' τ' (orderOf τ') c t / efac l' (orderOf τ') t, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `c s hs`. Establish `hs1 : s ≠ 1` using `hs`. Establish `hor : efac l (orderOf τ) s ≠ 0 ∨ efac l' (orderOf τ') s ≠ 0`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `no_common_zero hl hl' hne hh hh' hs1 hcon.1 hcon.2`. Conclude with `(glue_differentiableAt hEd hEd' (hWd c) (hWd' c) (hcross c) hor).differentiableWithinAt`. Introduce `c s hs`. Establish `h0` using `efac_ne_zero hl hh hs`.

Use `show (if efac l (orderOf τ) s ≠ 0 then _ else _) = _`. Rewrite using `[if_pos h0, ← hED c s hs, mul_div_cancel_left₀ _ h0]`. Introduce `k hk hq c choose q hq using hq`. Establish `hm : mult l (1 - (k : ℂ)) = ((l ^ k : ℕ) : ℂ)` using `mult_at_neg`. Establish `hnat : (l ^ k) ^ orderOf τ ≠ 1` using `ne_of_gt (Nat.one_lt_pow hh (Nat.one_lt_pow (by omega) hl.one_lt))`.

Establish `hE : efac l (orderOf τ) (1 - (k : ℂ)) = (((((l ^ k) ^ orderOf τ : ℕ) : ℚ) - 1 : ℚ) : ℂ)`. Simplify using `only [efac, hm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : efac l (orderOf τ) (1 - (k : ℂ)) ≠ 0`.

Rewrite using `[hE]`. Introduce `hz`. Establish `hz' : ((((l ^ k) ^ orderOf τ : ℕ) : ℚ) - 1 : ℚ) = 0` using `by exact_mod_cast hz`. Apply `hnat` to reduce the goal to its premises. Establish `: (((l ^ k) ^ orderOf τ : ℕ) : ℚ) = 1` using `by linarith`.

Conclude with `this` after adjusting the coercions. Establish `hW : wsum T l τ (orderOf τ) c (1 - (k : ℂ)) = ((∑ e ∈ Finset.range (orderOf τ), (((l ^ k : ℕ) : ℚ)) ^ e * q ((τ ^ e) c) : ℚ) : ℂ)`. Simplify using `only [wsum, hm, hq]`. Use `push_cast`. Both sides reduce to the same expression.

Use `⟨(∑ e ∈ Finset.range (orderOf τ), (((l ^ k : ℕ) : ℚ)) ^ e * q ((τ ^ e) c)) / ((((l ^ k) ^ orderOf τ : ℕ) : ℚ) - 1), ?_⟩` and prove the remaining obligations. Use `show (if efac l (orderOf τ) (1 - (k : ℂ)) ≠ 0 then _ else _) = _`. Rewrite using `[if_pos h0, hW, hE, Rat.cast_div]`.
-/
theorem continuation_of_two_relations :
    ∀ (G : Type) [Fintype G] (D T T' : G → ℂ → ℂ) (l l' : ℕ) (τ τ' : Equiv.Perm G),
    l.Prime → l'.Prime → l ≠ l' →
    (∀ c, Differentiable ℂ (T c)) → (∀ c, Differentiable ℂ (T' c)) →
    (∀ c s, 1 < s.re → (l : ℂ) ^ (1 - s) * D (τ c) s - D c s = T c s) →
    (∀ c s, 1 < s.re → (l' : ℂ) ^ (1 - s) * D (τ' c) s - D c s = T' c s) →
    ∃ Z : G → ℂ → ℂ, (∀ c, DifferentiableOn ℂ (Z c) {1}ᶜ) ∧ (∀ c s, 1 < s.re → Z c s = D c s) ∧
      ∀ k : ℕ, 1 ≤ k → (∀ c, ∃ q : ℚ, T c (1 - (k : ℂ)) = (q : ℂ)) →
        ∀ c, ∃ q : ℚ, Z c (1 - (k : ℂ)) = (q : ℂ) := by
  intro G _ D T T' l l' τ τ' hl hl' hne hT hT' hrel hrel'
  have hh : orderOf τ ≠ 0 := (orderOf_pos τ).ne'
  have hh' : orderOf τ' ≠ 0 := (orderOf_pos τ').ne'
  have hED : ∀ c s, 1 < s.re →
      efac l (orderOf τ) s * D c s = wsum T l τ (orderOf τ) c s :=
    fun c s hs => efac_mul_eq (fun c => hrel c s hs) c
  have hED' : ∀ c s, 1 < s.re →
      efac l' (orderOf τ') s * D c s = wsum T' l' τ' (orderOf τ') c s :=
    fun c s hs => efac_mul_eq (fun c => hrel' c s hs) c
  have hEd := efac_differentiable hl (orderOf τ)
  have hEd' := efac_differentiable hl' (orderOf τ')
  have hWd := fun c => wsum_differentiable hl hT τ (orderOf τ) c
  have hWd' := fun c => wsum_differentiable hl' hT' τ' (orderOf τ') c
  have hcross : ∀ c s, wsum T l τ (orderOf τ) c s * efac l' (orderOf τ') s
      = wsum T' l' τ' (orderOf τ') c s * efac l (orderOf τ) s := by
    intro c s
    have := entire_eq_of_halfplane
      (f := fun s => wsum T l τ (orderOf τ) c s * efac l' (orderOf τ') s)
      (g := fun s => wsum T' l' τ' (orderOf τ') c s * efac l (orderOf τ) s)
      ((hWd c).mul hEd') ((hWd' c).mul hEd)
      (fun s hs => by
        show wsum T l τ (orderOf τ) c s * efac l' (orderOf τ') s
          = wsum T' l' τ' (orderOf τ') c s * efac l (orderOf τ) s
        rw [← hED c s hs, ← hED' c s hs]; ring)
    exact congrFun this s
  refine ⟨fun c t => if efac l (orderOf τ) t ≠ 0 then
      wsum T l τ (orderOf τ) c t / efac l (orderOf τ) t
    else wsum T' l' τ' (orderOf τ') c t / efac l' (orderOf τ') t, ?_, ?_, ?_⟩
  · intro c s hs
    have hs1 : s ≠ 1 := hs
    have hor : efac l (orderOf τ) s ≠ 0 ∨ efac l' (orderOf τ') s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact no_common_zero hl hl' hne hh hh' hs1 hcon.1 hcon.2
    exact (glue_differentiableAt hEd hEd' (hWd c) (hWd' c) (hcross c) hor).differentiableWithinAt
  · intro c s hs
    have h0 := efac_ne_zero hl hh hs
    show (if efac l (orderOf τ) s ≠ 0 then _ else _) = _
    rw [if_pos h0, ← hED c s hs, mul_div_cancel_left₀ _ h0]
  · intro k hk hq c
    choose q hq using hq
    have hm : mult l (1 - (k : ℂ)) = ((l ^ k : ℕ) : ℂ) := mult_at_neg
    have hnat : (l ^ k) ^ orderOf τ ≠ 1 :=
      ne_of_gt (Nat.one_lt_pow hh (Nat.one_lt_pow (by omega) hl.one_lt))
    have hE : efac l (orderOf τ) (1 - (k : ℂ)) = (((((l ^ k) ^ orderOf τ : ℕ) : ℚ) - 1 : ℚ) : ℂ) := by
      simp only [efac, hm]
      push_cast
      ring
    have h0 : efac l (orderOf τ) (1 - (k : ℂ)) ≠ 0 := by
      rw [hE]
      intro hz
      have hz' : ((((l ^ k) ^ orderOf τ : ℕ) : ℚ) - 1 : ℚ) = 0 := by exact_mod_cast hz
      apply hnat
      have : (((l ^ k) ^ orderOf τ : ℕ) : ℚ) = 1 := by linarith
      exact_mod_cast this
    have hW : wsum T l τ (orderOf τ) c (1 - (k : ℂ))
        = ((∑ e ∈ Finset.range (orderOf τ), (((l ^ k : ℕ) : ℚ)) ^ e * q ((τ ^ e) c) : ℚ) : ℂ) := by
      simp only [wsum, hm, hq]
      push_cast
      rfl
    refine ⟨(∑ e ∈ Finset.range (orderOf τ), (((l ^ k : ℕ) : ℚ)) ^ e * q ((τ ^ e) c)) /
      ((((l ^ k) ^ orderOf τ : ℕ) : ℚ) - 1), ?_⟩
    show (if efac l (orderOf τ) (1 - (k : ℂ)) ≠ 0 then _ else _) = _
    rw [if_pos h0, hW, hE, Rat.cast_div]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.TwoRelations
