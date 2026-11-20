import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.PairGOps

noncomputable section

open Polynomial

namespace UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Inf

/- English proof (translation)
Establish `ha : AnalyticOnNhd ℂ f Set.univ` using `fun x _ => hf.analyticAt x`. Establish `h0 : f =ᶠ[nhds z] 0` using `Filter.eventually_of_mem (hU.mem_nhds hz) h`. Use function extensionality and compare the values at `s`. Conclude with `ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) h0 (Set.mem_univ s)`.
-/
private lemma zero_of_open {f : ℂ → ℂ} (hf : Differentiable ℂ f) {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    (h : ∀ s ∈ U, f s = 0) : f = 0 := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun x _ => hf.analyticAt x
  have h0 : f =ᶠ[nhds z] 0 := Filter.eventually_of_mem (hU.mem_nhds hz) h
  funext s
  exact ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) h0 (Set.mem_univ s)

/- English proof (translation)
The claim follows from `zero_of_open hf (U := {s : ℂ | s.re < c}) (isOpen_lt Complex.continuous_re continuous_const) (z := ((c - 1 : ℝ) : ℂ)) (by simp) h`.
-/
private lemma zero_of_left {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℝ) (h : ∀ s : ℂ, s.re < c → f s = 0) : f = 0 :=
  zero_of_open hf (U := {s : ℂ | s.re < c}) (isOpen_lt Complex.continuous_re continuous_const)
    (z := ((c - 1 : ℝ) : ℂ)) (by simp) h

/- English proof (translation)
The claim follows from `zero_of_open hf (U := {s : ℂ | c < s.re}) (isOpen_lt continuous_const Complex.continuous_re) (z := ((c + 1 : ℝ) : ℂ)) (by simp) h`.
-/
private lemma zero_of_right {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℝ) (h : ∀ s : ℂ, c < s.re → f s = 0) : f = 0 :=
  zero_of_open hf (U := {s : ℂ | c < s.re}) (isOpen_lt continuous_const Complex.continuous_re)
    (z := ((c + 1 : ℝ) : ℂ)) (by simp) h

/- English proof (translation)
Introduce `h`. Take `⟨z, hz⟩` from `Function.ne_iff.mp f0`. Use `g0 (zero_of_open hg (U := {s | f s ≠ 0}) (isOpen_ne_fun hf.continuous continuous_const) hz fun s hs => ?_)` and prove the remaining obligations. Conclude with `(mul_eq_zero.mp (congrFun h s)).resolve_left hs`.
-/
private lemma mul_ne {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (f0 : f ≠ 0) (g0 : g ≠ 0) :
    (fun s => f s * g s) ≠ 0 := by
  intro h
  obtain ⟨z, hz⟩ := Function.ne_iff.mp f0
  refine g0 (zero_of_open hg (U := {s | f s ≠ 0}) (isOpen_ne_fun hf.continuous continuous_const) hz fun s hs => ?_)
  exact (mul_eq_zero.mp (congrFun h s)).resolve_left hs

/- English proof (translation)
Introduce `h`. Apply `f0` to reduce the goal to its premises. Use function extensionality and compare the values at `s`. Simplify using `using congrFun h (s - 1)`.
-/
private lemma shift_ne {f : ℂ → ℂ} (f0 : f ≠ 0) : (fun s => f (s + 1)) ≠ 0 := by
  intro h
  apply f0
  funext s
  simpa using congrFun h (s - 1)

/- English proof (translation)
Establish `h0 : (q : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (by linarith)`. Rewrite using `[Complex.cpow_def_of_ne_zero h0, ← Complex.ofReal_log (by linarith)]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma cpow_eq {q : ℝ} (hq : 1 < q) (s : ℂ) :
    (q : ℂ) ^ (-s) = Complex.exp (((-Real.log q : ℝ) : ℂ) * (s + 0)) := by
  have h0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  rw [Complex.cpow_def_of_ne_zero h0, ← Complex.ofReal_log (by linarith)]
  congr 1
  push_cast
  ring

/- English proof (translation)
Establish `hl : ((Real.log q : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'`. Use `Polynomial.eq_zero_of_infinite_isRoot Q ?_` and prove the remaining obligations. Use `(Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun x hx => ?_` and prove the remaining obligations. Establish `hx' : x ≠ 0` using `hx`. Use `h (-(Complex.log x / (Real.log q : ℝ)))` as an intermediate fact.

Rewrite `this` using `[cpow_eq hq]`. Establish `e : ((-Real.log q : ℝ) : ℂ) * (-(Complex.log x / (Real.log q : ℝ)) + 0) = Complex.log x`. Rewrite using `[Complex.ofReal_neg]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite `this` using `[e, Complex.exp_log hx']`. Conclude with `this`.
-/
private lemma poly_zero {q : ℝ} (hq : 1 < q) (Q : ℂ[X]) (h : ∀ s : ℂ, Q.eval ((q : ℂ) ^ (-s)) = 0) : Q = 0 := by
  have hl : ((Real.log q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  refine Polynomial.eq_zero_of_infinite_isRoot Q ?_
  refine (Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun x hx => ?_
  have hx' : x ≠ 0 := hx
  have := h (-(Complex.log x / (Real.log q : ℝ)))
  rw [cpow_eq hq] at this
  have e : ((-Real.log q : ℝ) : ℂ) * (-(Complex.log x / (Real.log q : ℝ)) + 0) = Complex.log x := by
    rw [Complex.ofReal_neg]
    field_simp
    ring
  rw [e, Complex.exp_log hx'] at this
  exact this

/- English proof (translation)
Introduce `h0` and use `h (Polynomial.funext fun s => by simpa using congrFun h0 s)`.
-/
private lemma poly_fun_ne {β : ℂ[X]} (h : β ≠ 0) : (fun s : ℂ => β.eval s) ≠ 0 := fun h0 =>
  h (Polynomial.funext fun s => by simpa using congrFun h0 s)

/- English proof (translation)
Establish `h0 : (q : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (by linarith)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[fac, sub_eq_add_neg, Complex.cpow_add _ _ h0, Complex.cpow_one]`. Rewrite using `[fac, mul_add, mul_one, Complex.exp_add, show (1 : ℂ) - (s + 1) = -s by ring, show -(s + 1) = -1 + -s by ring, Complex.cpow_add _ _ h0, Complex.cpow_neg_one]`.
-/
private lemma fac_eq {q : ℝ} (hq : 1 < q) (c : ℂ) (t : ℝ) (P : ℂ[X]) (s : ℂ) :
    fac c t q P s = c * Complex.exp (t * s) * P.eval ((q : ℂ) ^ (-s)) / P.eval ((q : ℂ) * (q : ℂ) ^ (-s)) ∧
    fac c t q P (s + 1) = c * (Complex.exp (t * s) * Complex.exp t) * P.eval ((q : ℂ)⁻¹ * (q : ℂ) ^ (-s)) /
      P.eval ((q : ℂ) ^ (-s)) := by
  have h0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  constructor
  · rw [fac, sub_eq_add_neg, Complex.cpow_add _ _ h0, Complex.cpow_one]
  · rw [fac, mul_add, mul_one, Complex.exp_add, show (1 : ℂ) - (s + 1) = -s by ring,
      show -(s + 1) = -1 + -s by ring, Complex.cpow_add _ _ h0, Complex.cpow_neg_one]

/- English proof (translation)
Introduce and unpack `⟨hd, hmul, hc, -, hpe⟩ hind hsec L L' β β' q P P' hq β0 β'0 P1 P'1 ⟨Z₀, W₀, A₀, B₀, k₀, l₀, m₀, t₀, c₀, dZ₀, dW₀, Z₀0, k₀0, l₀0, hr₀, hl₀⟩ ⟨Z₁, W₁, A₁, B₁, k₁, l₁, m₁, t₁, c₁, dZ₁, dW₁, Z₁0, k₁0, l₁0, hr₁, hl₁⟩`. Establish `dsh : ∀ {f : ℂ → ℂ}, Differentiable ℂ f → Differentiable ℂ fun s => f (s + 1)` using `fun hf => hf.comp (differentiable_id.add_const 1)`. Establish `eP : ∀ Q : ℂ[X], IsExp fun s : ℂ => Q.eval ((q : ℂ) ^ (-s))` using `fun Q => by`. Simplify using `only [cpow_eq hq]`. Conclude with `hpe Q _ 0`.

Establish `nP : ∀ Q : ℂ[X], Q.eval 0 ≠ 0 → (fun s : ℂ => Q.eval ((q : ℂ) ^ (-s))) ≠ 0` using `fun Q hQ h => hQ (by rw [poly_zero hq Q fun s => congrFun h s]; simp)`. Establish `hR : (fun s => k₁ * β'.eval s * W₀ s * Z₁ s - k₀ * β.eval s * W₁ s * Z₀ s) = 0`. Use `zero_of_right ?_ (max c₀ c₁) fun s hs => ?_` and prove the remaining obligations. Use `β.differentiable` as an intermediate fact. Use `β'.differentiable` as an intermediate fact.

Use `fun_prop`. Take `⟨a1, a2⟩` from `hr₀ s (lt_of_le_of_lt (le_max_left _ _) hs)`. Take `⟨b1, b2⟩` from `hr₁ s (lt_of_le_of_lt (le_max_right _ _) hs)`. Simplify using `only [a1, a2, b1, b2]`. Expand and normalize the polynomial expressions, which then agree.

Use `set R : ℂ[X] := P.comp (C (q : ℂ)⁻¹ * X) * P.comp (C (q : ℂ) * X) * P' ^ 2 with hRdef`. Use `set R' : ℂ[X] := P'.comp (C (q : ℂ)⁻¹ * X) * P'.comp (C (q : ℂ) * X) * P ^ 2 with hR'def`. Use `set E : ℂ[X] := P * P.comp (C (q : ℂ) * X) * P' * P'.comp (C (q : ℂ) * X) with hEdef`. Use `set a : ℂ := k₁ * l₀ * Complex.exp t₀ with ha`. Use `set b : ℂ := k₀ * l₁ * Complex.exp t₁ with hb`.

Establish `a0 : a ≠ 0` using `mul_ne_zero (mul_ne_zero k₁0 l₀0) (Complex.exp_ne_zero _)`. Use `set U : ℂ → ℂ := fun s => (C a * R).eval ((q : ℂ) ^ (-s)) with hU`. Use `set V : ℂ → ℂ := fun s => (C b * R').eval ((q : ℂ) ^ (-s)) with hV`. Establish `eU : IsExp U` using `eP _`. Establish `eV : IsExp V` using `eP _`.

Establish `U0 : U ≠ 0` using `nP _ (by simpa [hRdef, eval_comp, P1, P'1] using a0)`. Establish `E0` using `nP E (by simp [hEdef, eval_comp, P1, P'1])`. Establish `dE` using `hd _ (eP E)`. Use `set c : ℝ := -(max c₀ c₁) - 1 with hcdef`. Establish `l0 : ∀ s : ℂ, s.re < c → s.re < -c₀ ∧ s.re < -c₁ ∧ (s + 1).re < -c₁` using `fun s hs => by`.

Use `le_max_left c₀ c₁` as an intermediate fact. Use `le_max_right c₀ c₁` as an intermediate fact. Simplify using `only [Complex.add_re, Complex.one_re]`. Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;> linarith`. Establish `dF : Differentiable ℂ fun s => β'.eval s * U s - β.eval s * V s` using `(β'.differentiable.mul (hd _ eU)).sub (β.differentiable.mul (hd _ eV))`.

Establish `dG : Differentiable ℂ fun s => Z₀ s * Z₁ s * Z₁ (s + 1)` using `(dZ₀.mul dZ₁).mul (dsh dZ₁)`. Establish `G0 : (fun s => Z₀ s * Z₁ s * Z₁ (s + 1)) ≠ 0` using `mul_ne (dZ₀.mul dZ₁) (dsh dZ₁) (mul_ne dZ₀ dZ₁ Z₀0 Z₁0) (shift_ne Z₁0)`. Establish `hF : (fun s => β'.eval s * U s - β.eval s * V s) = 0`. Assume the negation of the conclusion as `F0`. Use `mul_ne (dG.mul dE) dF (mul_ne dG dE G0 E0) F0 (zero_of_left ((dG.mul dE).mul dF) c fun s hs => ?_)` and prove the remaining obligations.

Take `⟨s1, s3, s4⟩` from `l0 s hs`. Take `⟨a3, a4⟩` from `hl₀ s s1`. Take `⟨b3, b4⟩` from `hl₁ s s3`. Take `⟨e3, -⟩` from `hl₁ (s + 1) s4`. Establish `h` using `congrFun hR s`.

Assume the negation of the conclusion as `hne`. Simplify using `only [Pi.mul_apply, mul_eq_zero, not_or] at hne`. Take `⟨⟨⟨⟨n0, n1⟩, n2⟩, n3⟩, n4⟩` from `hne`. Apply `n4` to reduce the goal to its premises. Establish `y1 : L' (s + 1) ≠ 0` using `fun h0 => n2 (by rw [e3, h0]; simp)`.

Establish `y2 : L' s ≠ 0` using `fun h0 => n0 (by rw [a3, h0]; simp)`. Establish `y3 : B₀ s ≠ 0` using `fun h0 => n0 (by rw [a3, h0]; simp)`. Establish `y4 : B₁ s ≠ 0` using `fun h0 => n1 (by rw [b3, h0]; simp)`. Establish `y5 : m₀ ≠ 0` using `fun h0 => n0 (by rw [a3, h0]; simp [fac])`. Establish `y6 : m₁ ≠ 0` using `fun h0 => n1 (by rw [b3, h0]; simp [fac])`.

Establish `y7` using `Complex.exp_ne_zero (t₀ * s)`. Establish `y8` using `Complex.exp_ne_zero (t₁ * s)`. Simplify using `only [hEdef, eval_mul, eval_comp, eval_C, eval_X, mul_eq_zero, not_or] at n3`. Take `⟨⟨⟨z1, z2⟩, z3⟩, z4⟩` from `n3`. Simplify using `only [a3, a4, b3, b4, Pi.zero_apply, (fac_eq hq _ _ _ s).1, (fac_eq hq _ _ _ s).2] at h`.

Simplify using `only [hU, hV, hRdef, hR'def, ha, hb, eval_mul, eval_comp, eval_C, eval_X, eval_pow]`. Generalize the expression as in `(q : ℂ) ^ (-s) = x at *`. Generalize the expression as in `P.eval x = p1 at *`. Generalize the expression as in `P'.eval x = p2 at *`. Generalize the expression as in `P.eval ((q : ℂ) * x) = p3 at *`.

Generalize the expression as in `P'.eval ((q : ℂ) * x) = p4 at *`. Generalize the expression as in `P.eval ((q : ℂ)⁻¹ * x) = p5 at *`. Generalize the expression as in `P'.eval ((q : ℂ)⁻¹ * x) = p6 at *`. Establish `y : L' (s + 1) * L' s * B₀ s * B₁ s * m₀ * m₁ * Complex.exp (t₀ * s) * Complex.exp (t₁ * s) ≠ 0`. Simplify using `[y1, y2, y3, y4, y5, y6]`.

Use `mul_left_cancel₀ y ?_` and prove the remaining obligations. Establish `h2` using `congrArg (· * (p1 * p2 * p3 * p4)) h`. Simplify using `only [zero_mul] at h2`. Rewrite using `[mul_zero, ← h2]`. Clear the denominators using the available nonvanishing facts.

Take `⟨u, v, u0, huv⟩` from `hind β' β U V eU eV U0 fun s => sub_eq_zero.mp (congrFun hF s)`. Establish `v0 : v ≠ 0`. Introduce and unpack `rfl`. Conclude with `mul_ne_zero (C_ne_zero.mpr u0) β'0 (by simpa using huv)`. Establish `hK : (fun s : ℂ => (C v * (C a * R) - C u * (C b * R')).eval ((q : ℂ) ^ (-s))) = 0`.

Assume the negation of the conclusion as `K0`. Use `mul_ne β.differentiable (hd _ (eP _)) (poly_fun_ne β0) K0 (funext fun s => ?_)` and prove the remaining obligations. Establish `h1` using `congrFun hF s`. Establish `h2` using `congrArg (Polynomial.eval s) huv`. Simplify using `only [hU, hV, eval_mul, eval_C, eval_sub, Pi.zero_apply] at h1 h2 ⊢`.

Take the linear combination `u * h1 - (a * R.eval ((q : ℂ) ^ (-s))) * h2`. Establish `hK'` using `poly_zero hq _ fun s => congrFun hK s`. Use `hsec q hq P P' (u * b / (v * a)) P1 P'1 ?_` and prove the remaining obligations. Establish `hva : (C (v * a) : ℂ[X]) ≠ 0` using `C_ne_zero.mpr (mul_ne_zero v0 a0)`. Express the relevant statement in the definitionally equal form `R = C _ * R'`.

Use `clear_value R R' U V a b`. Use `mul_left_cancel₀ hva ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc (C (v * a)), ← C_mul, mul_div_cancel₀ _ (mul_ne_zero v0 a0), C_mul (a := v), C_mul (a := u)]`. Take the linear combination `hK'`.
-/
theorem crossGOf : CrossGOf := by
  rintro ⟨hd, hmul, hc, -, hpe⟩ hind hsec L L' β β' q P P' hq β0 β'0 P1 P'1
    ⟨Z₀, W₀, A₀, B₀, k₀, l₀, m₀, t₀, c₀, dZ₀, dW₀, Z₀0, k₀0, l₀0, hr₀, hl₀⟩
    ⟨Z₁, W₁, A₁, B₁, k₁, l₁, m₁, t₁, c₁, dZ₁, dW₁, Z₁0, k₁0, l₁0, hr₁, hl₁⟩
  have dsh : ∀ {f : ℂ → ℂ}, Differentiable ℂ f → Differentiable ℂ fun s => f (s + 1) := fun hf =>
    hf.comp (differentiable_id.add_const 1)
  have eP : ∀ Q : ℂ[X], IsExp fun s : ℂ => Q.eval ((q : ℂ) ^ (-s)) := fun Q => by
    simp only [cpow_eq hq]
    exact hpe Q _ 0
  have nP : ∀ Q : ℂ[X], Q.eval 0 ≠ 0 → (fun s : ℂ => Q.eval ((q : ℂ) ^ (-s))) ≠ 0 := fun Q hQ h =>
    hQ (by rw [poly_zero hq Q fun s => congrFun h s]; simp)
  have hR : (fun s => k₁ * β'.eval s * W₀ s * Z₁ s - k₀ * β.eval s * W₁ s * Z₀ s) = 0 := by
    refine zero_of_right ?_ (max c₀ c₁) fun s hs => ?_
    · have := β.differentiable
      have := β'.differentiable
      fun_prop
    · obtain ⟨a1, a2⟩ := hr₀ s (lt_of_le_of_lt (le_max_left _ _) hs)
      obtain ⟨b1, b2⟩ := hr₁ s (lt_of_le_of_lt (le_max_right _ _) hs)
      simp only [a1, a2, b1, b2]
      ring
  set R : ℂ[X] := P.comp (C (q : ℂ)⁻¹ * X) * P.comp (C (q : ℂ) * X) * P' ^ 2 with hRdef
  set R' : ℂ[X] := P'.comp (C (q : ℂ)⁻¹ * X) * P'.comp (C (q : ℂ) * X) * P ^ 2 with hR'def
  set E : ℂ[X] := P * P.comp (C (q : ℂ) * X) * P' * P'.comp (C (q : ℂ) * X) with hEdef
  set a : ℂ := k₁ * l₀ * Complex.exp t₀ with ha
  set b : ℂ := k₀ * l₁ * Complex.exp t₁ with hb
  have a0 : a ≠ 0 := mul_ne_zero (mul_ne_zero k₁0 l₀0) (Complex.exp_ne_zero _)
  set U : ℂ → ℂ := fun s => (C a * R).eval ((q : ℂ) ^ (-s)) with hU
  set V : ℂ → ℂ := fun s => (C b * R').eval ((q : ℂ) ^ (-s)) with hV
  have eU : IsExp U := eP _
  have eV : IsExp V := eP _
  have U0 : U ≠ 0 := nP _ (by simpa [hRdef, eval_comp, P1, P'1] using a0)
  have E0 := nP E (by simp [hEdef, eval_comp, P1, P'1])
  have dE := hd _ (eP E)
  set c : ℝ := -(max c₀ c₁) - 1 with hcdef
  have l0 : ∀ s : ℂ, s.re < c → s.re < -c₀ ∧ s.re < -c₁ ∧ (s + 1).re < -c₁ := fun s hs => by
    have := le_max_left c₀ c₁
    have := le_max_right c₀ c₁
    simp only [Complex.add_re, Complex.one_re]
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  have dF : Differentiable ℂ fun s => β'.eval s * U s - β.eval s * V s :=
    (β'.differentiable.mul (hd _ eU)).sub (β.differentiable.mul (hd _ eV))
  have dG : Differentiable ℂ fun s => Z₀ s * Z₁ s * Z₁ (s + 1) := (dZ₀.mul dZ₁).mul (dsh dZ₁)
  have G0 : (fun s => Z₀ s * Z₁ s * Z₁ (s + 1)) ≠ 0 :=
    mul_ne (dZ₀.mul dZ₁) (dsh dZ₁) (mul_ne dZ₀ dZ₁ Z₀0 Z₁0) (shift_ne Z₁0)
  have hF : (fun s => β'.eval s * U s - β.eval s * V s) = 0 := by
    by_contra F0
    refine mul_ne (dG.mul dE) dF (mul_ne dG dE G0 E0) F0 (zero_of_left ((dG.mul dE).mul dF) c fun s hs => ?_)
    obtain ⟨s1, s3, s4⟩ := l0 s hs
    obtain ⟨a3, a4⟩ := hl₀ s s1
    obtain ⟨b3, b4⟩ := hl₁ s s3
    obtain ⟨e3, -⟩ := hl₁ (s + 1) s4
    have h := congrFun hR s
    by_contra hne
    simp only [Pi.mul_apply, mul_eq_zero, not_or] at hne
    obtain ⟨⟨⟨⟨n0, n1⟩, n2⟩, n3⟩, n4⟩ := hne
    apply n4
    have y1 : L' (s + 1) ≠ 0 := fun h0 => n2 (by rw [e3, h0]; simp)
    have y2 : L' s ≠ 0 := fun h0 => n0 (by rw [a3, h0]; simp)
    have y3 : B₀ s ≠ 0 := fun h0 => n0 (by rw [a3, h0]; simp)
    have y4 : B₁ s ≠ 0 := fun h0 => n1 (by rw [b3, h0]; simp)
    have y5 : m₀ ≠ 0 := fun h0 => n0 (by rw [a3, h0]; simp [fac])
    have y6 : m₁ ≠ 0 := fun h0 => n1 (by rw [b3, h0]; simp [fac])
    have y7 := Complex.exp_ne_zero (t₀ * s)
    have y8 := Complex.exp_ne_zero (t₁ * s)
    simp only [hEdef, eval_mul, eval_comp, eval_C, eval_X, mul_eq_zero, not_or] at n3
    obtain ⟨⟨⟨z1, z2⟩, z3⟩, z4⟩ := n3
    simp only [a3, a4, b3, b4, Pi.zero_apply, (fac_eq hq _ _ _ s).1, (fac_eq hq _ _ _ s).2] at h
    simp only [hU, hV, hRdef, hR'def, ha, hb, eval_mul, eval_comp, eval_C, eval_X, eval_pow]
    generalize (q : ℂ) ^ (-s) = x at *
    generalize P.eval x = p1 at *
    generalize P'.eval x = p2 at *
    generalize P.eval ((q : ℂ) * x) = p3 at *
    generalize P'.eval ((q : ℂ) * x) = p4 at *
    generalize P.eval ((q : ℂ)⁻¹ * x) = p5 at *
    generalize P'.eval ((q : ℂ)⁻¹ * x) = p6 at *
    have y : L' (s + 1) * L' s * B₀ s * B₁ s * m₀ * m₁ * Complex.exp (t₀ * s) * Complex.exp (t₁ * s) ≠ 0 := by
      simp [y1, y2, y3, y4, y5, y6]
    refine mul_left_cancel₀ y ?_
    have h2 := congrArg (· * (p1 * p2 * p3 * p4)) h
    simp only [zero_mul] at h2
    rw [mul_zero, ← h2]
    field_simp
  obtain ⟨u, v, u0, huv⟩ := hind β' β U V eU eV U0 fun s => sub_eq_zero.mp (congrFun hF s)
  have v0 : v ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (C_ne_zero.mpr u0) β'0 (by simpa using huv)
  have hK : (fun s : ℂ => (C v * (C a * R) - C u * (C b * R')).eval ((q : ℂ) ^ (-s))) = 0 := by
    by_contra K0
    refine mul_ne β.differentiable (hd _ (eP _)) (poly_fun_ne β0) K0 (funext fun s => ?_)
    have h1 := congrFun hF s
    have h2 := congrArg (Polynomial.eval s) huv
    simp only [hU, hV, eval_mul, eval_C, eval_sub, Pi.zero_apply] at h1 h2 ⊢
    linear_combination u * h1 - (a * R.eval ((q : ℂ) ^ (-s))) * h2
  have hK' := poly_zero hq _ fun s => congrFun hK s
  refine hsec q hq P P' (u * b / (v * a)) P1 P'1 ?_
  have hva : (C (v * a) : ℂ[X]) ≠ 0 := C_ne_zero.mpr (mul_ne_zero v0 a0)
  change R = C _ * R'
  clear_value R R' U V a b
  refine mul_left_cancel₀ hva ?_
  rw [← mul_assoc (C (v * a)), ← C_mul, mul_div_cancel₀ _ (mul_ne_zero v0 a0), C_mul (a := v), C_mul (a := u)]
  linear_combination hK'

end UpperTheory.V.Z.Gam
