import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.HomotheticLatticeIntegralS2
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveJetsUnitBall
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)
open Formalism.L2.Th1.A (shortW logSer expSer wpReg xS xPlus)
open Formalism.L2.Th1.C (HasSecondLogDeriv wpShift IsEndoZ IsEndoCurve wTr)

namespace CurveNormEndomorphisms

section Alg

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

/- English proof (translation)
Use extensionality with `n`. Simplify using `[PowerSeries.coeff_derivative]`.
-/
theorem map_derivative (f : PowerSeries K) :
    PowerSeries.map φ (PowerSeries.derivative K f) =
      PowerSeries.derivative K' (PowerSeries.map φ f) := by
  ext n
  simp [PowerSeries.coeff_derivative]

/- English proof (translation)
Use extensionality with `n`. Simplify using `[PowerSeries.coeff_rescale]`.
-/
theorem map_rescale (a : K) (f : PowerSeries K) :
    PowerSeries.map φ (PowerSeries.rescale a f) =
      PowerSeries.rescale (φ a) (PowerSeries.map φ f) := by
  ext n
  simp [PowerSeries.coeff_rescale]

/- English proof (translation)
Unfold `wpShift`. Simplify using the standard rewrite rules.
-/
theorem map_wpShift (e : PowerSeries K) (c : K) :
    PowerSeries.map φ (wpShift e c) = wpShift (PowerSeries.map φ e) (φ c) := by
  unfold wpShift
  simp

/- English proof (translation)
Unfold `HasSecondLogDeriv at h ⊢`. Use `congrArg (PowerSeries.map φ) h` as an intermediate fact. Simplify `this` using `[map_derivative]`.
-/
theorem second_log_derivative_map {f g : PowerSeries K} (h : HasSecondLogDeriv f g) :
    HasSecondLogDeriv (PowerSeries.map φ f) (PowerSeries.map φ g) := by
  unfold HasSecondLogDeriv at h ⊢
  have := congrArg (PowerSeries.map φ) h
  simpa [map_derivative] using this

/- English proof (translation)
Unfold `HasSecondLogDeriv at h h'`. Establish `hf0 : f ^ 2 ≠ 0`. Apply `pow_ne_zero` to reduce the goal to its premises. Introduce `h0`. Rewrite `hf` using `[h0, map_zero]`.

Conclude with `zero_ne_one hf`. Conclude with `mul_right_cancel₀ hf0 (h.symm.trans h')`.
-/
theorem second_log_derivative_unique {f g g' : PowerSeries K} (hf : PowerSeries.constantCoeff f = 1)
    (h : HasSecondLogDeriv f g) (h' : HasSecondLogDeriv f g') : g = g' := by
  unfold HasSecondLogDeriv at h h'
  have hf0 : f ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro h0
    rw [h0, map_zero] at hf
    exact zero_ne_one hf
  exact mul_right_cancel₀ hf0 (h.symm.trans h')

/- English proof (translation)
Unfold `wpShift`. Simplify using the standard rewrite rules.
-/
theorem cc_wpShift (e : PowerSeries K) (c : K) :
    PowerSeries.constantCoeff (wpShift e c) = 1 := by
  unfold wpShift
  simp

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨h1, fun P => ?_, ?_⟩` and prove the remaining obligations. Use `second_log_derivative_map φ (h2 P)` as an intermediate fact. Simplify using `only [map_sub, map_mul, map_ofNat, map_wpShift] at this`. Conclude with `this`.

Use `congrArg (PowerSeries.map φ) h3` as an intermediate fact. Simplify `this` using `[map_rescale]`.
-/
theorem isEndoZ_map {e : PowerSeries K} {ι : Type} [Fintype ι] {neg : ι → ι} {c : ι → K}
    {w : ι → PowerSeries K} {al : K} (h : IsEndoZ e neg c w al) :
    IsEndoZ (PowerSeries.map φ e) neg (fun P => φ (c P)) (fun P => PowerSeries.map φ (w P))
      (φ al) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun P => ?_, ?_⟩
  · have := second_log_derivative_map φ (h2 P)
    simp only [map_sub, map_mul, map_ofNat, map_wpShift] at this
    exact this
  · have := congrArg (PowerSeries.map φ) h3
    simpa [map_rescale] using this

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨hEq, h1, hneg, ?_⟩` and prove the remaining obligations. Establish `key : ∀ P, PowerSeries.map φ (wTr W (xP P) (yP P)) + PowerSeries.map φ (wTr W (xP (neg P)) (yP (neg P))) = wF P + wF (neg P)`. Introduce `P`. Establish `hc` using `second_log_derivative_map φ (Formalism.L2.Th1.C.curve_second_log_derivative K W (xP P) (yP P) (hEq P))`.

Rewrite `hc` using `[map_wpShift, ← (hneg P).2]`. Establish `hx : wTr W (xP P) (yP (neg P)) = wTr W (xP (neg P)) (yP (neg P))`. Rewrite using `[(hneg P).1]`. Rewrite `hc` using `[hx]`. Establish `hu` using `second_log_derivative_unique (cc_wpShift _ _) hc (h2 P)`.

Simplify using `only [map_sub, map_mul, map_ofNat] at hu`. Take the linear combination `-hu`. Establish `hinv : Function.Involutive neg` using `h1`. Establish `hs1 : ∑ P, PowerSeries.map φ (wTr W (xP (neg P)) (yP (neg P))) = ∑ P, PowerSeries.map φ (wTr W (xP P) (yP P))` using `Equiv.sum_comp hinv.toPerm (fun P => PowerSeries.map φ (wTr W (xP P) (yP P)))`. Establish `hs2 : ∑ P, wF (neg P) = ∑ P, wF P` using `Equiv.sum_comp hinv.toPerm wF`.

Establish `hsum : ∑ P, PowerSeries.map φ (wTr W (xP P) (yP P)) = ∑ P, wF P`. Establish `h4` using `Finset.sum_congr (rfl : (Finset.univ : Finset ι) = Finset.univ) (fun P _ => key P)`. Rewrite `h4` using `[Finset.sum_add_distrib, Finset.sum_add_distrib, hs1, hs2]`. Establish `h2' : (2 : PowerSeries K') ≠ 0`. Introduce `h0`.

Establish `h5` using `congrArg PowerSeries.constantCoeff h0`. Rewrite `h5` using `[map_ofNat, map_zero]`. Conclude with `two_ne_zero h5`. Apply `mul_left_cancel₀ h2'` to reduce the goal to its premises. Take the linear combination `h4`.

Apply `PowerSeries.map_injective φ φ.injective` to reduce the goal to its premises. Rewrite using `[map_mul, PowerSeries.map_C, map_pow, map_rescale, h3, map_add, map_sum]`. Simplify using `only [map_sub, PowerSeries.map_C, Finset.sum_sub_distrib]`. Rewrite using `[hsum]`.
-/
theorem endoCurve_of_endoZ [CharZero K] [CharZero K'] (W : WeierstrassCurve K) {ι : Type}
    [Fintype ι] {neg : ι → ι} {xP yP : ι → K} {al : K} {wF : ι → PowerSeries K'}
    (hEq : ∀ P, W.toAffine.Equation (xP P) (yP P))
    (hneg : ∀ P, xP (neg P) = xP P ∧ yP (neg P) = W.toAffine.negY (xP P) (yP P))
    (h : IsEndoZ (PowerSeries.map φ (wpReg W)) neg (fun P => φ (xP P + W.b₂ / 12)) wF (φ al)) :
    IsEndoCurve W neg xP yP al := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hEq, h1, hneg, ?_⟩
  have key : ∀ P, PowerSeries.map φ (wTr W (xP P) (yP P)) +
      PowerSeries.map φ (wTr W (xP (neg P)) (yP (neg P))) = wF P + wF (neg P) := by
    intro P
    have hc := second_log_derivative_map φ (Formalism.L2.Th1.C.curve_second_log_derivative K W (xP P) (yP P) (hEq P))
    rw [map_wpShift, ← (hneg P).2] at hc
    have hx : wTr W (xP P) (yP (neg P)) = wTr W (xP (neg P)) (yP (neg P)) := by
      rw [(hneg P).1]
    rw [hx] at hc
    have hu := second_log_derivative_unique (cc_wpShift _ _) hc (h2 P)
    simp only [map_sub, map_mul, map_ofNat] at hu
    linear_combination -hu
  have hinv : Function.Involutive neg := h1
  have hs1 : ∑ P, PowerSeries.map φ (wTr W (xP (neg P)) (yP (neg P))) =
      ∑ P, PowerSeries.map φ (wTr W (xP P) (yP P)) :=
    Equiv.sum_comp hinv.toPerm (fun P => PowerSeries.map φ (wTr W (xP P) (yP P)))
  have hs2 : ∑ P, wF (neg P) = ∑ P, wF P := Equiv.sum_comp hinv.toPerm wF
  have hsum : ∑ P, PowerSeries.map φ (wTr W (xP P) (yP P)) = ∑ P, wF P := by
    have h4 := Finset.sum_congr (rfl : (Finset.univ : Finset ι) = Finset.univ) (fun P _ => key P)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hs1, hs2] at h4
    have h2' : (2 : PowerSeries K') ≠ 0 := by
      intro h0
      have h5 := congrArg PowerSeries.constantCoeff h0
      rw [map_ofNat, map_zero] at h5
      exact two_ne_zero h5
    apply mul_left_cancel₀ h2'
    linear_combination h4
  apply PowerSeries.map_injective φ φ.injective
  rw [map_mul, PowerSeries.map_C, map_pow, map_rescale, h3, map_add, map_sum]
  simp only [map_sub, PowerSeries.map_C, Finset.sum_sub_distrib]
  rw [hsum]

end Alg

/- English proof (translation)
Establish `h : (((Real.sqrt d : ℝ) : ℂ)) ^ 2 = (d : ℂ)`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]`. Simplify using the standard rewrite rules. Unfold `omegaK`. Take the linear combination `(Complex.I ^ 2 / 4) * h + ((d : ℂ) / 4) * Complex.I_sq`.
-/
theorem omega_sq (d : ℕ) : omegaK d ^ 2 = omegaK d - (1 + (d : ℂ)) / 4 := by
  have h : (((Real.sqrt d : ℝ) : ℂ)) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  unfold omegaK
  linear_combination (Complex.I ^ 2 / 4) * h + ((d : ℂ) / 4) * Complex.I_sq

/- English proof (translation)
Take the linear combination `(-n ^ 2) * omega_sq d`.
-/
theorem mul_bar (d : ℕ) (m n : ℂ) :
    (m + n * omegaK d) * (m + n * (1 - omegaK d)) = m ^ 2 + m * n + n ^ 2 * ((1 + (d : ℂ)) / 4) := by
  linear_combination (-n ^ 2) * omega_sq d

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k : ℤ, (dK : ℤ) + 1 = 4 * k` from `⟨((dK : ℤ) + 1) / 4, by omega⟩`. Establish `hdiv : ((dK : ℤ) + 1) / 4 = k` using `by omega`. Establish `hr : (dK : ℝ) + 1 = 4 * (k : ℝ)` using `by exact_mod_cast hk`. Unfold `normInt`. Rewrite using `[hdiv]`.

Use `push_cast`. Establish `: (1 + (dK : ℝ)) / 4 = (k : ℝ)` using `by linarith`. Rewrite using `[this]`.
-/
theorem normInt_cast {dK : ℕ} (hmod : dK % 4 = 3) (m n : ℤ) :
    ((normInt dK m n : ℤ) : ℝ) =
      (m : ℝ) ^ 2 + (m : ℝ) * (n : ℝ) + (n : ℝ) ^ 2 * ((1 + (dK : ℝ)) / 4) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (dK : ℤ) + 1 = 4 * k := ⟨((dK : ℤ) + 1) / 4, by omega⟩
  have hdiv : ((dK : ℤ) + 1) / 4 = k := by omega
  have hr : (dK : ℝ) + 1 = 4 * (k : ℝ) := by exact_mod_cast hk
  unfold normInt
  rw [hdiv]
  push_cast
  have : (1 + (dK : ℝ)) / 4 = (k : ℝ) := by linarith
  rw [this]

/- English proof (translation)
Establish `hmn : (m, n) ≠ (0, 0)`. Introduce `h`. Rewrite `h` using `[Prod.mk.injEq]`. Apply `hN` to reduce the goal to its premises. Rewrite using `[h.1, h.2]`.

Simplify using `[normInt]`. Establish `hd : 0 < dK` using `by omega`. Take `⟨S, hS, hcard, -, hs2⟩` from `Formalism.L2.Th1.F.hasCMByIsogeny dK L hCM m n hmn hd`. Take `⟨hst, hnorm⟩` from `Formalism.L2.Th1.F.hasCMByStable dK L hCM m n`. Establish `hprod : ((m : ℂ) + (n : ℂ) * omegaK dK) * ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) = (S.card : ℂ) + 1`.

Rewrite using `[mul_bar]`. Use `congrArg (fun x : ℝ => (x : ℂ)) hcard` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[this]`. Establish `ha0 : (m : ℂ) + (n : ℂ) * omegaK dK ≠ 0`.

Introduce `h0`. Rewrite `hprod` using `[h0, zero_mul]`. Establish `h1 : ((S.card + 1 : ℕ) : ℂ) = 0` using `by push_cast; exact hprod.symm`. Conclude with `(Nat.succ_ne_zero _) (Nat.cast_eq_zero.mp h1)`. Take `⟨neg, hneg, hE⟩` from `Formalism.L2.Th1.F.endoZInstance L _ S ha0 hst hS`.

Use `⟨S, neg, ?_, ?_, ?_, hE, hprod, ?_⟩` and prove the remaining obligations. Establish `: (((S.card : ℤ) + 1 : ℤ) : ℝ) = ((normInt dK m n : ℤ) : ℝ)`. Rewrite using `[normInt_cast hmod, ← hcard]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `this` after adjusting the coercions. Introduce `P`. Use `⟨?_, (hS.1 P P.2).2⟩` and prove the remaining obligations. Establish `hbar` using `(Formalism.L2.Th1.F.hasCMByStable dK L hCM (m + n) (-n)).1`. Establish `h1` using `hbar _ (hS.1 P P.2).1`.

Establish `e : ((S.card + 1 : ℕ) : ℂ) * (P : ℂ) = (((m + n : ℤ) : ℂ) + ((-n : ℤ) : ℂ) * omegaK dK) * (((m : ℂ) + (n : ℂ) * omegaK dK) * (P : ℂ))`. Use `push_cast`. Rewrite using `[← hprod]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `h1`. Introduce `P`. Establish `e : (neg P : ℂ) = -(P : ℂ) + ((⟨_, hneg P⟩ : L.lattice) : ℂ)`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Rewrite using `[e, L.weierstrassP_add_coe, L.weierstrassP_neg]`. Rewrite using `[e, L.derivWeierstrassP_add_coe, L.derivWeierstrassP_neg]`. Rewrite using `[Finset.sum_coe_sort S (fun P => L.weierstrassP P), ← hs2, hnorm]`. Use `mul_bar dK (m : ℂ) (n : ℂ)` as an intermediate fact. Use `push_cast`.

Take the linear combination `(-Formalism.L2.Th1.F.s2 L) * this`.
-/
theorem cdata {dK : ℕ} (L : PeriodPair) (hmod : dK % 4 = 3) (hCM : Formalism.L2.Th1.CM.HasCMBy dK L)
    (m n : ℤ) (hN : normInt dK m n ≠ 0) :
    ∃ (S : Finset ℂ) (neg : S → S), ((S.card : ℤ) + 1 = normInt dK m n) ∧
      (∀ P : S, ((S.card + 1 : ℕ) : ℂ) * (P : ℂ) ∈ L.lattice ∧ (P : ℂ) ∉ L.lattice) ∧
      (∀ P : S, L.weierstrassP (neg P : ℂ) = L.weierstrassP (P : ℂ) ∧
        L.derivWeierstrassP (neg P : ℂ) = -L.derivWeierstrassP (P : ℂ)) ∧
      IsEndoZ (Formalism.L2.Th1.F.pSeries L) neg (fun P : S => L.weierstrassP (P : ℂ))
        (fun P : S => Formalism.L2.Th1.F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ))))
        ((m : ℂ) + (n : ℂ) * omegaK dK) ∧
      ((m : ℂ) + (n : ℂ) * omegaK dK) * ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) = (S.card : ℂ) + 1 ∧
      ((m : ℂ) + (n : ℂ) * omegaK dK) *
          (((m : ℂ) + (n : ℂ) * omegaK dK) - ((m : ℂ) + (n : ℂ) * (1 - omegaK dK))) *
          Formalism.L2.Th1.F.s2 L = ∑ P : S, L.weierstrassP (P : ℂ) := by
  have hmn : (m, n) ≠ (0, 0) := by
    intro h
    rw [Prod.mk.injEq] at h
    apply hN
    rw [h.1, h.2]
    simp [normInt]
  have hd : 0 < dK := by omega
  obtain ⟨S, hS, hcard, -, hs2⟩ := Formalism.L2.Th1.F.hasCMByIsogeny dK L hCM m n hmn hd
  obtain ⟨hst, hnorm⟩ := Formalism.L2.Th1.F.hasCMByStable dK L hCM m n
  have hprod : ((m : ℂ) + (n : ℂ) * omegaK dK) * ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) =
      (S.card : ℂ) + 1 := by
    rw [mul_bar]
    have := congrArg (fun x : ℝ => (x : ℂ)) hcard
    push_cast at this
    rw [this]
  have ha0 : (m : ℂ) + (n : ℂ) * omegaK dK ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    have h1 : ((S.card + 1 : ℕ) : ℂ) = 0 := by push_cast; exact hprod.symm
    exact (Nat.succ_ne_zero _) (Nat.cast_eq_zero.mp h1)
  obtain ⟨neg, hneg, hE⟩ := Formalism.L2.Th1.F.endoZInstance L _ S ha0 hst hS
  refine ⟨S, neg, ?_, ?_, ?_, hE, hprod, ?_⟩
  · have : (((S.card : ℤ) + 1 : ℤ) : ℝ) = ((normInt dK m n : ℤ) : ℝ) := by
      rw [normInt_cast hmod, ← hcard]
      push_cast
      ring
    exact_mod_cast this
  · intro P
    refine ⟨?_, (hS.1 P P.2).2⟩
    have hbar := (Formalism.L2.Th1.F.hasCMByStable dK L hCM (m + n) (-n)).1
    have h1 := hbar _ (hS.1 P P.2).1
    have e : ((S.card + 1 : ℕ) : ℂ) * (P : ℂ) =
        (((m + n : ℤ) : ℂ) + ((-n : ℤ) : ℂ) * omegaK dK) *
          (((m : ℂ) + (n : ℂ) * omegaK dK) * (P : ℂ)) := by
      push_cast
      rw [← hprod]
      ring
    rw [e]
    exact h1
  · intro P
    have e : (neg P : ℂ) = -(P : ℂ) + ((⟨_, hneg P⟩ : L.lattice) : ℂ) := by
      simp
    constructor
    · rw [e, L.weierstrassP_add_coe, L.weierstrassP_neg]
    · rw [e, L.derivWeierstrassP_add_coe, L.derivWeierstrassP_neg]
  · rw [Finset.sum_coe_sort S (fun P => L.weierstrassP P), ← hs2, hnorm]
    have := mul_bar dK (m : ℂ) (n : ℂ)
    push_cast
    linear_combination (-Formalism.L2.Th1.F.s2 L) * this

/- English proof (translation)
Establish `hmul : IsMul l α (mulS K l α)` using `Pair.isMul_mulF expSpec hl α`. Establish `hθ0` using `EAux.cc_theta hl g2 g3 ε`. Establish `hL0 : PowerSeries.constantCoeff (logSer (shortW g2 g3)) = 0` using `(Formalism.L2.Th1.C.curveFrame K ⊤ (shortW g2 g3) (by simp [Formalism.L2.Th1.C.CoeffIn])).1.1`. Establish `hcl : PowerSeries.constantCoeff (PowerSeries.C α * logSer (shortW g2 g3)) = 0`. Rewrite using `[map_mul, hL0, mul_zero]`.

Unfold `Formalism.L2.Th1.C.mulBy`. Rewrite using `[← Pair.ps_comp (τ := Unit) hθ0 hcl, EAux.subst_C_mul (τ := Unit) hθ0, EAux.log_theta hl]`. Use `conv_lhs => rw [EAux.thetaS_eq]`. Rewrite using `[← Pair.ps_comp (τ := Unit) hmul.1 (EAux.cc_a hl ε), EAux.subst_C_mul (τ := Unit) hmul.1, hmul.2]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `PowerSeries.C ε * (PowerSeries.C α * lgF K l) = PowerSeries.C α * (PowerSeries.C ε * lgF K l)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem theta_comm {K : Type} [Field K] [CharZero K] {l : ℕ} (hl : 2 ≤ l) (g2 g3 ε α : K) :
    PowerSeries.subst (mulS K l α) (thetaS l g2 g3 ε) =
      PowerSeries.subst (thetaS l g2 g3 ε)
        (Formalism.L2.Th1.C.mulBy (logSer (shortW g2 g3)) (expSer (shortW g2 g3)) α) := by
  have hmul : IsMul l α (mulS K l α) := Pair.isMul_mulF expSpec hl α
  have hθ0 := EAux.cc_theta hl g2 g3 ε
  have hL0 : PowerSeries.constantCoeff (logSer (shortW g2 g3)) = 0 :=
    (Formalism.L2.Th1.C.curveFrame K ⊤ (shortW g2 g3) (by simp [Formalism.L2.Th1.C.CoeffIn])).1.1
  have hcl : PowerSeries.constantCoeff (PowerSeries.C α * logSer (shortW g2 g3)) = 0 := by
    rw [map_mul, hL0, mul_zero]
  unfold Formalism.L2.Th1.C.mulBy
  rw [← Pair.ps_comp (τ := Unit) hθ0 hcl, EAux.subst_C_mul (τ := Unit) hθ0, EAux.log_theta hl]
  conv_lhs => rw [EAux.thetaS_eq]
  rw [← Pair.ps_comp (τ := Unit) hmul.1 (EAux.cc_a hl ε), EAux.subst_C_mul (τ := Unit) hmul.1,
    hmul.2]
  congr 1
  change PowerSeries.C ε * (PowerSeries.C α * lgF K l) = PowerSeries.C α * (PowerSeries.C ε * lgF K l)
  ring

/- English proof (translation)
Establish `hb2 : (shortW g2 g3).b₂ = 0` using `(Formalism.L2.Th1.A.shortInv K g2 g3).1`. Establish `hW` using `EAux.intModel hg2 hg3 h2`. Establish `hC : Formalism.L2.Th1.C.CoeffIn (Formalism.G.unitBall K) (shortW g2 g3)` using `hW`. Take `⟨hLP, hXW, hA, -, -⟩` from `Formalism.L2.Th1.C.curveFrame K (Formalism.G.unitBall K) (shortW g2 g3) hC`. Establish `hinv : ‖al⁻¹‖ ≤ 1` using `by rw [norm_inv, hal, inv_one]`.

Establish `h2inv : ‖(2 : K)⁻¹‖ ≤ 1` using `by rw [norm_inv, h2, inv_one]`. Establish `hR` using `Formalism.L2.Th1.C.curveEndoR K (Formalism.G.unitBall K) (shortW g2 g3) hC ι neg xP yP al albar hE hx hy hN hal.le hinv (by rw [hb2]; simp)`. Establish `hPh` using `(Formalism.L2.Th1.C.phOIsPh K (wpReg (shortW g2 g3)) (logSer (shortW g2 g3)) s2 hLP.1 hLP.2.1).2`. Establish `h` using `Formalism.L2.Th1.C.phNormFromDatum K (Formalism.G.unitBall K) (wpReg (shortW g2 g3)) s2 (logSer (shortW g2 g3)) (expSer (shortW g2 g3)) _ (xS (shortW g2 g3)) _ ι neg xP _ _ al albar hLP hPh hXW hA h2inv hR (by rw [hs, hb2]; simp)`. Establish `h'` using `(Formalism.L2.Th1.C.simeqIffCong K Unit _ _).2 h`.

Rewrite `h'` using `[MvPowerSeries.smul_eq_C_mul]`. Conclude with `h'`.
-/
theorem curveNorm {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
    (h2 : ‖(2 : K)‖ = 1) {g2 g3 : K} (s2 : K) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ ≤ 1) {ι : Type}
    [Fintype ι] {neg : ι → ι} {xP yP : ι → K} {al albar : K}
    (hE : IsEndoCurve (shortW g2 g3) neg xP yP al) (hx : ∀ P, ‖xP P‖ ≤ 1) (hy : ∀ P, ‖yP P‖ ≤ 1)
    (hN : al * albar = (Fintype.card ι : K) + 1) (hal : ‖al‖ = 1)
    (hs : al * (al - albar) * s2 = ∑ P, xP P) :
    Simeq (PowerSeries.subst
        (Formalism.L2.Th1.C.mulBy (logSer (shortW g2 g3)) (expSer (shortW g2 g3)) al)
        (phCurve g2 g3 s2) : MvPowerSeries Unit K)
      (MvPowerSeries.C (al * albar) * phCurve g2 g3 s2) := by
  have hb2 : (shortW g2 g3).b₂ = 0 := (Formalism.L2.Th1.A.shortInv K g2 g3).1
  have hW := EAux.intModel hg2 hg3 h2
  have hC : Formalism.L2.Th1.C.CoeffIn (Formalism.G.unitBall K) (shortW g2 g3) := hW
  obtain ⟨hLP, hXW, hA, -, -⟩ := Formalism.L2.Th1.C.curveFrame K (Formalism.G.unitBall K) (shortW g2 g3) hC
  have hinv : ‖al⁻¹‖ ≤ 1 := by rw [norm_inv, hal, inv_one]
  have h2inv : ‖(2 : K)⁻¹‖ ≤ 1 := by rw [norm_inv, h2, inv_one]
  have hR := Formalism.L2.Th1.C.curveEndoR K (Formalism.G.unitBall K) (shortW g2 g3) hC ι neg xP yP al albar
    hE hx hy hN hal.le hinv (by rw [hb2]; simp)
  have hPh := (Formalism.L2.Th1.C.phOIsPh K (wpReg (shortW g2 g3)) (logSer (shortW g2 g3)) s2
    hLP.1 hLP.2.1).2
  have h := Formalism.L2.Th1.C.phNormFromDatum K (Formalism.G.unitBall K) (wpReg (shortW g2 g3)) s2
    (logSer (shortW g2 g3)) (expSer (shortW g2 g3)) _ (xS (shortW g2 g3)) _ ι neg xP _ _ al albar
    hLP hPh hXW hA h2inv hR (by rw [hs, hb2]; simp)
  have h' := (Formalism.L2.Th1.C.simeqIffCong K Unit _ _).2 h
  rw [MvPowerSeries.smul_eq_C_mul] at h'
  exact h'

/- English proof (translation)
Establish `h` using `Formalism.L2.Th1.A.bridgeWp K (shortW g2 g3)`. Take `⟨-, e2, e3, -⟩` from `Formalism.L2.Th1.A.shortInv K g2 g3`. Rewrite `h` using `[e2, e3]`. Conclude with `Formalism.L2.Th1.F.isWpUnique K g2 g3 _ _ h (Formalism.L2.Th1.F.pOfIsWp K g2 g3)`.
-/
theorem wpReg_eq {K : Type} [Field K] [CharZero K] (g2 g3 : K) :
    wpReg (shortW g2 g3) = Formalism.L2.Th1.F.pOf g2 g3 := by
  have h := Formalism.L2.Th1.A.bridgeWp K (shortW g2 g3)
  obtain ⟨-, e2, e3, -⟩ := Formalism.L2.Th1.A.shortInv K g2 g3
  rw [e2, e3] at h
  exact Formalism.L2.Th1.F.isWpUnique K g2 g3 _ _ h (Formalism.L2.Th1.F.pOfIsWp K g2 g3)

/- English proof (translation)
Establish `hLP` using `(Formalism.L2.Th1.C.curveFrame K ⊤ (shortW g2 g3) (by simp [Formalism.L2.Th1.C.CoeffIn])).1`. Establish `hcl : PowerSeries.constantCoeff (PowerSeries.C α * logSer (shortW g2 g3)) = 0`. Rewrite using `[map_mul, hLP.1, mul_zero]`. Unfold `Formalism.L2.Th1.C.mulBy`. Conclude with `PowerSeries.constantCoeff_subst_eq_zero hcl _ hLP.2.2.1`.
-/
theorem cc_mulBy {K : Type} [Field K] [CharZero K] (g2 g3 α : K) :
    PowerSeries.constantCoeff
      (Formalism.L2.Th1.C.mulBy (logSer (shortW g2 g3)) (expSer (shortW g2 g3)) α) = 0 := by
  have hLP := (Formalism.L2.Th1.C.curveFrame K ⊤ (shortW g2 g3) (by simp [Formalism.L2.Th1.C.CoeffIn])).1
  have hcl : PowerSeries.constantCoeff (PowerSeries.C α * logSer (shortW g2 g3)) = 0 := by
    rw [map_mul, hLP.1, mul_zero]
  unfold Formalism.L2.Th1.C.mulBy
  exact PowerSeries.constantCoeff_subst_eq_zero hcl _ hLP.2.2.1

/- English proof (translation)
Use `le_antisymm (IsUltrametricDist.norm_natCast_le_one K N) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 ((hp.coprime_iff_not_dvd).2 hN)`. Establish `e : (1 : K) = (a : K) * (l : K) + (b : K) * (N : K)`.

Establish `h0` using `congrArg (fun z : ℤ => (z : K)) hab`. Move the coercions through the operations in `at h0`. Conclude with `h0.symm`. Establish `hl1 : ‖(l : K)‖ < 1`. Rewrite using `[hn]`.

Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)`. Establish `h1 : ‖(a : K) * (l : K)‖ < 1`. Rewrite using `[norm_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one K a)) hl1`. Establish `h2 : ‖(b : K) * (N : K)‖ < 1`.

Rewrite using `[norm_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one K b)) hlt`. Establish `: ‖(1 : K)‖ < 1`. Rewrite using `[e]`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)`.

Rewrite `this` using `[norm_one]`. Conclude with `lt_irrefl _ this`.
-/
theorem norm_natCast_eq_one {K : Type} [NormedField K] [IsUltrametricDist K] {l : ℕ}
    (hp : l.Prime) (hn : ‖(l : K)‖ = (l : ℝ)⁻¹) {N : ℕ} (hN : ¬ l ∣ N) : ‖(N : K)‖ = 1 := by
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K N) ?_
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((hp.coprime_iff_not_dvd).2 hN)
  have e : (1 : K) = (a : K) * (l : K) + (b : K) * (N : K) := by
    have h0 := congrArg (fun z : ℤ => (z : K)) hab
    push_cast at h0
    exact h0.symm
  have hl1 : ‖(l : K)‖ < 1 := by
    rw [hn]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have h1 : ‖(a : K) * (l : K)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _)
      (IsUltrametricDist.norm_intCast_le_one K a)) hl1
  have h2 : ‖(b : K) * (N : K)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _)
      (IsUltrametricDist.norm_intCast_le_one K b)) hlt
  have : ‖(1 : K)‖ < 1 := by
    rw [e]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)
  rw [norm_one] at this
  exact lt_irrefl _ this

end CurveNormEndomorphisms

/- English proof (translation)
Introduce `hCM4 dK L hsq hmod hCM l _ h5 hld hin ι g2 g3 ε s2 hGood hε hθ c hc hg2 hg3 hs2 σ hU m n hN α hα`. Establish `hl : 2 ≤ l` using `hU.1.two_le`. Establish `h2 : ‖(2 : MaximalUnramifiedExtension l)‖ = 1` using `EAux.norm_two hU.1 hU.2.1 hU.2.2.1`. Establish `hCM'` using `Formalism.L2.Th1.F.hasCMByScale dK L c hc hCM`. Generalize the expression as in `Formalism.L2.Th1.F.scalePair L c hc = L' at hg2 hg3 hs2 hCM'`.

Establish `hN0 : normInt dK m n ≠ 0`. Introduce `h`. Apply `hN` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `dvd_zero _`.

Take `⟨S, neg, hcard, hker, hnegP, hE, hprod, hs2C⟩` from `CurveNormEndomorphisms.cdata L' hmod hCM' m n hN0`. Take `⟨-, -, hn2, hn3, hdisc, -⟩` from `hGood`. Establish `hlN : ¬ l ∣ (S.card + 1)`. Introduce `h`. Apply `hN` to reduce the goal to its premises.

Rewrite using `[← hcard]`. Conclude with `h` after adjusting the coercions. Establish `hpts : ∀ P : S, ∃ x y : MaximalUnramifiedExtension l, (x : ℂ_[l]) = ι (L'.weierstrassP (P : ℂ)) ∧ (y : ℂ_[l]) = ι (L'.derivWeierstrassP (P : ℂ)) / 2 ∧ ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1`. Introduce `P`. Establish `h` using `hCM4 dK L' hsq hmod hCM' l h5 hld ι 1 one_ne_zero (by rw [one_pow, one_mul, ← hg2]; exact g2.2) (by rw [one_pow, one_mul, ← hg3]; exact g3.2) (by rw [one_pow, one_mul, ← hg2]; exact hn2) (by rw [one_pow, one_mul, ← hg3]; exact hn3) (by simp only [one_pow, one_mul]; rw [← hg2, ← h …`.

Simplify using `only [one_pow, one_mul] at h`. Take `⟨hx, hy, hxn, hyn⟩` from `h`. Use `⟨⟨_, hx⟩, ⟨_, hy⟩ / 2, rfl, ?_, hxn, ?_⟩` and prove the remaining obligations. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[norm_div, h2, div_one]`. Conclude with `hyn`. Use `choose xP yP hxP hyP hxn hyn using hpts`. Establish `hb2 : (shortW g2 g3).b₂ = 0` using `(Formalism.L2.Th1.A.shortInv (MaximalUnramifiedExtension l) g2 g3).1`. Establish `hEq : ∀ P, (shortW g2 g3).toAffine.Equation (xP P) (yP P)`.

Introduce `P`. Rewrite using `[WeierstrassCurve.Affine.equation_iff]`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `congrArg ι (L'.derivWeierstrassP_sq (P : ℂ) (hker P).2)`. Simplify using `only [map_pow, map_sub, map_mul, map_ofNat] at h`.

Simplify using `only [shortW]`. Use `push_cast`. Establish `h4 : ((4 : MaximalUnramifiedExtension l) : ℂ_[l]) = 4` using `rfl`. Rewrite using `[hxP, hyP, hg2, hg3, h4]`. Take the linear combination `h / 4`.

Establish `hneg : ∀ P, xP (neg P) = xP P ∧ yP (neg P) = (shortW g2 g3).toAffine.negY (xP P) (yP P)`. Introduce `P`. Prove the components needed by the constructor for the conclusion. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hxP, hxP, (hnegP P).1]`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [WeierstrassCurve.Affine.negY, shortW]`. Use `push_cast`. Rewrite using `[hyP, hyP, (hnegP P).2, map_neg]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmapE : PowerSeries.map (MaximalUnramifiedExtension l).subtype (wpReg (shortW g2 g3)) = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.pSeries L')`. Rewrite using `[CurveNormEndomorphisms.wpReg_eq, Formalism.L2.Th1.F.pOfLattice L', (Formalism.L2.Th1.F.seriesMap _ _ (MaximalUnramifiedExtension l).subtype g2 g3 0 0).2.2.1, (Formalism.L2.Th1.F.seriesMap _ _ (ι : ℂ →+* ℂ_[l]) L'.g₂ L'.g₃ 0 0).2.2.1]`. Express the relevant statement in the definitionally equal form `Formalism.L2.Th1.F.pOf (g2 : ℂ_[l]) (g3 : ℂ_[l]) = Formalism.L2.Th1.F.pOf (ι L'.g₂) (ι L'.g₃)`. Rewrite using `[hg2, hg3]`. Establish `hZ : IsEndoZ (PowerSeries.map (MaximalUnramifiedExtension l).subtype (wpReg (shortW g2 g3))) neg (fun P => (MaximalUnramifiedExtension l).subtype (xP P + (shortW g2 g3).b₂ / 12)) (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 (fun z => L'.weierstrassP …`.

Establish `h` using `CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[l]) hE`. Establish `e1 : (fun P => (MaximalUnramifiedExtension l).subtype (xP P + (shortW g2 g3).b₂ / 12)) = fun P : S => (ι : ℂ →+* ℂ_[l]) (L'.weierstrassP (P : ℂ))`. Use function extensionality and compare the values at `P`. Rewrite using `[hb2, zero_div, add_zero]`. Conclude with `hxP P`.

Establish `e2 : (MaximalUnramifiedExtension l).subtype α = (ι : ℂ →+* ℂ_[l]) ((m : ℂ) + (n : ℂ) * omegaK dK)` using `hα`. Rewrite using `[hmapE, e1, e2]`. Conclude with `h`. Establish `hEC` using `CurveNormEndomorphisms.endoCurve_of_endoZ (MaximalUnramifiedExtension l).subtype (shortW g2 g3) hEq hneg hZ`. Take `⟨hw, hσw⟩` from `hSq dK hsq hmod l h5 hin ι`.

Take `⟨w, hwc⟩ : ∃ w : MaximalUnramifiedExtension l, (w : ℂ_[l]) = ι (omegaK dK)` from `⟨⟨_, hw⟩, rfl⟩`. Establish `hσ : σ w = 1 - w` using `hσw σ hU w hwc`. Establish `hαw : α = (m : MaximalUnramifiedExtension l) + (n : MaximalUnramifiedExtension l) * w`. Apply `Subtype.ext` to reduce the goal to its premises. Use `push_cast`.

Rewrite using `[hα, hwc]`. Simplify using the standard rewrite rules. Establish `hσα : σ α = (m : MaximalUnramifiedExtension l) + (n : MaximalUnramifiedExtension l) * (1 - w)`. Rewrite using `[hαw]`. Simplify using `[hσ]`.

Establish `hσσ : σ (σ α) = α`. Rewrite using `[hσα, hαw]`. Simplify using `[hσ]`. Establish `hNK : α * σ α = (Fintype.card S : MaximalUnramifiedExtension l) + 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `h` using `congrArg ι hprod`. Simplify using `only [map_mul, map_add, map_sub, map_intCast, map_natCast, map_one] at h`. Rewrite using `[hσα, hαw, Fintype.card_coe]`. Use `push_cast`. Rewrite using `[hwc]`.

Conclude with `h`. Establish `hal : ‖α‖ = 1`. Establish `h1 : ‖α * σ α‖ = 1`. Rewrite using `[hNK, Fintype.card_coe]`. Use `CurveNormEndomorphisms.norm_natCast_eq_one (K := MaximalUnramifiedExtension l) hU.1 hU.2.2.1 hlN` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Rewrite `h1` using `[norm_mul, sigmaIsom (MaximalUnramifiedExtension l) l σ hU α]`. Conclude with `(mul_self_eq_one_iff.mp h1).resolve_right (by have := norm_nonneg α; linarith)`. Establish `hs : α * (α - σ α) * s2 = ∑ P, xP P`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `congrArg ι hs2C`. Simplify using `only [map_mul, map_add, map_sub, map_intCast, map_one, map_sum] at h`. Rewrite using `[hσα, hαw]`. Use `push_cast`.

Rewrite using `[hwc, hs2, h]`. Conclude with `Finset.sum_congr rfl (fun P _ => (hxP P).symm)`. Establish `hsim` using `CurveNormEndomorphisms.curveNorm h2 s2 hn2 hn3 hEC hxn hyn hNK hal hs`. Conclude with `transportNorm (MaximalUnramifiedExtension l) l σ hU (thetaS l g2 g3 ε) (phCurve g2 g3 s2) (phFF l g2 g3 s2 ε) _ α (EAux.cc_theta hl g2 g3 ε) hθ (CurveNormEndomorphisms.cc_mulBy g2 g3 α) hal.le hσσ (CurveNormEndomorphisms.theta_comm hl g2 g3 ε α) hsim (phCompare (MaximalUnramified …`.
-/
theorem NRDense_of (hSq : SqrtKur) : NRDense := by
  intro hCM4 dK L hsq hmod hCM l _ h5 hld hin ι g2 g3 ε s2 hGood hε hθ c hc hg2 hg3 hs2 σ hU m n hN
    α hα
  have hl : 2 ≤ l := hU.1.two_le
  have h2 : ‖(2 : MaximalUnramifiedExtension l)‖ = 1 := EAux.norm_two hU.1 hU.2.1 hU.2.2.1
  have hCM' := Formalism.L2.Th1.F.hasCMByScale dK L c hc hCM
  generalize Formalism.L2.Th1.F.scalePair L c hc = L' at hg2 hg3 hs2 hCM'
  have hN0 : normInt dK m n ≠ 0 := by
    intro h
    apply hN
    rw [h]
    exact dvd_zero _
  obtain ⟨S, neg, hcard, hker, hnegP, hE, hprod, hs2C⟩ := CurveNormEndomorphisms.cdata L' hmod hCM' m n hN0
  obtain ⟨-, -, hn2, hn3, hdisc, -⟩ := hGood
  have hlN : ¬ l ∣ (S.card + 1) := by
    intro h
    apply hN
    rw [← hcard]
    exact_mod_cast h
  have hpts : ∀ P : S, ∃ x y : MaximalUnramifiedExtension l, (x : ℂ_[l]) = ι (L'.weierstrassP (P : ℂ)) ∧
      (y : ℂ_[l]) = ι (L'.derivWeierstrassP (P : ℂ)) / 2 ∧ ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 := by
    intro P
    have h := hCM4 dK L' hsq hmod hCM' l h5 hld ι 1 one_ne_zero
      (by rw [one_pow, one_mul, ← hg2]; exact g2.2) (by rw [one_pow, one_mul, ← hg3]; exact g3.2)
      (by rw [one_pow, one_mul, ← hg2]; exact hn2) (by rw [one_pow, one_mul, ← hg3]; exact hn3)
      (by simp only [one_pow, one_mul]; rw [← hg2, ← hg3]; exact hdisc)
      (P : ℂ) (S.card + 1) (Nat.succ_pos _) hlN (hker P).1 (hker P).2
    simp only [one_pow, one_mul] at h
    obtain ⟨hx, hy, hxn, hyn⟩ := h
    refine ⟨⟨_, hx⟩, ⟨_, hy⟩ / 2, rfl, ?_, hxn, ?_⟩
    · push_cast
      rfl
    · rw [norm_div, h2, div_one]
      exact hyn
  choose xP yP hxP hyP hxn hyn using hpts
  have hb2 : (shortW g2 g3).b₂ = 0 := (Formalism.L2.Th1.A.shortInv (MaximalUnramifiedExtension l) g2 g3).1
  have hEq : ∀ P, (shortW g2 g3).toAffine.Equation (xP P) (yP P) := by
    intro P
    rw [WeierstrassCurve.Affine.equation_iff]
    apply Subtype.ext
    have h := congrArg ι (L'.derivWeierstrassP_sq (P : ℂ) (hker P).2)
    simp only [map_pow, map_sub, map_mul, map_ofNat] at h
    simp only [shortW]
    push_cast
    have h4 : ((4 : MaximalUnramifiedExtension l) : ℂ_[l]) = 4 := rfl
    rw [hxP, hyP, hg2, hg3, h4]
    linear_combination h / 4
  have hneg : ∀ P, xP (neg P) = xP P ∧
      yP (neg P) = (shortW g2 g3).toAffine.negY (xP P) (yP P) := by
    intro P
    constructor
    · apply Subtype.ext
      rw [hxP, hxP, (hnegP P).1]
    · apply Subtype.ext
      simp only [WeierstrassCurve.Affine.negY, shortW]
      push_cast
      rw [hyP, hyP, (hnegP P).2, map_neg]
      ring
  have hmapE : PowerSeries.map (MaximalUnramifiedExtension l).subtype (wpReg (shortW g2 g3)) =
      PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.pSeries L') := by
    rw [CurveNormEndomorphisms.wpReg_eq, Formalism.L2.Th1.F.pOfLattice L',
      (Formalism.L2.Th1.F.seriesMap _ _ (MaximalUnramifiedExtension l).subtype g2 g3 0 0).2.2.1,
      (Formalism.L2.Th1.F.seriesMap _ _ (ι : ℂ →+* ℂ_[l]) L'.g₂ L'.g₃ 0 0).2.2.1]
    change Formalism.L2.Th1.F.pOf (g2 : ℂ_[l]) (g3 : ℂ_[l]) = Formalism.L2.Th1.F.pOf (ι L'.g₂) (ι L'.g₃)
    rw [hg2, hg3]
  have hZ : IsEndoZ (PowerSeries.map (MaximalUnramifiedExtension l).subtype (wpReg (shortW g2 g3))) neg
      (fun P => (MaximalUnramifiedExtension l).subtype (xP P + (shortW g2 g3).b₂ / 12))
      (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[l])
        (Formalism.L2.Th1.F.taylor0 (fun z => L'.weierstrassP (z + (P : ℂ)))))
      ((MaximalUnramifiedExtension l).subtype α) := by
    have h := CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[l]) hE
    have e1 : (fun P => (MaximalUnramifiedExtension l).subtype (xP P + (shortW g2 g3).b₂ / 12)) =
        fun P : S => (ι : ℂ →+* ℂ_[l]) (L'.weierstrassP (P : ℂ)) := by
      funext P
      rw [hb2, zero_div, add_zero]
      exact hxP P
    have e2 : (MaximalUnramifiedExtension l).subtype α = (ι : ℂ →+* ℂ_[l]) ((m : ℂ) + (n : ℂ) * omegaK dK) := hα
    rw [hmapE, e1, e2]
    exact h
  have hEC := CurveNormEndomorphisms.endoCurve_of_endoZ (MaximalUnramifiedExtension l).subtype (shortW g2 g3) hEq hneg hZ
  obtain ⟨hw, hσw⟩ := hSq dK hsq hmod l h5 hin ι
  obtain ⟨w, hwc⟩ : ∃ w : MaximalUnramifiedExtension l, (w : ℂ_[l]) = ι (omegaK dK) := ⟨⟨_, hw⟩, rfl⟩
  have hσ : σ w = 1 - w := hσw σ hU w hwc
  have hαw : α = (m : MaximalUnramifiedExtension l) + (n : MaximalUnramifiedExtension l) * w := by
    apply Subtype.ext
    push_cast
    rw [hα, hwc]
    simp
  have hσα : σ α = (m : MaximalUnramifiedExtension l) + (n : MaximalUnramifiedExtension l) * (1 - w) := by
    rw [hαw]
    simp [hσ]
  have hσσ : σ (σ α) = α := by
    rw [hσα, hαw]
    simp [hσ]
  have hNK : α * σ α = (Fintype.card S : MaximalUnramifiedExtension l) + 1 := by
    apply Subtype.ext
    have h := congrArg ι hprod
    simp only [map_mul, map_add, map_sub, map_intCast, map_natCast, map_one] at h
    rw [hσα, hαw, Fintype.card_coe]
    push_cast
    rw [hwc]
    exact h
  have hal : ‖α‖ = 1 := by
    have h1 : ‖α * σ α‖ = 1 := by
      rw [hNK, Fintype.card_coe]
      have := CurveNormEndomorphisms.norm_natCast_eq_one (K := MaximalUnramifiedExtension l) hU.1 hU.2.2.1 hlN
      push_cast at this
      exact this
    rw [norm_mul, sigmaIsom (MaximalUnramifiedExtension l) l σ hU α] at h1
    exact (mul_self_eq_one_iff.mp h1).resolve_right (by have := norm_nonneg α; linarith)
  have hs : α * (α - σ α) * s2 = ∑ P, xP P := by
    apply Subtype.ext
    have h := congrArg ι hs2C
    simp only [map_mul, map_add, map_sub, map_intCast, map_one, map_sum] at h
    rw [hσα, hαw]
    push_cast
    rw [hwc, hs2, h]
    exact Finset.sum_congr rfl (fun P _ => (hxP P).symm)
  have hsim := CurveNormEndomorphisms.curveNorm h2 s2 hn2 hn3 hEC hxn hyn hNK hal hs
  exact transportNorm (MaximalUnramifiedExtension l) l σ hU (thetaS l g2 g3 ε) (phCurve g2 g3 s2) (phFF l g2 g3 s2 ε)
    _ α (EAux.cc_theta hl g2 g3 ε) hθ (CurveNormEndomorphisms.cc_mulBy g2 g3 α) hal.le hσσ
    (CurveNormEndomorphisms.theta_comm hl g2 g3 ε α) hsim (phCompare (MaximalUnramifiedExtension l) l hU.1 g2 g3 s2 ε hε hθ)

end Formalism.L2.Th1.D
