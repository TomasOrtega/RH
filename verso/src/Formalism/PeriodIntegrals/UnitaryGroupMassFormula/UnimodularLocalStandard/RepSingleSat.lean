import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepHSelfInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepExact

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

def zT {m : Type} [DecidableEq m] (T : Finset m) (y : m → ℂ) : m → ℂ := fun i => if i ∈ T then 0 else y i

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, hl.not_dvd_one, by rw [smul_zero]; exact zero_mem Λ⟩`.
-/
theorem rep_sat_zero {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) (hl : l.Prime) : SatMem l Λ 0 :=
  ⟨1, hl.not_dvd_one, by rw [smul_zero]; exact zero_mem Λ⟩

/- English proof (translation)
Take `⟨n, hn, hv⟩` from `hv`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm, Int.cast_smul_eq_zsmul]`. Conclude with `zsmul_mem hv r`.
-/
theorem rep_sat_zsmul {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) {v : m → ℂ} (hv : SatMem l Λ v) (r : ℤ) :
    SatMem l Λ ((r : ℂ) • v) := by
  obtain ⟨n, hn, hv⟩ := hv
  refine ⟨n, hn, ?_⟩
  rw [smul_comm, Int.cast_smul_eq_zsmul]
  exact zsmul_mem hv r

/- English proof (translation)
Take `⟨n, hn, hv⟩` from `hv`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `hθ _ hv`.
-/
theorem rep_sat_theta {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) {b : ℤ} {d : ℕ}
    (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ) {v : m → ℂ} (hv : SatMem l Λ v) : SatMem l Λ (cmTheta b d • v) := by
  obtain ⟨n, hn, hv⟩ := hv
  refine ⟨n, hn, ?_⟩
  rw [smul_comm]
  exact hθ _ hv

/- English proof (translation)
Establish `hconj : conj (cmTheta b d) = b - cmTheta b d`. Unfold `cmTheta`. Simplify using `only [map_div₀, map_add, map_mul, map_intCast, Complex.conj_I, Complex.conj_ofReal, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Establish `e : (((n : ℂ) - c * conj (cmTheta b d)) / s) • v = (((n - c * b : ℤ) : ℂ) / s) • v + ((c : ℂ) / s) • (cmTheta b d • v)`.

Rewrite using `[hconj, smul_smul, ← add_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `rep_sat_add (l := l) (Λ := Λ) hl (rep_sat_rat (l := l) (Λ := Λ) hl hv _ s hs) (rep_sat_rat (l := l) (Λ := Λ) hl (rep_sat_theta l Λ hθ hv) c s hs)`.
-/
theorem rep_sat_elt {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) (hl : l.Prime) {b : ℤ} {d : ℕ}
    (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ) {v : m → ℂ} (hv : SatMem l Λ v) (n c s : ℤ) (hs : ¬ (l : ℤ) ∣ s) :
    SatMem l Λ ((((n : ℂ) - c * conj (cmTheta b d)) / s) • v) := by
  have hconj : conj (cmTheta b d) = b - cmTheta b d := by
    unfold cmTheta
    simp only [map_div₀, map_add, map_mul, map_intCast, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  have e : (((n : ℂ) - c * conj (cmTheta b d)) / s) • v =
      (((n - c * b : ℤ) : ℂ) / s) • v + ((c : ℂ) / s) • (cmTheta b d • v) := by
    rw [hconj, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  rw [e]
  exact rep_sat_add (l := l) (Λ := Λ) hl (rep_sat_rat (l := l) (Λ := Λ) hl hv _ s hs) (rep_sat_rat (l := l) (Λ := Λ) hl (rep_sat_theta l Λ hθ hv) c s hs)

section Zero

variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]

/- English proof (translation)
Take `⟨hc4, -, -, -⟩` from `hOK`. Use `set θ := cmTheta b d with hθdef`. Establish `hsd : 0 < Real.sqrt d` using `Real.sqrt_pos.2 (by exact_mod_cast hd)`. Establish `hsq : Real.sqrt d ^ 2 = d` using `Real.sq_sqrt (by positivity)`. Establish `hθre : θ.re = b / 2` using `by simp [hθdef, cmTheta]`.

Establish `hθim : θ.im = Real.sqrt d / 2` using `by simp [hθdef, cmTheta]`. Establish `hconj : conj θ = b - θ`. Apply the tactic sequence `apply Complex.ext <;> simp [hθre, hθim] <;> ring`. Use `set α : ℂ := (x * a : ℂ) + y * θ with hαdef`. Use `set Q : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2 with hQdef`.

Establish `hαn : Complex.normSq α = a * Q`. Rewrite using `[Complex.normSq_apply]`. Establish `hre : α.re = x * a + y * (b / 2)` using `by simp [hαdef, hθre]`. Establish `him : α.im = y * (Real.sqrt d / 2)` using `by simp [hαdef, hθim]`. Rewrite using `[hre, him, hQdef]`.

Establish `hc4' : (b : ℝ) ^ 2 + d = 4 * a * c` using `by exact_mod_cast hc4.symm`. Use `push_cast`. Take the linear combination `(y ^ 2 / 4) * hsq + (y ^ 2 / 4) * hc4'`. Establish `hQ0 : Q ≠ 0` using `fun h => hQ (by rw [h]; exact dvd_zero _)`. Establish `hQ0' : (Q : ℂ) ≠ 0` using `by exact_mod_cast hQ0`.

Establish `ha0 : (a : ℂ) ≠ 0` using `by exact_mod_cast ha.ne'`. Establish `hα0 : α ≠ 0`. Introduce `h`. Establish `h1` using `hαn`. Rewrite `h1` using `[h, map_zero]`.

Establish `h2 : (a : ℝ) * Q ≠ 0` using `mul_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hQ0)`. Conclude with `h2 h1.symm`. Establish `hnl : Complex.normSq lam ≠ 0` using `(Complex.normSq_pos.2 hlam).ne'`. Establish `harea : area (cmL a b d ha hd lam hlam) = Complex.normSq lam * a * (Real.sqrt d / 2)`. Establish `e : conj (lam * (a : ℂ)) * (lam * θ) = ((Complex.normSq lam * a : ℝ) : ℂ) * θ`.

Rewrite using `[map_mul, Complex.conj_natCast]`. Use `push_cast`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Expand and normalize the polynomial expressions, which then agree. Use `show |(conj (lam * (a : ℂ)) * (lam * θ)).im| = _`.

Rewrite using `[e, Complex.im_ofReal_mul, hθim]`. Conclude with `abs_of_pos (by have := Complex.normSq_pos.2 hlam; positivity)`. Establish `hHs : ∀ u : ℂ, stdH (cmL a b d ha hd lam hlam) m z (Pi.single j u) = z j * ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj u`. Introduce `u`. Simplify using `only [stdH, matH, LinearMap.mk₂'ₛₗ_apply]`.

Rewrite using `[Finset.sum_eq_single j, Finset.sum_eq_single j]`. Simplify using `[Matrix.smul_apply]`. Introduce `j' _ hj'`. Simplify using `[Pi.single_apply, hj']`. Simplify using the standard rewrite rules.

Introduce `i _ hi`. Use `Finset.sum_eq_zero fun j' _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj' : j' = j`. Substitute `hj'` using the available equality. Simplify using `[Matrix.smul_apply, Matrix.one_apply_ne hi]`.

Simplify using `[Pi.single_apply, hj']`. Simplify using the standard rewrite rules. Take `⟨N, hN, hw⟩` from `hj`. Establish `hN0 : N ≠ 0` using `by rintro rfl; exact hN (dvd_zero _)`. Establish `hN0' : (N : ℂ) ≠ 0` using `by exact_mod_cast hN0`.

Establish `hz' : z ∈ dualLat (stdH (cmL a b d ha hd lam hlam) m) Λ` using `by rw [hΛ]; exact hz`. Establish `hwe : (N • Pi.single j (lam * α) : m → ℂ) = Pi.single j ((N : ℂ) * (lam * α))`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality.

Simplify using `[nsmul_eq_mul]`. Simplify using `[Pi.single_apply, hi]`. Establish `hθw : θ • Pi.single j ((N : ℂ) * (lam * α)) = Pi.single j (θ * ((N : ℂ) * (lam * α)))`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = j`.

Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hi]`. Take `⟨m1, hm1⟩` from `hz' _ hw`. Take `⟨m2, hm2⟩` from `hz' _ (hθ _ hw)`.

Simplify using `only [altE] at hm1 hm2`. Rewrite `hm1`, `hm2` using `[hwe]`. Rewrite `hm2` using `[hθw, hHs]`. Rewrite `hm1` using `[hHs]`. Use `set X := z j * ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj ((N : ℂ) * (lam * α)) with hXdef`.

Establish `hm2' : X.re * (-(Real.sqrt d / 2)) + X.im * (b / 2) = m2`. Establish `e : (X * conj θ).im = m2`. Rewrite using `[← hm2, hXdef, map_mul (starRingEnd ℂ) θ]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `e` using `[Complex.mul_im, Complex.conj_re, Complex.conj_im, hθre, hθim]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hm2'` using `[hm1]`. Establish `hX : X * (Real.sqrt d : ℂ) = 2 * ((m1 : ℂ) * θ - m2)`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using `only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, hθre, hθim, mul_zero, sub_zero, zero_mul, Complex.mul_im, Complex.sub_im]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.sub_re, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, hθre, hθim, mul_zero, zero_mul, add_zero, sub_zero, Complex.mul_re, hm1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcl : conj lam = (Complex.normSq lam : ℂ) / lam`.

Rewrite using `[eq_div_iff hlam, mul_comm, Complex.mul_conj]`. Establish `hca : conj α = (Complex.normSq α : ℂ) / α`. Rewrite using `[eq_div_iff hα0, mul_comm, Complex.mul_conj]`. Establish `hsdC : (Real.sqrt d : ℂ) ≠ 0` using `by exact_mod_cast hsd.ne'`. Establish `hnlC : (Complex.normSq lam : ℂ) ≠ 0` using `by exact_mod_cast hnl`.

Establish `hzj : z j = ((((m1 * b - m2 : ℤ) : ℂ) - (m1 : ℂ) * conj θ) / ((N * Q : ℤ) : ℂ)) * (lam * α)`. Establish `hareaC : ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ) ≠ 0`. Rewrite using `[harea]`. Use `push_cast`. Conclude with `mul_ne_zero (mul_ne_zero hnlC ha0) (div_ne_zero hsdC two_ne_zero)`.

Establish `hK : ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj ((N : ℂ) * (lam * α)) * (Real.sqrt d : ℂ) ≠ 0` using `mul_ne_zero (mul_ne_zero (inv_ne_zero hareaC) ((map_ne_zero _).2 (mul_ne_zero hN0' (mul_ne_zero hlam hα0)))) hsdC`. Apply `mul_right_cancel₀ hK` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[harea, map_mul, map_mul, map_natCast, hcl, hca, hαn, hconj]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hsing : Pi.single j (z j) = ((((m1 * b - m2 : ℤ) : ℂ) - (m1 : ℂ) * conj θ) / ((N * Q : ℤ) : ℂ)) • Pi.single j (lam * α)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = j`.

Substitute `hi` using the available equality. Simplify using `[hzj]`. Simplify using `[Pi.single_apply, hi]`. Establish `hs : ¬ (l : ℤ) ∣ (N * Q : ℤ)`. Establish `hp : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.1 hl`.

Introduce `h`. Break down `hp.dvd_or_dvd h with h1 | h1` into its components or cases. Conclude with `hN (Int.natCast_dvd_natCast.1 h1)`. Conclude with `hQ h1`. Rewrite using `[hsing]`.

Conclude with `rep_sat_elt l Λ hl hθ ⟨N, hN, hw⟩ (m1 * b - m2) m1 (N * Q) hs`.
-/
theorem rep_single_sat (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) (x y : ℤ) (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (j : m)
    (hj : SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) {z : m → ℂ} (hz : z ∈ Λ) :
    SatMem l Λ (Pi.single j (z j)) := by
  obtain ⟨hc4, -, -, -⟩ := hOK
  set θ := cmTheta b d with hθdef
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt (by positivity)
  have hθre : θ.re = b / 2 := by simp [hθdef, cmTheta]
  have hθim : θ.im = Real.sqrt d / 2 := by simp [hθdef, cmTheta]
  have hconj : conj θ = b - θ := by
    apply Complex.ext <;> simp [hθre, hθim] <;> ring
  set α : ℂ := (x * a : ℂ) + y * θ with hαdef
  set Q : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2 with hQdef

  have hαn : Complex.normSq α = a * Q := by
    rw [Complex.normSq_apply]
    have hre : α.re = x * a + y * (b / 2) := by simp [hαdef, hθre]
    have him : α.im = y * (Real.sqrt d / 2) := by simp [hαdef, hθim]
    rw [hre, him, hQdef]
    have hc4' : (b : ℝ) ^ 2 + d = 4 * a * c := by exact_mod_cast hc4.symm
    push_cast
    linear_combination (y ^ 2 / 4) * hsq + (y ^ 2 / 4) * hc4'
  have hQ0 : Q ≠ 0 := fun h => hQ (by rw [h]; exact dvd_zero _)
  have hQ0' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ0
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hα0 : α ≠ 0 := by
    intro h
    have h1 := hαn
    rw [h, map_zero] at h1
    have h2 : (a : ℝ) * Q ≠ 0 := mul_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hQ0)
    exact h2 h1.symm
  have hnl : Complex.normSq lam ≠ 0 := (Complex.normSq_pos.2 hlam).ne'
  have harea : area (cmL a b d ha hd lam hlam) = Complex.normSq lam * a * (Real.sqrt d / 2) := by
    have e : conj (lam * (a : ℂ)) * (lam * θ) = ((Complex.normSq lam * a : ℝ) : ℂ) * θ := by
      rw [map_mul, Complex.conj_natCast]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    show |(conj (lam * (a : ℂ)) * (lam * θ)).im| = _
    rw [e, Complex.im_ofReal_mul, hθim]
    exact abs_of_pos (by have := Complex.normSq_pos.2 hlam; positivity)

  have hHs : ∀ u : ℂ, stdH (cmL a b d ha hd lam hlam) m z (Pi.single j u) =
      z j * ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj u := by
    intro u
    simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply]
    rw [Finset.sum_eq_single j, Finset.sum_eq_single j]
    · simp [Matrix.smul_apply]
    · intro j' _ hj'
      simp [Pi.single_apply, hj']
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j' _ => ?_
      by_cases hj' : j' = j
      · subst hj'
        simp [Matrix.smul_apply, Matrix.one_apply_ne hi]
      · simp [Pi.single_apply, hj']
    · simp
  obtain ⟨N, hN, hw⟩ := hj
  have hN0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero _)
  have hN0' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hz' : z ∈ dualLat (stdH (cmL a b d ha hd lam hlam) m) Λ := by rw [hΛ]; exact hz
  have hwe : (N • Pi.single j (lam * α) : m → ℂ) = Pi.single j ((N : ℂ) * (lam * α)) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp [nsmul_eq_mul]
    · simp [Pi.single_apply, hi]
  have hθw : θ • Pi.single j ((N : ℂ) * (lam * α)) = Pi.single j (θ * ((N : ℂ) * (lam * α))) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp
    · simp [Pi.single_apply, hi]
  obtain ⟨m1, hm1⟩ := hz' _ hw
  obtain ⟨m2, hm2⟩ := hz' _ (hθ _ hw)
  simp only [altE] at hm1 hm2
  rw [hwe] at hm1 hm2
  rw [hθw, hHs] at hm2
  rw [hHs] at hm1
  set X := z j * ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj ((N : ℂ) * (lam * α)) with hXdef
  have hm2' : X.re * (-(Real.sqrt d / 2)) + X.im * (b / 2) = m2 := by
    have e : (X * conj θ).im = m2 := by
      rw [← hm2, hXdef, map_mul (starRingEnd ℂ) θ]
      congr 1
      ring
    rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, hθre, hθim] at e
    linarith
  rw [hm1] at hm2'
  have hX : X * (Real.sqrt d : ℂ) = 2 * ((m1 : ℂ) * θ - m2) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
        Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, hθre, hθim, mul_zero,
        sub_zero, zero_mul, Complex.mul_im, Complex.sub_im]
      linarith
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.sub_re,
        Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, hθre, hθim, mul_zero,
        zero_mul, add_zero, sub_zero, Complex.mul_re, hm1]
      ring

  have hcl : conj lam = (Complex.normSq lam : ℂ) / lam := by
    rw [eq_div_iff hlam, mul_comm, Complex.mul_conj]
  have hca : conj α = (Complex.normSq α : ℂ) / α := by
    rw [eq_div_iff hα0, mul_comm, Complex.mul_conj]
  have hsdC : (Real.sqrt d : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
  have hnlC : (Complex.normSq lam : ℂ) ≠ 0 := by exact_mod_cast hnl
  have hzj : z j = ((((m1 * b - m2 : ℤ) : ℂ) - (m1 : ℂ) * conj θ) / ((N * Q : ℤ) : ℂ)) * (lam * α) := by
    have hareaC : ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ) ≠ 0 := by
      rw [harea]
      push_cast
      exact mul_ne_zero (mul_ne_zero hnlC ha0) (div_ne_zero hsdC two_ne_zero)
    have hK : ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj ((N : ℂ) * (lam * α)) *
        (Real.sqrt d : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (inv_ne_zero hareaC)
        ((map_ne_zero _).2 (mul_ne_zero hN0' (mul_ne_zero hlam hα0)))) hsdC
    apply mul_right_cancel₀ hK
    calc z j * (((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj ((N : ℂ) * (lam * α)) *
          (Real.sqrt d : ℂ)) = X * (Real.sqrt d : ℂ) := by rw [hXdef]; ring
      _ = 2 * ((m1 : ℂ) * θ - m2) := hX
      _ = _ := by
          rw [harea, map_mul, map_mul, map_natCast, hcl, hca, hαn, hconj]
          push_cast
          field_simp
          ring
  have hsing : Pi.single j (z j) = ((((m1 * b - m2 : ℤ) : ℂ) - (m1 : ℂ) * conj θ) / ((N * Q : ℤ) : ℂ)) •
      Pi.single j (lam * α) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp [hzj]
    · simp [Pi.single_apply, hi]
  have hs : ¬ (l : ℤ) ∣ (N * Q : ℤ) := by
    have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
    intro h
    rcases hp.dvd_or_dvd h with h1 | h1
    · exact hN (Int.natCast_dvd_natCast.1 h1)
    · exact hQ h1
  rw [hsing]
  exact rep_sat_elt l Λ hl hθ ⟨N, hN, hw⟩ (m1 * b - m2) m1 (N * Q) hs

/- English proof (translation)
Establish `hsum : SatMem l Λ (∑ j ∈ T, Pi.single j (z j))` using `Finset.sum_induction _ (SatMem l Λ) (fun _ _ h1 h2 => rep_sat_add (l := l) (Λ := Λ) hl h1 h2) (rep_sat_zero l Λ hl) (fun j hj => rep_single_sat a b c d ha hd lam hlam m hOK Λ hΛ hθ hl x y hQ j (hT j hj) hz)`. Establish `e : zT T z = z - ∑ j ∈ T, Pi.single j (z j)`. Use function extensionality and compare the values at `i`. Simplify using `only [zT, Pi.sub_apply, Finset.sum_apply, Pi.single_apply]`. Rewrite using `[Finset.sum_ite_eq]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e]`. Conclude with `rep_sat_sub (l := l) (Λ := Λ) hl (rep_sat_of_mem (l := l) (Λ := Λ) hz hl) hsum`.
-/
theorem rep_zT_sat (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) (x y : ℤ) (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (T : Finset m)
    (hT : ∀ j ∈ T, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) {z : m → ℂ} (hz : z ∈ Λ) :
    SatMem l Λ (zT T z) := by
  have hsum : SatMem l Λ (∑ j ∈ T, Pi.single j (z j)) :=
    Finset.sum_induction _ (SatMem l Λ) (fun _ _ h1 h2 => rep_sat_add (l := l) (Λ := Λ) hl h1 h2) (rep_sat_zero l Λ hl)
      (fun j hj => rep_single_sat a b c d ha hd lam hlam m hOK Λ hΛ hθ hl x y hQ j (hT j hj) hz)
  have e : zT T z = z - ∑ j ∈ T, Pi.single j (z j) := by
    funext i
    simp only [zT, Pi.sub_apply, Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_ite_eq]
    split_ifs <;> simp
  rw [e]
  exact rep_sat_sub (l := l) (Λ := Λ) hl (rep_sat_of_mem (l := l) (Λ := Λ) hz hl) hsum

/- English proof (translation)
Simplify using `only [stdH, matH, LinearMap.mk₂'ₛₗ_apply]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Unfold `zT`. Distinguish the cases in `hj : j ∈ T`. Rewrite using `[if_pos hj, map_zero, mul_zero]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[hz i hj, zero_mul, zero_mul]`. Rewrite using `[Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero, mul_zero, zero_mul]`. Rewrite using `[if_neg hj]`.
-/
theorem rep_H_zT (T : Finset m) {z y : m → ℂ} (hz : ∀ j ∈ T, z j = 0) :
    stdH (cmL a b d ha hd lam hlam) m z (zT T y) = stdH (cmL a b d ha hd lam hlam) m z y := by
  simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold zT
  by_cases hj : j ∈ T
  · rw [if_pos hj, map_zero, mul_zero]
    by_cases hij : i = j
    · subst hij
      rw [hz i hj, zero_mul, zero_mul]
    · rw [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero, mul_zero, zero_mul]
  · rw [if_neg hj]

end Zero

end PI.UnitaryGroupMassFormula.UnimodLocStd
