import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RamDef

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

/- English proof (translation)
Introduce `a b c d ha hd lam hlam m _ _ Λ x0 y0 T i₀ hK x hxs hxT hx z₀ hz₀ hz₀T hz₀x hz₀ne`. Take `⟨hOK, hΛ, hθ, h1, h2, hl, hQ, hi₀, hT⟩` from `hK`. Establish `hdp : Prime (d : ℤ)` using `Nat.prime_iff_prime_int.mp hl`. Establish `hκ0 : repKappa a b d ha hd lam hlam ≠ 0` using `rep_kappa_ne a b d ha hd lam hlam`. Establish `hr0 : ((Real.sqrt d : ℝ) : ℂ) ≠ 0`.

Establish `: 0 < Real.sqrt d` using `Real.sqrt_pos.mpr (by exact_mod_cast hd)`. Conclude with `this.ne'` after adjusting the coercions. Establish `hπ : 2 * cmTheta b d - b = Complex.I * ((Real.sqrt d : ℝ) : ℂ)` using `by unfold cmTheta; ring`. Establish `hπ0 : (2 * cmTheta b d - b) ≠ 0` using `by rw [hπ]; exact mul_ne_zero Complex.I_ne_zero hr0`. Establish `hdc : (d : ℂ) ≠ 0` using `by exact_mod_cast hl.ne_zero`.

Establish `hππ : (2 * cmTheta b d - b)⁻¹ * conj (2 * cmTheta b d - b)⁻¹ = (d : ℂ)⁻¹`. Rewrite using `[map_inv₀, ← mul_inv]`. Use `congr 1`. Rewrite using `[hπ, map_mul, Complex.conj_I, Complex.conj_ofReal]`. Take the linear combination `(-((Real.sqrt d : ℝ) : ℂ) ^ 2) * Complex.I_sq + rep_sqrt_sq d`.

Establish `nz : ∀ {z : ℤ}, ¬ (d : ℤ) ∣ z → (z : ℂ) ≠ 0`. Introduce `z hz h; apply hz; rw [show z = 0 by exact_mod_cast h]; exact dvd_zero _`. Take `⟨n0, s0, hs0, e0⟩` from `sat_norm hOK hΛ hθ hl hz₀`. Establish `hn0 : n0 ≠ 0`. Introduce `h`.

Apply `H_self_ne m (cmL a b d ha hd lam hlam) hz₀ne` to reduce the goal to its premises. Rewrite using `[e0, h]`. Simplify using the standard rewrite rules. Set `P : ℕ → Prop` to `fun j => SatMem d Λ (((2 * cmTheta b d - b)⁻¹) ^ j • z₀)`. Establish `hbound : ∀ j, P j → j ≤ n0.natAbs`.

Introduce `j hj`. Take `⟨p, q, hq, e⟩` from `sat_norm hOK hΛ hθ hl hj`. Establish `eH : stdH (cmL a b d ha hd lam hlam) m (((2 * cmTheta b d - b)⁻¹) ^ j • z₀) (((2 * cmTheta b d - b)⁻¹) ^ j • z₀) = ((d : ℂ)⁻¹) ^ j * stdH (cmL a b d ha hd lam hlam) m z₀ z₀`. Rewrite using `[LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, map_pow, ← mul_assoc, ← mul_pow, hππ]`. Rewrite `e` using `[eH, e0]`.

Establish `e' : repKappa a b d ha hd lam hlam * ((p : ℂ) / q) = repKappa a b d ha hd lam hlam * ((n0 : ℂ) / ((s0 : ℂ) * (d : ℂ) ^ j))`. Combine the equalities or inequalities in the displayed calculation. Establish `e''` using `mul_left_cancel₀ hκ0 e'`. Rewrite `e''` using `[div_eq_div_iff (nz hq) (mul_ne_zero (nz hs0) (pow_ne_zero _ hdc))]`. Establish `hZ : p * (s0 * (d : ℤ) ^ j) = n0 * q` using `by exact_mod_cast e''`.

Establish `hdj : (d : ℤ) ^ j ∣ n0`. Establish `h' : (d : ℤ) ^ j ∣ n0 * q` using `⟨p * s0, by rw [← hZ]; ring⟩`. Establish `hcop : IsCoprime ((d : ℤ) ^ j) q` using `IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hdp).mpr hq)`. Conclude with `hcop.dvd_of_dvd_mul_right h'`. Establish `hle : d ^ j ≤ n0.natAbs`.

Use `Int.natAbs_dvd_natAbs.mpr hdj` as an intermediate fact. Rewrite `this` using `[Int.natAbs_pow, Int.natAbs_natCast]`. Conclude with `Nat.le_of_dvd (Int.natAbs_pos.mpr hn0) this`. Establish `hlt : j < d ^ j` using `Nat.lt_pow_self hl.one_lt`. Use linear arithmetic over natural numbers and integers.

Establish `hP0 : P 0` using `by simpa [P] using hz₀`. Use `set J := Nat.findGreatest P n0.natAbs with hJ`. Establish `hPJ : P J` using `Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0`. Establish `hPJ1 : ¬ P (J + 1)`. Introduce `h`.

Distinguish the cases in `hle : J + 1 ≤ n0.natAbs`. Conclude with `Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hle h`. Conclude with `hle (hbound _ h)`. Use `set xh : m → ℂ := ((2 * cmTheta b d - b)⁻¹) ^ J • z₀ with hxh`. Establish `hxhT : ∀ j ∈ T, xh j = 0` using `by intro j hj; simp [xh, hz₀T j hj]`.

Establish `hxhx : stdH (cmL a b d ha hd lam hlam) m xh x = 0`. Rewrite using `[hxh, LinearMap.map_smul, LinearMap.smul_apply, hz₀x, smul_zero]`. Establish `hnot : ¬ SatMem d Λ ((2 * cmTheta b d - b)⁻¹ • xh)`. Rewrite using `[hxh, smul_smul, ← pow_succ']`. Conclude with `hPJ1`.

Establish `hxhs : SatMem d Λ xh` using `hPJ`. Take `⟨s, hs, hsx⟩` from `hPJ`. Establish `hs' : ¬ (d : ℤ) ∣ (s : ℤ)` using `fun h => hs (by exact_mod_cast h)`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy, n, c₂, hny, hdn⟩ : ∃ y ∈ Λ, ∃ n c₂ : ℤ, stdH (cmL a b d ha hd lam hlam) m (s • xh) y = repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) ∧ ¬ (d : ℤ) ∣ 2 * n - c₂ * b := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Apply `hnot` to reduce the goal to its premises. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm, ← hΛ]`. Introduce `y' hy'`.

Take `⟨n', c', e1, -⟩` from `rep_H_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hsx hy'`. Take `⟨k, hk⟩` from `hcon y' hy' n' c' e1`. Use `⟨-k, ?_⟩` and prove the remaining obligations. Unfold `altE`. Rewrite using `[LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, e1, im_pi_inv, hk]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use `set yz := zT T y with hyzdef`. Establish `hyz : SatMem d Λ yz` using `rep_zT_sat a b c d ha hd lam hlam m hOK Λ hΛ hθ hl x0 y0 hQ T hT hy`. Use `set μ := stdH (cmL a b d ha hd lam hlam) m yz x / stdH (cmL a b d ha hd lam hlam) m x x with hμdef`.

Use `set y' := yz - μ • x with hy'def`. Establish `hy's : SatMem d Λ y'`. Break down `hx with rfl | ⟨p, q, hp, hq, e⟩` into its components or cases. Simplify `hyz` using `[y']`. Take `⟨n2, c3, s2, hs2, e2⟩` from `sat_pair hOK hΛ hθ hl hyz hxs`.

Establish `hμ : μ = (((q * n2 : ℤ) : ℂ) - ((q * c3 : ℤ) : ℂ) * conj (cmTheta b d)) / ((s2 * p : ℤ) : ℂ)`. Establish `hp0` using `nz hp`. Establish `hq0` using `nz hq`. Establish `hs20` using `nz hs2`. Rewrite using `[hμdef, e2, e]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use `rep_sat_sub d Λ hl hyz ?_` and prove the remaining obligations. Rewrite using `[hμ]`. Conclude with `rep_sat_elt d Λ hl hθ hxs _ _ _ (not_dvd_mul' hl hs2 hp)`.

Establish `hy'T : ∀ j ∈ T, y' j = 0`. Introduce `j hj`. Simplify using `[y', yz, zT, hj, hxT j hj]`. Establish `hy'x : stdH (cmL a b d ha hd lam hlam) m y' x = 0`. Break down `hx with rfl | ⟨p, q, hp, hq, e⟩` into its components or cases.

Simplify using the standard rewrite rules. Establish `hxx : stdH (cmL a b d ha hd lam hlam) m x x ≠ 0`. Rewrite using `[e]`. Conclude with `div_ne_zero (mul_ne_zero hκ0 (nz hp)) (nz hq)`. Rewrite using `[hy'def, map_sub, LinearMap.sub_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, hμdef, div_mul_cancel₀ _ hxx, sub_self]`.

Establish `hxhy' : stdH (cmL a b d ha hd lam hlam) m xh y' = stdH (cmL a b d ha hd lam hlam) m xh y`. Rewrite using `[hy'def, map_sub, (stdH (cmL a b d ha hd lam hlam) m xh).map_smulₛₗ μ x, hxhx, smul_zero, sub_zero]`. Conclude with `rep_H_zT a b d ha hd lam hlam m T hxhT`. Establish `hsc : (s : ℂ) ≠ 0` using `by exact_mod_cast nz hs'`. Establish `hxhy : stdH (cmL a b d ha hd lam hlam) m xh y = repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) / s`.

Establish `e3 : stdH (cmL a b d ha hd lam hlam) m (s • xh) y = (s : ℂ) * stdH (cmL a b d ha hd lam hlam) m xh y`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]`. Rewrite `e3` using `[hny]`. Rewrite using `[eq_div_iff hsc]`. Take the linear combination `(-1 : ℂ) * e3`.

Take `⟨p1, q1, hq1, e1⟩` from `sat_norm hOK hΛ hθ hl hxhs`. Take `⟨p2, q2, hq2, e2⟩` from `sat_norm hOK hΛ hθ hl hy's`. Distinguish the cases in `hp1 : (d : ℤ) ∣ p1`. Distinguish the cases in `hp2 : (d : ℤ) ∣ p2`. Use `⟨xh + y', rep_sat_add d Λ hl hxhs hy's, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `j hj`. Simplify using `[hxhT j hj, hy'T j hj]`. Rewrite using `[map_add, LinearMap.add_apply, hxhx, hy'x, add_zero]`. Use `⟨p1 * q2 * s + p2 * q1 * s + (2 * n - c₂ * b) * q1 * q2, q1 * q2 * s, ?_, not_dvd_mul' hl (not_dvd_mul' hl hq1 hq2) hs', ?_⟩` and prove the remaining obligations. Introduce `hdv`.

Establish `e4 : (2 * n - c₂ * b) * q1 * q2 = (p1 * q2 * s + p2 * q1 * s + (2 * n - c₂ * b) * q1 * q2) - (p1 * q2 * s + p2 * q1 * s)` using `by ring`. Establish `: (d : ℤ) ∣ (2 * n - c₂ * b) * q1 * q2`. Rewrite using `[e4]`. Conclude with `dvd_sub hdv (dvd_add ((hp1.mul_right _).mul_right _) ((hp2.mul_right _).mul_right _))`. Conclude with `not_dvd_mul' hl (not_dvd_mul' hl hdn hq1) hq2 this`.

Establish `hyx : stdH (cmL a b d ha hd lam hlam) m y' xh = repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * cmTheta b d) / s`. Rewrite using `[← rep_H_conj (cmL a b d ha hd lam hlam) m xh y', hxhy', hxhy]`. Simplify using `only [map_div₀, map_mul, map_sub, map_intCast, map_natCast, Complex.conj_conj, kappa_real a b d ha hd lam hlam]`. Rewrite using `[map_add (stdH (cmL a b d ha hd lam hlam) m) xh y', LinearMap.add_apply, map_add, map_add, e1, e2, hxhy', hxhy, hyx]`. Establish `htb` using `rep_theta_add_conj b d`.

Establish `hA : (q1 : ℂ) * (q1 : ℂ)⁻¹ = 1` using `mul_inv_cancel₀ (nz hq1)`. Establish `hB : (q2 : ℂ) * (q2 : ℂ)⁻¹ = 1` using `mul_inv_cancel₀ (nz hq2)`. Establish `hC : (s : ℂ) * (s : ℂ)⁻¹ = 1` using `mul_inv_cancel₀ hsc`. Use `set κ := repKappa a b d ha hd lam hlam`. Use `push_cast`.

Simplify using `only [div_eq_mul_inv, mul_inv]`. Take the linear combination `(-κ * p2 * (q2 : ℂ)⁻¹ * ((s : ℂ) * (s : ℂ)⁻¹) - κ * (s : ℂ)⁻¹ * (2 * n - c₂ * b) * ((q2 : ℂ) * (q2 : ℂ)⁻¹)) * hA + (-κ * p1 * (q1 : ℂ)⁻¹ * ((s : ℂ) * (s : ℂ)⁻¹) - κ * (s : ℂ)⁻¹ * (2 * n - c₂ * b)) * hB + (-κ * p1 * (q1 : ℂ)⁻¹ - κ * p2 * (q2 : ℂ)⁻¹) * hC + (-κ * (s : ℂ)⁻¹ * c₂) * …`. Conclude with `⟨y', hy's, hy'T, hy'x, p2, q2, hp2, hq2, e2⟩`. Conclude with `⟨xh, hxhs, hxhT, hxhx, p1, q1, hp1, hq1, e1⟩`.
-/
theorem unitVecRam : UnitVecRam := by
  classical
  intro a b c d ha hd lam hlam m _ _ Λ x0 y0 T i₀ hK x hxs hxT hx z₀ hz₀ hz₀T hz₀x hz₀ne
  obtain ⟨hOK, hΛ, hθ, h1, h2, hl, hQ, hi₀, hT⟩ := hK
  have hdp : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hκ0 : repKappa a b d ha hd lam hlam ≠ 0 := rep_kappa_ne a b d ha hd lam hlam
  have hr0 : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have hπ : 2 * cmTheta b d - b = Complex.I * ((Real.sqrt d : ℝ) : ℂ) := by unfold cmTheta; ring
  have hπ0 : (2 * cmTheta b d - b) ≠ 0 := by rw [hπ]; exact mul_ne_zero Complex.I_ne_zero hr0
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hππ : (2 * cmTheta b d - b)⁻¹ * conj (2 * cmTheta b d - b)⁻¹ = (d : ℂ)⁻¹ := by
    rw [map_inv₀, ← mul_inv]
    congr 1
    rw [hπ, map_mul, Complex.conj_I, Complex.conj_ofReal]
    linear_combination (-((Real.sqrt d : ℝ) : ℂ) ^ 2) * Complex.I_sq + rep_sqrt_sq d
  have nz : ∀ {z : ℤ}, ¬ (d : ℤ) ∣ z → (z : ℂ) ≠ 0 := by
    intro z hz h; apply hz; rw [show z = 0 by exact_mod_cast h]; exact dvd_zero _

  obtain ⟨n0, s0, hs0, e0⟩ := sat_norm hOK hΛ hθ hl hz₀
  have hn0 : n0 ≠ 0 := by
    intro h
    apply H_self_ne m (cmL a b d ha hd lam hlam) hz₀ne
    rw [e0, h]; simp
  let P : ℕ → Prop := fun j => SatMem d Λ (((2 * cmTheta b d - b)⁻¹) ^ j • z₀)
  have hbound : ∀ j, P j → j ≤ n0.natAbs := by
    intro j hj
    obtain ⟨p, q, hq, e⟩ := sat_norm hOK hΛ hθ hl hj
    have eH : stdH (cmL a b d ha hd lam hlam) m (((2 * cmTheta b d - b)⁻¹) ^ j • z₀) (((2 * cmTheta b d - b)⁻¹) ^ j • z₀)
        = ((d : ℂ)⁻¹) ^ j * stdH (cmL a b d ha hd lam hlam) m z₀ z₀ := by
      rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, map_pow,
        ← mul_assoc, ← mul_pow, hππ]
    rw [eH, e0] at e
    have e' : repKappa a b d ha hd lam hlam * ((p : ℂ) / q) =
        repKappa a b d ha hd lam hlam * ((n0 : ℂ) / ((s0 : ℂ) * (d : ℂ) ^ j)) := by
      calc _ = repKappa a b d ha hd lam hlam * p / q := by ring
        _ = _ := e.symm
        _ = _ := by ring
    have e'' := mul_left_cancel₀ hκ0 e'
    rw [div_eq_div_iff (nz hq) (mul_ne_zero (nz hs0) (pow_ne_zero _ hdc))] at e''
    have hZ : p * (s0 * (d : ℤ) ^ j) = n0 * q := by exact_mod_cast e''
    have hdj : (d : ℤ) ^ j ∣ n0 := by
      have h' : (d : ℤ) ^ j ∣ n0 * q := ⟨p * s0, by rw [← hZ]; ring⟩
      have hcop : IsCoprime ((d : ℤ) ^ j) q := IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hdp).mpr hq)
      exact hcop.dvd_of_dvd_mul_right h'
    have hle : d ^ j ≤ n0.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hdj
      rw [Int.natAbs_pow, Int.natAbs_natCast] at this
      exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn0) this
    have hlt : j < d ^ j := Nat.lt_pow_self hl.one_lt
    omega
  have hP0 : P 0 := by simpa [P] using hz₀
  set J := Nat.findGreatest P n0.natAbs with hJ
  have hPJ : P J := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  have hPJ1 : ¬ P (J + 1) := by
    intro h
    by_cases hle : J + 1 ≤ n0.natAbs
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hle h
    · exact hle (hbound _ h)
  set xh : m → ℂ := ((2 * cmTheta b d - b)⁻¹) ^ J • z₀ with hxh
  have hxhT : ∀ j ∈ T, xh j = 0 := by intro j hj; simp [xh, hz₀T j hj]
  have hxhx : stdH (cmL a b d ha hd lam hlam) m xh x = 0 := by
    rw [hxh, LinearMap.map_smul, LinearMap.smul_apply, hz₀x, smul_zero]
  have hnot : ¬ SatMem d Λ ((2 * cmTheta b d - b)⁻¹ • xh) := by
    rw [hxh, smul_smul, ← pow_succ']; exact hPJ1
  have hxhs : SatMem d Λ xh := hPJ
  obtain ⟨s, hs, hsx⟩ := hPJ
  have hs' : ¬ (d : ℤ) ∣ (s : ℤ) := fun h => hs (by exact_mod_cast h)

  obtain ⟨y, hy, n, c₂, hny, hdn⟩ : ∃ y ∈ Λ, ∃ n c₂ : ℤ,
      stdH (cmL a b d ha hd lam hlam) m (s • xh) y = repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) ∧
      ¬ (d : ℤ) ∣ 2 * n - c₂ * b := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    refine ⟨s, hs, ?_⟩
    rw [smul_comm, ← hΛ]
    intro y' hy'
    obtain ⟨n', c', e1, -⟩ := rep_H_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hsx hy'
    obtain ⟨k, hk⟩ := hcon y' hy' n' c' e1
    refine ⟨-k, ?_⟩
    unfold altE
    rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, e1, im_pi_inv, hk]
    push_cast
    field_simp

  set yz := zT T y with hyzdef
  have hyz : SatMem d Λ yz := rep_zT_sat a b c d ha hd lam hlam m hOK Λ hΛ hθ hl x0 y0 hQ T hT hy
  set μ := stdH (cmL a b d ha hd lam hlam) m yz x / stdH (cmL a b d ha hd lam hlam) m x x with hμdef
  set y' := yz - μ • x with hy'def
  have hy's : SatMem d Λ y' := by
    rcases hx with rfl | ⟨p, q, hp, hq, e⟩
    · simpa [y'] using hyz
    · obtain ⟨n2, c3, s2, hs2, e2⟩ := sat_pair hOK hΛ hθ hl hyz hxs
      have hμ : μ = (((q * n2 : ℤ) : ℂ) - ((q * c3 : ℤ) : ℂ) * conj (cmTheta b d)) / ((s2 * p : ℤ) : ℂ) := by
        have hp0 := nz hp
        have hq0 := nz hq
        have hs20 := nz hs2
        rw [hμdef, e2, e]
        push_cast
        field_simp
      refine rep_sat_sub d Λ hl hyz ?_
      rw [hμ]
      exact rep_sat_elt d Λ hl hθ hxs _ _ _ (not_dvd_mul' hl hs2 hp)
  have hy'T : ∀ j ∈ T, y' j = 0 := by
    intro j hj; simp [y', yz, zT, hj, hxT j hj]
  have hy'x : stdH (cmL a b d ha hd lam hlam) m y' x = 0 := by
    rcases hx with rfl | ⟨p, q, hp, hq, e⟩
    · simp
    · have hxx : stdH (cmL a b d ha hd lam hlam) m x x ≠ 0 := by
        rw [e]; exact div_ne_zero (mul_ne_zero hκ0 (nz hp)) (nz hq)
      rw [hy'def, map_sub, LinearMap.sub_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, hμdef,
        div_mul_cancel₀ _ hxx, sub_self]
  have hxhy' : stdH (cmL a b d ha hd lam hlam) m xh y' = stdH (cmL a b d ha hd lam hlam) m xh y := by
    rw [hy'def, map_sub, (stdH (cmL a b d ha hd lam hlam) m xh).map_smulₛₗ μ x, hxhx, smul_zero, sub_zero]
    exact rep_H_zT a b d ha hd lam hlam m T hxhT
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast nz hs'
  have hxhy : stdH (cmL a b d ha hd lam hlam) m xh y =
      repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) / s := by
    have e3 : stdH (cmL a b d ha hd lam hlam) m (s • xh) y = (s : ℂ) * stdH (cmL a b d ha hd lam hlam) m xh y := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hny] at e3
    rw [eq_div_iff hsc]
    linear_combination (-1 : ℂ) * e3

  obtain ⟨p1, q1, hq1, e1⟩ := sat_norm hOK hΛ hθ hl hxhs
  obtain ⟨p2, q2, hq2, e2⟩ := sat_norm hOK hΛ hθ hl hy's
  by_cases hp1 : (d : ℤ) ∣ p1
  · by_cases hp2 : (d : ℤ) ∣ p2
    · refine ⟨xh + y', rep_sat_add d Λ hl hxhs hy's, ?_, ?_, ?_⟩
      · intro j hj; simp [hxhT j hj, hy'T j hj]
      · rw [map_add, LinearMap.add_apply, hxhx, hy'x, add_zero]
      · refine ⟨p1 * q2 * s + p2 * q1 * s + (2 * n - c₂ * b) * q1 * q2, q1 * q2 * s, ?_,
          not_dvd_mul' hl (not_dvd_mul' hl hq1 hq2) hs', ?_⟩
        · intro hdv
          have e4 : (2 * n - c₂ * b) * q1 * q2 =
              (p1 * q2 * s + p2 * q1 * s + (2 * n - c₂ * b) * q1 * q2) - (p1 * q2 * s + p2 * q1 * s) := by ring
          have : (d : ℤ) ∣ (2 * n - c₂ * b) * q1 * q2 := by
            rw [e4]
            exact dvd_sub hdv (dvd_add ((hp1.mul_right _).mul_right _) ((hp2.mul_right _).mul_right _))
          exact not_dvd_mul' hl (not_dvd_mul' hl hdn hq1) hq2 this
        · have hyx : stdH (cmL a b d ha hd lam hlam) m y' xh =
              repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * cmTheta b d) / s := by
            rw [← rep_H_conj (cmL a b d ha hd lam hlam) m xh y', hxhy', hxhy]
            simp only [map_div₀, map_mul, map_sub, map_intCast, map_natCast, Complex.conj_conj,
              kappa_real a b d ha hd lam hlam]
          rw [map_add (stdH (cmL a b d ha hd lam hlam) m) xh y', LinearMap.add_apply, map_add, map_add, e1, e2, hxhy',
            hxhy, hyx]
          have htb := rep_theta_add_conj b d
          have hA : (q1 : ℂ) * (q1 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (nz hq1)
          have hB : (q2 : ℂ) * (q2 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (nz hq2)
          have hC : (s : ℂ) * (s : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hsc
          set κ := repKappa a b d ha hd lam hlam
          push_cast
          simp only [div_eq_mul_inv, mul_inv]
          linear_combination
            (-κ * p2 * (q2 : ℂ)⁻¹ * ((s : ℂ) * (s : ℂ)⁻¹) - κ * (s : ℂ)⁻¹ * (2 * n - c₂ * b) * ((q2 : ℂ) * (q2 : ℂ)⁻¹)) * hA +
            (-κ * p1 * (q1 : ℂ)⁻¹ * ((s : ℂ) * (s : ℂ)⁻¹) - κ * (s : ℂ)⁻¹ * (2 * n - c₂ * b)) * hB +
            (-κ * p1 * (q1 : ℂ)⁻¹ - κ * p2 * (q2 : ℂ)⁻¹) * hC +
            (-κ * (s : ℂ)⁻¹ * c₂) * htb
    · exact ⟨y', hy's, hy'T, hy'x, p2, q2, hp2, hq2, e2⟩
  · exact ⟨xh, hxhs, hxhT, hxhx, p1, q1, hp1, hq1, e1⟩

end PI.UnitaryGroupMassFormula.UnimodLocStd
