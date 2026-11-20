import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepExact

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Simplify using `[stdH, matH, Matrix.smul_apply, Matrix.one_apply, Pi.single_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[stdH, matH, Matrix.smul_apply, Matrix.one_apply, Pi.single_apply, apply_ite (starRingEnd ℂ), mul_ite]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (i₀ : m) (φ : ℂ)
    (g : m → ℂ) :
    stdH L m (Pi.single i₀ φ) g = ((area L : ℂ))⁻¹ * (φ * conj (g i₀)) ∧
    stdH L m g (Pi.single i₀ φ) = ((area L : ℂ))⁻¹ * (g i₀ * conj φ) := by
  constructor
  · simp [stdH, matH, Matrix.smul_apply, Matrix.one_apply, Pi.single_apply]
    ring
  · simp [stdH, matH, Matrix.smul_apply, Matrix.one_apply, Pi.single_apply,
      apply_ite (starRingEnd ℂ), mul_ite]
    ring

/- English proof (translation)
Simplify using `only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hrc]`. Apply `mul_left_cancel₀ hN` to reduce the goal to its premises. Take the linear combination `(N₁ * (1 - 2 * rc + rc ^ 2)) * hww + (N₁ * rc ^ 2) * hff + (rc - rc ^ 2) * hX + (κ * (rc - 1)) * hrD`.
-/
private theorem H_affine_combination_eq_of_quadratic_relation {m : Type} [Fintype m] [DecidableEq m] (H : PI.ULS.Sesq (m → ℂ))
    (f w : m → ℂ) (κ rc Q N₁ γ ε : ℂ) (hN : N₁ ≠ 0)
    (hff : H f f = κ * Q) (hww : H w w = κ * Q * (1 + ε)) (hX : N₁ * (H f w + H w f) = κ * γ)
    (hrc : conj rc = rc) (hrD : rc * (N₁ * (2 * Q + Q * ε) - γ) = N₁ * Q * ε) :
    H (w + rc • (f - w)) (w + rc • (f - w)) = κ * Q := by
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hrc]
  apply mul_left_cancel₀ hN
  linear_combination (N₁ * (1 - 2 * rc + rc ^ 2)) * hww + (N₁ * rc ^ 2) * hff +
    (rc - rc ^ 2) * hX + (κ * (rc - 1)) * hrD

/- English proof (translation)
Take `⟨h4, -, -, -⟩` from `h`. Establish `hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules. Establish `h4' : (4:ℂ) * a * c = (b:ℂ)^2 + d` using `by exact_mod_cast h4`.

Establish `hc : conj (cmTheta b d) = ((b:ℂ) - Complex.I * (Real.sqrt d : ℝ)) / 2`. Simplify using `[cmTheta, map_div₀, Complex.conj_ofReal, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc]`. Prove the components needed by the constructor for the conclusion.

Simplify using `only [cmTheta]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [cmTheta]`. Take the linear combination `(-((Real.sqrt d : ℝ) : ℂ)^2/4) * Complex.I_sq + (1/4) * hs - (1/4) * h4'`.
-/
private theorem cmTheta_add_conj_and_mul_conj (a : ℕ) (b c : ℤ) (d : ℕ) (h : CmOK a b c d) :
    cmTheta b d + conj (cmTheta b d) = b ∧ cmTheta b d * conj (cmTheta b d) = (a:ℂ) * c := by
  obtain ⟨h4, -, -, -⟩ := h
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have h4' : (4:ℂ) * a * c = (b:ℂ)^2 + d := by exact_mod_cast h4
  have hc : conj (cmTheta b d) = ((b:ℂ) - Complex.I * (Real.sqrt d : ℝ)) / 2 := by
    simp [cmTheta, map_div₀, Complex.conj_ofReal, map_ofNat]
    ring
  rw [hc]
  constructor
  · simp only [cmTheta]; ring
  · simp only [cmTheta]
    linear_combination (-((Real.sqrt d : ℝ) : ℂ)^2/4) * Complex.I_sq + (1/4) * hs - (1/4) * h4'

/- English proof (translation)
Introduce `hdvd`. Establish `hp : Prime (l:ℤ)` using `Nat.prime_iff_prime_int.mp hl`. Establish `hne : (l:ℤ) ^ g ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hl.ne_zero)`. Establish `h1 : (l:ℤ) ^ 3 ∣ ((M₄:ℤ) * n₁ * Q₀) * (2 * (2 * q + (l:ℤ) ^ k * p))`. Establish `e1 : (l:ℤ) ^ (g + 3) = (l:ℤ) ^ g * (l:ℤ) ^ 3` using `pow_add _ _ _`.

Establish `e2 : 2 * ((l ^ g * M₄ * n₁ : ℕ) : ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) = (l:ℤ) ^ g * (((M₄:ℤ) * n₁ * Q₀) * (2 * (2 * q + (l:ℤ) ^ k * p)))` using `by push_cast; ring`. Rewrite `hdvd` using `[e1, e2]`. Conclude with `(mul_dvd_mul_iff_left hne).mp hdvd`. Establish `hnd : ¬ (l:ℤ) ∣ ((M₄:ℤ) * n₁ * Q₀)`. Introduce `h`.

Break down `hp.dvd_or_dvd h with h | h` into its components or cases. Break down `hp.dvd_or_dvd h with h | h` into its components or cases. Conclude with `hM (Int.natCast_dvd_natCast.mp h)`. Conclude with `hn (Int.natCast_dvd_natCast.mp h)`. Conclude with `hQ h`.

Establish `h2` using `hp.pow_dvd_of_dvd_mul_left 3 hnd h1`. Establish `h3 : (l:ℤ) ^ 3 ∣ 2 * (l:ℤ) ^ k * p` using `Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ hk) _) _`. Establish `h4 : (l:ℤ) ^ 3 ∣ q * 4`. Establish `e3 : q * 4 = 2 * (2 * q + (l:ℤ) ^ k * p) - 2 * (l:ℤ) ^ k * p` using `by ring`. Rewrite using `[e3]`.

Conclude with `dvd_sub h2 h3`. Establish `h5` using `hp.pow_dvd_of_dvd_mul_left 3 hq h4`. Establish `h6` using `Int.le_of_dvd (by norm_num) h5`. Establish `hl2 : (2:ℤ) ≤ l` using `by exact_mod_cast hl.two_le`. Establish `h7 : (2:ℤ) ^ 3 ≤ (l:ℤ) ^ 3` using `by gcongr`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem not_pow_dvd_two_mul_mul_of_not_dvd (l : ℕ) (hl : Nat.Prime l) (g k : ℕ) (hk : 3 ≤ k) (M₄ n₁ : ℕ)
    (hM : ¬ l ∣ M₄) (hn : ¬ l ∣ n₁) (Q₀ p q : ℤ) (hQ : ¬ (l:ℤ) ∣ Q₀) (hq : ¬ (l:ℤ) ∣ q) :
    ¬ (l:ℤ) ^ (g + 3) ∣ 2 * ((l ^ g * M₄ * n₁ : ℕ) : ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) := by
  intro hdvd
  have hp : Prime (l:ℤ) := Nat.prime_iff_prime_int.mp hl
  have hne : (l:ℤ) ^ g ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  have h1 : (l:ℤ) ^ 3 ∣ ((M₄:ℤ) * n₁ * Q₀) * (2 * (2 * q + (l:ℤ) ^ k * p)) := by
    have e1 : (l:ℤ) ^ (g + 3) = (l:ℤ) ^ g * (l:ℤ) ^ 3 := pow_add _ _ _
    have e2 : 2 * ((l ^ g * M₄ * n₁ : ℕ) : ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) =
        (l:ℤ) ^ g * (((M₄:ℤ) * n₁ * Q₀) * (2 * (2 * q + (l:ℤ) ^ k * p))) := by
      push_cast; ring
    rw [e1, e2] at hdvd
    exact (mul_dvd_mul_iff_left hne).mp hdvd
  have hnd : ¬ (l:ℤ) ∣ ((M₄:ℤ) * n₁ * Q₀) := by
    intro h
    rcases hp.dvd_or_dvd h with h | h
    · rcases hp.dvd_or_dvd h with h | h
      · exact hM (Int.natCast_dvd_natCast.mp h)
      · exact hn (Int.natCast_dvd_natCast.mp h)
    · exact hQ h
  have h2 := hp.pow_dvd_of_dvd_mul_left 3 hnd h1
  have h3 : (l:ℤ) ^ 3 ∣ 2 * (l:ℤ) ^ k * p :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ hk) _) _
  have h4 : (l:ℤ) ^ 3 ∣ q * 4 := by
    have e3 : q * 4 = 2 * (2 * q + (l:ℤ) ^ k * p) - 2 * (l:ℤ) ^ k * p := by ring
    rw [e3]
    exact dvd_sub h2 h3
  have h5 := hp.pow_dvd_of_dvd_mul_left 3 hq h4
  have h6 := Int.le_of_dvd (by norm_num) h5
  have hl2 : (2:ℤ) ≤ l := by exact_mod_cast hl.two_le
  have h7 : (2:ℤ) ^ 3 ≤ (l:ℤ) ^ 3 := by gcongr
  linarith

/- English proof (translation)
Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg z`. Simplify `h` using `[natCast_zsmul]`. Simplify `h` using `[natCast_zsmul]`.
-/
private theorem natAbs_smul_mem_of_zsmul_mem {V : Type} [AddCommGroup V] (Λ : AddSubgroup V) (z : ℤ) (v : V)
    (h : z • v ∈ Λ) : z.natAbs • v ∈ Λ := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · simpa [natCast_zsmul] using h
  · simpa [natCast_zsmul] using h

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply]`. Simplify using `only [zsmul_eq_mul, nsmul_eq_mul, smul_eq_mul]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem zsmul_affine_combination_eq {m : Type} (w f : m → ℂ) (E₀ P : ℤ) (n₁ M₃ l t h : ℕ) (hE : (E₀:ℂ) ≠ 0) :
    (E₀ * n₁ * M₃ : ℤ) • (w + ((l:ℂ) ^ (t + h) * P / E₀) • (f - w)) =
      (M₃ * E₀ - (l:ℤ) ^ (t + h) * P * M₃) • (n₁ • w) + ((l:ℤ) ^ t * P * n₁) • ((l ^ h * M₃) • f) := by
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
  simp only [zsmul_eq_mul, nsmul_eq_mul, smul_eq_mul]
  push_cast
  field_simp
  ring

/- English proof (translation)
Introduce `a b c d ha hd lam hlam m _ _ Λ l x y T i₀ hK`. Take `⟨hcm, -, -, hr1, hr2, hl, hQ, hi₀, -⟩` from `hK`. Establish `hl1 : l ≠ 1` using `hl.one_lt.ne'`. Take `⟨g, M₄, hM₄, hM₁⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hr1 l hl1`. Take `⟨h, M₃, hM₃, hM₂⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hr2 l hl1`.

Use `⟨g + h + 3, fun k hk w hw => ?_⟩` and prove the remaining obligations. Take `⟨⟨n₁, hn₁, hn₁w⟩, hzero, p, q, hlq, hHw⟩` from `hw`. Take `⟨hθs, hθp⟩` from `cmTheta_add_conj_and_mul_conj a b c d hcm`. Use `set L := cmL a b d ha hd lam hlam with hLdef`. Use `set θ := cmTheta b d with hθdef`.

Use `set φ : ℂ := lam * (↑x * ↑a + ↑y * θ) with hφ`. Establish `hf : fvec a b d lam x y i₀ = Pi.single i₀ φ` using `rfl`. Rewrite `hHw`, the goal using `[hf]`. Establish `hω1 : L.ω₁ = lam * a` using `rfl`. Establish `hω2 : L.ω₂ = lam * θ` using `rfl`.

Establish `hwstd : (relIdx (stdLat L m) Λ) • (n₁ • w) ∈ stdLat L m` using `AddSubgroup.nsmul_relIndex_mem (stdLat L m) hn₁w`. Rewrite `hwstd` using `[hM₁]`. Establish `hw0` using `(AddSubgroup.mem_pi _).mp hwstd i₀ (Set.mem_univ _)`. Take `⟨α, β, hαβ⟩` from `PeriodPair.mem_lattice.mp hw0`. Use `set N₁ : ℕ := l ^ g * M₄ * n₁ with hN₁`.

Establish `hwi : (N₁:ℂ) * w i₀ = lam * (α * a + β * θ)`. Establish `e : ((l ^ g * M₄) • n₁ • w) i₀ = (N₁:ℂ) * w i₀`. Simplify using `[hN₁, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e, ← hαβ, hω1, hω2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hfΛ : (relIdx Λ (stdLat L m)) • (Pi.single i₀ φ) ∈ Λ`. Apply `AddSubgroup.nsmul_relIndex_mem Λ` to reduce the goal to its premises. Rewrite using `[stdLat, AddSubgroup.mem_pi]`. Introduce `i _`.

Distinguish the cases in `hi : i = i₀`. Substitute `hi` using the available equality. Simplify using `only [Pi.single_eq_same]`. Conclude with `PeriodPair.mem_lattice.mpr ⟨x, y, by rw [hω1, hω2, hφ]; ring⟩`. Simplify using `[Pi.single_eq_of_ne hi]`.

Rewrite `hfΛ` using `[hM₂]`. Use `set A : ℂ := ((area L : ℂ))⁻¹ with hA`. Use `set Q₀ : ℤ := ↑a * x ^ 2 + b * x * y + c * y ^ 2 with hQ₀`. Use `set γ : ℤ := 2 * α * x * a + (α * y + β * x) * b + 2 * β * y * c with hγ`. Use `set κ : ℂ := A * (lam * conj lam * a) with hκ`.

Establish `hcφ : conj φ = conj lam * (x * a + y * conj θ)` using `by simp [hφ]`. Establish `hff : stdH L m (Pi.single i₀ φ) (Pi.single i₀ φ) = κ * Q₀`. Rewrite using `[(sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg L m i₀ φ _).1]`. Simplify using `only [Pi.single_eq_same]`. Rewrite using `[hcφ, hφ, hκ, hQ₀]`.

Use `push_cast`. Take the linear combination `(A * lam * conj lam * x * y * a) * hθs + (A * lam * conj lam * y ^ 2) * hθp`. Establish `hwc : (N₁:ℂ) * conj (w i₀) = conj lam * (α * a + β * conj θ)`. Use `congrArg (starRingEnd ℂ) hwi` as an intermediate fact. Simplify using `using this`.

Establish `hX : (N₁:ℂ) * (stdH L m (Pi.single i₀ φ) w + stdH L m w (Pi.single i₀ φ)) = κ * γ`. Rewrite using `[(sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg L m i₀ φ w).1, (sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg L m i₀ φ w).2, hcφ, hφ, hκ, hγ]`. Use `push_cast`. Take the linear combination `(A * lam * (x * a + y * θ)) * hwc + (A * conj lam * (x * a + y * conj θ)) * hwi + (A * lam * conj lam * a * (x * β + y * α)) * hθs + (A * lam * conj lam * 2 * β * y) * hθp`. Establish `hww : stdH L m w w = κ * Q₀ * (1 + (l:ℂ) ^ k * p / q)` using `by rw [hHw, hff]`.

Establish `hsum` using `not_pow_dvd_two_mul_mul_of_not_dvd l hl g k (by omega) M₄ n₁ hM₄ hn₁ Q₀ p q hQ hlq`. Choose the witnesses or unpack the hypotheses as in `⟨w', γ', hw'Λ, hw'z, hw'w, hw'X, hndv⟩ : ∃ (w' : m → ℂ) (γ' : ℤ), n₁ • w' ∈ Λ ∧ (∀ j ∈ T, w' j = 0) ∧ stdH L m w' w' = κ * Q₀ * (1 + (l:ℂ) ^ k * p / q) ∧ (N₁:ℂ) * (stdH L m (Pi.single i₀ φ) w' + stdH L m w' (Pi.single i₀ φ)) = κ * γ' ∧ ¬ (l:ℤ) ^ (g + 3) ∣ (N₁:ℤ) * Q₀ * (2 * q + ( …`. Distinguish the cases in `hE : (l:ℤ) ^ (g + 3) ∣ (N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ * q`. Use `⟨-w, -γ, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_neg]`.

Conclude with `neg_mem hn₁w`. Introduce `j hj`. Simplify using `[hzero j hj]`. Simplify using `[hww]`. Simplify using `only [map_neg, LinearMap.neg_apply]`.

Use `push_cast`. Take the linear combination `-hX`. Introduce `hE'`. Apply `hsum` to reduce the goal to its premises. Establish `e : 2 * ((l ^ g * M₄ * n₁ : ℕ) : ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) = ((N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ * q) + ((N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - (-γ) * q)`.

Rewrite using `[hN₁]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_add hE hE'`.

Conclude with `⟨w, γ, hn₁w, hzero, hww, hX, hE⟩`. Use `set E : ℤ := (N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ' * q with hEdef`. Establish `hE0 : E ≠ 0` using `fun h0 => hndv (h0 ▸ dvd_zero _)`. Take `⟨j, e₀, he₀, hEabs⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hE0) l hl1`. Establish `hj : j ≤ g + 2`.

Assume the negation of the conclusion as `hj`. Apply `hndv` to reduce the goal to its premises. Establish `h1 : l ^ (g + 3) ∣ E.natAbs` using `hEabs ▸ Dvd.dvd.mul_right (pow_dvd_pow l (by omega)) _`. Establish `h2 : ((l ^ (g + 3) : ℕ) : ℤ) ∣ E` using `Int.natCast_dvd.mpr h1`. Simplify using `using h2`.

Use `set E₀ : ℤ := E.sign * e₀ with hE₀def`. Establish `hEE : E = (l:ℤ) ^ j * E₀` using `by conv_lhs => rw [← Int.sign_mul_natAbs E, hEabs]`. Rewrite using `[hE₀def]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hE₀ : ¬ (l:ℤ) ∣ E₀`. Introduce `hd'`. Apply `he₀` to reduce the goal to its premises. Establish `h1` using `Int.natCast_dvd.mp hd'`. Rewrite `h1` using `[hE₀def, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hE0, one_mul, Int.natAbs_natCast]`. Then use the resulting hypothesis.

Establish `hE₀ne : (E₀:ℂ) ≠ 0`. Establish `: E₀ ≠ 0` using `fun h0 => hE₀ (h0 ▸ dvd_zero _)`. Conclude with `this` after adjusting the coercions. Establish `hqne : (q:ℂ) ≠ 0`. Establish `: q ≠ 0` using `fun h0 => hlq (h0 ▸ dvd_zero _)`.

Conclude with `this` after adjusting the coercions. Establish `hN₁ne : (N₁:ℂ) ≠ 0`. Establish `hM₄0 : M₄ ≠ 0` using `by rintro rfl; exact hM₄ (dvd_zero _)`. Establish `hn₁0 : n₁ ≠ 0` using `by rintro rfl; exact hn₁ (dvd_zero _)`. Establish `: N₁ ≠ 0`.

Rewrite using `[hN₁]`. Conclude with `mul_ne_zero (mul_ne_zero (pow_ne_zero _ hl.ne_zero) hM₄0) hn₁0`. Conclude with `this` after adjusting the coercions. Use `set t := k - j - h with ht`. Establish `hkj : k - j = t + h` using `by omega`.

Use `set P : ℤ := Q₀ * p * N₁ with hP`. Use `set rc : ℂ := (l:ℂ) ^ (k - j) * P / E₀ with hrcdef`. Establish `hrc : conj rc = rc`. Rewrite using `[hrcdef]`. Simplify using `[map_div₀]`.

Establish `hrD : rc * (N₁ * (2 * (Q₀:ℂ) + Q₀ * ((l:ℂ) ^ k * p / q)) - γ') = N₁ * Q₀ * ((l:ℂ) ^ k * p / q)`. Establish `hEc : (E:ℂ) = (l:ℂ) ^ j * E₀` using `by exact_mod_cast hEE`. Establish `hEc2 : (E:ℂ) = N₁ * Q₀ * (2 * q + (l:ℂ) ^ k * p) - γ' * q`. Rewrite using `[hEdef]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hpow : (l:ℂ) ^ k = (l:ℂ) ^ (k - j) * (l:ℂ) ^ j`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Establish `e1 : (N₁:ℂ) * (2 * (Q₀:ℂ) + Q₀ * ((l:ℂ) ^ k * p / q)) - γ' = (l:ℂ) ^ j * E₀ / q`. Rewrite using `[← hEc, hEc2]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Rewrite using `[e1, hrcdef, hP, hpow]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Use `⟨w' + rc • (Pi.single i₀ φ - w'), ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hmem : (E₀ * n₁ * M₃ : ℤ) • (w' + rc • (Pi.single i₀ φ - w')) ∈ Λ`.

Establish `key : (E₀ * n₁ * M₃ : ℤ) • (w' + rc • (Pi.single i₀ φ - w')) = (M₃ * E₀ - (l:ℤ) ^ (k - j) * P * M₃) • (n₁ • w') + ((l:ℤ) ^ t * P * n₁) • ((l ^ h * M₃) • Pi.single i₀ φ)`. Rewrite using `[hrcdef, hkj]`. Conclude with `zsmul_affine_combination_eq w' (Pi.single i₀ φ) E₀ P n₁ M₃ l t h hE₀ne`. Rewrite using `[key]`. Conclude with `add_mem (AddSubgroup.zsmul_mem _ hw'Λ _) (AddSubgroup.zsmul_mem _ hfΛ _)`.

Use `⟨(E₀ * n₁ * M₃).natAbs, ?_, natAbs_smul_mem_of_zsmul_mem Λ _ _ hmem⟩` and prove the remaining obligations. Introduce `hd'`. Establish `hp : Prime (l:ℤ)` using `Nat.prime_iff_prime_int.mp hl`. Establish `h1 : (l:ℤ) ∣ E₀ * n₁ * M₃` using `Int.natCast_dvd.mpr hd'`. Break down `hp.dvd_or_dvd h1 with h2 | h2` into its components or cases.

Break down `hp.dvd_or_dvd h2 with h3 | h3` into its components or cases. Conclude with `hE₀ h3`. Conclude with `hn₁ (Int.natCast_dvd_natCast.mp h3)`. Conclude with `hM₃ (Int.natCast_dvd_natCast.mp h2)`. Introduce `j' hj'`.

Establish `hne : j' ≠ i₀` using `fun h' => hi₀ (h' ▸ hj')`. Simplify using `[hw'z j' hj', Pi.single_eq_of_ne hne]`. Rewrite using `[H_affine_combination_eq_of_quadratic_relation (stdH L m) (Pi.single i₀ φ) w' κ rc Q₀ N₁ γ' ((l:ℂ) ^ k * p / q) hN₁ne hff hw'w hw'X hrc hrD, hff]`.
-/
theorem keyExact : KeyExact := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ hK
  obtain ⟨hcm, -, -, hr1, hr2, hl, hQ, hi₀, -⟩ := hK
  have hl1 : l ≠ 1 := hl.one_lt.ne'
  obtain ⟨g, M₄, hM₄, hM₁⟩ := Nat.exists_eq_pow_mul_and_not_dvd hr1 l hl1
  obtain ⟨h, M₃, hM₃, hM₂⟩ := Nat.exists_eq_pow_mul_and_not_dvd hr2 l hl1
  refine ⟨g + h + 3, fun k hk w hw => ?_⟩
  obtain ⟨⟨n₁, hn₁, hn₁w⟩, hzero, p, q, hlq, hHw⟩ := hw
  obtain ⟨hθs, hθp⟩ := cmTheta_add_conj_and_mul_conj a b c d hcm
  set L := cmL a b d ha hd lam hlam with hLdef
  set θ := cmTheta b d with hθdef
  set φ : ℂ := lam * (↑x * ↑a + ↑y * θ) with hφ
  have hf : fvec a b d lam x y i₀ = Pi.single i₀ φ := rfl
  rw [hf] at hHw ⊢
  have hω1 : L.ω₁ = lam * a := rfl
  have hω2 : L.ω₂ = lam * θ := rfl
  have hwstd : (relIdx (stdLat L m) Λ) • (n₁ • w) ∈ stdLat L m :=
    AddSubgroup.nsmul_relIndex_mem (stdLat L m) hn₁w
  rw [hM₁] at hwstd
  have hw0 := (AddSubgroup.mem_pi _).mp hwstd i₀ (Set.mem_univ _)
  obtain ⟨α, β, hαβ⟩ := PeriodPair.mem_lattice.mp hw0
  set N₁ : ℕ := l ^ g * M₄ * n₁ with hN₁
  have hwi : (N₁:ℂ) * w i₀ = lam * (α * a + β * θ) := by
    have e : ((l ^ g * M₄) • n₁ • w) i₀ = (N₁:ℂ) * w i₀ := by
      simp [hN₁, nsmul_eq_mul]
      ring
    rw [← e, ← hαβ, hω1, hω2]
    ring
  have hfΛ : (relIdx Λ (stdLat L m)) • (Pi.single i₀ φ) ∈ Λ := by
    apply AddSubgroup.nsmul_relIndex_mem Λ
    rw [stdLat, AddSubgroup.mem_pi]
    intro i _
    by_cases hi : i = i₀
    · subst hi
      simp only [Pi.single_eq_same]
      exact PeriodPair.mem_lattice.mpr ⟨x, y, by rw [hω1, hω2, hφ]; ring⟩
    · simp [Pi.single_eq_of_ne hi]
  rw [hM₂] at hfΛ
  set A : ℂ := ((area L : ℂ))⁻¹ with hA
  set Q₀ : ℤ := ↑a * x ^ 2 + b * x * y + c * y ^ 2 with hQ₀
  set γ : ℤ := 2 * α * x * a + (α * y + β * x) * b + 2 * β * y * c with hγ
  set κ : ℂ := A * (lam * conj lam * a) with hκ
  have hcφ : conj φ = conj lam * (x * a + y * conj θ) := by simp [hφ]
  have hff : stdH L m (Pi.single i₀ φ) (Pi.single i₀ φ) = κ * Q₀ := by
    rw [(sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg L m i₀ φ _).1]
    simp only [Pi.single_eq_same]
    rw [hcφ, hφ, hκ, hQ₀]
    push_cast
    linear_combination (A * lam * conj lam * x * y * a) * hθs + (A * lam * conj lam * y ^ 2) * hθp
  have hwc : (N₁:ℂ) * conj (w i₀) = conj lam * (α * a + β * conj θ) := by
    have := congrArg (starRingEnd ℂ) hwi
    simpa using this
  have hX : (N₁:ℂ) * (stdH L m (Pi.single i₀ φ) w + stdH L m w (Pi.single i₀ φ)) = κ * γ := by
    rw [(sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg L m i₀ φ w).1, (sum_sum_sub_isotropic_shift_eq_of_conj_eq_neg L m i₀ φ w).2, hcφ, hφ, hκ, hγ]
    push_cast
    linear_combination (A * lam * (x * a + y * θ)) * hwc +
      (A * conj lam * (x * a + y * conj θ)) * hwi +
      (A * lam * conj lam * a * (x * β + y * α)) * hθs + (A * lam * conj lam * 2 * β * y) * hθp
  have hww : stdH L m w w = κ * Q₀ * (1 + (l:ℂ) ^ k * p / q) := by rw [hHw, hff]
  have hsum := not_pow_dvd_two_mul_mul_of_not_dvd l hl g k (by omega) M₄ n₁ hM₄ hn₁ Q₀ p q hQ hlq
  obtain ⟨w', γ', hw'Λ, hw'z, hw'w, hw'X, hndv⟩ : ∃ (w' : m → ℂ) (γ' : ℤ), n₁ • w' ∈ Λ ∧
      (∀ j ∈ T, w' j = 0) ∧ stdH L m w' w' = κ * Q₀ * (1 + (l:ℂ) ^ k * p / q) ∧
      (N₁:ℂ) * (stdH L m (Pi.single i₀ φ) w' + stdH L m w' (Pi.single i₀ φ)) = κ * γ' ∧
      ¬ (l:ℤ) ^ (g + 3) ∣ (N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ' * q := by
    by_cases hE : (l:ℤ) ^ (g + 3) ∣ (N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ * q
    · refine ⟨-w, -γ, ?_, ?_, ?_, ?_, ?_⟩
      · rw [smul_neg]; exact neg_mem hn₁w
      · intro j hj; simp [hzero j hj]
      · simp [hww]
      · simp only [map_neg, LinearMap.neg_apply]
        push_cast
        linear_combination -hX
      · intro hE'
        apply hsum
        have e : 2 * ((l ^ g * M₄ * n₁ : ℕ) : ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) =
            ((N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ * q) +
            ((N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - (-γ) * q) := by
          rw [hN₁]
          push_cast
          ring
        rw [e]
        exact dvd_add hE hE'
    · exact ⟨w, γ, hn₁w, hzero, hww, hX, hE⟩
  set E : ℤ := (N₁:ℤ) * Q₀ * (2 * q + (l:ℤ) ^ k * p) - γ' * q with hEdef
  have hE0 : E ≠ 0 := fun h0 => hndv (h0 ▸ dvd_zero _)
  obtain ⟨j, e₀, he₀, hEabs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hE0) l hl1
  have hj : j ≤ g + 2 := by
    by_contra hj
    apply hndv
    have h1 : l ^ (g + 3) ∣ E.natAbs := hEabs ▸ Dvd.dvd.mul_right (pow_dvd_pow l (by omega)) _
    have h2 : ((l ^ (g + 3) : ℕ) : ℤ) ∣ E := Int.natCast_dvd.mpr h1
    simpa using h2
  set E₀ : ℤ := E.sign * e₀ with hE₀def
  have hEE : E = (l:ℤ) ^ j * E₀ := by
    conv_lhs => rw [← Int.sign_mul_natAbs E, hEabs]
    rw [hE₀def]
    push_cast
    ring
  have hE₀ : ¬ (l:ℤ) ∣ E₀ := by
    intro hd'
    apply he₀
    have h1 := Int.natCast_dvd.mp hd'
    rwa [hE₀def, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hE0, one_mul, Int.natAbs_natCast] at h1
  have hE₀ne : (E₀:ℂ) ≠ 0 := by
    have : E₀ ≠ 0 := fun h0 => hE₀ (h0 ▸ dvd_zero _)
    exact_mod_cast this
  have hqne : (q:ℂ) ≠ 0 := by
    have : q ≠ 0 := fun h0 => hlq (h0 ▸ dvd_zero _)
    exact_mod_cast this
  have hN₁ne : (N₁:ℂ) ≠ 0 := by
    have hM₄0 : M₄ ≠ 0 := by rintro rfl; exact hM₄ (dvd_zero _)
    have hn₁0 : n₁ ≠ 0 := by rintro rfl; exact hn₁ (dvd_zero _)
    have : N₁ ≠ 0 := by
      rw [hN₁]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hl.ne_zero) hM₄0) hn₁0
    exact_mod_cast this
  set t := k - j - h with ht
  have hkj : k - j = t + h := by omega
  set P : ℤ := Q₀ * p * N₁ with hP
  set rc : ℂ := (l:ℂ) ^ (k - j) * P / E₀ with hrcdef
  have hrc : conj rc = rc := by
    rw [hrcdef]
    simp [map_div₀]
  have hrD : rc * (N₁ * (2 * (Q₀:ℂ) + Q₀ * ((l:ℂ) ^ k * p / q)) - γ') =
      N₁ * Q₀ * ((l:ℂ) ^ k * p / q) := by
    have hEc : (E:ℂ) = (l:ℂ) ^ j * E₀ := by exact_mod_cast hEE
    have hEc2 : (E:ℂ) = N₁ * Q₀ * (2 * q + (l:ℂ) ^ k * p) - γ' * q := by
      rw [hEdef]; push_cast; ring
    have hpow : (l:ℂ) ^ k = (l:ℂ) ^ (k - j) * (l:ℂ) ^ j := by
      rw [← pow_add]; congr 1; omega
    have e1 : (N₁:ℂ) * (2 * (Q₀:ℂ) + Q₀ * ((l:ℂ) ^ k * p / q)) - γ' = (l:ℂ) ^ j * E₀ / q := by
      rw [← hEc, hEc2]
      field_simp
      try ring
    rw [e1, hrcdef, hP, hpow]
    push_cast
    field_simp
    try ring
  refine ⟨w' + rc • (Pi.single i₀ φ - w'), ?_, ?_, ?_⟩
  · have hmem : (E₀ * n₁ * M₃ : ℤ) • (w' + rc • (Pi.single i₀ φ - w')) ∈ Λ := by
      have key : (E₀ * n₁ * M₃ : ℤ) • (w' + rc • (Pi.single i₀ φ - w')) =
          (M₃ * E₀ - (l:ℤ) ^ (k - j) * P * M₃) • (n₁ • w') +
          ((l:ℤ) ^ t * P * n₁) • ((l ^ h * M₃) • Pi.single i₀ φ) := by
        rw [hrcdef, hkj]
        exact zsmul_affine_combination_eq w' (Pi.single i₀ φ) E₀ P n₁ M₃ l t h hE₀ne
      rw [key]
      exact add_mem (AddSubgroup.zsmul_mem _ hw'Λ _) (AddSubgroup.zsmul_mem _ hfΛ _)
    refine ⟨(E₀ * n₁ * M₃).natAbs, ?_, natAbs_smul_mem_of_zsmul_mem Λ _ _ hmem⟩
    intro hd'
    have hp : Prime (l:ℤ) := Nat.prime_iff_prime_int.mp hl
    have h1 : (l:ℤ) ∣ E₀ * n₁ * M₃ := Int.natCast_dvd.mpr hd'
    rcases hp.dvd_or_dvd h1 with h2 | h2
    · rcases hp.dvd_or_dvd h2 with h3 | h3
      · exact hE₀ h3
      · exact hn₁ (Int.natCast_dvd_natCast.mp h3)
    · exact hM₃ (Int.natCast_dvd_natCast.mp h2)
  · intro j' hj'
    have hne : j' ≠ i₀ := fun h' => hi₀ (h' ▸ hj')
    simp [hw'z j' hj', Pi.single_eq_of_ne hne]
  · rw [H_affine_combination_eq_of_quadratic_relation (stdH L m) (Pi.single i₀ φ) w' κ rc Q₀ N₁ γ' ((l:ℂ) ^ k * p / q) hN₁ne hff hw'w
      hw'X hrc hrD, hff]

end PI.UnitaryGroupMassFormula.UnimodLocStd
