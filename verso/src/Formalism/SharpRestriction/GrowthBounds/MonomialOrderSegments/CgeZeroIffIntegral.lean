import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MemPolKIff

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))

/- English proof (translation)
Apply the tactic sequence `cases u <;> cases w <;> simp`.
-/
private lemma map_ratCast_le_map_ratCast_iff {u w : WithTop ℚ} :
    u.map (fun n : ℚ => (n : ℝ)) ≤ w.map (fun n : ℚ => (n : ℝ)) ↔ u ≤ w := by
  cases u <;> cases w <;> simp

/- English proof (translation)
The claim follows from `map_ratCast_le_map_ratCast_iff`.
-/
private lemma vR_le_vR_iff {x y : K} : vR v x ≤ vR v y ↔ v x ≤ v y := map_ratCast_le_map_ratCast_iff

/- English proof (translation)
Unfold `vge vR`. Simplify using the standard rewrite rules.
-/
theorem vge_zero (a : ℝ) : vge v a (0 : K) := by
  unfold vge vR
  simp

/- English proof (translation)
Unfold `vge at *`. Conclude with `le_trans (WithTop.coe_le_coe.mpr h) hx`.
-/
theorem vge_mono {a b : ℝ} {x : K} (h : b ≤ a) (hx : vge v a x) : vge v b x := by
  unfold vge at *
  exact le_trans (WithTop.coe_le_coe.mpr h) hx

/- English proof (translation)
Unfold `vle at *`. Conclude with `le_trans hx (WithTop.coe_le_coe.mpr h)`.
-/
theorem vle_mono {a b : ℝ} {x : K} (h : a ≤ b) (hx : vle v a x) : vle v b x := by
  unfold vle at *
  exact le_trans hx (WithTop.coe_le_coe.mpr h)

/- English proof (translation)
Unfold `vge vR`. Apply the tactic sequence `cases h : v x <;> simp`.
-/
theorem vge_rat_iff (n : ℚ) (x : K) : vge v (n : ℝ) x ↔ (n : WithTop ℚ) ≤ v x := by
  unfold vge vR
  cases h : v x <;> simp

/- English proof (translation)
Unfold `vge vR`. Apply the tactic sequence `cases h : v x <;> simp`.
-/
theorem vge_zero_iff (x : K) : vge v 0 x ↔ 0 ≤ v x := by
  unfold vge vR
  cases h : v x <;> simp

/- English proof (translation)
Use `vge_rat_iff v (c : ℚ) x` as an intermediate fact. Simplify using `using this`.
-/
theorem vge_natCast_bound (c : ℕ) (x : K) : vge v (c : ℝ) x ↔ ((c : ℕ) : WithTop ℚ) ≤ v x := by
  have := vge_rat_iff v (c : ℚ) x
  simpa using this

/- English proof (translation)
Unfold `vge at *`. Establish `hm` using `v.map_add x y`. Break down `le_total (v x) (v y) with h | h` into its components or cases. Rewrite `hm` using `[min_eq_left h]`. Conclude with `hx.trans ((vR_le_vR_iff v).mpr hm)`.

Rewrite `hm` using `[min_eq_right h]`. Conclude with `hy.trans ((vR_le_vR_iff v).mpr hm)`.
-/
theorem vge_add {a : ℝ} {x y : K} (hx : vge v a x) (hy : vge v a y) : vge v a (x + y) := by
  unfold vge at *
  have hm := v.map_add x y
  rcases le_total (v x) (v y) with h | h
  · rw [min_eq_left h] at hm
    exact hx.trans ((vR_le_vR_iff v).mpr hm)
  · rw [min_eq_right h] at hm
    exact hy.trans ((vR_le_vR_iff v).mpr hm)

/- English proof (translation)
Unfold `vge vR at *`. Rewrite using `[AddValuation.map_neg]` and apply the resulting hypothesis.
-/
theorem vge_neg {a : ℝ} {x : K} (hx : vge v a x) : vge v a (-x) := by
  unfold vge vR at *
  rwa [AddValuation.map_neg]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `vge_add v hx (vge_neg v hy)`.
-/
theorem vge_sub {a : ℝ} {x y : K} (hx : vge v a x) (hy : vge v a y) : vge v a (x - y) := by
  rw [sub_eq_add_neg]
  exact vge_add v hx (vge_neg v hy)

/- English proof (translation)
The claim follows from `Finset.sum_induction f (vge v a) (fun _ _ => vge_add v) (vge_zero v a) h`.
-/
theorem vge_sum {ι : Type*} {a : ℝ} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, vge v a (f i)) :
    vge v a (∑ i ∈ s, f i) := Finset.sum_induction f (vge v a) (fun _ _ => vge_add v) (vge_zero v a) h

/- English proof (translation)
Unfold `vR`. Rewrite using `[AddValuation.map_mul]`. Apply the tactic sequence `cases h1 : v x <;> cases h2 : v y`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite using `[← WithTop.coe_add, WithTop.map_coe, WithTop.map_coe, WithTop.map_coe, Rat.cast_add, WithTop.coe_add]`.
-/
theorem vR_mul (x y : K) : vR v (x * y) = vR v x + vR v y := by
  unfold vR
  rw [AddValuation.map_mul]
  cases h1 : v x <;> cases h2 : v y
  · simp
  · simp
  · simp
  · rw [← WithTop.coe_add, WithTop.map_coe, WithTop.map_coe, WithTop.map_coe, Rat.cast_add,
      WithTop.coe_add]

/- English proof (translation)
Unfold `vge at *`. Rewrite using `[vR_mul, WithTop.coe_add]`. Conclude with `add_le_add hx hy`.
-/
theorem vge_mul {a b : ℝ} {x y : K} (hx : vge v a x) (hy : vge v b y) : vge v (a + b) (x * y) := by
  unfold vge at *
  rw [vR_mul, WithTop.coe_add]
  exact add_le_add hx hy

/- English proof (translation)
Unfold `vle at *`. Rewrite using `[vR_mul, WithTop.coe_add]`. Conclude with `add_le_add hx hy`.
-/
theorem vle_mul {a b : ℝ} {x y : K} (hx : vle v a x) (hy : vle v b y) : vle v (a + b) (x * y) := by
  unfold vle at *
  rw [vR_mul, WithTop.coe_add]
  exact add_le_add hx hy

/- English proof (translation)
Unfold `vge vR`. Simplify using the standard rewrite rules.
-/
theorem vge_one : vge v 0 (1 : K) := by
  unfold vge vR
  simp

/- English proof (translation)
Unfold `vle vge at *`. Establish `hlt : vR v x < vR v y` using `lt_of_le_of_lt hx (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hab) hy)`. Establish `hlt' : v x < v y` using `not_le.mp fun h => absurd ((vR_le_vR_iff v).mpr h) (not_le.mpr hlt)`. Establish `e : vR v (x + y) = vR v x`. Unfold `vR`.

Rewrite using `[AddValuation.map_add_eq_of_lt_left v hlt']`. Rewrite using `[e]`. Conclude with `hx`.
-/
theorem vle_add_of_lt {a b : ℝ} {x y : K} (hx : vle v a x) (hy : vge v b y) (hab : a < b) :
    vle v a (x + y) := by
  unfold vle vge at *
  have hlt : vR v x < vR v y :=
    lt_of_le_of_lt hx (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hab) hy)
  have hlt' : v x < v y :=
    not_le.mp fun h => absurd ((vR_le_vR_iff v).mpr h) (not_le.mpr hlt)
  have e : vR v (x + y) = vR v x := by
    unfold vR
    rw [AddValuation.map_add_eq_of_lt_left v hlt']
  rw [e]
  exact hx

/- English proof (translation)
Introduce `α`. Rewrite using `[MvPolynomial.coeff_zero]`. Conclude with `vge_zero v a`.
-/
theorem cge_zero {σ : Type} (a : ℝ) : cge v a (0 : MvPolynomial σ K) := by
  intro α
  rw [MvPolynomial.coeff_zero]
  exact vge_zero v a

/- English proof (translation)
Introduce `α` and use `vge_mono v h (hF α)`.
-/
theorem cge_mono {σ : Type} {a b : ℝ} {F : MvPolynomial σ K} (h : b ≤ a) (hF : cge v a F) :
    cge v b F := fun α => vge_mono v h (hF α)

/- English proof (translation)
Introduce `α`. Rewrite using `[MvPolynomial.coeff_add]`. Conclude with `vge_add v (hF α) (hG α)`.
-/
theorem cge_add {σ : Type} {a : ℝ} {F G : MvPolynomial σ K} (hF : cge v a F) (hG : cge v a G) :
    cge v a (F + G) := by
  intro α
  rw [MvPolynomial.coeff_add]
  exact vge_add v (hF α) (hG α)

/- English proof (translation)
Introduce `α`. Rewrite using `[MvPolynomial.coeff_sum]`. Conclude with `vge_sum v s _ fun i hi => h i hi α`.
-/
theorem cge_sum {σ ι : Type} {a : ℝ} (s : Finset ι) (f : ι → MvPolynomial σ K)
    (h : ∀ i ∈ s, cge v a (f i)) : cge v a (∑ i ∈ s, f i) := by
  intro α
  rw [MvPolynomial.coeff_sum]
  exact vge_sum v s _ fun i hi => h i hi α

/- English proof (translation)
Introduce `α`. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul]`. Conclude with `vge_mul v hc (hF α)`.
-/
theorem cge_smul {σ : Type} {a b : ℝ} {c : K} {F : MvPolynomial σ K} (hc : vge v a c)
    (hF : cge v b F) : cge v (a + b) (c • F) := by
  intro α
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  exact vge_mul v hc (hF α)

/- English proof (translation)
Introduce `β`. Rewrite using `[MvPolynomial.coeff_monomial]`. Use `split_ifs`. Conclude with `hc`. Conclude with `vge_zero v a`.
-/
theorem cge_monomial {σ : Type} {a : ℝ} {c : K} (α : σ →₀ ℕ) (hc : vge v a c) :
    cge v a (monomial α c) := by
  classical
  intro β
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact hc
  · exact vge_zero v a

/- English proof (translation)
The claim follows from `forall_congr' fun α => vge_zero_iff v _`.
-/
theorem cge_zero_iff_Integral {σ : Type} (F : MvPolynomial σ K) : cge v 0 F ↔ Integral v F := forall_congr' fun α => vge_zero_iff v _

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial α c`. Establish `e : monomial α c = c • (basisMonomials σ K) α`. Rewrite using `[coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]`. Unfold `dg`.

Rewrite using `[e, map_smul, Module.Basis.constr_basis, coe_basisMonomials]`. Simplify using `only [coeff_smul, coeff_monomial, smul_eq_mul]`. Use `split_ifs with h`. Substitute `h` using the available equality. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Consider the case `add F G hF hG => rw [map_add, coeff_add, coeff_add, hF, hG, mul_add]`.
-/
private lemma coeff_dg_eq_mul_coeff {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) (β : σ →₀ ℕ) :
    (dg f F).coeff β = f β * F.coeff β := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial α c =>
    have e : monomial α c = c • (basisMonomials σ K) α := by
      rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    unfold dg
    rw [e, map_smul, Module.Basis.constr_basis, coe_basisMonomials]
    simp only [coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · subst h
      ring
    · simp
  | add F G hF hG => rw [map_add, coeff_add, coeff_add, hF, hG, mul_add]

/- English proof (translation)
Introduce `β`. Rewrite using `[coeff_dg_eq_mul_coeff]`. Conclude with `vge_mul v (hf β) (hF β)`.
-/
theorem cge_dg {σ : Type} {a b : ℝ} {f : (σ →₀ ℕ) → K} {F : MvPolynomial σ K}
    (hf : ∀ α, vge v a (f α)) (hF : cge v b F) : cge v (a + b) (dg f F) := by
  intro β
  rw [coeff_dg_eq_mul_coeff]
  exact vge_mul v (hf β) (hF β)

/- English proof (translation)
Introduce `α`. Rewrite using `[MvPolynomial.coeff_mul]`. Conclude with `vge_sum v _ _ fun x _ => vge_mul v (hF _) (hG _)`.
-/
theorem cge_mul {σ : Type} {a b : ℝ} {F G : MvPolynomial σ K} (hF : cge v a F) (hG : cge v b G) :
    cge v (a + b) (F * G) := by
  classical
  intro α
  rw [MvPolynomial.coeff_mul]
  exact vge_sum v _ _ fun x _ => vge_mul v (hF _) (hG _)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Use `push_cast`. Conclude with `le_trans (le_min ih (by simp)) (v.map_add _ _)`.
-/
theorem v_natCast_nonneg (n : ℕ) : 0 ≤ v (n : K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact le_trans (le_min ih (by simp)) (v.map_add _ _)

/- English proof (translation)
Consider the cases of `z with`. Consider the case `ofNat n => simpa using v_natCast_nonneg v n`. Consider the case `negSucc n`. Rewrite using `[Int.cast_negSucc, AddValuation.map_neg]`. Conclude with `v_natCast_nonneg v (n + 1)`.
-/
theorem v_intCast_nonneg (z : ℤ) : 0 ≤ v (z : K) := by
  cases z with
  | ofNat n => simpa using v_natCast_nonneg v n
  | negSucc n =>
    rw [Int.cast_negSucc, AddValuation.map_neg]
    exact v_natCast_nonneg v (n + 1)

/- English proof (translation)
The claim follows from `(vge_zero_iff v _).mpr (v_natCast_nonneg v n)`.
-/
theorem vge_natCast (n : ℕ) : vge v 0 (n : K) := (vge_zero_iff v _).mpr (v_natCast_nonneg v n)

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => simp`. Consider the case `succ e ih`. Rewrite using `[succ_nsmul, ih]`. Use `norm_cast`.
-/
theorem nsmul_one_withTop (e : ℕ) : e • (1 : WithTop ℚ) = ((e : ℚ) : WithTop ℚ) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [succ_nsmul, ih]
    norm_cast

/- English proof (translation)
Establish `hx : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`. Use `v.map_mul x x⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ hx, AddValuation.map_one, h, zero_add]`.

Conclude with `this.symm`.
-/
theorem v_unit_inv {x : K} (h : v x = 0) : v x⁻¹ = 0 := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp at h
  have := v.map_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, AddValuation.map_one, h, zero_add] at this
  exact this.symm

/- English proof (translation)
Rewrite using `[AddValuation.map_pow, h, nsmul_zero]`.
-/
theorem v_unit_pow {x : K} (h : v x = 0) (n : ℕ) : v (x ^ n) = 0 := by
  rw [AddValuation.map_pow, h, nsmul_zero]

/- English proof (translation)
Consider the cases of `ε with`. Consider the case `ofNat n`. Rewrite using `[Int.ofNat_eq_coe, zpow_natCast]`. Conclude with `v_unit_pow v h n`. Consider the case `negSucc n`.

Rewrite using `[zpow_negSucc]`. Conclude with `v_unit_inv v (v_unit_pow v h _)`.
-/
theorem v_unit_zpow {x : K} (h : v x = 0) (ε : ℤ) : v (x ^ ε) = 0 := by
  cases ε with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, zpow_natCast]
    exact v_unit_pow v h n
  | negSucc n =>
    rw [zpow_negSucc]
    exact v_unit_inv v (v_unit_pow v h _)

/- English proof (translation)
Rewrite using `[v.map_mul, hx, hy, add_zero]`.
-/
theorem v_unit_mul {x y : K} (hx : v x = 0) (hy : v y = 0) : v (x * y) = 0 := by
  rw [v.map_mul, hx, hy, add_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(vge_zero_iff v _).mpr h.ge, (vge_zero_iff v _).mpr (v_unit_inv v h).ge, fun ε => (vge_zero_iff v _).mpr (v_unit_zpow v h ε).ge⟩`.
-/
theorem vge_unit {x : K} (h : v x = 0) :
    vge v 0 x ∧ vge v 0 x⁻¹ ∧ ∀ ε : ℤ, vge v 0 (x ^ ε) := ⟨(vge_zero_iff v _).mpr h.ge, (vge_zero_iff v _).mpr (v_unit_inv v h).ge,
    fun ε => (vge_zero_iff v _).mpr (v_unit_zpow v h ε).ge⟩

section DVR

variable {v} {p : ℕ} [CharZero K]

/- English proof (translation)
Establish `hc : Nat.Coprime m p` using `((Nat.Prime.coprime_iff_not_dvd hD.prime).mpr h).symm`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.mpr hc`. Establish `e : (a : K) * m + (b : K) * p = 1`. Use `congrArg (Int.cast : ℤ → K) hab` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`. Establish `h1` using `v.map_add ((a : K) * m) ((b : K) * p)`. Rewrite `h1` using `[e, AddValuation.map_one]`. Establish `h01 : (0 : WithTop ℚ) < 1` using `by exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)`. Establish `hbp : 0 < v ((b : K) * p)`.

Rewrite using `[v.map_mul, hD.vp]`. Conclude with `lt_of_lt_of_le h01 (le_add_of_nonneg_left (v_intCast_nonneg v b))`. Establish `ham : v ((a : K) * m) ≤ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `absurd h1 (not_le.mpr (lt_min hc hbp))`. Rewrite `ham` using `[v.map_mul]`. Conclude with `le_antisymm (le_trans (le_add_of_nonneg_left (v_intCast_nonneg v a)) ham) (v_natCast_nonneg v m)`.
-/
theorem v_natCast_of_not_dvd (hD : DVRHyp v p) {m : ℕ} (h : ¬ p ∣ m) : v (m : K) = 0 := by
  have hc : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hD.prime).mpr h).symm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have e : (a : K) * m + (b : K) * p = 1 := by
    have := congrArg (Int.cast : ℤ → K) hab
    push_cast at this
    exact this
  have h1 := v.map_add ((a : K) * m) ((b : K) * p)
  rw [e, AddValuation.map_one] at h1
  have h01 : (0 : WithTop ℚ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)
  have hbp : 0 < v ((b : K) * p) := by
    rw [v.map_mul, hD.vp]
    exact lt_of_lt_of_le h01 (le_add_of_nonneg_left (v_intCast_nonneg v b))
  have ham : v ((a : K) * m) ≤ 0 := by
    by_contra hc
    push_neg at hc
    exact absurd h1 (not_le.mpr (lt_min hc hbp))
  rw [v.map_mul] at ham
  exact le_antisymm (le_trans (le_add_of_nonneg_left (v_intCast_nonneg v a)) ham)
    (v_natCast_nonneg v m)

/- English proof (translation)
Rewrite using `[AddValuation.map_pow, hD.vp, nsmul_one_withTop]`.
-/
theorem v_p_pow (hD : DVRHyp v p) (n : ℕ) : v ((p : K) ^ n) = ((n : ℚ) : WithTop ℚ) := by
  rw [AddValuation.map_pow, hD.vp, nsmul_one_withTop]

/- English proof (translation)
Use `haveI := Fact.mk hD.prime`. Take `⟨e, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn p hD.prime.ne_one`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hm (dvd_zero p)`.

Rewrite using `[padicValNat.mul (pow_ne_zero _ hD.prime.ne_zero) hm0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero, Nat.cast_mul, Nat.cast_pow, v.map_mul, v_p_pow hD, v_natCast_of_not_dvd hD hm, add_zero]`.
-/
theorem v_natCast (hD : DVRHyp v p) {n : ℕ} (hn : n ≠ 0) :
    v (n : K) = ((padicValNat p n : ℚ) : WithTop ℚ) := by
  haveI := Fact.mk hD.prime
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hD.prime.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [padicValNat.mul (pow_ne_zero _ hD.prime.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero, Nat.cast_mul, Nat.cast_pow, v.map_mul,
    v_p_pow hD, v_natCast_of_not_dvd hD hm, add_zero]

/- English proof (translation)
Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[vN]`. Unfold `vN`. Rewrite using `[v_natCast hD hn, WithTop.untopD_coe, Rat.cast_natCast]`.
-/
theorem vN_eq (hD : DVRHyp v p) (n : ℕ) : vN v n = padicValNat p n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [vN]
  · unfold vN
    rw [v_natCast hD hn, WithTop.untopD_coe, Rat.cast_natCast]

/- English proof (translation)
Rewrite using `[vN_eq hD]`. Check the signs of the components of the expression.
-/
theorem vN_nonneg (hD : DVRHyp v p) (n : ℕ) : 0 ≤ vN v n := by
  rw [vN_eq hD]
  positivity

/- English proof (translation)
Unfold `vge vR vN`. Rewrite using `[v_natCast hD hn, WithTop.untopD_coe, WithTop.map_coe]`.
-/
theorem vge_vN (hD : DVRHyp v p) {n : ℕ} (hn : n ≠ 0) : vge v (vN v n) (n : K) := by
  unfold vge vR vN
  rw [v_natCast hD hn, WithTop.untopD_coe, WithTop.map_coe]

/- English proof (translation)
Unfold `vle vR vN`. Rewrite using `[v_natCast hD hn, WithTop.untopD_coe, WithTop.map_coe]`.
-/
theorem vle_vN (hD : DVRHyp v p) {n : ℕ} (hn : n ≠ 0) : vle v (vN v n) (n : K) := by
  unfold vle vR vN
  rw [v_natCast hD hn, WithTop.untopD_coe, WithTop.map_coe]

/- English proof (translation)
Rewrite using `[vN_eq hD]`. Simplify using the standard rewrite rules.
-/
theorem vN_one (hD : DVRHyp v p) : vN v 1 = 0 := by
  rw [vN_eq hD]
  simp

/- English proof (translation)
Use `haveI := Fact.mk hD.prime`. Rewrite using `[vN_eq hD, vN_eq hD, vN_eq hD, padicValNat.mul hm hn]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vN_mul (hD : DVRHyp v p) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    vN v (m * n) = vN v m + vN v n := by
  haveI := Fact.mk hD.prime
  rw [vN_eq hD, vN_eq hD, vN_eq hD, padicValNat.mul hm hn]
  push_cast
  ring

/- English proof (translation)
Proceed by induction on `s using Finset.cons_induction with`. Consider the case `empty => simp [vN_one hD]`. Consider the case `cons i s hi ih`. Rewrite using `[Finset.prod_cons, Finset.sum_cons, vN_mul hD (hf i (by simp)) (Finset.prod_ne_zero_iff.mpr fun j hj => hf j (by simp [hj])), ih fun j hj => hf j (by simp [hj])]`.
-/
theorem vN_prod (hD : DVRHyp v p) {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    vN v (∏ i ∈ s, f i) = ∑ i ∈ s, vN v (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [vN_one hD]
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      vN_mul hD (hf i (by simp)) (Finset.prod_ne_zero_iff.mpr fun j hj => hf j (by simp [hj])),
      ih fun j hj => hf j (by simp [hj])]

/- English proof (translation)
Use `(vge_rat_iff v (n : ℚ) ((p : K) ^ n)).mpr (le_of_eq (v_p_pow hD n).symm)` as an intermediate fact. Simplify using `using this`.
-/
theorem vge_p_pow (hD : DVRHyp v p) (n : ℕ) : vge v (n : ℝ) ((p : K) ^ n) := by
  have := (vge_rat_iff v (n : ℚ) ((p : K) ^ n)).mpr (le_of_eq (v_p_pow hD n).symm)
  simpa using this

/- English proof (translation)
Unfold `vle vR`. Rewrite using `[v_p_pow hD]`. Simplify using the standard rewrite rules.
-/
theorem vle_p_pow (hD : DVRHyp v p) (n : ℕ) : vle v (n : ℝ) ((p : K) ^ n) := by
  unfold vle vR
  rw [v_p_pow hD]
  simp

/- English proof (translation)
Rewrite using `[add_comm]`. Conclude with `vle_mul v (vle_p_pow hD n) hx`.
-/
theorem vle_pow_p (hD : DVRHyp v p) {a : ℝ} {x : K} (n : ℕ) (hx : vle v a x) :
    vle v (a + n) ((p : K) ^ n * x) := by
  rw [add_comm]
  exact vle_mul v (vle_p_pow hD n) hx

/- English proof (translation)
Rewrite using `[vN_eq hD]`. Use `@Nat.factorization_choose_le_log p n k` as an intermediate fact. Rewrite `this` using `[Nat.factorization_def _ hD.prime]`. Conclude with `this` after adjusting the coercions.
-/
theorem vN_choose_le (hD : DVRHyp v p) (n k : ℕ) : vN v (n.choose k) ≤ Nat.log p n := by
  rw [vN_eq hD]
  have := @Nat.factorization_choose_le_log p n k
  rw [Nat.factorization_def _ hD.prime] at this
  exact_mod_cast this

end DVR

/- English proof (translation)
Unfold `fact Finsupp.prod`. Conclude with `Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _`.
-/
theorem fact_ne_zero {σ : Type} (α : σ →₀ ℕ) : fact α ≠ 0 := by
  unfold fact Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _

/- English proof (translation)
Unfold `fact`. Conclude with `Finsupp.prod_add_index_of_disjoint h _`.
-/
theorem fact_add_of_disjoint {σ : Type} {α β : σ →₀ ℕ} (h : Disjoint α.support β.support) :
    fact (α + β) = fact α * fact β := by
  unfold fact
  exact Finsupp.prod_add_index_of_disjoint h _

/- English proof (translation)
Unfold `fact`. Conclude with `Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)`.
-/
theorem fact_eq_prod {σ : Type} [Fintype σ] (α : σ →₀ ℕ) : fact α = ∏ x, (α x).factorial := by
  unfold fact
  exact Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)

/- English proof (translation)
Unfold `eOut eIn`. Conclude with `Finsupp.filter_pos_add_filter_neg α _`.
-/
theorem eOut_add_eIn_n {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out] (α : L × Fin r →₀ ℕ) :
    eOut out α + eIn out α = α := by
  unfold eOut eIn
  exact Finsupp.filter_pos_add_filter_neg α _

/- English proof (translation)
Unfold `eOut eIn`. Rewrite using `[Finset.disjoint_left]`. Introduce `x h1 h2`. Rewrite `h1`, `h2` using `[Finsupp.support_filter, Finset.mem_filter]`. Conclude with `h2.2 h1.2`.
-/
theorem disjoint_eOut_eIn {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out]
    (α β : L × Fin r →₀ ℕ) : Disjoint (eOut out α).support (eIn out β).support := by
  unfold eOut eIn
  rw [Finset.disjoint_left]
  intro x h1 h2
  rw [Finsupp.support_filter, Finset.mem_filter] at h1 h2
  exact h2.2 h1.2

/- English proof (translation)
Use `conv_lhs => rw [← eOut_add_eIn_n out α]`. Conclude with `fact_add_of_disjoint (disjoint_eOut_eIn out α α)`.
-/
theorem fact_eq_out_mul_in {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out]
    (α : L × Fin r →₀ ℕ) : fact α = fact (eOut out α) * fact (eIn out α) := by
  conv_lhs => rw [← eOut_add_eIn_n out α]
  exact fact_add_of_disjoint (disjoint_eOut_eIn out α α)

/- English proof (translation)
Rewrite using `[fact_eq_prod, Fintype.prod_prod_type]`.
-/
theorem fact_eq_prod_letters {L : Type} [Fintype L] {r : ℕ} (α : L × Fin r →₀ ℕ) :
    fact α = ∏ i : L, ∏ a : Fin r, (α (i, a)).factorial := by
  rw [fact_eq_prod, Fintype.prod_prod_type]

/- English proof (translation)
Rewrite using `[fact_eq_prod_letters, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← h i]`. Simplify using `only [ldeg]`. Conclude with `(Nat.multinomial_spec _ _).symm`.
-/
theorem prod_factorial_eq {L : Type} [Fintype L] {r : ℕ} {α : L × Fin r →₀ ℕ} {d : L → ℕ}
    (h : ∀ i, ldeg α i = d i) :
    ∏ i, (d i).factorial = fact α * ∏ i : L, Nat.multinomial univ fun a : Fin r => α (i, a) := by
  rw [fact_eq_prod_letters, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← h i]
  simp only [ldeg]
  exact (Nat.multinomial_spec _ _).symm

/- English proof (translation)
Rewrite using `[fact_eq_prod, fact_eq_prod, fact_eq_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.add_apply, Nat.add_choose_mul_factorial_mul_factorial]`.
-/
theorem fact_add_eq {σ : Type} [Fintype σ] (α α' : σ →₀ ℕ) :
    fact (α + α') = (∏ x, (α x + α' x).choose (α' x)) * fact α * fact α' := by
  rw [fact_eq_prod, fact_eq_prod, fact_eq_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finsupp.add_apply, Nat.add_choose_mul_factorial_mul_factorial]

def kapL (p r : ℕ) {L : Type} [Fintype L] (d : L → ℕ) : ℝ :=
  ∑ i, if d i = 0 then 0 else (r : ℝ) * Real.logb p ((d i : ℝ) + r)

/- English proof (translation)
Apply `Real.logb_nonneg` to reduce the goal to its premises. Conclude with `(by omega : 1 < p)` after adjusting the coercions. Conclude with `h` after adjusting the coercions.
-/
theorem logb_add_nonneg {p : ℕ} (hp : 2 ≤ p) (r a : ℕ) (h : 1 ≤ a + r) :
    0 ≤ Real.logb p ((a : ℝ) + r) := by
  apply Real.logb_nonneg
  · exact_mod_cast (by omega : 1 < p)
  · exact_mod_cast h

/- English proof (translation)
Apply `Real.logb_le_logb_of_le` to reduce the goal to its premises. Conclude with `(by omega : 1 < p)` after adjusting the coercions. Establish `: (1 : ℝ) ≤ a + r` using `by exact_mod_cast h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: (a : ℝ) ≤ b` using `by exact_mod_cast hab`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logb_add_mono {p : ℕ} (hp : 2 ≤ p) (r : ℕ) {a b : ℕ} (h : 1 ≤ a + r) (hab : a ≤ b) :
    Real.logb p ((a : ℝ) + r) ≤ Real.logb p ((b : ℝ) + r) := by
  apply Real.logb_le_logb_of_le
  · exact_mod_cast (by omega : 1 < p)
  · have : (1 : ℝ) ≤ a + r := by exact_mod_cast h
    linarith
  · have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith

/- English proof (translation)
Use `split_ifs with ha`. Conclude with `le_refl 0`. Conclude with `mul_nonneg (Nat.cast_nonneg r) (logb_add_nonneg hp r a (by omega))`.
-/
theorem kapL_term_nonneg {p : ℕ} (hp : 2 ≤ p) (r a : ℕ) :
    0 ≤ (if a = 0 then 0 else (r : ℝ) * Real.logb p ((a : ℝ) + r)) := by
  split_ifs with ha
  · exact le_refl 0
  · exact mul_nonneg (Nat.cast_nonneg r) (logb_add_nonneg hp r a (by omega))

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun i _ => kapL_term_nonneg hp r (d i)`.
-/
theorem kapL_nonneg {p : ℕ} (hp : 2 ≤ p) (r : ℕ) {L : Type} [Fintype L] (d : L → ℕ) :
    0 ≤ kapL p r d := Finset.sum_nonneg fun i _ => kapL_term_nonneg hp r (d i)

/- English proof (translation)
Unfold `kapL`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Distinguish the cases in `h0 : d i = 0`. Rewrite using `[if_pos h0]`.

Conclude with `kapL_term_nonneg hp r (d' i)`. Establish `h1 : d' i ≠ 0`. Use `h i` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h0, if_neg h1]`.

Conclude with `mul_le_mul_of_nonneg_left (logb_add_mono hp r (by omega) (h i)) (Nat.cast_nonneg r)`.
-/
theorem kapL_mono {p : ℕ} (hp : 2 ≤ p) (r : ℕ) {L : Type} [Fintype L] {d d' : L → ℕ}
    (h : ∀ i, d i ≤ d' i) : kapL p r d ≤ kapL p r d' := by
  unfold kapL
  apply Finset.sum_le_sum
  intro i _
  by_cases h0 : d i = 0
  · rw [if_pos h0]
    exact kapL_term_nonneg hp r (d' i)
  · have h1 : d' i ≠ 0 := by
      have := h i
      omega
    rw [if_neg h0, if_neg h1]
    exact mul_le_mul_of_nonneg_left (logb_add_mono hp r (by omega) (h i)) (Nat.cast_nonneg r)

/- English proof (translation)
Unfold `kapL kap lg`. Establish `e : (Fintype.card L : ℝ) * r = ∑ _i : L, (r : ℝ)` using `by simp`. Rewrite using `[e, ← Finset.sum_add_distrib]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`.

Establish `hl` using `logb_add_nonneg hp r (d i) (by omega)`. Establish `hr0 : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`. Use `split_ifs with h0`. Use the polynomial consequences of the given equalities and inequalities. Apply `le_of_eq` to reduce the goal to its premises.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem kapL_le_kap {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) {L : Type} [Fintype L] (d : L → ℕ) :
    kapL p r d + (Fintype.card L : ℝ) * r ≤ kap p r d := by
  unfold kapL kap lg
  have e : (Fintype.card L : ℝ) * r = ∑ _i : L, (r : ℝ) := by simp
  rw [e, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hl := logb_add_nonneg hp r (d i) (by omega)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  split_ifs with h0
  · nlinarith
  · apply le_of_eq
    ring

/- English proof (translation)
The claim follows from `le_trans (le_add_of_nonneg_right (by positivity)) (kapL_le_kap hp hr d)`.
-/
theorem kapL_le_kap' {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) {L : Type} [Fintype L] (d : L → ℕ) :
    kapL p r d ≤ kap p r d := le_trans (le_add_of_nonneg_right (by positivity)) (kapL_le_kap hp hr d)

/- English proof (translation)
Unfold `lg`. Combine the linear relations using `[logb_add_nonneg hp r a (by omega)]`.
-/
theorem lg_ge_one {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) (a : ℕ) : 1 ≤ lg p r a := by
  unfold lg
  linarith [logb_add_nonneg hp r a (by omega)]

/- English proof (translation)
The claim follows from `le_trans (le_add_of_nonneg_left (kapL_nonneg hp r d)) (kapL_le_kap hp hr d)`.
-/
theorem kap_ge_card {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) {L : Type} [Fintype L] (d : L → ℕ) :
    (Fintype.card L : ℝ) * r ≤ kap p r d := le_trans (le_add_of_nonneg_left (kapL_nonneg hp r d)) (kapL_le_kap hp hr d)

/- English proof (translation)
Use `split_ifs with ha`. Rewrite using `[ha, Nat.log_zero_right]`. Simplify using the standard rewrite rules. Apply `mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg r)` to reduce the goal to its premises. Establish `ha0 : (0 : ℝ) < a` using `Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha)`.

Establish `hr0 : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`. Rewrite using `[Real.le_logb_iff_rpow_le (by exact_mod_cast (by omega : 1 < p)) (by linarith), Real.rpow_natCast]`. Establish `h2 : ((p ^ Nat.log p a : ℕ) : ℝ) ≤ a` using `by exact_mod_cast Nat.pow_log_le_self p ha`. Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem natLog_le_term {p : ℕ} (hp : 2 ≤ p) (r a : ℕ) :
    (r : ℝ) * (Nat.log p a : ℝ) ≤ (if a = 0 then 0 else (r : ℝ) * Real.logb p ((a : ℝ) + r)) := by
  split_ifs with ha
  · rw [ha, Nat.log_zero_right]
    simp
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg r)
    have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha)
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    rw [Real.le_logb_iff_rpow_le (by exact_mod_cast (by omega : 1 < p)) (by linarith),
      Real.rpow_natCast]
    have h2 : ((p ^ Nat.log p a : ℕ) : ℝ) ≤ a := by exact_mod_cast Nat.pow_log_le_self p ha
    push_cast at h2
    linarith

section DVR2

variable {v} {p : ℕ} [CharZero K]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `@insert a s ha ih`. Rewrite using `[Nat.multinomial_insert ha, Nat.factorization_mul (Nat.choose_pos (by omega)).ne' (Nat.multinomial_pos _ _).ne', Finsupp.add_apply, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]`. Establish `h1` using `@Nat.factorization_choose_le_log q (f a + ∑ i ∈ s, f i) (f a)`.

Establish `h2 : Nat.log q (∑ i ∈ s, f i) ≤ Nat.log q (f a + ∑ i ∈ s, f i)` using `Nat.log_mono_right (by omega)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem multinomial_fact_le {ι : Type*} (q : ℕ) (f : ι → ℕ) (s : Finset ι) :
    (Nat.multinomial s f).factorization q ≤ s.card * Nat.log q (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Nat.multinomial_insert ha,
      Nat.factorization_mul (Nat.choose_pos (by omega)).ne' (Nat.multinomial_pos _ _).ne',
      Finsupp.add_apply, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    have h1 := @Nat.factorization_choose_le_log q (f a + ∑ i ∈ s, f i) (f a)
    have h2 : Nat.log q (∑ i ∈ s, f i) ≤ Nat.log q (f a + ∑ i ∈ s, f i) :=
      Nat.log_mono_right (by omega)
    calc _ ≤ Nat.log q (f a + ∑ i ∈ s, f i) + s.card * Nat.log q (∑ i ∈ s, f i) := add_le_add h1 ih
      _ ≤ Nat.log q (f a + ∑ i ∈ s, f i) + s.card * Nat.log q (f a + ∑ i ∈ s, f i) := by gcongr
      _ = (s.card + 1) * Nat.log q (f a + ∑ i ∈ s, f i) := by ring

/- English proof (translation)
Rewrite using `[vN_eq hD, ← Nat.factorization_def _ hD.prime]`. Use `multinomial_fact_le p f Finset.univ` as an intermediate fact. Rewrite `this` using `[Finset.card_univ, Fintype.card_fin]`. Conclude with `this` after adjusting the coercions.
-/
theorem vN_multinomial_le (hD : DVRHyp v p) {r : ℕ} (f : Fin r → ℕ) :
    vN v (Nat.multinomial univ f) ≤ (r : ℝ) * (Nat.log p (∑ a, f a) : ℝ) := by
  rw [vN_eq hD, ← Nat.factorization_def _ hD.prime]
  have := multinomial_fact_le p f Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this

/- English proof (translation)
The claim follows from `hD.prime.two_le`.
-/
theorem two_le_p (hD : DVRHyp v p) : 2 ≤ p := hD.prime.two_le

/- English proof (translation)
Rewrite using `[prod_factorial_eq h, vN_mul hD (fact_ne_zero α) (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.multinomial_pos _ _).ne'), vN_prod hD _ _ (fun i _ => (Nat.multinomial_pos _ _).ne')]`.
-/
theorem vN_prod_factorial_eq (hD : DVRHyp v p) {L : Type} [Fintype L] {r : ℕ}
    {α : L × Fin r →₀ ℕ} {d : L → ℕ} (h : ∀ i, ldeg α i = d i) :
    vN v (∏ i, (d i).factorial) =
      vN v (fact α) + ∑ i : L, vN v (Nat.multinomial univ fun a : Fin r => α (i, a)) := by
  rw [prod_factorial_eq h,
    vN_mul hD (fact_ne_zero α) (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.multinomial_pos _ _).ne'),
    vN_prod hD _ _ (fun i _ => (Nat.multinomial_pos _ _).ne')]

/- English proof (translation)
Rewrite using `[vN_prod_factorial_eq hD h]`. Conclude with `le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => vN_nonneg hD _)`.
-/
theorem fact_upper (hD : DVRHyp v p) {L : Type} [Fintype L] {r : ℕ}
    {α : L × Fin r →₀ ℕ} {d : L → ℕ} (h : ∀ i, ldeg α i = d i) :
    vN v (fact α) ≤ vN v (∏ i, (d i).factorial) := by
  rw [vN_prod_factorial_eq hD h]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => vN_nonneg hD _)

/- English proof (translation)
Rewrite using `[vN_prod_factorial_eq hD h]`. Establish `hs : ∑ i : L, vN v (Nat.multinomial univ fun a : Fin r => α (i, a)) ≤ kapL p r d`. Unfold `kapL`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`.

Establish `e : ∑ a : Fin r, α (i, a) = d i` using `h i`. Use `vN_multinomial_le hD (fun a : Fin r => α (i, a))` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `this.trans (natLog_le_term (two_le_p hD) r (d i))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fact_lower (hD : DVRHyp v p) {L : Type} [Fintype L] {r : ℕ}
    {α : L × Fin r →₀ ℕ} {d : L → ℕ} (h : ∀ i, ldeg α i = d i) :
    vN v (∏ i, (d i).factorial) - kapL p r d ≤ vN v (fact α) := by
  rw [vN_prod_factorial_eq hD h]
  have hs : ∑ i : L, vN v (Nat.multinomial univ fun a : Fin r => α (i, a)) ≤ kapL p r d := by
    unfold kapL
    apply Finset.sum_le_sum
    intro i _
    have e : ∑ a : Fin r, α (i, a) = d i := h i
    have := vN_multinomial_le hD (fun a : Fin r => α (i, a))
    rw [e] at this
    exact this.trans (natLog_le_term (two_le_p hD) r (d i))
  linarith

/- English proof (translation)
Establish `hf` using `fact_add_eq α α'`. Establish `hne : ∏ x, (α x + α' x).choose (α' x) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun x _ => (Nat.choose_pos (by omega)).ne'`. Establish `hv : vN v (fact (α + α')) = vN v (∏ x, (α x + α' x).choose (α' x)) + vN v (fact α) + vN v (fact α')`. Rewrite using `[hf, vN_mul hD (mul_ne_zero hne (fact_ne_zero α)) (fact_ne_zero α'), vN_mul hD hne (fact_ne_zero α)]`. Establish `hl` using `fact_lower hD h`.

Establish `hc : vN v (∏ x, (α x + α' x).choose (α' x)) ≤ kapL p r d`. Rewrite using `[vN_prod hD _ _ (fun x _ => (Nat.choose_pos (by omega)).ne'), Fintype.sum_prod_type]`. Unfold `kapL`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`.

Establish `hb : ∀ a : Fin r, α (i, a) + α' (i, a) ≤ d i`. Introduce `a`. Rewrite using `[← h i]`. Unfold `ldeg`. Use `Finset.single_le_sum (f := fun b : Fin r => (α + α') (i, b)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)` as an intermediate fact.

Simplify using `using this`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `a _`. Use `(vN_choose_le hD _ _).trans ?_` and prove the remaining obligations.

Conclude with `Nat.log_mono_right (hb a)` after adjusting the coercions. Use `_ = (r : ℝ) * (Nat.log p (d i) : ℝ) := by simp`. Use `_ ≤ _ := natLog_le_term (two_le_p hD) r (d i)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fact_add_lower (hD : DVRHyp v p) {L : Type} [Fintype L] {r : ℕ}
    {α α' : L × Fin r →₀ ℕ} {d : L → ℕ} (h : ∀ i, ldeg (α + α') i = d i) :
    vN v (∏ i, (d i).factorial) - 2 * kapL p r d ≤ vN v (fact α) + vN v (fact α') := by
  have hf := fact_add_eq α α'
  have hne : ∏ x, (α x + α' x).choose (α' x) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun x _ => (Nat.choose_pos (by omega)).ne'
  have hv : vN v (fact (α + α')) =
      vN v (∏ x, (α x + α' x).choose (α' x)) + vN v (fact α) + vN v (fact α') := by
    rw [hf, vN_mul hD (mul_ne_zero hne (fact_ne_zero α)) (fact_ne_zero α'),
      vN_mul hD hne (fact_ne_zero α)]
  have hl := fact_lower hD h
  have hc : vN v (∏ x, (α x + α' x).choose (α' x)) ≤ kapL p r d := by
    rw [vN_prod hD _ _ (fun x _ => (Nat.choose_pos (by omega)).ne'), Fintype.sum_prod_type]
    unfold kapL
    apply Finset.sum_le_sum
    intro i _
    have hb : ∀ a : Fin r, α (i, a) + α' (i, a) ≤ d i := by
      intro a
      rw [← h i]
      unfold ldeg
      have := Finset.single_le_sum (f := fun b : Fin r => (α + α') (i, b))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      simpa using this
    calc ∑ a : Fin r, vN v ((α (i, a) + α' (i, a)).choose (α' (i, a)))
        ≤ ∑ _a : Fin r, (Nat.log p (d i) : ℝ) := by
          apply Finset.sum_le_sum
          intro a _
          refine (vN_choose_le hD _ _).trans ?_
          exact_mod_cast Nat.log_mono_right (hb a)
      _ = (r : ℝ) * (Nat.log p (d i) : ℝ) := by simp
      _ ≤ _ := natLog_le_term (two_le_p hD) r (d i)
  linarith

end DVR2

section Star

variable {v} {p : ℕ} [CharZero K]

/- English proof (translation)
Introduce `α`. Distinguish the cases in `h0 : F.coeff α = 0`. Rewrite using `[h0]`. Conclude with `vge_zero v _`. Establish `hα : ∀ i, ldeg α i = d i`.

Unfold `PolK at hF`. Rewrite `hF` using `[MvPolynomial.mem_restrictSupport_iff]`. Conclude with `hF (MvPolynomial.mem_support_iff.mpr h0)`. Establish `hl` using `fact_lower hD hα`. Use `vge_mono v ?_ (h α)` and prove the remaining obligations.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bge_of_cge (hD : DVRHyp v p) {L : Type} [Fintype L] {r : ℕ} {d : L → ℕ} {a : ℝ}
    {F : MvPolynomial (L × Fin r) K} (hF : F ∈ PolK K r d) (h : cge v a F) :
    bge v (a + (vN v (∏ i, (d i).factorial) - kapL p r d) / 2) F := by
  intro α
  by_cases h0 : F.coeff α = 0
  · rw [h0]
    exact vge_zero v _
  · have hα : ∀ i, ldeg α i = d i := by
      unfold PolK at hF
      rw [MvPolynomial.mem_restrictSupport_iff] at hF
      exact hF (MvPolynomial.mem_support_iff.mpr h0)
    have hl := fact_lower hD hα
    refine vge_mono v ?_ (h α)
    linarith

/- English proof (translation)
Introduce `α`. Distinguish the cases in `h0 : F.coeff α = 0`. Rewrite using `[h0]`. Conclude with `vge_zero v _`. Establish `hα : ∀ i, ldeg α i = d i`.

Unfold `PolK at hF`. Rewrite `hF` using `[MvPolynomial.mem_restrictSupport_iff]`. Conclude with `hF (MvPolynomial.mem_support_iff.mpr h0)`. Establish `hu` using `fact_upper hD hα`. Use `vge_mono v ?_ (h α)` and prove the remaining obligations.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cge_of_bge (hD : DVRHyp v p) {L : Type} [Fintype L] {r : ℕ} {d : L → ℕ} {a : ℝ}
    {F : MvPolynomial (L × Fin r) K} (hF : F ∈ PolK K r d) (h : bge v a F) :
    cge v (a - vN v (∏ i, (d i).factorial) / 2) F := by
  intro α
  by_cases h0 : F.coeff α = 0
  · rw [h0]
    exact vge_zero v _
  · have hα : ∀ i, ldeg α i = d i := by
      unfold PolK at hF
      rw [MvPolynomial.mem_restrictSupport_iff] at hF
      exact hF (MvPolynomial.mem_support_iff.mpr h0)
    have hu := fact_upper hD hα
    refine vge_mono v ?_ (h α)
    linarith

end Star

end Formalism.MainNotions.PlaneGram
