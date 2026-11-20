import ReciprocityTheory.DualLattices.IsUnitOfNotMem

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij⟩ : ∃ i j, e i j ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `he (Matrix.ext hc)`. Establish `h1` using `congrFun (congrFun h i) j`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul] at h1`. Establish `h2` using `congrArg (algebraMap R C) h1`. Rewrite `h2` using `[map_mul, map_mul]`. Establish `hne : algebraMap R C (e i j) ≠ 0`. Introduce `h0`.

Rewrite `h0` using `[← map_zero (algebraMap R C)]`. Conclude with `hij (hv.hom_inj h0)`. Conclude with `hv.hom_inj (mul_right_cancel₀ hne h2)`.
-/
theorem smul_cancel (hv : v.Integers R) {n : Type} {e : Matrix n n R} (he : e ≠ 0) {x y : R}
    (h : x • e = y • e) : x = y := by
  obtain ⟨i, j, hij⟩ : ∃ i j, e i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact he (Matrix.ext hc)
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1
  have h2 := congrArg (algebraMap R C) h1
  rw [map_mul, map_mul] at h2
  have hne : algebraMap R C (e i j) ≠ 0 := by
    intro h0
    rw [← map_zero (algebraMap R C)] at h0
    exact hij (hv.hom_inj h0)
  exact hv.hom_inj (mul_right_cancel₀ hne h2)

/- English proof (translation)
Establish `hpow : ∀ k : ℕ, (N.map (algebraMap ℤ_[p] R)) ^ k * e = x ^ k • e`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, mul_assoc, h, Matrix.mul_smul, ih, smul_smul, ← pow_succ']`.

Establish `hN' : (N.map (algebraMap ℤ_[p] R)) ^ m = 1`. Use `congrArg (algebraMap ℤ_[p] R).mapMatrix hN` as an intermediate fact. Rewrite `this` using `[map_pow, map_one, RingHom.mapMatrix_apply]`. Then use the resulting hypothesis. Establish `h1` using `hpow m`. Rewrite `h1` using `[hN', one_mul]`.

Conclude with `(smul_cancel hv he (by rw [one_smul]; exact h1)).symm`.
-/
theorem eig_pow_eq_one (hv : v.Integers R) {p : ℕ} [Fact p.Prime] {n : Type} [Fintype n] [DecidableEq n]
    [Algebra ℤ_[p] R] (N : Matrix n n ℤ_[p]) (e : Matrix n n R) (he : e ≠ 0) (x : R)
    (h : N.map (algebraMap ℤ_[p] R) * e = x • e) {m : ℕ} (hN : N ^ m = 1) : x ^ m = 1 := by
  have hpow : ∀ k : ℕ, (N.map (algebraMap ℤ_[p] R)) ^ k * e = x ^ k • e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, h, Matrix.mul_smul, ih, smul_smul, ← pow_succ']
  have hN' : (N.map (algebraMap ℤ_[p] R)) ^ m = 1 := by
    have := congrArg (algebraMap ℤ_[p] R).mapMatrix hN
    rwa [map_pow, map_one, RingHom.mapMatrix_apply] at this
  have h1 := hpow m
  rw [hN', one_mul] at h1
  exact (smul_cancel hv he (by rw [one_smul]; exact h1)).symm

/- English proof (translation)
Establish `hz : z ^ p - z ∈ Ideal.span {(p : ℤ_[p])}`. Rewrite using `[← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, ZMod.pow_card, sub_self]`. Take `⟨w, hw⟩` from `Ideal.mem_span_singleton'.mp hz`. Establish `hp0 : res hv (p : R) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hpv`. Establish `h0 : res hv (algebraMap ℤ_[p] R (z ^ p - z)) = 0`. Rewrite using `[← hw, map_mul, map_mul, map_natCast (algebraMap ℤ_[p] R), hp0, mul_zero]`. Rewrite `h0` using `[map_sub, map_sub, map_pow, map_pow, sub_eq_zero]`. Conclude with `h0`.
-/
theorem fermat (p : ℕ) [Fact p.Prime] (hv : v.Integers R) (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] (z : ℤ_[p]) :
    res hv (algebraMap ℤ_[p] R z) ^ p = res hv (algebraMap ℤ_[p] R z) := by
  have hz : z ^ p - z ∈ Ideal.span {(p : ℤ_[p])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
      ZMod.pow_card, sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hz
  have hp0 : res hv (p : R) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hpv
  have h0 : res hv (algebraMap ℤ_[p] R (z ^ p - z)) = 0 := by
    rw [← hw, map_mul, map_mul, map_natCast (algebraMap ℤ_[p] R), hp0, mul_zero]
  rw [map_sub, map_sub, map_pow, map_pow, sub_eq_zero] at h0
  exact h0

/- English proof (translation)
Establish `hApow : ∀ γ (k : ℕ), A (γ ^ k) = A γ ^ k`. Introduce `γ k`. Proceed by induction on `k with`. Consider the case `zero => simp [hA1]`. Consider the case `succ k ih => rw [pow_succ, hA, ih, pow_succ]`.

Establish `hmul : ∀ j, εT j ≠ 0 → ∀ γ γ', ψ j (γ * γ') = ψ j γ * ψ j γ'`. Introduce `j hj γ γ'`. Apply `smul_cancel hv hj` to reduce the goal to its premises. Establish `e1` using `heig j (γ * γ')`. Rewrite `e1` using `[hA, Matrix.map_mul, Matrix.mul_assoc, heig j γ', Matrix.mul_smul, heig j γ, smul_smul]`.

Rewrite using `[← e1, mul_comm (ψ j γ')]`. Establish `hn1 : 1 ≤ Fintype.card G` using `Fintype.card_pos`. Establish `hpowG : ∀ j, εT j ≠ 0 → ∀ γ, ψ j γ ^ Fintype.card G = 1` using `fun j hj γ => eig_pow_eq_one hv (A γ) (εT j) hj (ψ j γ) (heig j γ) (by rw [← hApow, pow_card_eq_one, hA1])`. Establish `hiv : ∀ j, εT j ≠ 0 → ∀ γ, ψ j γ ^ (Fintype.card G - 1) * ψ j γ = 1`. Introduce `j hj γ`.

Rewrite using `[← pow_succ, Nat.sub_add_cancel hn1, hpowG j hj γ]`. Establish `hsum0 : ∀ χ : G → R, (∀ γ γ', χ (γ * γ') = χ γ * χ γ') → ∀ γ0, χ γ0 ≠ 1 → ∑ γ, χ γ = 0`. Introduce `χ hχ γ0 h0`. Establish `e : ∑ γ, χ γ = χ γ0 * ∑ γ, χ γ`. Rewrite using `[Finset.mul_sum]`.

Conclude with `(Fintype.sum_bijective (γ0 * ·) (Group.mulLeft_bijective γ0) (fun γ => χ γ0 * χ γ) χ (fun γ => (hχ γ0 γ).symm)).symm`. Establish `e2 : (1 - χ γ0) * ∑ γ, χ γ = 0` using `by rw [sub_mul, one_mul, ← e, sub_self]`. Establish `e3` using `congrArg (algebraMap R C) e2`. Rewrite `e3` using `[map_mul, map_zero]`. Break down `mul_eq_zero.mp e3 with h | h` into its components or cases.

Conclude with `absurd (sub_eq_zero.mp (hv.hom_inj (h.trans (map_zero _).symm))).symm h0`. Conclude with `hv.hom_inj (h.trans (map_zero _).symm)`. Establish `hPe : ∀ (c : G → R) j, (∑ γ, c γ • (A γ).map (algebraMap ℤ_[p] R)) * εT j = (∑ γ, c γ * ψ j γ) • εT j`. Introduce `c j`. Rewrite using `[Finset.sum_mul, Finset.sum_smul]`.

Use `Finset.sum_congr rfl fun γ _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_mul, heig, smul_smul]`. Establish `hdecomp : ∀ M : Matrix n n R, M = ∑ j, M * εT j` using `fun M => by`. Rewrite using `[← Finset.mul_sum, hsum, Matrix.mul_one]`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hP'0 : (∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p • (A γ).map (algebraMap ℤ_[p] R)) = 0`. Rewrite using `[hdecomp (∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p • (A γ).map (algebraMap ℤ_[p] R))]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : εT j = 0`.

Rewrite using `[hj, Matrix.mul_zero]`. Rewrite using `[hPe (fun γ => (ψ i γ ^ (Fintype.card G - 1)) ^ p) j]`. Take `⟨γ0, hγ0⟩` from `hcon j hj`. Establish `hz` using `hsum0 (fun γ => (ψ i γ ^ (Fintype.card G - 1)) ^ p * ψ j γ) (fun γ γ' => by simp only [hmul i hi, hmul j hj]; ring) γ0 (by`. Introduce `h1`.

Apply `hγ0` to reduce the goal to its premises. Apply the tactic sequence `try simp only at h1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hiv i hi, one_pow, one_mul]`. Use `_ = ((ψ i γ0 ^ (Fintype.card G - 1)) ^ p * ψ j γ0) * ψ i γ0 ^ p := by ring`.

Use `_ = ψ i γ0 ^ p := by rw [h1, one_mul])`. Apply the tactic sequence `try simp only at hz`. Rewrite using `[hz, zero_smul]`. Establish `hPi : (∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)) = (Fintype.card G : R) • εT i`. Rewrite using `[hdecomp (∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)), Finset.sum_eq_single i]`.

Rewrite using `[hPe (fun γ => ψ i γ ^ (Fintype.card G - 1)) i]`. Simplify using `only [hiv i hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]`. Introduce `j _ hji`. Distinguish the cases in `hj : εT j = 0`. Rewrite using `[hj, Matrix.mul_zero]`.

Rewrite using `[hPe (fun γ => ψ i γ ^ (Fintype.card G - 1)) j]`. Take `⟨γ0, hγ0⟩` from `hsep j i hj hi hji`. Establish `hz` using `hsum0 (fun γ => ψ i γ ^ (Fintype.card G - 1) * ψ j γ) (fun γ γ' => by simp only [hmul i hi, hmul j hj]; ring) γ0 (by`. Introduce `h1`. Apply `hγ0` to reduce the goal to its premises.

Apply the tactic sequence `try simp only at h1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hiv i hi, one_mul]`. Use `_ = (ψ i γ0 ^ (Fintype.card G - 1) * ψ j γ0) * ψ i γ0 := by ring`. Use `_ = ψ i γ0 := by rw [h1, one_mul])`.

Apply the tactic sequence `try simp only at hz`. Rewrite using `[hz, zero_smul]`. Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab⟩ : ∃ a b, εT i a b ∉ mI hv := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hi (idem_eq_zero hv (εT i) (by rw [horth, if_pos rfl]) hc)`. Use `haveI := charP p hv hpv`. Establish `hfrob : res hv ((∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p • (A γ).map (algebraMap ℤ_[p] R)) a b) = res hv ((∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)) a b) ^ p`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum, map_mul, map_pow]`.

Rewrite using `[sum_pow_char]`. Use `Finset.sum_congr rfl fun γ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_pow, fermat p hv hpv]`. Establish `hres_n : res hv (Fintype.card G : R) ≠ 0`. Introduce `h0`.

Establish `h1 : IsUnit (res hv (Fintype.card G : R))` using `hG.map (res hv)`. Rewrite `h1` using `[h0]`. Conclude with `not_isUnit_zero h1`. Establish `hres_e : res hv (εT i a b) ≠ 0`. Introduce `h0`.

Conclude with `hab (Ideal.Quotient.eq_zero_iff_mem.mp h0)`. Rewrite `hfrob` using `[hP'0, hPi]`. Simplify using `only [Matrix.zero_apply, map_zero, Matrix.smul_apply, smul_eq_mul, map_mul] at hfrob`. Conclude with `pow_ne_zero p (mul_ne_zero hres_n hres_e) hfrob.symm`.
-/
theorem proj (p : ℕ) [Fact p.Prime] (hv : v.Integers R) (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]
    {G : Type} [CommGroup G] [Fintype G] (hG : IsUnit (Fintype.card G : R))
    (A : G → Matrix n n ℤ_[p]) (hA : ∀ γ γ', A (γ * γ') = A γ * A γ') (hA1 : A 1 = 1)
    (εT : ι → Matrix n n R) (horth : ∀ i j, εT i * εT j = if i = j then εT i else 0)
    (hsum : ∑ i, εT i = 1) (ψ : ι → G → R)
    (heig : ∀ j γ, (A γ).map (algebraMap ℤ_[p] R) * εT j = ψ j γ • εT j)
    (hsep : ∀ j k, εT j ≠ 0 → εT k ≠ 0 → j ≠ k → ∃ γ, ψ j γ ≠ ψ k γ)
    (i : ι) (hi : εT i ≠ 0) : ∃ j, εT j ≠ 0 ∧ ∀ γ, ψ j γ = ψ i γ ^ p := by
  classical
  have hApow : ∀ γ (k : ℕ), A (γ ^ k) = A γ ^ k := by
    intro γ k
    induction k with
    | zero => simp [hA1]
    | succ k ih => rw [pow_succ, hA, ih, pow_succ]
  have hmul : ∀ j, εT j ≠ 0 → ∀ γ γ', ψ j (γ * γ') = ψ j γ * ψ j γ' := by
    intro j hj γ γ'
    apply smul_cancel hv hj
    have e1 := heig j (γ * γ')
    rw [hA, Matrix.map_mul, Matrix.mul_assoc, heig j γ', Matrix.mul_smul, heig j γ, smul_smul] at e1
    rw [← e1, mul_comm (ψ j γ')]
  have hn1 : 1 ≤ Fintype.card G := Fintype.card_pos
  have hpowG : ∀ j, εT j ≠ 0 → ∀ γ, ψ j γ ^ Fintype.card G = 1 := fun j hj γ =>
    eig_pow_eq_one hv (A γ) (εT j) hj (ψ j γ) (heig j γ) (by rw [← hApow, pow_card_eq_one, hA1])
  have hiv : ∀ j, εT j ≠ 0 → ∀ γ, ψ j γ ^ (Fintype.card G - 1) * ψ j γ = 1 := by
    intro j hj γ
    rw [← pow_succ, Nat.sub_add_cancel hn1, hpowG j hj γ]
  have hsum0 : ∀ χ : G → R, (∀ γ γ', χ (γ * γ') = χ γ * χ γ') → ∀ γ0, χ γ0 ≠ 1 →
      ∑ γ, χ γ = 0 := by
    intro χ hχ γ0 h0
    have e : ∑ γ, χ γ = χ γ0 * ∑ γ, χ γ := by
      rw [Finset.mul_sum]
      exact (Fintype.sum_bijective (γ0 * ·) (Group.mulLeft_bijective γ0) (fun γ => χ γ0 * χ γ) χ
        (fun γ => (hχ γ0 γ).symm)).symm
    have e2 : (1 - χ γ0) * ∑ γ, χ γ = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    have e3 := congrArg (algebraMap R C) e2
    rw [map_mul, map_zero] at e3
    rcases mul_eq_zero.mp e3 with h | h
    · exact absurd (sub_eq_zero.mp (hv.hom_inj (h.trans (map_zero _).symm))).symm h0
    · exact hv.hom_inj (h.trans (map_zero _).symm)
  have hPe : ∀ (c : G → R) j, (∑ γ, c γ • (A γ).map (algebraMap ℤ_[p] R)) * εT j =
      (∑ γ, c γ * ψ j γ) • εT j := by
    intro c j
    rw [Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Matrix.smul_mul, heig, smul_smul]
  have hdecomp : ∀ M : Matrix n n R, M = ∑ j, M * εT j := fun M => by
    rw [← Finset.mul_sum, hsum, Matrix.mul_one]
  by_contra hcon
  push_neg at hcon
  have hP'0 : (∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p • (A γ).map (algebraMap ℤ_[p] R)) = 0 := by
    rw [hdecomp (∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p • (A γ).map (algebraMap ℤ_[p] R))]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : εT j = 0
    · rw [hj, Matrix.mul_zero]
    · rw [hPe (fun γ => (ψ i γ ^ (Fintype.card G - 1)) ^ p) j]
      obtain ⟨γ0, hγ0⟩ := hcon j hj
      have hz := hsum0 (fun γ => (ψ i γ ^ (Fintype.card G - 1)) ^ p * ψ j γ)
        (fun γ γ' => by simp only [hmul i hi, hmul j hj]; ring) γ0 (by
          intro h1
          apply hγ0
          try simp only at h1
          calc ψ j γ0 = (ψ i γ0 ^ (Fintype.card G - 1) * ψ i γ0) ^ p * ψ j γ0 := by
                rw [hiv i hi, one_pow, one_mul]
            _ = ((ψ i γ0 ^ (Fintype.card G - 1)) ^ p * ψ j γ0) * ψ i γ0 ^ p := by ring
            _ = ψ i γ0 ^ p := by rw [h1, one_mul])
      try simp only at hz
      rw [hz, zero_smul]
  have hPi : (∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)) =
      (Fintype.card G : R) • εT i := by
    rw [hdecomp (∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)),
      Finset.sum_eq_single i]
    · rw [hPe (fun γ => ψ i γ ^ (Fintype.card G - 1)) i]
      simp only [hiv i hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    · intro j _ hji
      by_cases hj : εT j = 0
      · rw [hj, Matrix.mul_zero]
      · rw [hPe (fun γ => ψ i γ ^ (Fintype.card G - 1)) j]
        obtain ⟨γ0, hγ0⟩ := hsep j i hj hi hji
        have hz := hsum0 (fun γ => ψ i γ ^ (Fintype.card G - 1) * ψ j γ)
          (fun γ γ' => by simp only [hmul i hi, hmul j hj]; ring) γ0 (by
            intro h1
            apply hγ0
            try simp only at h1
            calc ψ j γ0 = (ψ i γ0 ^ (Fintype.card G - 1) * ψ i γ0) * ψ j γ0 := by
                  rw [hiv i hi, one_mul]
              _ = (ψ i γ0 ^ (Fintype.card G - 1) * ψ j γ0) * ψ i γ0 := by ring
              _ = ψ i γ0 := by rw [h1, one_mul])
        try simp only at hz
        rw [hz, zero_smul]
    · simp
  obtain ⟨a, b, hab⟩ : ∃ a b, εT i a b ∉ mI hv := by
    by_contra hc
    push_neg at hc
    exact hi (idem_eq_zero hv (εT i) (by rw [horth, if_pos rfl]) hc)
  haveI := charP p hv hpv
  have hfrob : res hv ((∑ γ, (ψ i γ ^ (Fintype.card G - 1)) ^ p •
      (A γ).map (algebraMap ℤ_[p] R)) a b) =
      res hv ((∑ γ, ψ i γ ^ (Fintype.card G - 1) • (A γ).map (algebraMap ℤ_[p] R)) a b) ^ p := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum, map_mul,
      map_pow]
    rw [sum_pow_char]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [mul_pow, fermat p hv hpv]
  have hres_n : res hv (Fintype.card G : R) ≠ 0 := by
    intro h0
    have h1 : IsUnit (res hv (Fintype.card G : R)) := hG.map (res hv)
    rw [h0] at h1
    exact not_isUnit_zero h1
  have hres_e : res hv (εT i a b) ≠ 0 := by
    intro h0
    exact hab (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  rw [hP'0, hPi] at hfrob
  simp only [Matrix.zero_apply, map_zero, Matrix.smul_apply, smul_eq_mul, map_mul] at hfrob
  exact pow_ne_zero p (mul_ne_zero hres_n hres_e) hfrob.symm

end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
