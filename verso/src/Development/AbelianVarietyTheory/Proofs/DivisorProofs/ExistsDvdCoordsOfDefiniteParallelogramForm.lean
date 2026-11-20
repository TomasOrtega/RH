import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `h0 : Q 0 = 0`. Use `hQ 0 0` as an intermediate fact. Simplify using `only [add_zero, sub_zero] at this`. Use linear arithmetic over natural numbers and integers. Establish `hneg : ∀ g, Q (-g) = Q g`.

Introduce `g`. Use `hQ 0 g` as an intermediate fact. Simplify using `only [zero_add, zero_sub, h0] at this`. Use linear arithmetic over natural numbers and integers. Establish `hnat : ∀ n : ℕ, Q ((n : ℤ) • f) = (n : ℤ) ^ 2 * Q f ∧ Q (((n : ℤ) + 1) • f) = ((n : ℤ) + 1) ^ 2 * Q f`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [h0]`. Consider the case `succ n ih`. Use `⟨by push_cast; exact ih.2, ?_⟩` and prove the remaining obligations.

Establish `h` using `hQ (((n : ℤ) + 1) • f) f`. Establish `e1 : ((n : ℤ) + 1) • f + f = (((n + 1 : ℕ) : ℤ) + 1) • f` using `by push_cast; module`. Establish `e2 : ((n : ℤ) + 1) • f - f = (n : ℤ) • f` using `by module`. Rewrite `h` using `[e1, e2, ih.1, ih.2]`. Move the coercions through the operations in `at h ⊢`.

Take the linear combination `h`. Take `⟨n, rfl | rfl⟩` from `k.eq_nat_or_neg`. Conclude with `(hnat n).1`. Rewrite using `[neg_smul, hneg, (hnat n).1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem parallelogram_zsmul {E : Type} [AddCommGroup E] (Q : E → ℤ)
    (hQ : ∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) (k : ℤ) (f : E) :
    Q (k • f) = k ^ 2 * Q f := by
  have h0 : Q 0 = 0 := by
    have := hQ 0 0
    simp only [add_zero, sub_zero] at this
    omega
  have hneg : ∀ g, Q (-g) = Q g := by
    intro g
    have := hQ 0 g
    simp only [zero_add, zero_sub, h0] at this
    omega
  have hnat : ∀ n : ℕ, Q ((n : ℤ) • f) = (n : ℤ) ^ 2 * Q f ∧
      Q (((n : ℤ) + 1) • f) = ((n : ℤ) + 1) ^ 2 * Q f := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have h := hQ (((n : ℤ) + 1) • f) f
      have e1 : ((n : ℤ) + 1) • f + f = (((n + 1 : ℕ) : ℤ) + 1) • f := by
        push_cast; module
      have e2 : ((n : ℤ) + 1) • f - f = (n : ℤ) • f := by module
      rw [e1, e2, ih.1, ih.2] at h
      push_cast at h ⊢
      linear_combination h
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · exact (hnat n).1
  · rw [neg_smul, hneg, (hnat n).1]; ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `⟨0, fun z M _ => ?_⟩` and prove the remaining obligations. Use `parallelogram_zsmul Q hQ 0 0` as an intermediate fact. Simplify using `at this`.

Simplify using `[this]`. Consider the case `insert a s ha ih`. Take `⟨C, hC⟩` from `ih`. Use `⟨2 * (Q (u a)).toNat + 2 * C, fun z M hz => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_insert ha]`.

Establish `h1` using `hQ (z a • u a) (∑ i ∈ s, z i • u i)`. Establish `h2` using `hpos (z a • u a - ∑ i ∈ s, z i • u i)`. Establish `h3` using `hC z M hz`. Establish `h4` using `parallelogram_zsmul Q hQ (z a) (u a)`. Establish `h5 : z a ^ 2 ≤ M ^ 2`.

Rewrite using `[← sq_abs (z a)]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) (hz a) 2`. Establish `h6` using `mul_le_mul_of_nonneg_right h5 (hpos (u a))`. Use `push_cast`. Rewrite using `[Int.toNat_of_nonneg (hpos (u a))]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem parallelogram_sum_le {E ι : Type} [AddCommGroup E] (Q : E → ℤ)
    (hQ : ∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) (hpos : ∀ f, 0 ≤ Q f)
    (u : ι → E) (s : Finset ι) :
    ∃ C : ℕ, ∀ (z : ι → ℤ) (M : ℤ), (∀ i, |z i| ≤ M) →
      Q (∑ i ∈ s, z i • u i) ≤ C * M ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, fun z M _ => ?_⟩
    have := parallelogram_zsmul Q hQ 0 0
    simp at this
    simp [this]
  | insert a s ha ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨2 * (Q (u a)).toNat + 2 * C, fun z M hz => ?_⟩
    rw [Finset.sum_insert ha]
    have h1 := hQ (z a • u a) (∑ i ∈ s, z i • u i)
    have h2 := hpos (z a • u a - ∑ i ∈ s, z i • u i)
    have h3 := hC z M hz
    have h4 := parallelogram_zsmul Q hQ (z a) (u a)
    have h5 : z a ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs (z a)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hz a) 2
    have h6 := mul_le_mul_of_nonneg_right h5 (hpos (u a))
    push_cast
    rw [Int.toNat_of_nonneg (hpos (u a))]
    nlinarith

/- English proof (translation)
Introduce `E _ H Q hQ hpos hdef n u hu hli`. Take `⟨C, hC⟩` from `parallelogram_sum_le Q hQ hpos u Finset.univ`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Use `set R : ℕ := C + 1 with hR`. Use `⟨(R ^ n).factorial, Nat.factorial_pos _, fun k m h hh hk => ?_⟩` and prove the remaining obligations.

Break down `Nat.eq_zero_or_pos k with rfl | hkpos` into its components or cases. Introduce `i`. Use `hli m (by simpa using hk.symm) i` as an intermediate fact. Simplify using `[this]`. Establish `hk0 : (0 : ℤ) < k` using `by exact_mod_cast hkpos`.

Establish `hR0 : (0 : ℤ) < R` using `by positivity`. Take `⟨a, ha, b, hb, hab, hf⟩` from `Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (R ^ n + 1)) (t := Fintype.piFinset (fun _ : Fin n => Finset.Ico (0 : ℤ) R)) (f := fun (j : ℕ) (i : Fin n) => ((R : ℤ) * (((j : ℤ) * m i) % k)) / k) (by simp [Fintype.card_piFinset]) (by`. Introduce `j _`. Simplify using `only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Ico]`. Introduce `i`.

Establish `h1` using `Int.emod_nonneg ((j : ℤ) * m i) hk0.ne'`. Establish `h2` using `Int.emod_lt_of_pos ((j : ℤ) * m i) hk0`. Use `⟨Int.ediv_nonneg (by positivity) hk0.le, ?_⟩` and prove the remaining obligations. Apply `Int.ediv_lt_of_lt_mul hk0` to reduce the goal to its premises. Conclude with `mul_lt_mul_of_pos_left h2 hR0)`.

Use `set y : Fin n → ℤ := fun i => ((a : ℤ) * m i) % k - ((b : ℤ) * m i) % k with hy`. Use `set q : Fin n → ℤ := fun i => ((a : ℤ) * m i) / k - ((b : ℤ) * m i) / k with hq`. Establish `hyq : ∀ i, y i = ((a : ℤ) - b) * m i - k * q i`. Introduce `i`. Simplify using `only [hy, hq, Int.emod_def]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hbound : ∀ i, |(R : ℤ) * y i| ≤ k`. Introduce `i`. Establish `e` using `congrFun hf i`. Use `beta_reduce at e`.

Establish `a1` using `Int.emod_nonneg ((R : ℤ) * (((a : ℤ) * m i) % k)) hk0.ne'`. Establish `a2` using `Int.emod_lt_of_pos ((R : ℤ) * (((a : ℤ) * m i) % k)) hk0`. Establish `b1` using `Int.emod_nonneg ((R : ℤ) * (((b : ℤ) * m i) % k)) hk0.ne'`. Establish `b2` using `Int.emod_lt_of_pos ((R : ℤ) * (((b : ℤ) * m i) % k)) hk0`. Rewrite `a1`, `a2`, `b1`, `b2` using `[Int.emod_def]`.

Rewrite `a1`, `a2` using `[e]`. Simplify using `only [hy]`. Rewrite using `[abs_le, mul_sub]`. Apply the tactic sequence `constructor <;> linarith`. Use `set w : E := ((a : ℤ) - b) • h - ∑ i, q i • u i with hw`.

Establish `hwH : w ∈ H` using `H.sub_mem (H.zsmul_mem hh _) (H.sum_mem fun i _ => H.zsmul_mem (hu i) _)`. Establish `hkw : (k : ℤ) • w = ∑ i, y i • u i`. Rewrite using `[hw, smul_sub, smul_comm, natCast_zsmul h k, hk, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hyq i, smul_smul, smul_smul, sub_smul]`.

Establish `hRkw : ((R : ℤ) * k) • w = ∑ i, ((R : ℤ) * y i) • u i`. Rewrite using `[mul_smul, hkw, Finset.smul_sum]`. Simplify using `only [smul_smul]`. Establish `hle` using `hC (fun i => (R : ℤ) * y i) k hbound`. Rewrite `hle` using `[← hRkw, parallelogram_zsmul Q hQ]`.

Establish `hQw : Q w = 0`. Assume the negation of the conclusion as `hne`. Establish `h1 : 1 ≤ Q w` using `by have := hpos w; omega`. Establish `h2 : ((R : ℤ) * k) ^ 2 ≤ ((R : ℤ) * k) ^ 2 * Q w` using `le_mul_of_one_le_right (by positivity) h1`. Establish `h3 : (C : ℤ) < (R : ℤ) ^ 2`.

Rewrite using `[hR]`. Use `push_cast`. Use polynomial arithmetic with `[Int.natCast_nonneg C]`. Establish `h4` using `mul_lt_mul_of_pos_right h3 (show (0 : ℤ) < (k : ℤ) ^ 2 by positivity)`. Rewrite `h2`, `hle` using `[mul_pow]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hw0` using `hdef w hwH hQw`. Rewrite `hkw` using `[hw0, smul_zero]`. Introduce `i`. Establish `hyi` using `hli y hkw.symm i`.

Establish `hd : (k : ℤ) ∣ ((a : ℤ) - b) * m i` using `⟨q i, by have := hyq i; linarith⟩`. Use `hd.trans (mul_dvd_mul_right ?_ _)` and prove the remaining obligations. Rewrite using `[← Int.natAbs_dvd, Int.natCast_dvd_natCast]`. Rewrite `ha`, `hb` using `[Finset.mem_range]`. Apply `Nat.dvd_factorial` to reduce the goal to its premises.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_dvd_coords_of_definite_form :
    ∀ (E : Type) [AddCommGroup E] (H : AddSubgroup E) (Q : E → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f ∈ H, Q f = 0 → f = 0) → ∀ (n : ℕ) (u : Fin n → E), (∀ i, u i ∈ H) → LinearIndependent ℤ u → ∃ e : ℕ, 0 < e ∧ ∀ (k : ℕ) (m : Fin n → ℤ) (h : E), h ∈ H → k • h = ∑ i, m i • u i → ∀ i, (k : ℤ) ∣ e * m i := by
  intro E _ H Q hQ hpos hdef n u hu hli
  obtain ⟨C, hC⟩ := parallelogram_sum_le Q hQ hpos u Finset.univ
  rw [Fintype.linearIndependent_iff] at hli
  set R : ℕ := C + 1 with hR
  refine ⟨(R ^ n).factorial, Nat.factorial_pos _, fun k m h hh hk => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · intro i
    have := hli m (by simpa using hk.symm) i
    simp [this]
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hR0 : (0 : ℤ) < R := by positivity
  obtain ⟨a, ha, b, hb, hab, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (R ^ n + 1))
    (t := Fintype.piFinset (fun _ : Fin n => Finset.Ico (0 : ℤ) R))
    (f := fun (j : ℕ) (i : Fin n) => ((R : ℤ) * (((j : ℤ) * m i) % k)) / k)
    (by simp [Fintype.card_piFinset])
    (by
      intro j _
      simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Ico]
      intro i
      have h1 := Int.emod_nonneg ((j : ℤ) * m i) hk0.ne'
      have h2 := Int.emod_lt_of_pos ((j : ℤ) * m i) hk0
      refine ⟨Int.ediv_nonneg (by positivity) hk0.le, ?_⟩
      apply Int.ediv_lt_of_lt_mul hk0
      exact mul_lt_mul_of_pos_left h2 hR0)
  set y : Fin n → ℤ := fun i => ((a : ℤ) * m i) % k - ((b : ℤ) * m i) % k with hy
  set q : Fin n → ℤ := fun i => ((a : ℤ) * m i) / k - ((b : ℤ) * m i) / k with hq
  have hyq : ∀ i, y i = ((a : ℤ) - b) * m i - k * q i := by
    intro i
    simp only [hy, hq, Int.emod_def]
    ring
  have hbound : ∀ i, |(R : ℤ) * y i| ≤ k := by
    intro i
    have e := congrFun hf i
    beta_reduce at e
    have a1 := Int.emod_nonneg ((R : ℤ) * (((a : ℤ) * m i) % k)) hk0.ne'
    have a2 := Int.emod_lt_of_pos ((R : ℤ) * (((a : ℤ) * m i) % k)) hk0
    have b1 := Int.emod_nonneg ((R : ℤ) * (((b : ℤ) * m i) % k)) hk0.ne'
    have b2 := Int.emod_lt_of_pos ((R : ℤ) * (((b : ℤ) * m i) % k)) hk0
    rw [Int.emod_def] at a1 a2 b1 b2
    rw [e] at a1 a2
    simp only [hy]
    rw [abs_le, mul_sub]
    constructor <;> linarith
  set w : E := ((a : ℤ) - b) • h - ∑ i, q i • u i with hw
  have hwH : w ∈ H := H.sub_mem (H.zsmul_mem hh _) (H.sum_mem fun i _ => H.zsmul_mem (hu i) _)
  have hkw : (k : ℤ) • w = ∑ i, y i • u i := by
    rw [hw, smul_sub, smul_comm, natCast_zsmul h k, hk, Finset.smul_sum, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hyq i, smul_smul, smul_smul, sub_smul]
  have hRkw : ((R : ℤ) * k) • w = ∑ i, ((R : ℤ) * y i) • u i := by
    rw [mul_smul, hkw, Finset.smul_sum]
    simp only [smul_smul]
  have hle := hC (fun i => (R : ℤ) * y i) k hbound
  rw [← hRkw, parallelogram_zsmul Q hQ] at hle
  have hQw : Q w = 0 := by
    by_contra hne
    have h1 : 1 ≤ Q w := by have := hpos w; omega
    have h2 : ((R : ℤ) * k) ^ 2 ≤ ((R : ℤ) * k) ^ 2 * Q w := le_mul_of_one_le_right (by positivity) h1
    have h3 : (C : ℤ) < (R : ℤ) ^ 2 := by
      rw [hR]; push_cast; nlinarith [Int.natCast_nonneg C]
    have h4 := mul_lt_mul_of_pos_right h3 (show (0 : ℤ) < (k : ℤ) ^ 2 by positivity)
    rw [mul_pow] at h2 hle
    linarith
  have hw0 := hdef w hwH hQw
  rw [hw0, smul_zero] at hkw
  intro i
  have hyi := hli y hkw.symm i
  have hd : (k : ℤ) ∣ ((a : ℤ) - b) * m i := ⟨q i, by have := hyq i; linarith⟩
  refine hd.trans (mul_dvd_mul_right ?_ _)
  rw [← Int.natAbs_dvd, Int.natCast_dvd_natCast]
  rw [Finset.mem_range] at ha hb
  apply Nat.dvd_factorial
  · omega
  · omega

end GlobalTheory
