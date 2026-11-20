import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ

/- English proof (translation)
The claim follows from `(ZMod.intCast_eq_intCast_iff_dvd_sub x y k).2 (by rw [← neg_sub]; exact dvd_neg.2 h)`.
-/
theorem intCast_eq_of_dvd_sub {k : ℕ} {x y : ℤ} (h : (k : ℤ) ∣ x - y) : (x : ZMod k) = (y : ZMod k) :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub x y k).2 (by rw [← neg_sub]; exact dvd_neg.2 h)

/- English proof (translation)
Introduce `N l a M _ hl _ hlN _ hlM`. Take `⟨Q, hQ⟩ : ∃ Q : ℤ, Q = ((M * N : ℕ) : ℤ)` from `⟨_, rfl⟩`. Take `⟨L, hL⟩ : ∃ L : ℤ, L = ((l ^ (a + 1) : ℕ) : ℤ)` from `⟨_, rfl⟩`. Establish `hcop : IsCoprime Q L`. Rewrite using `[hQ, hL, Nat.isCoprime_iff_coprime]`.

Conclude with `Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2 (fun h => (hl.dvd_mul.1 h).elim hlM hlN)))`. Take `⟨α, β, hab⟩` from `hcop`. Take `⟨t, ht⟩ : ∃ t : ℤ, t = β * L - α * Q` from `⟨_, rfl⟩`. Take `⟨m, hm⟩ : ∃ m : ℤ, m = Q * L` from `⟨_, rfl⟩`. Establish `e1 : t * t + m * (4 * α * β) = 1`.

Rewrite using `[ht, hm]`. Take the linear combination `(α * Q + β * L + 1) * hab`. Establish `hc : IsCoprime t (m ^ 2)` using `IsCoprime.pow_right ⟨t, 4 * α * β, by linear_combination e1⟩`. Take `⟨u, v, e2⟩` from `hc`. Establish `hut : u - t = m * (4 * α * β * u - t * v * m)` using `by linear_combination (-u) * e1 + t * e2`.

Establish `ht1 : t - 1 = Q * (-2 * α)` using `by rw [ht]; linear_combination hab`. Establish `ht2 : t - -1 = L * (2 * β)` using `by rw [ht]; linear_combination (-1 : ℤ) * hab`. Take `⟨c, hcm⟩ : ∃ c : SL(2, ℤ), (c : Matrix (Fin 2) (Fin 2) ℤ) = !![t, -(m * v); m, u]` from `⟨⟨!![t, -(m * v); m, u], by rw [Matrix.det_fin_two_of]; linear_combination e2⟩, rfl⟩`. Establish `h00 : (c : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = t` using `by rw [hcm]; rfl`. Establish `h01 : (c : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -(m * v)` using `by rw [hcm]; rfl`.

Establish `h10 : (c : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = m` using `by rw [hcm]; rfl`. Establish `h11 : (c : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = u` using `by rw [hcm]; rfl`. Establish `hNQ : (N : ℤ) ∣ Q` using `hQ ▸ Int.natCast_dvd_natCast.2 (dvd_mul_left N M)`. Establish `hlaL : ((l ^ a : ℕ) : ℤ) ∣ L` using `hL ▸ Int.natCast_dvd_natCast.2 (pow_dvd_pow l (Nat.le_succ a))`. Establish `hlL : (l : ℤ) ∣ L` using `hL ▸ Int.natCast_dvd_natCast.2 (dvd_pow_self l (Nat.succ_ne_zero a))`.

Establish `hKm : ((M * N * l ^ a : ℕ) : ℤ) ∣ m`. Rewrite using `[hm, hQ, hL, ← Nat.cast_mul]`. Conclude with `Int.natCast_dvd_natCast.2 (Nat.mul_dvd_mul_left _ (pow_dvd_pow l (Nat.le_succ a)))`. Establish `hNm : (N : ℤ) ∣ m` using `hm ▸ hNQ.mul_right L`. Establish `hlm : (l : ℤ) ∣ m` using `hm ▸ hlL.mul_left Q`.

Establish `hlam : ((l ^ a : ℕ) : ℤ) ∣ m` using `hm ▸ hlaL.mul_left Q`. Establish `tN : ((t : ℤ) : ZMod N) = 1`. Simplify using `using intCast_eq_of_dvd_sub (k := N) (y := 1) (hNQ.trans ⟨_, ht1⟩)`. Establish `uN : ((u : ℤ) : ZMod N) = 1`. Establish `hd : (N : ℤ) ∣ u - 1`.

Rewrite using `[show u - 1 = (u - t) + (t - 1) by ring]`. Conclude with `dvd_add (hNm.trans ⟨_, hut⟩) (hNQ.trans ⟨_, ht1⟩)`. Simplify using `using intCast_eq_of_dvd_sub (k := N) hd`. Establish `mN : ((m : ℤ) : ZMod N) = 0` using `by simpa using intCast_eq_of_dvd_sub (k := N) (y := 0) (by simpa using hNm)`. Establish `ml : ((m : ℤ) : ZMod l) = 0` using `by simpa using intCast_eq_of_dvd_sub (k := l) (y := 0) (by simpa using hlm)`.

Establish `tla : ((t : ℤ) : ZMod (l ^ a)) = -1`. Simplify using `using intCast_eq_of_dvd_sub (k := l ^ a) (y := -1) (hlaL.trans ⟨_, ht2⟩)`. Establish `ula : ((u : ℤ) : ZMod (l ^ a)) = -1`. Establish `hd : ((l ^ a : ℕ) : ℤ) ∣ u - -1`. Rewrite using `[show u - -1 = (u - t) + (t - -1) by ring]`.

Conclude with `dvd_add (hlam.trans ⟨_, hut⟩) (hlaL.trans ⟨_, ht2⟩)`. Simplify using `using intCast_eq_of_dvd_sub (k := l ^ a) hd`. Establish `mla : ((m : ℤ) : ZMod (l ^ a)) = 0`. Simplify `hlam)` using `using intCast_eq_of_dvd_sub (k := l ^ a) (y := 0) (by simpa`. Establish `mK : ((m : ℤ) : ZMod (M * N * l ^ a)) = 0`.

Simplify `hKm)` using `using intCast_eq_of_dvd_sub (k := M * N * l ^ a) (y := 0) (by simpa`. Establish `uK : ((u : ℤ) : ZMod (M * N * l ^ a)) = t` using `intCast_eq_of_dvd_sub (hKm.trans ⟨_, hut⟩)`. Use `⟨c, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Gam, Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem]`. Simplify using `only [h00, h11, h10, tN, uN, mN, ml, and_self]`.

Introduce `g`. Rewrite using `[CongruenceSubgroup.Gamma_mem', map_mul, map_mul, map_mul, map_inv, map_inv]`. Use `set φ := Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod (M * N * l ^ a)))`. Establish `hsc : (↑(φ c) : Matrix (Fin 2) (Fin 2) (ZMod (M * N * l ^ a))) = ((t : ℤ) : ZMod (M * N * l ^ a)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod (M * N * l ^ a)))`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[φ, Matrix.SpecialLinearGroup.map_apply_coe, h00, h01, h10, h11, mK, uK]`. Establish `hcomm : φ c * φ g = φ g * φ c`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Matrix.SpecialLinearGroup.coe_mul]`.

Rewrite using `[hsc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]`. Rewrite using `[hcomm, mul_inv_cancel_right, mul_inv_cancel]`. Apply the tactic sequence `intro i j fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, tla, ula, mla]`.
-/
theorem exists_scalar_mod_level : ∀ (N l a M : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → 0 < M → ¬ l ∣ M →
    ∃ c ∈ Gam N l, (∀ g : SL(2, ℤ), c * g * c⁻¹ * g⁻¹ ∈ CongruenceSubgroup.Gamma (M * N * l ^ a)) ∧
      ∀ i j, (((c : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (l ^ a)) = if i = j then -1 else 0 := by
  intro N l a M _ hl _ hlN _ hlM
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = ((M * N : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = ((l ^ (a + 1) : ℕ) : ℤ) := ⟨_, rfl⟩
  have hcop : IsCoprime Q L := by
    rw [hQ, hL, Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2
      (fun h => (hl.dvd_mul.1 h).elim hlM hlN)))
  obtain ⟨α, β, hab⟩ := hcop
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = β * L - α * Q := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = Q * L := ⟨_, rfl⟩
  have e1 : t * t + m * (4 * α * β) = 1 := by
    rw [ht, hm]; linear_combination (α * Q + β * L + 1) * hab
  have hc : IsCoprime t (m ^ 2) := IsCoprime.pow_right ⟨t, 4 * α * β, by linear_combination e1⟩
  obtain ⟨u, v, e2⟩ := hc
  have hut : u - t = m * (4 * α * β * u - t * v * m) := by linear_combination (-u) * e1 + t * e2
  have ht1 : t - 1 = Q * (-2 * α) := by rw [ht]; linear_combination hab
  have ht2 : t - -1 = L * (2 * β) := by rw [ht]; linear_combination (-1 : ℤ) * hab
  obtain ⟨c, hcm⟩ : ∃ c : SL(2, ℤ), (c : Matrix (Fin 2) (Fin 2) ℤ) = !![t, -(m * v); m, u] :=
    ⟨⟨!![t, -(m * v); m, u], by rw [Matrix.det_fin_two_of]; linear_combination e2⟩, rfl⟩
  have h00 : (c : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = t := by rw [hcm]; rfl
  have h01 : (c : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -(m * v) := by rw [hcm]; rfl
  have h10 : (c : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = m := by rw [hcm]; rfl
  have h11 : (c : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = u := by rw [hcm]; rfl
  have hNQ : (N : ℤ) ∣ Q := hQ ▸ Int.natCast_dvd_natCast.2 (dvd_mul_left N M)
  have hlaL : ((l ^ a : ℕ) : ℤ) ∣ L := hL ▸ Int.natCast_dvd_natCast.2 (pow_dvd_pow l (Nat.le_succ a))
  have hlL : (l : ℤ) ∣ L := hL ▸ Int.natCast_dvd_natCast.2 (dvd_pow_self l (Nat.succ_ne_zero a))
  have hKm : ((M * N * l ^ a : ℕ) : ℤ) ∣ m := by
    rw [hm, hQ, hL, ← Nat.cast_mul]
    exact Int.natCast_dvd_natCast.2 (Nat.mul_dvd_mul_left _ (pow_dvd_pow l (Nat.le_succ a)))
  have hNm : (N : ℤ) ∣ m := hm ▸ hNQ.mul_right L
  have hlm : (l : ℤ) ∣ m := hm ▸ hlL.mul_left Q
  have hlam : ((l ^ a : ℕ) : ℤ) ∣ m := hm ▸ hlaL.mul_left Q

  have tN : ((t : ℤ) : ZMod N) = 1 := by
    simpa using intCast_eq_of_dvd_sub (k := N) (y := 1) (hNQ.trans ⟨_, ht1⟩)
  have uN : ((u : ℤ) : ZMod N) = 1 := by
    have hd : (N : ℤ) ∣ u - 1 := by
      rw [show u - 1 = (u - t) + (t - 1) by ring]
      exact dvd_add (hNm.trans ⟨_, hut⟩) (hNQ.trans ⟨_, ht1⟩)
    simpa using intCast_eq_of_dvd_sub (k := N) hd
  have mN : ((m : ℤ) : ZMod N) = 0 := by simpa using intCast_eq_of_dvd_sub (k := N) (y := 0) (by simpa using hNm)
  have ml : ((m : ℤ) : ZMod l) = 0 := by simpa using intCast_eq_of_dvd_sub (k := l) (y := 0) (by simpa using hlm)

  have tla : ((t : ℤ) : ZMod (l ^ a)) = -1 := by
    simpa using intCast_eq_of_dvd_sub (k := l ^ a) (y := -1) (hlaL.trans ⟨_, ht2⟩)
  have ula : ((u : ℤ) : ZMod (l ^ a)) = -1 := by
    have hd : ((l ^ a : ℕ) : ℤ) ∣ u - -1 := by
      rw [show u - -1 = (u - t) + (t - -1) by ring]
      exact dvd_add (hlam.trans ⟨_, hut⟩) (hlaL.trans ⟨_, ht2⟩)
    simpa using intCast_eq_of_dvd_sub (k := l ^ a) hd
  have mla : ((m : ℤ) : ZMod (l ^ a)) = 0 := by
    simpa using intCast_eq_of_dvd_sub (k := l ^ a) (y := 0) (by simpa using hlam)

  have mK : ((m : ℤ) : ZMod (M * N * l ^ a)) = 0 := by
    simpa using intCast_eq_of_dvd_sub (k := M * N * l ^ a) (y := 0) (by simpa using hKm)
  have uK : ((u : ℤ) : ZMod (M * N * l ^ a)) = t := intCast_eq_of_dvd_sub (hKm.trans ⟨_, hut⟩)
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [Gam, Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem]
    simp only [h00, h11, h10, tN, uN, mN, ml, and_self]
  · intro g
    rw [CongruenceSubgroup.Gamma_mem', map_mul, map_mul, map_mul, map_inv, map_inv]
    set φ := Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod (M * N * l ^ a)))
    have hsc : (↑(φ c) : Matrix (Fin 2) (Fin 2) (ZMod (M * N * l ^ a))) =
        ((t : ℤ) : ZMod (M * N * l ^ a)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod (M * N * l ^ a))) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [φ, Matrix.SpecialLinearGroup.map_apply_coe, h00, h01, h10, h11, mK, uK]
    have hcomm : φ c * φ g = φ g * φ c := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hsc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    rw [hcomm, mul_inv_cancel_right, mul_inv_cancel]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, tla, ula, mla]

end GlobalTheory.KZ
