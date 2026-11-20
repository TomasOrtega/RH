import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

/- English proof (translation)
Introduce `R _ _ p hp π M d ζ hζ hv hMd`. Establish `hpp : p.Prime` using `hp.out`. Establish `hM : M ≠ 0`. Introduce and unpack `rfl`. Rewrite `hMd` using `[zero_mul]`.

Use `hpp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hd : d ≠ 0`. Introduce and unpack `rfl`. Rewrite `hMd` using `[mul_zero]`.

Use `hpp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `haveI : NeZero M := ⟨hM⟩`. Establish `U : ∀ r s : R, r ^ M = 1 → s ^ M = 1 → π r = π s → r = s`. Introduce `r s hr hs h`.

Take `⟨i, hi, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hr`. Take `⟨j, hj, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hs`. Rewrite `h` using `[map_pow, map_pow]`. Rewrite using `[hv.pow_inj hi hj h]`. Establish `E : ∀ y : ZMod p, y ^ M = 1 → ∃ r : R, r ^ M = 1 ∧ π r = y`.

Introduce `y hy`. Take `⟨i, -, rfl⟩` from `hv.eq_pow_of_pow_eq_one hy`. Use `⟨ζ ^ i, ?_, by rw [map_pow]⟩` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]`. Establish `P : ∀ x : ZMod p, x ≠ 0 → (x ^ d) ^ M = 1`.

Introduce `x hx`. Rewrite using `[← pow_mul, mul_comm, hMd]`. Conclude with `ZMod.pow_card_sub_one_eq_one hx`. Set `L : ZMod p → R` to `fun x => if h : x = 0 then 0 else (E _ (P x h)).choose`. Establish `L1 : ∀ x (h : x ≠ 0), L x ^ M = 1 ∧ π (L x) = x ^ d`.

Introduce `x h`. Simplify using `only [L, dif_neg h]`. Conclude with `(E _ (P x h)).choose_spec`. Establish `L0 : L 0 = 0` using `by simp [L]`. Set `χ : MulChar (ZMod p) R` to `{ toFun := L map_one' := by`.

Establish `h1` using `L1 1 one_ne_zero`. Conclude with `U _ _ h1.1 (one_pow M) (by rw [h1.2, one_pow, map_one])`. Use the proof step `map_mul' := by`. Introduce `x y`. Distinguish the cases in `hx : x = 0`.

Rewrite using `[hx, zero_mul, L0, zero_mul]`. Distinguish the cases in `hy : y = 0`. Rewrite using `[hy, mul_zero, L0, mul_zero]`. Establish `hxy` using `L1 (x * y) (mul_ne_zero hx hy)`. Establish `h1` using `L1 x hx`.

Establish `h2` using `L1 y hy`. Use `U _ _ hxy.1 (by rw [mul_pow, h1.1, h2.1, one_mul]) ?_` and prove the remaining obligations. Rewrite using `[hxy.2, map_mul, h1.2, h2.2, mul_pow]`. Use the proof step `map_nonunit' := by`. Introduce `a ha`.

Establish `: a = 0`. Assume the negation of the conclusion as `h`. Conclude with `ha (isUnit_iff_ne_zero.mpr h)`. Rewrite using `[this]`. Conclude with `L0 }`.

Establish `hχ : ∀ x : ZMod p, x ≠ 0 → χ x ^ M = 1 ∧ π (χ x) = x ^ d` using `L1`. Use `⟨χ, hχ, ?_⟩` and prove the remaining obligations. Establish `hpow : χ ^ M = 1`. Use extensionality with `a`. Rewrite using `[MulChar.pow_apply_coe, MulChar.one_apply_coe]`.

Conclude with `(hχ a a.ne_zero).1`. Establish `hdvd : orderOf χ ∣ M` using `orderOf_dvd_of_pow_eq_one hpow`. Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := (ZMod p)ˣ)`. Establish `hog : orderOf g = p - 1`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]`.

Use `set k := orderOf χ with hk`. Establish `hk1 : χ ^ k = 1` using `pow_orderOf_eq_one χ`. Establish `hgk : (χ g) ^ k = 1`. Rewrite using `[← MulChar.pow_apply_coe, hk1, MulChar.one_apply_coe]`. Establish `hgdk : g ^ (d * k) = 1`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_one, pow_mul, ← (hχ g g.ne_zero).2, ← map_pow, hgk, map_one]`. Establish `h2 : M * d ∣ d * k`. Rewrite using `[hMd, ← hog]`. Conclude with `orderOf_dvd_of_pow_eq_one hgdk`.

Rewrite `h2` using `[mul_comm M d]`. Establish `h3 : M ∣ k` using `(Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd)).mp h2`. Conclude with `Nat.dvd_antisymm hdvd h3`.
-/
theorem UpperTheory.V.Stick.teich :
    ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ) [Fact p.Prime] (π : R →+* ZMod p) (M d : ℕ) (ζ : R),
    IsPrimitiveRoot ζ M → IsPrimitiveRoot (π ζ) M → M * d = p - 1 →
    ∃ χ : MulChar (ZMod p) R, (∀ x : ZMod p, x ≠ 0 → χ x ^ M = 1 ∧ π (χ x) = x ^ d) ∧ orderOf χ = M := by
  intro R _ _ p hp π M d ζ hζ hv hMd
  have hpp : p.Prime := hp.out
  have hM : M ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hMd
    have := hpp.two_le
    omega
  have hd : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hMd
    have := hpp.two_le
    omega
  haveI : NeZero M := ⟨hM⟩
  have U : ∀ r s : R, r ^ M = 1 → s ^ M = 1 → π r = π s → r = s := by
    intro r s hr hs h
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hr
    obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one hs
    rw [map_pow, map_pow] at h
    rw [hv.pow_inj hi hj h]
  have E : ∀ y : ZMod p, y ^ M = 1 → ∃ r : R, r ^ M = 1 ∧ π r = y := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := hv.eq_pow_of_pow_eq_one hy
    refine ⟨ζ ^ i, ?_, by rw [map_pow]⟩
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have P : ∀ x : ZMod p, x ≠ 0 → (x ^ d) ^ M = 1 := by
    intro x hx
    rw [← pow_mul, mul_comm, hMd]
    exact ZMod.pow_card_sub_one_eq_one hx
  classical
  let L : ZMod p → R := fun x => if h : x = 0 then 0 else (E _ (P x h)).choose
  have L1 : ∀ x (h : x ≠ 0), L x ^ M = 1 ∧ π (L x) = x ^ d := by
    intro x h
    simp only [L, dif_neg h]
    exact (E _ (P x h)).choose_spec
  have L0 : L 0 = 0 := by simp [L]
  let χ : MulChar (ZMod p) R :=
    { toFun := L
      map_one' := by
        have h1 := L1 1 one_ne_zero
        exact U _ _ h1.1 (one_pow M) (by rw [h1.2, one_pow, map_one])
      map_mul' := by
        intro x y
        by_cases hx : x = 0
        · rw [hx, zero_mul, L0, zero_mul]
        by_cases hy : y = 0
        · rw [hy, mul_zero, L0, mul_zero]
        have hxy := L1 (x * y) (mul_ne_zero hx hy)
        have h1 := L1 x hx
        have h2 := L1 y hy
        refine U _ _ hxy.1 (by rw [mul_pow, h1.1, h2.1, one_mul]) ?_
        rw [hxy.2, map_mul, h1.2, h2.2, mul_pow]
      map_nonunit' := by
        intro a ha
        have : a = 0 := by
          by_contra h
          exact ha (isUnit_iff_ne_zero.mpr h)
        rw [this]
        exact L0 }
  have hχ : ∀ x : ZMod p, x ≠ 0 → χ x ^ M = 1 ∧ π (χ x) = x ^ d := L1
  refine ⟨χ, hχ, ?_⟩
  have hpow : χ ^ M = 1 := by
    ext a
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    exact (hχ a a.ne_zero).1
  have hdvd : orderOf χ ∣ M := orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  set k := orderOf χ with hk
  have hk1 : χ ^ k = 1 := pow_orderOf_eq_one χ
  have hgk : (χ g) ^ k = 1 := by
    rw [← MulChar.pow_apply_coe, hk1, MulChar.one_apply_coe]
  have hgdk : g ^ (d * k) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_mul, ← (hχ g g.ne_zero).2, ← map_pow, hgk,
      map_one]
  have h2 : M * d ∣ d * k := by
    rw [hMd, ← hog]
    exact orderOf_dvd_of_pow_eq_one hgdk
  rw [mul_comm M d] at h2
  have h3 : M ∣ k := (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd)).mp h2
  exact Nat.dvd_antisymm hdvd h3
