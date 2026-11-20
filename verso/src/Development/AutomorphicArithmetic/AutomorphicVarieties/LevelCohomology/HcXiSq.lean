import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hd', χ₀, rfl⟩ a ha hda`. Rewrite using `[DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hd' ha]`. Establish `: ((a : ℤ) : ZMod d) = 1`. Establish `h0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) d).mpr hda`.

Move the coercions through the operations in `at h0`. Conclude with `sub_eq_zero.mp h0`. Rewrite using `[this, map_one]`. Introduce `h`. Rewrite using `[DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]`.

Introduce `x hx`. Rewrite `hx`, the goal using `[MonoidHom.mem_ker]`. Use `set a : ℤ := ((x : ZMod n).val : ℤ) with ha_def`. Establish `hax : ((a : ℤ) : ZMod n) = (x : ZMod n)`. Simplify using `[ha_def, ZMod.natCast_zmod_val]`.

Establish `hcop : IsCoprime a n`. Establish `hu : IsUnit ((a : ℤ) : ZMod n)` using `by rw [hax]; exact x.isUnit`. Rewrite `hu` using `[ZMod.coe_int_isUnit_iff_isCoprime]`. Conclude with `hu.symm`. Establish `hd1 : (d : ℤ) ∣ a - 1`.

Apply `(ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) d).mp` to reduce the goal to its premises. Establish `h1` using `congrArg (fun u : (ZMod d)ˣ => (u : ZMod d)) hx`. Simplify using `only [ZMod.unitsMap_val, Units.val_one] at h1`. Rewrite `h1` using `[ZMod.cast_eq_val]`. Use `push_cast`.

Rewrite using `[ha_def]`. Use `push_cast`. Rewrite using `[h1, sub_self]`. Use `h a hcop hd1` as an intermediate fact. Rewrite `this` using `[hax]`.

Use `ext`. Simplify using `using this`.
-/
private theorem UpperTheory.V.X.xiSq_ft {R : Type} [CommRing R] {n d : ℕ} [NeZero n] (χ : DirichletCharacter R n)
    (hd : d ∣ n) : χ.FactorsThrough d ↔ ∀ a : ℤ, IsCoprime a n → (d : ℤ) ∣ a - 1 → χ a = 1 := by
  constructor
  · rintro ⟨hd', χ₀, rfl⟩ a ha hda
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hd' ha]
    have : ((a : ℤ) : ZMod d) = 1 := by
      have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) d).mpr hda
      push_cast at h0
      exact sub_eq_zero.mp h0
    rw [this, map_one]
  · intro h
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    set a : ℤ := ((x : ZMod n).val : ℤ) with ha_def
    have hax : ((a : ℤ) : ZMod n) = (x : ZMod n) := by
      simp [ha_def, ZMod.natCast_zmod_val]
    have hcop : IsCoprime a n := by
      have hu : IsUnit ((a : ℤ) : ZMod n) := by rw [hax]; exact x.isUnit
      rw [ZMod.coe_int_isUnit_iff_isCoprime] at hu
      exact hu.symm
    have hd1 : (d : ℤ) ∣ a - 1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) d).mp
      have h1 := congrArg (fun u : (ZMod d)ˣ => (u : ZMod d)) hx
      simp only [ZMod.unitsMap_val, Units.val_one] at h1
      rw [ZMod.cast_eq_val] at h1
      push_cast
      rw [ha_def]
      push_cast
      rw [h1, sub_self]
    have := h a hcop hd1
    rw [hax] at this
    ext
    simpa using this

/- English proof (translation)
Use `congr 1`. Conclude with `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (dvd_sub_comm.mp h)`.
-/
private theorem UpperTheory.V.X.xiSq_cong {R : Type} [CommRing R] {n : ℕ} (χ : DirichletCharacter R n)
    {a b : ℤ} (h : (n : ℤ) ∣ a - b) : χ a = χ b := by
  congr 1
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (dvd_sub_comm.mp h)

/- English proof (translation)
Use `push_cast`. Conclude with `IsCoprime.pow_right ⟨1, -t, by ring⟩`.
-/
private theorem UpperTheory.V.X.xiSq_cop (t : ℤ) (m : ℕ) : IsCoprime (1 + 2 * t) ((2 ^ m : ℕ) : ℤ) := by
  push_cast
  exact IsCoprime.pow_right ⟨1, -t, by ring⟩

/- English proof (translation)
Establish `h4 : 4 ∣ 2 ^ (k + 4)` using `Dvd.intro (2 ^ k * 4) (by ring)`. Set `χ4O : DirichletCharacter O 4` to `ZMod.χ₄.ringHomComp (Int.castRingHom O)`. Set `φ : DirichletCharacter O (2 ^ (k + 4))` to `ψ ^ 2 * DirichletCharacter.changeLevel h4 χ4O`. Establish `hsq : ∀ a : ℤ, ψ a ^ 2 = ψ ((a ^ 2 : ℤ) : ZMod (2 ^ (k + 4)))`. Introduce `a`.

Rewrite using `[Int.cast_pow, map_pow]`. Establish `h1 : ψ ((1 : ℤ) : ZMod (2 ^ (k + 4))) = 1` using `by rw [Int.cast_one, map_one]`. Establish `hc4 : ∀ a : ℤ, (4 : ℤ) ∣ a - 1 → ((ZMod.χ₄ a : ℤ) : O) = 1`. Introduce `a ha`. Use `UpperTheory.V.X.xiSq_cong ZMod.χ₄ (n := 4) (a := a) (b := 1) (by exact_mod_cast ha)` as an intermediate fact.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `hval : ∀ a : ℤ, IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) → φ a = ψ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O)`. Introduce `a ha`. Simplify using `only [φ, MulChar.coeToFun_mul, Pi.mul_apply, MulChar.pow_apply' _ two_ne_zero]`.

Rewrite using `[DirichletCharacter.changeLevel_eq_cast_of_dvd' _ h4 ha]`. Simplify using `[χ4O, MulChar.ringHomComp_apply]`. Establish `hd : 2 ^ (k + 3) ∣ 2 ^ (k + 4)` using `pow_dvd_pow 2 (by omega)`. Establish `hft : φ.FactorsThrough (2 ^ (k + 3))`. Rewrite using `[UpperTheory.V.X.xiSq_ft φ hd]`.

Introduce `a ha hda`. Rewrite using `[hval a ha]`. Take `⟨t, ht⟩` from `hda`. Move the coercions through the operations in `at ht`. Establish `ha' : a = 1 + 2 ^ (k + 3) * t` using `by linarith`.

Rewrite using `[hc4 a ⟨2 ^ (k + 1) * t, by rw [ha']; ring⟩, mul_one, hsq]`. Rewrite using `[UpperTheory.V.X.xiSq_cong ψ (a := a ^ 2) (b := 1) ⟨t + 2 ^ (k + 2) * t ^ 2, by push_cast; rw [ha']; ring⟩]`. Conclude with `h1`. Take `⟨hd', ξ, hξ⟩` from `hft`. Establish `hξv : ∀ a : ℤ, IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) → ξ a = ψ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O)`.

Introduce `a ha`. Rewrite using `[← DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ hd' ha, ← hξ, hval a ha]`. Use `⟨ξ, ?_, hξv⟩` and prove the remaining obligations. Take `⟨j, hj, hj'⟩` from `(Nat.dvd_prime_pow Nat.prime_two).mp ξ.conductor_dvd_level`. Use `show ξ.conductor = 2 ^ (k + 3)`.

Rewrite using `[hj']`. Break down `Nat.lt_or_ge j (k + 3) with hlt | hge` into its components or cases. It suffices to derive a contradiction. Establish `hf : ξ.FactorsThrough (2 ^ (k + 2))` using `DirichletCharacter.FactorsThrough.mono ξ ξ.factorsThrough_conductor (by rw [hj']; exact pow_dvd_pow 2 (by omega)) (pow_dvd_pow 2 (by omega))`. Rewrite `hf` using `[UpperTheory.V.X.xiSq_ft ξ (pow_dvd_pow 2 (by omega))]`.

Use `set b : ℤ := 1 + 2 * 2 ^ (k + 1) with hb`. Establish `hb3` using `hf b (by simpa [hb] using UpperTheory.V.X.xiSq_cop (2 ^ (k + 1)) (k + 3)) ⟨1, by push_cast; rw [hb]; ring⟩`. Rewrite `hb3` using `[hξv b (by simpa [hb] using UpperTheory.V.X.xiSq_cop (2 ^ (k + 1)) (k + 4)), hc4 b ⟨2 ^ k, by rw [hb]; ring⟩, mul_one, hsq, UpperTheory.V.X.xiSq_cong ψ (a := b ^ 2) (b := 1 + 2 ^ (k + 3)) ⟨2 ^ k, by push_cast; rw [hb]; ring⟩]`. Establish `hψf : ψ.FactorsThrough (2 ^ (k + 3))`. Rewrite using `[UpperTheory.V.X.xiSq_ft ψ hd]`.

Introduce `a ha hda`. Take `⟨t, ht⟩` from `hda`. Move the coercions through the operations in `at ht`. Take `⟨s, hs | hs⟩` from `Int.even_or_odd' t`. Rewrite using `[UpperTheory.V.X.xiSq_cong ψ (a := a) (b := 1) ⟨s, by push_cast; rw [hs] at ht; linear_combination ht⟩]`.

Conclude with `h1`. Rewrite using `[UpperTheory.V.X.xiSq_cong ψ (a := a) (b := 1 + 2 ^ (k + 3)) ⟨s, by push_cast; rw [hs] at ht; linear_combination ht⟩]`. Conclude with `hb3`. Establish `hle : ψ.conductor ≤ 2 ^ (k + 3)` using `Nat.sInf_le hψf`. Establish `hpr : ψ.conductor = 2 ^ (k + 4)` using `hψ`.

Rewrite `hle` using `[hpr]`. Use `Nat.pow_lt_pow_right (a := 2) (by norm_num) (show k + 3 < k + 4 by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
private theorem UpperTheory.V.X.exists_primitive_square_twist {O : Type} [CommRing O] (k : ℕ) (ψ : DirichletCharacter O (2 ^ (k + 4)))
    (hψ : ψ.IsPrimitive) : ∃ ξ : DirichletCharacter O (2 ^ (k + 3)), ξ.IsPrimitive ∧
      ∀ a : ℤ, IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) → ξ a = ψ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
  have h4 : 4 ∣ 2 ^ (k + 4) := Dvd.intro (2 ^ k * 4) (by ring)
  let χ4O : DirichletCharacter O 4 := ZMod.χ₄.ringHomComp (Int.castRingHom O)
  let φ : DirichletCharacter O (2 ^ (k + 4)) := ψ ^ 2 * DirichletCharacter.changeLevel h4 χ4O
  have hsq : ∀ a : ℤ, ψ a ^ 2 = ψ ((a ^ 2 : ℤ) : ZMod (2 ^ (k + 4))) := by
    intro a
    rw [Int.cast_pow, map_pow]
  have h1 : ψ ((1 : ℤ) : ZMod (2 ^ (k + 4))) = 1 := by rw [Int.cast_one, map_one]
  have hc4 : ∀ a : ℤ, (4 : ℤ) ∣ a - 1 → ((ZMod.χ₄ a : ℤ) : O) = 1 := by
    intro a ha
    have := UpperTheory.V.X.xiSq_cong ZMod.χ₄ (n := 4) (a := a) (b := 1) (by exact_mod_cast ha)
    rw [this]
    simp
  have hval : ∀ a : ℤ, IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) →
      φ a = ψ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
    intro a ha
    simp only [φ, MulChar.coeToFun_mul, Pi.mul_apply, MulChar.pow_apply' _ two_ne_zero]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' _ h4 ha]
    simp [χ4O, MulChar.ringHomComp_apply]
  have hd : 2 ^ (k + 3) ∣ 2 ^ (k + 4) := pow_dvd_pow 2 (by omega)
  have hft : φ.FactorsThrough (2 ^ (k + 3)) := by
    rw [UpperTheory.V.X.xiSq_ft φ hd]
    intro a ha hda
    rw [hval a ha]
    obtain ⟨t, ht⟩ := hda
    push_cast at ht
    have ha' : a = 1 + 2 ^ (k + 3) * t := by linarith
    rw [hc4 a ⟨2 ^ (k + 1) * t, by rw [ha']; ring⟩, mul_one, hsq]
    rw [UpperTheory.V.X.xiSq_cong ψ (a := a ^ 2) (b := 1) ⟨t + 2 ^ (k + 2) * t ^ 2, by push_cast; rw [ha']; ring⟩]
    exact h1
  obtain ⟨hd', ξ, hξ⟩ := hft
  have hξv : ∀ a : ℤ, IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) → ξ a = ψ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
    intro a ha
    rw [← DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ hd' ha, ← hξ, hval a ha]
  refine ⟨ξ, ?_, hξv⟩
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ξ.conductor_dvd_level
  show ξ.conductor = 2 ^ (k + 3)
  rw [hj']
  rcases Nat.lt_or_ge j (k + 3) with hlt | hge
  · exfalso
    have hf : ξ.FactorsThrough (2 ^ (k + 2)) :=
      DirichletCharacter.FactorsThrough.mono ξ ξ.factorsThrough_conductor
        (by rw [hj']; exact pow_dvd_pow 2 (by omega)) (pow_dvd_pow 2 (by omega))
    rw [UpperTheory.V.X.xiSq_ft ξ (pow_dvd_pow 2 (by omega))] at hf
    set b : ℤ := 1 + 2 * 2 ^ (k + 1) with hb
    have hb3 := hf b (by simpa [hb] using UpperTheory.V.X.xiSq_cop (2 ^ (k + 1)) (k + 3))
      ⟨1, by push_cast; rw [hb]; ring⟩
    rw [hξv b (by simpa [hb] using UpperTheory.V.X.xiSq_cop (2 ^ (k + 1)) (k + 4)),
      hc4 b ⟨2 ^ k, by rw [hb]; ring⟩, mul_one, hsq,
      UpperTheory.V.X.xiSq_cong ψ (a := b ^ 2) (b := 1 + 2 ^ (k + 3)) ⟨2 ^ k, by push_cast; rw [hb]; ring⟩] at hb3
    have hψf : ψ.FactorsThrough (2 ^ (k + 3)) := by
      rw [UpperTheory.V.X.xiSq_ft ψ hd]
      intro a ha hda
      obtain ⟨t, ht⟩ := hda
      push_cast at ht
      obtain ⟨s, hs | hs⟩ := Int.even_or_odd' t
      · rw [UpperTheory.V.X.xiSq_cong ψ (a := a) (b := 1) ⟨s, by push_cast; rw [hs] at ht; linear_combination ht⟩]
        exact h1
      · rw [UpperTheory.V.X.xiSq_cong ψ (a := a) (b := 1 + 2 ^ (k + 3)) ⟨s, by push_cast; rw [hs] at ht; linear_combination ht⟩]
        exact hb3
    have hle : ψ.conductor ≤ 2 ^ (k + 3) := Nat.sInf_le hψf
    have hpr : ψ.conductor = 2 ^ (k + 4) := hψ
    rw [hpr] at hle
    have := Nat.pow_lt_pow_right (a := 2) (by norm_num) (show k + 3 < k + 4 by omega)
    omega
  · congr 1
    omega

/- English proof (translation)
Introduce `O _ _ _ N _ χ c hc hcond`. Take `⟨k, rfl⟩ : ∃ k, c = k + 4` from `⟨c - 4, by omega⟩`. Establish `hf : χ.FactorsThrough (2 ^ (k + 4))` using `hcond ▸ χ.factorsThrough_conductor`. Take `⟨hdv, ψ, hψχ⟩` from `hf`. Establish `hψp : ψ.IsPrimitive` using `by show ψ.conductor = 2 ^ (k + 4)`.

Establish `h` using `DirichletCharacter.conductor_changeLevel ψ hdv`. Rewrite `h` using `[← hψχ, hcond]`. Conclude with `h.symm`. Take `⟨ξ, hp, hv⟩` from `UpperTheory.V.X.exists_primitive_square_twist k ψ hψp`. Use `⟨ξ, hp, fun a ha => ?_⟩` and prove the remaining obligations.

Establish `ha' : IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ)` using `ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hdv)`. Rewrite using `[hv a ha', hψχ, DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hdv ha]`.
-/
theorem UpperTheory.V.X.xiSq :
    ∀ (O : Type) [CommRing O] [IsDomain O], (2 : O) ≠ 0 → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter O N) (c : ℕ), 4 ≤ c → χ.conductor = 2 ^ c → ∃ ξ : DirichletCharacter O (2 ^ (c - 1)), ξ.IsPrimitive ∧ ∀ a : ℤ, IsCoprime a N → ξ a = χ a ^ 2 * ((ZMod.χ₄ a : ℤ) : O) := by
  intro O _ _ _ N _ χ c hc hcond
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 4 := ⟨c - 4, by omega⟩
  have hf : χ.FactorsThrough (2 ^ (k + 4)) := hcond ▸ χ.factorsThrough_conductor
  obtain ⟨hdv, ψ, hψχ⟩ := hf
  have hψp : ψ.IsPrimitive := by
    show ψ.conductor = 2 ^ (k + 4)
    have h := DirichletCharacter.conductor_changeLevel ψ hdv
    rw [← hψχ, hcond] at h
    exact h.symm
  obtain ⟨ξ, hp, hv⟩ := UpperTheory.V.X.exists_primitive_square_twist k ψ hψp
  refine ⟨ξ, hp, fun a ha => ?_⟩
  have ha' : IsCoprime a ((2 ^ (k + 4) : ℕ) : ℤ) :=
    ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hdv)
  rw [hv a ha', hψχ, DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hdv ha]
