import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Take `⟨N, hN, j, ζ, h1, h2, h3⟩` from `hL`. Take `⟨hl, hker⟩` from `hA`. Take `⟨k, hk⟩` from `hl.trans h1`. Use `haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne⟩`. Use `haveI : IsGalois ℚ (CyclotomicField N ℚ) := @IsCyclotomicExtension.isGalois {N} ℚ _ _ _ _ (CyclotomicField.isCyclotomicExtension N ℚ)`.

Establish `hη : IsPrimitiveRoot (ζ ^ k) l` using `h2.pow (NeZero.pos N) (by rw [hk, mul_comm])`. Establish `key : ∀ b : ℕ, (ζ ^ k) ^ b = (ζ ^ k) ^ (b % l)` using `fun b => by conv_lhs => rw [← Nat.mod_add_div b l]`. Rewrite using `[pow_add, pow_mul, hη.pow_eq_one, one_pow, mul_one]`. Establish `hmem : ζ ^ k ∈ j.fieldRange`. Rewrite using `[← IsGalois.fixedField_fixingSubgroup j.fieldRange, IntermediateField.mem_fixedField_iff]`.

Introduce `τ hτ`. Rewrite `hτ` using `[IntermediateField.mem_fixingSubgroup_iff]`. Establish `hfix : ∀ x : L, τ (j x) = j x` using `fun x => hτ _ ⟨x, rfl⟩`. Establish `hτN : (τ ζ) ^ N = 1` using `by rw [← map_pow, h2.pow_eq_one, map_one]`. Take `⟨a, -, ha⟩` from `h2.eq_pow_of_pow_eq_one hτN`.

Establish `hmod : a ≡ 1 [MOD l]` using `hker a ((h3 τ a ha.symm).1 hfix)`. Establish `hpow : (ζ ^ k) ^ a = (ζ ^ k) ^ 1`. Rewrite using `[key a, key 1, show a % l = 1 % l from hmod]`. Rewrite using `[map_pow, ← ha, ← pow_mul, mul_comm, pow_mul, hpow, pow_one]`. Take `⟨x, hx⟩` from `hmem`.

Use `⟨x, IsPrimitiveRoot.of_map_of_injective (f := (j : L →+* CyclotomicField N ℚ)) ?_ j.toRingHom.injective⟩` and prove the remaining obligations. Rewrite using `[show (j : L →+* CyclotomicField N ℚ) x = ζ ^ k from hx]`. Conclude with `hη`.
-/
private theorem root_of_hasMu (l : ℕ) (A : AbF) (L : Type) [Field L] [NumberField L] (hA : A.HasMu l)
    (hL : IsAbField A L) : ∃ ζ : L, IsPrimitiveRoot ζ l := by
  obtain ⟨N, hN, j, ζ, h1, h2, h3⟩ := hL
  obtain ⟨hl, hker⟩ := hA
  obtain ⟨k, hk⟩ := hl.trans h1
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne⟩
  haveI : IsGalois ℚ (CyclotomicField N ℚ) :=
    @IsCyclotomicExtension.isGalois {N} ℚ _ _ _ _ (CyclotomicField.isCyclotomicExtension N ℚ)
  have hη : IsPrimitiveRoot (ζ ^ k) l := h2.pow (NeZero.pos N) (by rw [hk, mul_comm])
  have key : ∀ b : ℕ, (ζ ^ k) ^ b = (ζ ^ k) ^ (b % l) := fun b => by
    conv_lhs => rw [← Nat.mod_add_div b l]
    rw [pow_add, pow_mul, hη.pow_eq_one, one_pow, mul_one]
  have hmem : ζ ^ k ∈ j.fieldRange := by
    rw [← IsGalois.fixedField_fixingSubgroup j.fieldRange, IntermediateField.mem_fixedField_iff]
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    have hfix : ∀ x : L, τ (j x) = j x := fun x => hτ _ ⟨x, rfl⟩
    have hτN : (τ ζ) ^ N = 1 := by rw [← map_pow, h2.pow_eq_one, map_one]
    obtain ⟨a, -, ha⟩ := h2.eq_pow_of_pow_eq_one hτN
    have hmod : a ≡ 1 [MOD l] := hker a ((h3 τ a ha.symm).1 hfix)
    have hpow : (ζ ^ k) ^ a = (ζ ^ k) ^ 1 := by
      rw [key a, key 1, show a % l = 1 % l from hmod]
    rw [map_pow, ← ha, ← pow_mul, mul_comm, pow_mul, hpow, pow_one]
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, IsPrimitiveRoot.of_map_of_injective (f := (j : L →+* CyclotomicField N ℚ)) ?_ j.toRingHom.injective⟩
  rw [show (j : L →+* CyclotomicField N ℚ) x = ζ ^ k from hx]
  exact hη

/- English proof (translation)
Rewrite using `[ZMod.unitsMap_def]`. Simplify using `[Units.coe_map, ZMod.castHom_apply, e, ZMod.cast_natCast h]`.
-/
private theorem unitsMap_nat {m n a : ℕ} (h : m ∣ n) (u : (ZMod n)ˣ) (e : (u : ZMod n) = (a : ZMod n)) :
    ((ZMod.unitsMap h u : (ZMod m)ˣ) : ZMod m) = (a : ZMod m) := by
  rw [ZMod.unitsMap_def]
  simp [Units.coe_map, ZMod.castHom_apply, e, ZMod.cast_natCast h]

/- English proof (translation)
Take `⟨u, ⟨hu1, hu2⟩, e⟩` from `h`. Conclude with `⟨⟨_, hu1, unitsMap_nat _ _ e⟩, ⟨_, hu2, unitsMap_nat _ _ e⟩⟩`.
-/
private theorem ker_sup {A B : AbF} {a : ℕ} (h : (A.sup B).ker a) : A.ker a ∧ B.ker a := by
  obtain ⟨u, ⟨hu1, hu2⟩, e⟩ := h
  exact ⟨⟨_, hu1, unitsMap_nat _ _ e⟩, ⟨_, hu2, unitsMap_nat _ _ e⟩⟩

/- English proof (translation)
Conclude with `⟨dvd_mul_of_dvd_left h.1 _, fun a ha => h.2 a (ker_sup ha).1⟩`.
-/
private theorem hasMu_sup_left {A : AbF} (B : AbF) {l : ℕ} (h : A.HasMu l) : (A.sup B).HasMu l := by
  exact ⟨dvd_mul_of_dvd_left h.1 _, fun a ha => h.2 a (ker_sup ha).1⟩

/- English proof (translation)
Conclude with `⟨dvd_mul_of_dvd_right h.1 _, fun a ha => h.2 a (ker_sup ha).2⟩`.
-/
private theorem hasMu_sup_right (A : AbF) {B : AbF} {l : ℕ} (h : B.HasMu l) : (A.sup B).HasMu l := by
  exact ⟨dvd_mul_of_dvd_right h.1 _, fun a ha => h.2 a (ker_sup ha).2⟩

/- English proof (translation)
The claim follows from `hasMu_sup_right M (AbF.hasMu_cyc (l := 4) (q := 1) (by norm_num) (by norm_num))`.
-/
private theorem hasMu_withI (M : AbF) : (withI M).HasMu 4 :=
  hasMu_sup_right M (AbF.hasMu_cyc (l := 4) (q := 1) (by norm_num) (by norm_num))

/- English proof (translation)
Use `⟨fun l A L _ _ hA hL => root_of_hasMu l A L hA hL, fun M L _ _ hL => root_of_hasMu 4 _ L (hasMu_withI M) hL, fun M q d L _ _ hL => root_of_hasMu 4 _ L ?_ hL⟩` and prove the remaining obligations. Conclude with `hasMu_sup_left _ (hasMu_sup_left _ (hasMu_withI M))`.
-/
theorem UpperTheory.V.Two.hasMuQ :
    (∀ (l : ℕ) (A : AbF) (L : Type) [Field L] [NumberField L], A.HasMu l → IsAbField A L → ∃ ζ : L, IsPrimitiveRoot ζ l) ∧
      (∀ (M : AbF) (L : Type) [Field L] [NumberField L], IsAbField (withI M) L → ∃ ζ : L, IsPrimitiveRoot ζ 4) ∧
      ∀ (M : AbF) (q d : ℕ) (L : Type) [Field L] [NumberField L], IsAbField (base2 M q d) L → ∃ ζ : L, IsPrimitiveRoot ζ 4 := by
  refine ⟨fun l A L _ _ hA hL => root_of_hasMu l A L hA hL,
    fun M L _ _ hL => root_of_hasMu 4 _ L (hasMu_withI M) hL,
    fun M q d L _ _ hL => root_of_hasMu 4 _ L ?_ hL⟩
  exact hasMu_sup_left _ (hasMu_sup_left _ (hasMu_withI M))
