import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Condmap
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Formalism.GaloisCohomology.LocalTateDualityK

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

/- English proof (translation)
Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Take `rfl : inst = DivisionRing.toRatAlgebra` from `Subsingleton.elim _ _`. Conclude with `(Chr.clsOnto Ω N).1`.
-/
private theorem cls_onto {Ω : Type} [Field Ω] [inst : Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] :
    Function.Surjective (Chr.cls ℚ Ω N) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact (Chr.clsOnto Ω N).1

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Use `haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩`. Use `haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance`. Establish `hpow : ∀ t : Ω, t ^ l ^ 1 = 1 → t ^ (1 : ZMod (l ^ 1)).val = t`.

Introduce `t ht`. Rewrite using `[ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ht, pow_one]`. Establish `h1 : (cyclotomicCharacter Ω l g.toRingEquiv).val.toZModPow 1 = 1`. Rewrite using `[cyclotomicCharacter.toZModPow]`. Use `(modularCyclotomicCharacter.unique Ω _ _ fun t ht => ?_).symm` and prove the remaining obligations.

Establish `ht' : (t : Ω) ^ l ^ 1 = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]`. Rewrite using `[hpow _ ht']`. Conclude with `h _ (by rwa [pow_one] at ht')`. Rewrite `h1` using `[← sub_eq_zero, ← map_one (PadicInt.toZModPow (p := l) 1), ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one, Ideal.mem_span_singleton]`.

Take `⟨y, hy⟩` from `h1`. Establish `e : (chiO ℚ Ω l O g : O) = algebraMap ℤ_[l] O (cyclotomicCharacter Ω l g.toRingEquiv).val` using `rfl`. Rewrite using `[e, sub_eq_iff_eq_add.1 hy]`. Simplify using the standard rewrite rules.
-/
private theorem red_chi {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    {O k : Type} [CommRing O] [Algebra ℤ_[l] O] [Field k] [CharP k l] (red : O →+* k) (g : G ℚ Ω)
    (h : ∀ t : Ω, t ^ l = 1 → g t = t) : red (chiO ℚ Ω l O g : O) = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hpow : ∀ t : Ω, t ^ l ^ 1 = 1 → t ^ (1 : ZMod (l ^ 1)).val = t := by
    intro t ht
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ht, pow_one]
  have h1 : (cyclotomicCharacter Ω l g.toRingEquiv).val.toZModPow 1 = 1 := by
    rw [cyclotomicCharacter.toZModPow]
    refine (modularCyclotomicCharacter.unique Ω _ _ fun t ht => ?_).symm
    have ht' : (t : Ω) ^ l ^ 1 = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]
    rw [hpow _ ht']
    exact h _ (by rwa [pow_one] at ht')
  rw [← sub_eq_zero, ← map_one (PadicInt.toZModPow (p := l) 1), ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    pow_one, Ideal.mem_span_singleton] at h1
  obtain ⟨y, hy⟩ := h1
  have e : (chiO ℚ Ω l O g : O) = algebraMap ℤ_[l] O (cyclotomicCharacter Ω l g.toRingEquiv).val := rfl
  rw [e, sub_eq_iff_eq_add.1 hy]
  simp

/- English proof (translation)
Rewrite using `[prodX, MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd]`.
-/
private theorem prodX_unit {R : Type} [CommRing R] {f n : ℕ} (φ : DirichletCharacter R f) (ξ : DirichletCharacter R (2 ^ n))
    (u : (ZMod (f * 2 ^ n))ˣ) :
    prodX φ ξ (u : ZMod (f * 2 ^ n)) = φ (ZMod.cast (u : ZMod (f * 2 ^ n))) * ξ (ZMod.cast (u : ZMod (f * 2 ^ n))) := by
  rw [prodX, MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd]

/- English proof (translation)
Use extensionality with `u`. Rewrite using `[MulChar.ringHomComp_apply, prodX_unit, prodX_unit, map_mul, MulChar.ringHomComp_apply, MulChar.ringHomComp_apply]`.
-/
private theorem prodX_map {R S : Type} [CommRing R] [CommRing S] (j : R →+* S) {f n : ℕ} (φ : DirichletCharacter R f)
    (ξ : DirichletCharacter R (2 ^ n)) : (prodX φ ξ).ringHomComp j = prodX (φ.ringHomComp j) (ξ.ringHomComp j) := by
  ext u
  rw [MulChar.ringHomComp_apply, prodX_unit, prodX_unit, map_mul, MulChar.ringHomComp_apply, MulChar.ringHomComp_apply]

/- English proof (translation)
Rewrite using `[prodX, prodX, mul_inv, map_inv, map_inv]`.
-/
private theorem prodX_inv {R : Type} [CommRing R] {f n : ℕ} (φ : DirichletCharacter R f)
    (ξ : DirichletCharacter R (2 ^ n)) : (prodX φ ξ)⁻¹ = prodX φ⁻¹ ξ⁻¹ := by
  rw [prodX, prodX, mul_inv, map_inv, map_inv]

/- English proof (translation)
Rewrite using `[MulChar.inv_apply]`. Use `congr 1`. Establish `: ((-1 : (ZMod N)ˣ) : ZMod N) = -1` using `by simp`. Rewrite using `[← this, Ring.inverse_unit]`. Simplify using the standard rewrite rules.
-/
private theorem chr_inv_neg {R : Type} [CommRing R] {N : ℕ} (χ : DirichletCharacter R N) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply]
  congr 1
  have : ((-1 : (ZMod N)ˣ) : ZMod N) = -1 := by simp
  rw [← this, Ring.inverse_unit]
  simp

/- English proof (translation)
The claim follows from `h.d_pos four := h.four f_odd := h.f_odd prim := by rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact h.prim ord := by rw [orderOf_inv]; exact h.ord prim2 := by rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact h.prim2 …`.
-/
private theorem xd_inv {l d : ℕ} {R : Type} [CommRing R] {f n : ℕ} {φ : DirichletCharacter R f}
    {ξ : DirichletCharacter R (2 ^ n)} (h : XData l d φ ξ) : XData l d φ⁻¹ ξ⁻¹ where
  d_pos := h.d_pos
  four := h.four
  f_odd := h.f_odd
  prim := by rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact h.prim
  ord := by rw [orderOf_inv]; exact h.ord
  prim2 := by rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact h.prim2
  big := h.big
  odd := by rw [chr_inv_neg, chr_inv_neg]; exact h.odd

/- English proof (translation)
Use `haveI : NeZero f := ⟨h.f_odd.pos.ne'⟩`. Use `⟨h.d_pos, h.four, h.f_odd, ?_, ?_, ?_, h.big, ?_⟩` and prove the remaining obligations. Rewrite using `[DirichletCharacter.isPrimitive_def, (Bern.b_condmap j hj φ).1]`. Conclude with `h.prim`. Rewrite using `[orderOf_dvd_iff_pow_eq_one, MulChar.ringHomComp_pow, orderOf_dvd_iff_pow_eq_one.1 h.ord, MulChar.ringHomComp_one]`.

Rewrite using `[DirichletCharacter.isPrimitive_def, (Bern.b_condmap j hj ξ).1]`. Conclude with `h.prim2`. Rewrite using `[MulChar.ringHomComp_apply, MulChar.ringHomComp_apply, ← map_mul, h.odd, map_neg, map_one]`.
-/
private theorem xd_map {l d : ℕ} {R S : Type} [CommRing R] [CommRing S] (j : R →+* S) (hj : Function.Injective j) {f n : ℕ}
    {φ : DirichletCharacter R f} {ξ : DirichletCharacter R (2 ^ n)} (h : XData l d φ ξ) :
    XData l d (φ.ringHomComp j) (ξ.ringHomComp j) := by
  haveI : NeZero f := ⟨h.f_odd.pos.ne'⟩
  refine ⟨h.d_pos, h.four, h.f_odd, ?_, ?_, ?_, h.big, ?_⟩
  · rw [DirichletCharacter.isPrimitive_def, (Bern.b_condmap j hj φ).1]; exact h.prim
  · rw [orderOf_dvd_iff_pow_eq_one, MulChar.ringHomComp_pow, orderOf_dvd_iff_pow_eq_one.1 h.ord, MulChar.ringHomComp_one]
  · rw [DirichletCharacter.isPrimitive_def, (Bern.b_condmap j hj ξ).1]; exact h.prim2
  · rw [MulChar.ringHomComp_apply, MulChar.ringHomComp_apply, ← map_mul, h.odd, map_neg, map_one]

/- English proof (translation)
The claim follows from `Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hl.one_lt)`.
-/
private theorem xd_pos {l d : ℕ} (hl : l.Prime) (hd : 0 < d) : 0 < l ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hl.one_lt)

/- English proof (translation)
Introduce and unpack `rfl`. Take `⟨e, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hd.ne'`. Establish `: 0 < 2 ^ e` using `by positivity`. Rewrite `h` using `[pow_succ]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem xd_ne_two {l d : ℕ} (hd : 0 < d) (h : 4 ∣ l ^ d - 1) : l ≠ 2 := by
  rintro rfl
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have : 0 < 2 ^ e := by positivity
  rw [pow_succ] at h
  omega

/- English proof (translation)
Establish `h1 : Nat.totient (2 ^ n) ∣ 2 ^ n`. Break down `n with _ | m` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[Nat.totient_prime_pow_succ Nat.prime_two]`. Simplify using `[pow_succ]`.

Take `⟨e, he⟩` from `h1`. Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val]`. Use `conv_lhs => enter [2, 1, 2]`. Rewrite using `[he]`. Rewrite using `[pow_mul, ZMod.pow_totient, one_pow, Units.val_one, map_one]`.
-/
private theorem xi_pow {R : Type} [CommRing R] {n : ℕ} (ξ : DirichletCharacter R (2 ^ n)) (u : (ZMod (2 ^ n))ˣ) :
    ξ (u : ZMod (2 ^ n)) ^ 2 ^ n = 1 := by
  have h1 : Nat.totient (2 ^ n) ∣ 2 ^ n := by
    rcases n with _ | m
    · simp
    · rw [Nat.totient_prime_pow_succ Nat.prime_two]; simp [pow_succ]
  obtain ⟨e, he⟩ := h1
  rw [← map_pow, ← Units.val_pow_eq_pow_val]
  conv_lhs => enter [2, 1, 2]; rw [he]
  rw [pow_mul, ZMod.pow_totient, one_pow, Units.val_one, map_one]

/- English proof (translation)
Establish `h1 : ξ ^ 2 ^ n = 1`. Use extensionality with `u`. Rewrite using `[MulChar.pow_apply_coe, xi_pow, MulChar.one_apply_coe]`. Establish `h2 : prodX φ ξ ^ ((l ^ d - 1) * 2 ^ n) = 1`. Rewrite using `[prodX, mul_pow, ← map_pow, ← map_pow, pow_mul, orderOf_dvd_iff_pow_eq_one.1 h.ord, pow_mul', h1]`.

Simplify using the standard rewrite rules. Introduce `hd`. Break down `(Nat.Prime.dvd_mul hl).1 (hd.trans (orderOf_dvd_of_pow_eq_one h2)) with h3 | h3` into its components or cases. Establish `h4 : l ∣ l ^ d` using `dvd_pow_self l h.d_pos.ne'`. Establish `h5` using `(Nat.dvd_sub_iff_right (Nat.one_le_pow d l hl.pos) h4).1 h3`.

Conclude with `hl.one_lt.ne' (Nat.dvd_one.1 h5)`. Conclude with `xd_ne_two h.d_pos h.four ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h3))`.
-/
private theorem xd_ord {l d : ℕ} (hl : l.Prime) {R : Type} [CommRing R] {f n : ℕ}
    {φ : DirichletCharacter R f} {ξ : DirichletCharacter R (2 ^ n)} (h : XData l d φ ξ) : ¬ l ∣ orderOf (prodX φ ξ) := by
  have h1 : ξ ^ 2 ^ n = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, xi_pow, MulChar.one_apply_coe]
  have h2 : prodX φ ξ ^ ((l ^ d - 1) * 2 ^ n) = 1 := by
    rw [prodX, mul_pow, ← map_pow, ← map_pow, pow_mul, orderOf_dvd_iff_pow_eq_one.1 h.ord, pow_mul', h1]
    simp
  intro hd
  rcases (Nat.Prime.dvd_mul hl).1 (hd.trans (orderOf_dvd_of_pow_eq_one h2)) with h3 | h3
  · have h4 : l ∣ l ^ d := dvd_pow_self l h.d_pos.ne'
    have h5 := (Nat.dvd_sub_iff_right (Nat.one_le_pow d l hl.pos) h4).1 h3
    exact hl.one_lt.ne' (Nat.dvd_one.1 h5)
  · exact xd_ne_two h.d_pos h.four ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h3))

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro h; exact absurd (by simpa using h) hx`. Consider the case `succ m ih`. Introduce `h`.

Rewrite `h` using `[pow_succ, pow_mul, pow_two, mul_self_eq_one_iff]`. Conclude with `h.elim ih fun h => ⟨_, h⟩`.
-/
private theorem neg_one_of {R : Type} [CommRing R] [IsDomain R] (x : R) (hx : x ≠ 1) :
    ∀ m : ℕ, x ^ 2 ^ m = 1 → ∃ j : ℕ, x ^ j = -1 := by
  intro m
  induction m with
  | zero => intro h; exact absurd (by simpa using h) hx
  | succ m ih =>
    intro h
    rw [pow_succ, pow_mul, pow_two, mul_self_eq_one_iff] at h
    exact h.elim ih fun h => ⟨_, h⟩

/- English proof (translation)
Establish `h0 : 1 ≤ (l ^ d - 1).factorization 2` using `(Nat.prime_two.dvd_iff_one_le_factorization (xd_pos hl h.d_pos).ne').1 (dvd_trans (by norm_num) h.four)`. Establish `h1 : 4 ≤ 2 ^ n`. Use `le_trans ?_ h.big` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ξ ≠ 1`.

Introduce and unpack `rfl`. Use `h.prim2` as an intermediate fact. Rewrite `this` using `[DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one]`. Use linear arithmetic over natural numbers and integers. Take `⟨u, hu⟩` from `MulChar.ne_one_iff.1 h2`.

Take `⟨j, hj⟩` from `neg_one_of _ hu n (xi_pow ξ u)`. Conclude with `⟨u ^ j, by rw [Units.val_pow_eq_pow_val, map_pow, hj]⟩`.
-/
private theorem xd_neg {l d : ℕ} (hl : l.Prime) {R : Type} [CommRing R] [IsDomain R] {f n : ℕ}
    {φ : DirichletCharacter R f} {ξ : DirichletCharacter R (2 ^ n)} (h : XData l d φ ξ) :
    ∃ b : (ZMod (2 ^ n))ˣ, ξ (b : ZMod (2 ^ n)) = -1 := by
  have h0 : 1 ≤ (l ^ d - 1).factorization 2 :=
    (Nat.prime_two.dvd_iff_one_le_factorization (xd_pos hl h.d_pos).ne').1 (dvd_trans (by norm_num) h.four)
  have h1 : 4 ≤ 2 ^ n := by
    refine le_trans ?_ h.big
    calc 4 = 1 * 4 ^ 1 := by norm_num
      _ ≤ _ := Nat.mul_le_mul h.f_odd.pos (Nat.pow_le_pow_right (by norm_num) h0)
  have h2 : ξ ≠ 1 := by
    rintro rfl
    have := h.prim2
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at this
    omega
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.1 h2
  obtain ⟨j, hj⟩ := neg_one_of _ hu n (xi_pow ξ u)
  exact ⟨u ^ j, by rw [Units.val_pow_eq_pow_val, map_pow, hj]⟩

/- English proof (translation)
Take `⟨b, hb⟩` from `xd_neg hl h`. Establish `hodd : Odd (l * f)` using `(hl.odd_of_ne_two (xd_ne_two h.d_pos h.four)).mul h.f_odd`. Establish `hco : (l * f).Coprime (2 ^ n)` using `(Nat.coprime_two_right.2 hodd).pow_right n`. Take `⟨a, ha1, ha2⟩` from `Nat.chineseRemainder hco 1 (b : ZMod (2 ^ n)).val`. Establish `hc : a.Coprime (l * f * 2 ^ n)`.

Use `Nat.Coprime.mul_right ?_ ?_` and prove the remaining obligations. Rewrite using `[Nat.Coprime, ha1.gcd_eq]`. Simplify using the standard rewrite rules. Rewrite using `[Nat.Coprime, ha2.gcd_eq]`. Conclude with `ZMod.val_coe_unit_coprime b`.

Use `haveI : NeZero (l * f * 2 ^ n) := ⟨mul_ne_zero hodd.pos.ne' (by positivity)⟩`. Take `⟨g, hg⟩` from `cls_onto (Ω := Ω) (l * f * 2 ^ n) (ZMod.unitOfCoprime a hc)`. Use `⟨g, fun t ht => ?_, ?_⟩` and prove the remaining obligations. Establish `hM : t ^ (l * f * 2 ^ n) = 1` using `by rw [mul_assoc, pow_mul, ht, one_pow]`. Rewrite using `[Chr.cls_spec _ g t hM, hg, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod _ hM, pow_eq_pow_mod _ ht, ha1.of_mul_right f, ← pow_eq_pow_mod _ ht, pow_one]`.

Establish `hd : f * 2 ^ n ∣ l * f * 2 ^ n` using `by rw [mul_assoc]; exact dvd_mul_left _ _`. Establish `e1 : ((Chr.cls ℚ Ω (f * 2 ^ n) g : (ZMod (f * 2 ^ n))ˣ) : ZMod (f * 2 ^ n)) = a`. Rewrite using `[← (Chr.clsFacts ℚ Ω (l * f * 2 ^ n)).2.1 _ hd, MonoidHom.comp_apply, hg, ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd]`. Rewrite using `[Chr.dirG, MonoidHom.comp_apply, MulChar.coe_toUnitHom, prodX_unit, e1, ZMod.cast_natCast (dvd_mul_right _ _), ZMod.cast_natCast (dvd_mul_left _ _), (ZMod.natCast_eq_natCast_iff _ _ _).2 (ha1.of_mul_left l), (ZMod.natCast_eq_natCast_iff _ _ _).2 ha2, ZMod.natCast_zmod_val, hb]`. Simplify using the standard rewrite rules.
-/
private theorem xd_gal {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l d : ℕ} (hl : l.Prime) {R : Type} [CommRing R]
    [IsDomain R] {f n : ℕ} [NeZero (f * 2 ^ n)] {φ : DirichletCharacter R f} {ξ : DirichletCharacter R (2 ^ n)}
    (h : XData l d φ ξ) :
    ∃ g : G ℚ Ω, (∀ t : Ω, t ^ l = 1 → g t = t) ∧ (Chr.dirG ℚ Ω (prodX φ ξ) g : R) = -1 := by
  obtain ⟨b, hb⟩ := xd_neg hl h
  have hodd : Odd (l * f) := (hl.odd_of_ne_two (xd_ne_two h.d_pos h.four)).mul h.f_odd
  have hco : (l * f).Coprime (2 ^ n) := (Nat.coprime_two_right.2 hodd).pow_right n
  obtain ⟨a, ha1, ha2⟩ := Nat.chineseRemainder hco 1 (b : ZMod (2 ^ n)).val
  have hc : a.Coprime (l * f * 2 ^ n) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.Coprime, ha1.gcd_eq]; simp
    · rw [Nat.Coprime, ha2.gcd_eq]; exact ZMod.val_coe_unit_coprime b
  haveI : NeZero (l * f * 2 ^ n) := ⟨mul_ne_zero hodd.pos.ne' (by positivity)⟩
  obtain ⟨g, hg⟩ := cls_onto (Ω := Ω) (l * f * 2 ^ n) (ZMod.unitOfCoprime a hc)
  refine ⟨g, fun t ht => ?_, ?_⟩
  · have hM : t ^ (l * f * 2 ^ n) = 1 := by rw [mul_assoc, pow_mul, ht, one_pow]
    rw [Chr.cls_spec _ g t hM, hg, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod _ hM,
      pow_eq_pow_mod _ ht, ha1.of_mul_right f, ← pow_eq_pow_mod _ ht, pow_one]
  · have hd : f * 2 ^ n ∣ l * f * 2 ^ n := by rw [mul_assoc]; exact dvd_mul_left _ _
    have e1 : ((Chr.cls ℚ Ω (f * 2 ^ n) g : (ZMod (f * 2 ^ n))ˣ) : ZMod (f * 2 ^ n)) = a := by
      rw [← (Chr.clsFacts ℚ Ω (l * f * 2 ^ n)).2.1 _ hd, MonoidHom.comp_apply, hg, ZMod.unitsMap_val,
        ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd]
    rw [Chr.dirG, MonoidHom.comp_apply, MulChar.coe_toUnitHom, prodX_unit, e1, ZMod.cast_natCast (dvd_mul_right _ _),
      ZMod.cast_natCast (dvd_mul_left _ _), (ZMod.natCast_eq_natCast_iff _ _ _).2 (ha1.of_mul_left l),
      (ZMod.natCast_eq_natCast_iff _ _ _).2 ha2, ZMod.natCast_zmod_val, hb]
    simp

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `h2` using `xd_ne_two h.d_pos h.four`. Take `⟨g, hg1, hg2⟩` from `xd_gal (Ω := Ω) hl h`. Establish `hne : (-1 : k) ≠ 1`. Introduce `e`.

Establish `: ((2 : ℕ) : k) = 0` using `by rw [Nat.cast_ofNat, ← one_add_one_eq_two]; nth_rewrite 1 [← e]; simp`. Conclude with `h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 ((CharP.cast_eq_zero_iff k l 2).1 this))`. Establish `hg3 : (redChar Ω red (prodX φ ξ) g : k) = -1`. Establish `: (redChar Ω red (prodX φ ξ) g : k) = red (Chr.dirG ℚ Ω (prodX φ ξ) g : c.O)` using `rfl`. Rewrite using `[this, hg2, map_neg, map_one]`.

Use `h16 Ω l h2 c k red _ (prodX φ ξ) (fun e => hne ?_) (xd_ord hl h) ⟨g, ?_⟩ ?_ z hz hu` and prove the remaining obligations. Rewrite using `[← hg3, e, redChar, Chr.dirG]`. Simplify using the standard rewrite rules. Rewrite using `[hg3, red_chi l red g hg1]`. Conclude with `hne`.

Rewrite using `[prodX_inv, prodX_map]`. Conclude with `hX l d f n _ _ (xd_map _ Subtype.val_injective (xd_inv h))`.
-/
private theorem main (hX : LemmaX) (h16 : UnramifiedCocycleIsCoboundaryOfBernoulliUnit) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (c : HV.Coef l) (k : Type) [Field k] [CharP k l] (red : c.O →+* k) (d f n : ℕ) [NeZero (f * 2 ^ n)]
    (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)) (h : XData l d φ ξ) (z : G ℚ Ω → k)
    (hz : IsCoc (redChar Ω red (prodX φ ξ)) z) (hu : UnrEv l (redChar Ω red (prodX φ ξ)) z) :
    ∃ m : k, ∀ g, z g = (redChar Ω red (prodX φ ξ) g : k) * m - m := by
  have hl : l.Prime := Fact.out
  have h2 := xd_ne_two h.d_pos h.four
  obtain ⟨g, hg1, hg2⟩ := xd_gal (Ω := Ω) hl h
  have hne : (-1 : k) ≠ 1 := by
    intro e
    have : ((2 : ℕ) : k) = 0 := by rw [Nat.cast_ofNat, ← one_add_one_eq_two]; nth_rewrite 1 [← e]; simp
    exact h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 ((CharP.cast_eq_zero_iff k l 2).1 this))
  have hg3 : (redChar Ω red (prodX φ ξ) g : k) = -1 := by
    have : (redChar Ω red (prodX φ ξ) g : k) = red (Chr.dirG ℚ Ω (prodX φ ξ) g : c.O) := rfl
    rw [this, hg2, map_neg, map_one]
  refine h16 Ω l h2 c k red _ (prodX φ ξ) (fun e => hne ?_) (xd_ord hl h) ⟨g, ?_⟩ ?_ z hz hu
  · rw [← hg3, e, redChar, Chr.dirG]
    simp
  · rw [hg3, red_chi l red g hg1]; exact hne
  · rw [prodX_inv, prodX_map]
    exact hX l d f n _ _ (xd_map _ Subtype.val_injective (xd_inv h))

/- English proof (translation)
Introduce `hX h16 Ω _ _ _ l _ c k _ _ red d f n _ φ ξ h γ hγ z hz hu`. Break down `hγ with rfl | rfl` into its components or cases. Conclude with `main hX h16 Ω l c k red d f n φ ξ h z hz hu`. Establish `e : (redChar Ω red (prodX φ ξ))⁻¹ = redChar Ω red (prodX φ⁻¹ ξ⁻¹)`. Rewrite using `[← prodX_inv, inv_eq_iff_mul_eq_one]`.

Use extensionality with `g`. Establish `: ∀ χ : DirichletCharacter c.O (f * 2 ^ n), (redChar Ω red χ g : k) = red (χ (Chr.cls ℚ Ω (f * 2 ^ n) g : (ZMod (f * 2 ^ n))ˣ))` using `fun χ => congrArg red (MulChar.coe_toUnitHom χ _)`. Rewrite using `[MonoidHom.mul_apply, Units.val_mul, this, this, ← map_mul, ← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]`. Simplify using the standard rewrite rules. Rewrite `hz`, `hu`, the goal using `[e]`.

Conclude with `main hX h16 Ω l c k red d f n _ _ (xd_inv h) z hz hu`.
-/
theorem UpperTheory.V.X.corX :
    LemmaX → UnramifiedCocycleIsCoboundaryOfBernoulliUnit → CorX := by
  intro hX h16 Ω _ _ _ l _ c k _ _ red d f n _ φ ξ h γ hγ z hz hu
  rcases hγ with rfl | rfl
  · exact main hX h16 Ω l c k red d f n φ ξ h z hz hu
  · have e : (redChar Ω red (prodX φ ξ))⁻¹ = redChar Ω red (prodX φ⁻¹ ξ⁻¹) := by
      rw [← prodX_inv, inv_eq_iff_mul_eq_one]
      ext g
      have : ∀ χ : DirichletCharacter c.O (f * 2 ^ n), (redChar Ω red χ g : k) = red (χ (Chr.cls ℚ Ω (f * 2 ^ n) g : (ZMod (f * 2 ^ n))ˣ)) :=
        fun χ => congrArg red (MulChar.coe_toUnitHom χ _)
      rw [MonoidHom.mul_apply, Units.val_mul, this, this, ← map_mul, ← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
      simp
    rw [e] at hz hu ⊢
    exact main hX h16 Ω l c k red d f n _ _ (xd_inv h) z hz hu
