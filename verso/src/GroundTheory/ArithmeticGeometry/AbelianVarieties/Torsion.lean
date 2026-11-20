import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KernelCard

namespace GroundTheory.Arith.Abelian

open AddSubgroup

section Group

variable {A : Type*} [AddCommGroup A]

/- English proof (translation)
Establish `hex : AddMonoid.ExponentExists A` using `⟨n, hn, hA⟩`. Take `⟨P, hP⟩` from `AddMonoid.exists_addOrderOf_eq_exponent hex`. Use `⟨P, hP.trans ?_⟩` and prove the remaining obligations. Establish `he : AddMonoid.exponent A ∣ n` using `AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero hA`. Establish `hepos : 0 < AddMonoid.exponent A` using `Nat.pos_of_dvd_of_pos he hn`.

Establish `h1 : Nat.card {a : A // AddMonoid.exponent A • a = 0} = Nat.card A` using `Nat.card_congr (Equiv.subtypeUnivEquiv fun a => AddMonoid.exponent_nsmul_eq_zero a)`. Establish `h2` using `hker _ he`. Rewrite `h2` using `[h1, hcard]`. Establish `h3 : n ≤ AddMonoid.exponent A`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Use `Nat.pow_lt_pow_left h (two_ne_zero)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `le_antisymm (Nat.le_of_dvd hn he) h3`.
-/
theorem exists_addOrderOf_eq_of_card {n : ℕ} (hn : 0 < n) (hA : ∀ a : A, n • a = 0)
    (hcard : Nat.card A = n ^ 2)
    (hker : ∀ m, m ∣ n → Nat.card {a : A // m • a = 0} ≤ m ^ 2) :
    ∃ P : A, addOrderOf P = n := by
  have hex : AddMonoid.ExponentExists A := ⟨n, hn, hA⟩
  obtain ⟨P, hP⟩ := AddMonoid.exists_addOrderOf_eq_exponent hex
  refine ⟨P, hP.trans ?_⟩
  have he : AddMonoid.exponent A ∣ n := AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero hA
  have hepos : 0 < AddMonoid.exponent A := Nat.pos_of_dvd_of_pos he hn
  have h1 : Nat.card {a : A // AddMonoid.exponent A • a = 0} = Nat.card A :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun a => AddMonoid.exponent_nsmul_eq_zero a)
  have h2 := hker _ he
  rw [h1, hcard] at h2
  have h3 : n ≤ AddMonoid.exponent A := by
    by_contra h
    push Not at h
    have := Nat.pow_lt_pow_left h (two_ne_zero)
    omega
  exact le_antisymm (Nat.le_of_dvd hn he) h3

private noncomputable def zmodHom (n : ℕ) (P : A) (hP : n • P = 0) : ZMod n →+ A :=
  ZMod.lift n ⟨zmultiplesHom A P, by simp [hP]⟩

/- English proof (translation)
Establish `h : ((a.val : ℤ) : ZMod n) = a` using `by simp`. Use `conv_lhs => rw [← h]`. Rewrite using `[zmodHom, ZMod.lift_coe]`. Simplify using `only [zmultiplesHom_apply, natCast_zsmul]`.
-/
private theorem zmodHom_apply {n : ℕ} [NeZero n] (P : A) (hP : n • P = 0) (a : ZMod n) :
    zmodHom n P hP a = a.val • P := by
  have h : ((a.val : ℤ) : ZMod n) = a := by simp
  conv_lhs => rw [← h]
  rw [zmodHom, ZMod.lift_coe]
  simp only [zmultiplesHom_apply, natCast_zsmul]

/- English proof (translation)
Establish `: Finite A` using `Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)`. Establish `: NeZero n` using `⟨hn.ne'⟩`. Take `⟨P, hP⟩` from `exists_addOrderOf_eq_of_card hn hA hcard hker`. Use `set C := AddSubgroup.zmultiples P with hCdef`. Establish `hC : Nat.card C = n` using `by rw [Nat.card_zmultiples, hP]`.

Establish `hB : Nat.card (A ⧸ C) = n`. Establish `h` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup C`. Rewrite `h` using `[hcard, hC]`. Establish `: n * n = Nat.card (A ⧸ C) * n` using `by rw [← h]; ring`. Conclude with `(Nat.eq_of_mul_eq_mul_right hn this).symm`.

Establish `hBn : ∀ b : A ⧸ C, n • b = 0`. Introduce `b`. Proceed by induction on `b using QuotientAddGroup.induction_on with`. Consider the case `H a => rw [← QuotientAddGroup.mk_nsmul, hA, QuotientAddGroup.mk_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨Qb, hQb⟩ : ∃ Qb : A ⧸ C, addOrderOf Qb = n := by`.

Establish `hexB : AddMonoid.ExponentExists (A ⧸ C)` using `⟨n, hn, hBn⟩`. Take `⟨Qb, hQ⟩` from `AddMonoid.exists_addOrderOf_eq_exponent hexB`. Use `⟨Qb, hQ.trans ?_⟩` and prove the remaining obligations. Use `set m := AddMonoid.exponent (A ⧸ C) with hmdef`. Establish `hm : m ∣ n` using `AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero hBn`.

Establish `hmpos : 0 < m` using `Nat.pos_of_dvd_of_pos hm hn`. Take `⟨d, hd⟩` from `hm`. Establish `hdpos : 0 < d` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hd; omega)`. Set `φ : A →+ A` to `{ toFun := fun a => m • a map_zero' := nsmul_zero m map_add' := fun a b => nsmul_add a b m }`. Establish `hφ : ∀ a, φ a = m • a` using `fun a => rfl`.

Establish `hkerφ : Nat.card φ.ker ≤ m ^ 2`. Establish `: Nat.card φ.ker = Nat.card {a : A // m • a = 0}` using `Nat.card_congr (Equiv.subtypeEquivRight fun a => by rw [AddMonoidHom.mem_ker, hφ])`. Rewrite using `[this]`. Conclude with `hker m ⟨d, hd⟩`. Establish `hrange : Nat.card φ.range ≤ d`.

Establish `hmem : ∀ x : φ.range, (x : A) ∈ C`. Introduce and unpack `⟨_, a, rfl⟩`. Use `show φ a ∈ C`. Rewrite using `[← QuotientAddGroup.eq_zero_iff, hφ, QuotientAddGroup.mk_nsmul]`. Conclude with `AddMonoid.exponent_nsmul_eq_zero _`.

Establish `hd' : ∀ x : φ.range, d • (x : A) = 0`. Introduce and unpack `⟨_, a, rfl⟩`. Use `show d • φ a = 0`. Rewrite using `[hφ, ← mul_nsmul', mul_comm, ← hd, hA]`. Set `ι : φ.range → {c : C // d • c = 0}` to `fun x => ⟨⟨x, hmem x⟩, by`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]`. Conclude with `hd' x⟩`. Establish `hι : Function.Injective ι`. Introduce `x y h`.

Use `congrArg (fun z => ((z.1 : C) : A)) h` as an intermediate fact. Conclude with `Subtype.ext this`. Establish `hle` using `Nat.card_le_card_of_injective ι hι`. Establish `: Fintype C` using `Fintype.ofFinite C`. Establish `hcyc` using `IsAddCyclic.card_nsmul_eq_zero_le (α := C) hdpos`.

Rewrite `hle` using `[Nat.card_eq_fintype_card (α := {c : C // d • c = 0}), Fintype.card_subtype]`. Conclude with `hle.trans (by convert hcyc)`. Establish `htot : Nat.card A = Nat.card φ.ker * Nat.card φ.range`. Rewrite using `[AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker, Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, mul_comm]`. Rewrite `htot` using `[hcard, hd]`.

Establish `h1 : (m * d) ^ 2 ≤ m ^ 2 * d`. Rewrite using `[htot]`. Conclude with `Nat.mul_le_mul hkerφ hrange`. Establish `hd1 : d ≤ 1`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Establish `: m ^ 2 * d < (m * d) ^ 2`. Rewrite using `[mul_pow]`. Establish `: d < d ^ 2` using `by nlinarith`. Conclude with `Nat.mul_lt_mul_of_pos_left this (by positivity)`.

Use linear arithmetic over natural numbers and integers. Establish `: d = 1` using `by omega`. Rewrite using `[hd, this, mul_one]`. Take `⟨Q, rfl⟩` from `QuotientAddGroup.mk_surjective Qb`. Establish `hQn : n • Q = 0` using `hA Q`.

Set `f : ZMod n × ZMod n →+ A` to `(zmodHom n P (hA P)).coprod (zmodHom n Q hQn)`. Establish `hf : ∀ x : ZMod n × ZMod n, f x = x.1.val • P + x.2.val • Q`. Introduce `x`. Simplify using `[f, AddMonoidHom.coprod_apply, zmodHom_apply]`. Establish `hinj : Function.Injective f`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `⟨a, b⟩ hab`. Rewrite `hab` using `[hf]`. Establish `hPC : (P : A ⧸ C) = 0` using `(QuotientAddGroup.eq_zero_iff P).mpr (AddSubgroup.mem_zmultiples P)`. Establish `hb : b.val • (Q : A ⧸ C) = 0`.

Use `congrArg (QuotientAddGroup.mk (s := C)) hab` as an intermediate fact. Simplify `this` using `[QuotientAddGroup.mk_add, QuotientAddGroup.mk_nsmul, hPC]`. Rewrite `hb` using `[← addOrderOf_dvd_iff_nsmul_eq_zero, hQb]`. Establish `hb0 : b = 0`. Rewrite using `[← ZMod.val_eq_zero]`.

Conclude with `Nat.eq_zero_of_dvd_of_lt hb (ZMod.val_lt b)`. Substitute `hb0` using the available equality. Simplify using `only [ZMod.val_zero, zero_smul, add_zero] at hab`. Rewrite `hab` using `[← addOrderOf_dvd_iff_nsmul_eq_zero, hP]`. Establish `ha0 : a = 0`.

Rewrite using `[← ZMod.val_eq_zero]`. Conclude with `Nat.eq_zero_of_dvd_of_lt hab (ZMod.val_lt a)`. Simplify using `[ha0]`. Establish `hbij : Function.Bijective f` using `hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_prod, Nat.card_zmod, sq])`. Conclude with `⟨(AddEquiv.ofBijective f hbij).symm⟩`.
-/
theorem nonempty_addEquiv_zmod_prod {n : ℕ} (hn : 0 < n) (hA : ∀ a : A, n • a = 0)
    (hcard : Nat.card A = n ^ 2)
    (hker : ∀ m, m ∣ n → Nat.card {a : A // m • a = 0} ≤ m ^ 2) :
    Nonempty (A ≃+ ZMod n × ZMod n) := by
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨P, hP⟩ := exists_addOrderOf_eq_of_card hn hA hcard hker
  set C := AddSubgroup.zmultiples P with hCdef
  have hC : Nat.card C = n := by rw [Nat.card_zmultiples, hP]
  have hB : Nat.card (A ⧸ C) = n := by
    have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup C
    rw [hcard, hC] at h
    have : n * n = Nat.card (A ⧸ C) * n := by rw [← h]; ring
    exact (Nat.eq_of_mul_eq_mul_right hn this).symm
  have hBn : ∀ b : A ⧸ C, n • b = 0 := by
    intro b
    induction b using QuotientAddGroup.induction_on with
    | H a => rw [← QuotientAddGroup.mk_nsmul, hA, QuotientAddGroup.mk_zero]

  obtain ⟨Qb, hQb⟩ : ∃ Qb : A ⧸ C, addOrderOf Qb = n := by
    have hexB : AddMonoid.ExponentExists (A ⧸ C) := ⟨n, hn, hBn⟩
    obtain ⟨Qb, hQ⟩ := AddMonoid.exists_addOrderOf_eq_exponent hexB
    refine ⟨Qb, hQ.trans ?_⟩
    set m := AddMonoid.exponent (A ⧸ C) with hmdef
    have hm : m ∣ n := AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero hBn
    have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hm hn
    obtain ⟨d, hd⟩ := hm
    have hdpos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; omega)
    let φ : A →+ A :=
      { toFun := fun a => m • a
        map_zero' := nsmul_zero m
        map_add' := fun a b => nsmul_add a b m }
    have hφ : ∀ a, φ a = m • a := fun a => rfl

    have hkerφ : Nat.card φ.ker ≤ m ^ 2 := by
      have : Nat.card φ.ker = Nat.card {a : A // m • a = 0} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun a => by rw [AddMonoidHom.mem_ker, hφ])
      rw [this]
      exact hker m ⟨d, hd⟩

    have hrange : Nat.card φ.range ≤ d := by
      have hmem : ∀ x : φ.range, (x : A) ∈ C := by
        rintro ⟨_, a, rfl⟩
        show φ a ∈ C
        rw [← QuotientAddGroup.eq_zero_iff, hφ, QuotientAddGroup.mk_nsmul]
        exact AddMonoid.exponent_nsmul_eq_zero _
      have hd' : ∀ x : φ.range, d • (x : A) = 0 := by
        rintro ⟨_, a, rfl⟩
        show d • φ a = 0
        rw [hφ, ← mul_nsmul', mul_comm, ← hd, hA]
      let ι : φ.range → {c : C // d • c = 0} := fun x =>
        ⟨⟨x, hmem x⟩, by
          apply Subtype.ext
          simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
          exact hd' x⟩
      have hι : Function.Injective ι := by
        intro x y h
        have := congrArg (fun z => ((z.1 : C) : A)) h
        exact Subtype.ext this
      have hle := Nat.card_le_card_of_injective ι hι
      classical
      have : Fintype C := Fintype.ofFinite C
      have hcyc := IsAddCyclic.card_nsmul_eq_zero_le (α := C) hdpos
      rw [Nat.card_eq_fintype_card (α := {c : C // d • c = 0}), Fintype.card_subtype] at hle
      exact hle.trans (by convert hcyc)
    have htot : Nat.card A = Nat.card φ.ker * Nat.card φ.range := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
        Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
    rw [hcard, hd] at htot
    have h1 : (m * d) ^ 2 ≤ m ^ 2 * d := by
      rw [htot]; exact Nat.mul_le_mul hkerφ hrange
    have hd1 : d ≤ 1 := by
      by_contra h
      push Not at h
      have : m ^ 2 * d < (m * d) ^ 2 := by
        rw [mul_pow]
        have : d < d ^ 2 := by nlinarith
        exact Nat.mul_lt_mul_of_pos_left this (by positivity)
      omega
    have : d = 1 := by omega
    rw [hd, this, mul_one]
  obtain ⟨Q, rfl⟩ := QuotientAddGroup.mk_surjective Qb
  have hQn : n • Q = 0 := hA Q
  let f : ZMod n × ZMod n →+ A := (zmodHom n P (hA P)).coprod (zmodHom n Q hQn)
  have hf : ∀ x : ZMod n × ZMod n, f x = x.1.val • P + x.2.val • Q := by
    intro x
    simp [f, AddMonoidHom.coprod_apply, zmodHom_apply]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    rw [hf] at hab
    have hPC : (P : A ⧸ C) = 0 := (QuotientAddGroup.eq_zero_iff P).mpr (AddSubgroup.mem_zmultiples P)
    have hb : b.val • (Q : A ⧸ C) = 0 := by
      have := congrArg (QuotientAddGroup.mk (s := C)) hab
      simpa [QuotientAddGroup.mk_add, QuotientAddGroup.mk_nsmul, hPC] using this
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hQb] at hb
    have hb0 : b = 0 := by
      rw [← ZMod.val_eq_zero]
      exact Nat.eq_zero_of_dvd_of_lt hb (ZMod.val_lt b)
    subst hb0
    simp only [ZMod.val_zero, zero_smul, add_zero] at hab
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hP] at hab
    have ha0 : a = 0 := by
      rw [← ZMod.val_eq_zero]
      exact Nat.eq_zero_of_dvd_of_lt hab (ZMod.val_lt a)
    simp [ha0]
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_prod, Nat.card_zmod, sq])
  exact ⟨(AddEquiv.ofBijective f hbij).symm⟩

end Group

section Curve

variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]

/- English proof (translation)
Establish `h` using `card_zsmul_eq_zero W (n := (n : ℤ)) (by exact_mod_cast hn)`. Rewrite `h` using `[Int.natAbs_natCast]`. Rewrite using `[← h]`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight fun P => Submodule.mem_torsionBy_iff _ _)`.
-/
theorem card_torsionBy {n : ℕ} (hn : (n : F) ≠ 0) :
    Nat.card (torsionBy W.toAffine.Point n) = n ^ 2 := by
  classical
  have h := card_zsmul_eq_zero W (n := (n : ℤ)) (by exact_mod_cast hn)
  rw [Int.natAbs_natCast] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun P => Submodule.mem_torsionBy_iff _ _)

/- English proof (translation)
Establish `hn0 : 0 < n` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hn)`. Use `nonempty_addEquiv_zmod_prod hn0 (fun x => torsionBy.nsmul x) (card_torsionBy W hn) ?_` and prove the remaining obligations. Introduce `m hm`. Establish `hmF : (m : F) ≠ 0`. Take `⟨k, rfl⟩` from `hm`.

Introduce `h`. Conclude with `hn (by push_cast; rw [h, zero_mul])`. Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at hmF`. Establish `: Finite (torsionBy W.toAffine.Point m)` using `Nat.finite_of_card_ne_zero (by rw [card_torsionBy W hmF]; exact pow_ne_zero _ hm0)`. Rewrite using `[← card_torsionBy W hmF]`.

Use `Nat.card_le_card_of_injective (fun x => ⟨x.1.1, torsionBy.nsmul_iff.mpr ?_⟩) ?_` and prove the remaining obligations. Use `congrArg Subtype.val x.2` as an intermediate fact. Simplify using `using this`. Introduce `x y h`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using congrArg Subtype.val h`.
-/
theorem nonempty_torsionBy_addEquiv {n : ℕ} (hn : (n : F) ≠ 0) :
    Nonempty (torsionBy W.toAffine.Point n ≃+ ZMod n × ZMod n) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  refine nonempty_addEquiv_zmod_prod hn0 (fun x => torsionBy.nsmul x) (card_torsionBy W hn) ?_
  intro m hm
  have hmF : (m : F) ≠ 0 := by
    obtain ⟨k, rfl⟩ := hm
    intro h
    exact hn (by push_cast; rw [h, zero_mul])
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmF
  have : Finite (torsionBy W.toAffine.Point m) :=
    Nat.finite_of_card_ne_zero (by rw [card_torsionBy W hmF]; exact pow_ne_zero _ hm0)
  rw [← card_torsionBy W hmF]
  refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, torsionBy.nsmul_iff.mpr ?_⟩) ?_
  · have := congrArg Subtype.val x.2
    simpa using this
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h

end Curve

end GroundTheory.Arith.Abelian
