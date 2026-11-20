import Mathlib

open Function Cardinal

namespace GlobalTheory

/- English proof (translation)
Use `mk_le_of_injective (f := fun g => (ι.comp g).comp f) ?_` and prove the remaining obligations. Introduce `g h hgh`. Use extensionality with `x`. Take `⟨a, rfl⟩` from `hf x`. Conclude with `hι (DFunLike.congr_fun hgh a)`.
-/
theorem mk_addMonoidHom_le_of_surjective_of_injective {A A' X Y : Type} [AddCommGroup A]
    [AddCommGroup A'] [AddCommGroup X] [AddCommGroup Y] (f : A →+ A') (hf : Surjective f)
    (ι : X →+ Y) (hι : Injective ι) : #(A' →+ X) ≤ #(A →+ Y) := by
  refine mk_le_of_injective (f := fun g => (ι.comp g).comp f) ?_
  intro g h hgh
  ext x
  obtain ⟨a, rfl⟩ := hf x
  exact hι (DFunLike.congr_fun hgh a)

/- English proof (translation)
Take `⟨k, rfl⟩` from `h`. Establish `ha : a ≠ 0` using `left_ne_zero_of_mul hn`. Establish `hk : k ≠ 0` using `right_ne_zero_of_mul hn`. Use `haveI : NeZero a := ⟨ha⟩`. Use `⟨ZMod.lift a ⟨zmultiplesHom (ZMod (a * k)) (k : ZMod (a * k)), ?_⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul]`. Rewrite using `[← Nat.cast_mul, ZMod.natCast_self]`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `h2 : ((x.val : ℤ) : ZMod a) = x` using `by simp`.

Rewrite `hx` using `[← h2, ZMod.lift_coe]`. Simplify using `only [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul] at hx`. Rewrite `hx` using `[← Nat.cast_mul, ZMod.natCast_eq_zero_iff]`. Establish `hd : a ∣ x.val` using `Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hk) hx`. Establish `hv : x.val = 0` using `Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt x)`.

Rewrite using `[← ZMod.natCast_zmod_val x, hv, Nat.cast_zero]`.
-/
theorem exists_injective_zmod_addMonoidHom {a n : ℕ} (hn : n ≠ 0) (h : a ∣ n) :
    ∃ ι : ZMod a →+ ZMod n, Injective ι := by
  obtain ⟨k, rfl⟩ := h
  have ha : a ≠ 0 := left_ne_zero_of_mul hn
  have hk : k ≠ 0 := right_ne_zero_of_mul hn
  haveI : NeZero a := ⟨ha⟩
  refine ⟨ZMod.lift a ⟨zmultiplesHom (ZMod (a * k)) (k : ZMod (a * k)), ?_⟩, ?_⟩
  · simp only [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul]
    rw [← Nat.cast_mul, ZMod.natCast_self]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h2 : ((x.val : ℤ) : ZMod a) = x := by simp
    rw [← h2, ZMod.lift_coe] at hx
    simp only [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul] at hx
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hx
    have hd : a ∣ x.val := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hk) hx
    have hv : x.val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt x)
    rw [← ZMod.natCast_zmod_val x, hv, Nat.cast_zero]

/- English proof (translation)
Use `haveI : NeZero p := ⟨hp.out.ne_zero⟩`. Use `letI : Module (ZMod p) V := AddCommGroup.zmodModule hV`. Set `b` to `Module.Basis.ofVectorSpace (ZMod p) V`. Use `set ι := Module.Basis.ofVectorSpaceIndex (ZMod p) V`. Establish `hι : Infinite ι`.

Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_infinite_iff_finite]`. Use `haveI := h`. Use `haveI : Finite V := Finite.of_equiv _ b.equivFun.toEquiv.symm`. Conclude with `not_finite V`.

Establish `hV1 : #V = #ι`. Rewrite using `[b.repr.toEquiv.cardinal_eq, mk_finsupp_of_infinite, max_eq_left]`. Conclude with `(lt_aleph0_of_finite _).le.trans (aleph0_le_mk ι)`. Establish `hr : Module.rank (ZMod p) V = #ι` using `b.mk_eq_rank''.symm`. Establish `h0 : ℵ₀ ≤ Module.rank (ZMod p) V` using `hr ▸ aleph0_le_mk ι`.

Establish `h1` using `lift_rank_lt_rank_dual h0`. Rewrite `h1` using `[lift_id, rank_dual_eq_card_dual_of_aleph0_le_rank h0]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mk_lt_mk_addMonoidHom_zmod_prime (p : ℕ) [hp : Fact p.Prime] (V : Type) [AddCommGroup V]
    (hV : ∀ x : V, p • x = 0) [Infinite V] : #V < #(V →+ ZMod p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  letI : Module (ZMod p) V := AddCommGroup.zmodModule hV
  let b := Module.Basis.ofVectorSpace (ZMod p) V
  set ι := Module.Basis.ofVectorSpaceIndex (ZMod p) V
  have hι : Infinite ι := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    haveI := h
    haveI : Finite V := Finite.of_equiv _ b.equivFun.toEquiv.symm
    exact not_finite V
  have hV1 : #V = #ι := by
    rw [b.repr.toEquiv.cardinal_eq, mk_finsupp_of_infinite, max_eq_left]
    exact (lt_aleph0_of_finite _).le.trans (aleph0_le_mk ι)
  have hr : Module.rank (ZMod p) V = #ι := b.mk_eq_rank''.symm
  have h0 : ℵ₀ ≤ Module.rank (ZMod p) V := hr ▸ aleph0_le_mk ι
  have h1 := lift_rank_lt_rank_dual h0
  rw [lift_id, rank_dual_eq_card_dual_of_aleph0_le_rank h0] at h1
  calc #V = Module.rank (ZMod p) V := by rw [hV1, hr]
    _ < #(V →ₗ[ZMod p] ZMod p) := h1
    _ = #(V →+ ZMod p) := ((AddMonoidHom.toZModLinearMapEquiv p).toEquiv.cardinal_eq).symm

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `A _ hA hn hinf`. Break down `eq_or_ne n 1 with rfl | h1` into its components or cases. Use `exfalso haveI : Subsingleton A := ⟨fun x y => by`.

Establish `hx : x = 0` using `by simpa using hA x`. Establish `hy : y = 0` using `by simpa using hA y`. Rewrite using `[hx, hy]⟩`. Conclude with `not_finite A`. Take `⟨p, hp, m, rfl⟩ : ∃ p, p.Prime ∧ ∃ m, n = p * m` from `⟨n.minFac, Nat.minFac_prime h1, n / n.minFac, (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm⟩`.

Use `haveI := Fact.mk hp`. Establish `hm : m ≠ 0` using `right_ne_zero_of_mul hn`. Set `f : A →+ A` to `AddMonoidHom.mk' (fun x => p • x) (fun x y => nsmul_add x y p)`. Set `P : AddSubgroup A` to `f.range`. Establish `hmul : #A = #(A ⧸ P) * #P`.

Rewrite using `[(AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := P)).cardinal_eq, mk_prod, lift_id, lift_id]`. Establish `hPle : #P ≤ #A` using `mk_le_of_injective Subtype.val_injective`. Establish `hQle : #(A ⧸ P) ≤ #A` using `mk_le_of_surjective (QuotientAddGroup.mk_surjective)`. Establish `hAinf : ℵ₀ ≤ #A` using `aleph0_le_mk A`. Break down `hPle.lt_or_eq with hPlt | hPeq` into its components or cases.

Break down `hQle.lt_or_eq with hQlt | hQeq` into its components or cases. Conclude with `absurd hmul (ne_of_gt (mul_lt_of_lt hAinf hQlt hPlt))`. Use `letI : Infinite (A ⧸ P) := Cardinal.infinite_iff.mpr (hQeq ▸ hAinf)`. Establish `hQp : ∀ y : A ⧸ P, p • y = 0`. Introduce `y`.

Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective y`. Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]`. Conclude with `⟨x, rfl⟩`. Take `⟨ι, hι⟩` from `exists_injective_zmod_addMonoidHom hn (dvd_mul_right p m)`. Combine the equalities or inequalities in the displayed calculation.

Use `letI : Infinite P := Cardinal.infinite_iff.mpr (hPeq ▸ hAinf)`. Establish `hPm : ∀ y : P, m • y = 0`. Introduce and unpack `⟨_, x, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show m • (p • x) = 0`.

Rewrite using `[smul_smul, mul_comm, hA x]`. Establish `hlt : m < p * m`. Use `hp.two_le` as an intermediate fact. Use `Nat.pos_of_ne_zero hm` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hP` using `ih m hlt P hPm hm inferInstance`. Take `⟨ι, hι⟩` from `exists_injective_zmod_addMonoidHom hn (dvd_mul_left m p)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mk_lt_mk_addMonoidHom_zmod (n : ℕ) : ∀ (A : Type) [AddCommGroup A],
    (∀ x : A, n • x = 0) → n ≠ 0 → Infinite A → #A < #(A →+ ZMod n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ hA hn hinf
  rcases eq_or_ne n 1 with rfl | h1
  · exfalso
    haveI : Subsingleton A := ⟨fun x y => by
      have hx : x = 0 := by simpa using hA x
      have hy : y = 0 := by simpa using hA y
      rw [hx, hy]⟩
    exact not_finite A
  obtain ⟨p, hp, m, rfl⟩ : ∃ p, p.Prime ∧ ∃ m, n = p * m :=
    ⟨n.minFac, Nat.minFac_prime h1, n / n.minFac, (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm⟩
  haveI := Fact.mk hp
  have hm : m ≠ 0 := right_ne_zero_of_mul hn
  let f : A →+ A := AddMonoidHom.mk' (fun x => p • x) (fun x y => nsmul_add x y p)
  let P : AddSubgroup A := f.range
  have hmul : #A = #(A ⧸ P) * #P := by
    rw [(AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := P)).cardinal_eq, mk_prod,
      lift_id, lift_id]
  have hPle : #P ≤ #A := mk_le_of_injective Subtype.val_injective
  have hQle : #(A ⧸ P) ≤ #A := mk_le_of_surjective (QuotientAddGroup.mk_surjective)
  have hAinf : ℵ₀ ≤ #A := aleph0_le_mk A
  rcases hPle.lt_or_eq with hPlt | hPeq
  · rcases hQle.lt_or_eq with hQlt | hQeq
    · exact absurd hmul (ne_of_gt (mul_lt_of_lt hAinf hQlt hPlt))

    · letI : Infinite (A ⧸ P) := Cardinal.infinite_iff.mpr (hQeq ▸ hAinf)
      have hQp : ∀ y : A ⧸ P, p • y = 0 := by
        intro y
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
        rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
        exact ⟨x, rfl⟩
      obtain ⟨ι, hι⟩ := exists_injective_zmod_addMonoidHom hn (dvd_mul_right p m)
      calc #A = #(A ⧸ P) := hQeq.symm
        _ < #(A ⧸ P →+ ZMod p) := mk_lt_mk_addMonoidHom_zmod_prime p (A ⧸ P) hQp
        _ ≤ #(A →+ ZMod (p * m)) :=
          mk_addMonoidHom_le_of_surjective_of_injective (QuotientAddGroup.mk' P)
            (QuotientAddGroup.mk_surjective) ι hι

  · letI : Infinite P := Cardinal.infinite_iff.mpr (hPeq ▸ hAinf)
    have hPm : ∀ y : P, m • y = 0 := by
      rintro ⟨_, x, rfl⟩
      apply Subtype.ext
      show m • (p • x) = 0
      rw [smul_smul, mul_comm, hA x]
    have hlt : m < p * m := by
      have := hp.two_le
      have := Nat.pos_of_ne_zero hm
      nlinarith
    have hP := ih m hlt P hPm hm inferInstance
    obtain ⟨ι, hι⟩ := exists_injective_zmod_addMonoidHom hn (dvd_mul_left m p)
    calc #A = #P := hPeq.symm
      _ < #(P →+ ZMod m) := hP
      _ ≤ #(A →+ ZMod (p * m)) :=
        mk_addMonoidHom_le_of_surjective_of_injective f.rangeRestrict
          f.rangeRestrict_surjective ι hι

/- English proof (translation)
Introduce `n _ A B C _ _ _ _ _ _ _ b ⟨e⟩ hb hbf`. Establish `key : ∀ (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [AddCommGroup Y] [Module (ZMod n) Y] (c : X →ₗ[ZMod n] Y →ₗ[ZMod n] C), Bijective c.flip → Infinite X → #X < #Y`. Introduce `X Y _ _ _ _ c hc hX`. Establish `h1 : #Y = #(X →+ ZMod n)`. Establish `e1` using `(LinearEquiv.ofBijective c.flip hc).toEquiv`.

Establish `e2 : (X →ₗ[ZMod n] C) ≃ (X →ₗ[ZMod n] ZMod n)` using `{ toFun := fun g => e.toLinearMap ∘ₗ g invFun := fun g => e.symm.toLinearMap ∘ₗ g left_inv := fun g => by ext; simp right_inv := fun g => by ext; simp }`. Establish `e3` using `(AddMonoidHom.toZModLinearMapEquiv n (M := X) (M₁ := ZMod n)).toEquiv.symm`. Conclude with `(e1.trans (e2.trans e3)).cardinal_eq`. Rewrite using `[h1]`. Use `mk_lt_mk_addMonoidHom_zmod n X (fun x => ?_) (NeZero.ne n) hX` and prove the remaining obligations.

Rewrite using `[← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]`. Establish `hbff : Bijective b.flip.flip` using `by simpa using hb`. Establish `hA : Finite A`. Assume the negation of the conclusion as `hA`. Rewrite `hA` using `[not_finite_iff_infinite]`.

Establish `h1` using `key A B b hbf hA`. Use `haveI : Infinite B := Cardinal.infinite_iff.mpr ((aleph0_le_mk A).trans h1.le)`. Conclude with `lt_asymm h1 (key B A b.flip hbff inferInstance)`. Establish `hB : Finite B`. Assume the negation of the conclusion as `hB`.

Rewrite `hB` using `[not_finite_iff_infinite]`. Establish `h1` using `key B A b.flip hbff hB`. Use `haveI : Infinite A := Cardinal.infinite_iff.mpr ((aleph0_le_mk B).trans h1.le)`. Conclude with `not_finite A`. Conclude with `⟨hA, hB⟩`.
-/
theorem finite_of_perfect_pairing_zmod : ∀ (n : ℕ) [NeZero n] (A B C : Type) [AddCommGroup A]
    [Module (ZMod n) A] [AddCommGroup B] [Module (ZMod n) B] [AddCommGroup C]
    [Module (ZMod n) C] [Finite C] (b : A →ₗ[ZMod n] B →ₗ[ZMod n] C),
    Nonempty (C ≃ₗ[ZMod n] ZMod n) → Bijective b → Bijective b.flip → Finite A ∧ Finite B := by
  intro n _ A B C _ _ _ _ _ _ _ b ⟨e⟩ hb hbf
  have key : ∀ (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [AddCommGroup Y]
      [Module (ZMod n) Y] (c : X →ₗ[ZMod n] Y →ₗ[ZMod n] C), Bijective c.flip → Infinite X →
      #X < #Y := by
    intro X Y _ _ _ _ c hc hX
    have h1 : #Y = #(X →+ ZMod n) := by
      have e1 := (LinearEquiv.ofBijective c.flip hc).toEquiv
      have e2 : (X →ₗ[ZMod n] C) ≃ (X →ₗ[ZMod n] ZMod n) :=
        { toFun := fun g => e.toLinearMap ∘ₗ g
          invFun := fun g => e.symm.toLinearMap ∘ₗ g
          left_inv := fun g => by ext; simp
          right_inv := fun g => by ext; simp }
      have e3 := (AddMonoidHom.toZModLinearMapEquiv n (M := X) (M₁ := ZMod n)).toEquiv.symm
      exact (e1.trans (e2.trans e3)).cardinal_eq
    rw [h1]
    refine mk_lt_mk_addMonoidHom_zmod n X (fun x => ?_) (NeZero.ne n) hX
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  have hbff : Bijective b.flip.flip := by simpa using hb
  have hA : Finite A := by
    by_contra hA
    rw [not_finite_iff_infinite] at hA
    have h1 := key A B b hbf hA
    haveI : Infinite B := Cardinal.infinite_iff.mpr ((aleph0_le_mk A).trans h1.le)
    exact lt_asymm h1 (key B A b.flip hbff inferInstance)
  have hB : Finite B := by
    by_contra hB
    rw [not_finite_iff_infinite] at hB
    have h1 := key B A b.flip hbff hB
    haveI : Infinite A := Cardinal.infinite_iff.mpr ((aleph0_le_mk B).trans h1.le)
    exact not_finite A
  exact ⟨hA, hB⟩

end GlobalTheory
