import Mathlib

open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.FundGen

/- English proof (translation)
Establish `: NeZero p` using `⟨(Fact.out : p.Prime).ne_zero⟩`. Set `_ : Algebra (ZMod p) F` to `ZMod.algebra F p`. Establish `hcomm : ∀ r : ZMod p, α (algebraMap (ZMod p) F r) = algebraMap (ZMod p) F r` using `fun r => DFunLike.congr_fun (Subsingleton.elim (α.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) r`. Set `β : F →ₐ[ZMod p] F` to `{ α with commutes' := hcomm }`. Take `⟨n, hn⟩` from `(FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F).2 β`.

Establish `hrank : Module.finrank (ZMod p) F = f`. Establish `h1` using `Module.card_eq_pow_finrank (K := ZMod p) (V := F)`. Rewrite `h1` using `[ZMod.card, hc]`. Conclude with `(Nat.pow_right_injective (Fact.out : p.Prime).two_le h1).symm`. Establish `key : ∀ k : ℕ, ∀ x : F, (FiniteField.frobeniusAlgHom (ZMod p) F ^ k) x = x ^ p ^ k`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `x`. Rewrite using `[pow_succ (FiniteField.frobeniusAlgHom (ZMod p) F) k, AlgHom.mul_apply, ih, FiniteField.frobeniusAlgHom_apply, ZMod.card, ← pow_mul, pow_succ' p k]`. Use `⟨(n : ℕ), lt_of_lt_of_eq n.isLt hrank, fun a => ?_⟩` and prove the remaining obligations. Establish `h2 : (FiniteField.frobeniusAlgHom (ZMod p) F ^ (n : ℕ)) a = β a` using `DFunLike.congr_fun hn a`. Rewrite `h2` using `[key]`.

Conclude with `h2.symm`.
-/
theorem ringHom_eq_frob_pow (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p]
    (f : ℕ) (hc : Fintype.card F = p ^ f) (α : F →+* F) :
    ∃ n < f, ∀ a, α a = a ^ p ^ n := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let _ : Algebra (ZMod p) F := ZMod.algebra F p
  have hcomm : ∀ r : ZMod p, α (algebraMap (ZMod p) F r) = algebraMap (ZMod p) F r := fun r =>
    DFunLike.congr_fun
      (Subsingleton.elim (α.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) r
  let β : F →ₐ[ZMod p] F := { α with commutes' := hcomm }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F).2 β
  have hrank : Module.finrank (ZMod p) F = f := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod p) (V := F)
    rw [ZMod.card, hc] at h1
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h1).symm
  have key : ∀ k : ℕ, ∀ x : F, (FiniteField.frobeniusAlgHom (ZMod p) F ^ k) x = x ^ p ^ k := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ (FiniteField.frobeniusAlgHom (ZMod p) F) k, AlgHom.mul_apply, ih,
        FiniteField.frobeniusAlgHom_apply, ZMod.card, ← pow_mul, pow_succ' p k]
  refine ⟨(n : ℕ), lt_of_lt_of_eq n.isLt hrank, fun a => ?_⟩
  have h2 : (FiniteField.frobeniusAlgHom (ZMod p) F ^ (n : ℕ)) a = β a := DFunLike.congr_fun hn a
  rw [key] at h2
  exact h2.symm

def mIdeal {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hv : v.Integers R) : Ideal R where
  carrier := {r | v (algebraMap R C r) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    exact v.map_add_lt ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one c)) hx

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem mem_mIdeal {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (r : R) :
    r ∈ mIdeal v R hv ↔ v (algebraMap R C r) < 1 := by
  exact Iff.rfl

/- English proof (translation)
Introduce `h`. Establish `h1 : (1 : R) ∈ mIdeal v R hv` using `by rw [h]; exact Submodule.mem_top`. Rewrite `h1` using `[mem_mIdeal, map_one, map_one]`. Conclude with `lt_irrefl _ h1`.
-/
theorem mIdeal_ne_top {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) : mIdeal v R hv ≠ ⊤ := by
  intro h
  have h1 : (1 : R) ∈ mIdeal v R hv := by rw [h]; exact Submodule.mem_top
  rw [mem_mIdeal, map_one, map_one] at h1
  exact lt_irrefl _ h1

def toHom {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hv : v.Integers R) {p : ℕ} (hp : v (p : C) < 1) (F : Type) [Field F]
    (σ : MulChar F R) (hσ : ∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) :
    F →+* R ⧸ mIdeal v R hv where
  toFun a := Ideal.Quotient.mk _ (σ a)
  map_one' := by rw [map_one, map_one]
  map_mul' a b := by rw [map_mul, map_mul]
  map_zero' := by rw [MulChar.map_zero, map_zero]
  map_add' a b := by
    have hle : Ideal.span {(p : R)} ≤ mIdeal v R hv := by
      rw [Ideal.span_singleton_le_iff_mem, mem_mIdeal]
      simpa using hp
    have := Ideal.Quotient.eq_zero_iff_mem.2 (hle (hσ a b))
    rw [map_sub, map_sub, sub_sub, sub_eq_zero] at this
    exact this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toHom_apply {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) {p : ℕ} (hp : v (p : C) < 1) (F : Type) [Field F]
    (σ : MulChar F R) (hσ : ∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) (a : F) :
    toHom v R hv hp F σ hσ a = Ideal.Quotient.mk _ (σ a) := rfl

/- English proof (translation)
Establish `: Nontrivial (R ⧸ mIdeal v R hv)` using `Ideal.Quotient.nontrivial_iff.2 (mIdeal_ne_top v R hv)`. Conclude with `(toHom v R hv hp F σ hσ).injective`.
-/
theorem toHom_injective {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) {p : ℕ} (hp : v (p : C) < 1) (F : Type) [Field F]
    (σ : MulChar F R) (hσ : ∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) :
    Function.Injective (toHom v R hv hp F σ hσ) := by
  have : Nontrivial (R ⧸ mIdeal v R hv) := Ideal.Quotient.nontrivial_iff.2 (mIdeal_ne_top v R hv)
  exact (toHom v R hv hp F σ hσ).injective

/- English proof (translation)
Apply `MulChar.ext` to reduce the goal to its premises. Introduce `a`. Take `⟨k, rfl⟩` from `(Submonoid.mem_powers_iff _ _).1 (hg a)`. Rewrite using `[Units.val_pow_eq_pow_val, map_pow, map_pow, h]`.
-/
theorem mulChar_eq_of_gen {F R : Type} [Field F] [CommRing R] (g : Fˣ)
    (hg : ∀ y : Fˣ, y ∈ Submonoid.powers g) (χ χ' : MulChar F R)
    (h : χ (g : F) = χ' (g : F)) : χ = χ' := by
  apply MulChar.ext
  intro a
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (hg a)
  rw [Units.val_pow_eq_pow_val, map_pow, map_pow, h]

/- English proof (translation)
Establish `hpn : p ^ n ≠ 0` using `pow_ne_zero _ (Fact.out : p.Prime).ne_zero`. Establish `e : ∀ x : F, (σ ^ p ^ n) x = σ (x ^ p ^ n)` using `fun x => by`. Rewrite using `[MulChar.pow_apply' σ hpn, map_pow]`. Rewrite using `[e, e, e, add_pow_char_pow]`. Conclude with `hσ _ _`.
-/
theorem frob_pow_additive {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] (F : Type) [Field F]
    [CharP F p] (σ : MulChar F R)
    (hσ : ∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) (n : ℕ) (a b : F) :
    (σ ^ p ^ n) (a + b) - (σ ^ p ^ n) a - (σ ^ p ^ n) b ∈ Ideal.span {(p : R)} := by
  have hpn : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have e : ∀ x : F, (σ ^ p ^ n) x = σ (x ^ p ^ n) := fun x => by
    rw [MulChar.pow_apply' σ hpn, map_pow]
  rw [e, e, e, add_pow_char_pow]
  exact hσ _ _

/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc σ hσ`. Establish `: IsDomain R` using `Function.Injective.isDomain (algebraMap R C) hv.hom_inj`. Establish `hinj : Function.Injective σ` using `fun a b hab => toHom_injective v R hv hp F σ hσ (by rw [toHom_apply, toHom_apply, hab])`. Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := Fˣ)`. Establish `hg' : ∀ y : Fˣ, y ∈ Submonoid.powers g` using `fun y => mem_powers_iff_mem_zpowers.2 (hg y)`.

Establish `hq : Fintype.card Fˣ = p ^ f - 1` using `by rw [Fintype.card_units, hc]`. Establish `hq1 : 1 ≤ p ^ f - 1` using `hq ▸ Fintype.card_pos`. Establish `hog : orderOf g = p ^ f - 1`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hq]`. Establish `hpowg : ∀ k : ℕ, (σ ^ k) (g : F) = σ (g : F) ^ k`.

Introduce `k`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Rewrite using `[pow_zero, pow_zero, MulChar.one_apply g.isUnit]`. Conclude with `MulChar.pow_apply' σ hk.ne' _`. Establish `hζ : IsPrimitiveRoot (σ (g : F)) (p ^ f - 1)`.

Use `⟨?_, fun l hl => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, ← hog, pow_orderOf_eq_one, Units.val_one, map_one]`. Rewrite using `[← hog]`. Apply `orderOf_dvd_of_pow_eq_one` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, map_pow, hl, Units.val_one, map_one]`. Establish `partB : ∀ χ : MulChar F R, ∃ m, 1 ≤ m ∧ m ≤ p ^ f - 1 ∧ χ = σ ^ m`. Introduce `χ`. Establish `hχ : χ (g : F) ^ (p ^ f - 1) = 1`.

Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, ← hq, pow_card_eq_one, Units.val_one, map_one]`. Establish `: NeZero (p ^ f - 1)` using `⟨by omega⟩`. Take `⟨i, hi, hi'⟩` from `hζ.eq_pow_of_pow_eq_one hχ`. Distinguish the cases in `hi0 : i = 0`. Use `⟨p ^ f - 1, hq1, le_rfl, mulChar_eq_of_gen g hg' _ _ ?_⟩` and prove the remaining obligations.

Rewrite using `[hpowg, hζ.pow_eq_one, ← hi', hi0, pow_zero]`. Use `⟨i, Nat.one_le_iff_ne_zero.2 hi0, hi.le, mulChar_eq_of_gen g hg' _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[hpowg, hi']`. Use `⟨?_, partB, fun n => frob_pow_additive p F σ hσ n, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[orderOf_eq_iff (by omega)]`.

Use `⟨?_, fun m hm hm0 h => ?_⟩` and prove the remaining obligations. Apply `MulChar.ext` to reduce the goal to its premises. Introduce `a`. Rewrite using `[MulChar.pow_apply' σ (by omega), ← map_pow, ← Units.val_pow_eq_pow_val, ← hq, pow_card_eq_one, Units.val_one, map_one, MulChar.one_apply (Units.isUnit a)]`. Establish `h3` using `DFunLike.congr_fun h (g : F)`.

Rewrite `h3` using `[hpowg, MulChar.one_apply g.isUnit]`. Conclude with `hζ.pow_ne_one_of_pos_of_lt hm0.ne' hm h3`. Introduce `τ hτ`. Take `⟨m, hm1, hmq, rfl⟩` from `partB τ`. Establish `e : ∀ x : F, (σ ^ m) x = σ (x ^ m)` using `fun x => by`.

Rewrite using `[MulChar.pow_apply' σ (by omega), map_pow]`. Establish `hadd : ∀ a b : F, (a + b) ^ m = a ^ m + b ^ m`. Introduce `a b`. Apply `toHom_injective v R hv hp F σ hσ` to reduce the goal to its premises. Establish `h3` using `map_add (toHom v R hv hp F (σ ^ m) hτ) a b`.

Rewrite `h3` using `[toHom_apply, toHom_apply, toHom_apply, e, e, e]`. Rewrite using `[map_add, toHom_apply, toHom_apply, toHom_apply, h3]`. Set `α : F →+* F` to `{ toFun := fun x => x ^ m map_one' := one_pow m map_mul' := fun a b => mul_pow a b m map_zero' := zero_pow (by omega) map_add' := hadd }`. Take `⟨n, hn, hα⟩` from `ringHom_eq_frob_pow p F f hc α`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations.

Apply `MulChar.ext` to reduce the goal to its premises. Introduce `a`. Rewrite using `[e, MulChar.pow_apply' σ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), ← map_pow]`. Use `congr 1`. Conclude with `hα a`.

Introduce `a b hab`. Establish `h1 : σ a - σ b ∉ mIdeal v R hv`. Introduce `hmem`. Apply `hab` to reduce the goal to its premises. Apply `toHom_injective v R hv hp F σ hσ` to reduce the goal to its premises.

Rewrite using `[toHom_apply, toHom_apply]`. Conclude with `Ideal.Quotient.eq.2 hmem`. Rewrite `h1` using `[mem_mIdeal, not_lt]`. Conclude with `le_antisymm (hv.map_le_one _) h1`.
-/
theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → orderOf σ = p ^ f - 1 ∧ (∀ χ : MulChar F R, ∃ m, 1 ≤ m ∧ m ≤ p ^ f - 1 ∧ χ = σ ^ m) ∧ (∀ n, (∀ a b, (σ ^ p ^ n) (a + b) - (σ ^ p ^ n) a - (σ ^ p ^ n) b ∈ Ideal.span {(p : R)})) ∧ (∀ τ : MulChar F R, (∀ a b, τ (a + b) - τ a - τ b ∈ Ideal.span {(p : R)}) → ∃ n < f, τ = σ ^ p ^ n) ∧ (∀ a b : F, a ≠ b → v (algebraMap R C (σ a - σ b)) = 1) := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc σ hσ
  have : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  have hinj : Function.Injective σ := fun a b hab =>
    toHom_injective v R hv hp F σ hσ (by rw [toHom_apply, toHom_apply, hab])
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hg' : ∀ y : Fˣ, y ∈ Submonoid.powers g := fun y => mem_powers_iff_mem_zpowers.2 (hg y)
  have hq : Fintype.card Fˣ = p ^ f - 1 := by rw [Fintype.card_units, hc]
  have hq1 : 1 ≤ p ^ f - 1 := hq ▸ Fintype.card_pos
  have hog : orderOf g = p ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hq]
  have hpowg : ∀ k : ℕ, (σ ^ k) (g : F) = σ (g : F) ^ k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pow_zero, pow_zero, MulChar.one_apply g.isUnit]
    · exact MulChar.pow_apply' σ hk.ne' _
  have hζ : IsPrimitiveRoot (σ (g : F)) (p ^ f - 1) := by
    refine ⟨?_, fun l hl => ?_⟩
    · rw [← map_pow, ← Units.val_pow_eq_pow_val, ← hog, pow_orderOf_eq_one, Units.val_one, map_one]
    · rw [← hog]
      apply orderOf_dvd_of_pow_eq_one
      apply Units.ext
      apply hinj
      rw [Units.val_pow_eq_pow_val, map_pow, hl, Units.val_one, map_one]
  have partB : ∀ χ : MulChar F R, ∃ m, 1 ≤ m ∧ m ≤ p ^ f - 1 ∧ χ = σ ^ m := by
    intro χ
    have hχ : χ (g : F) ^ (p ^ f - 1) = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, ← hq, pow_card_eq_one, Units.val_one, map_one]
    have : NeZero (p ^ f - 1) := ⟨by omega⟩
    obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one hχ
    by_cases hi0 : i = 0
    · refine ⟨p ^ f - 1, hq1, le_rfl, mulChar_eq_of_gen g hg' _ _ ?_⟩
      rw [hpowg, hζ.pow_eq_one, ← hi', hi0, pow_zero]
    · refine ⟨i, Nat.one_le_iff_ne_zero.2 hi0, hi.le, mulChar_eq_of_gen g hg' _ _ ?_⟩
      rw [hpowg, hi']
  refine ⟨?_, partB, fun n => frob_pow_additive p F σ hσ n, ?_, ?_⟩
  · rw [orderOf_eq_iff (by omega)]
    refine ⟨?_, fun m hm hm0 h => ?_⟩
    · apply MulChar.ext
      intro a
      rw [MulChar.pow_apply' σ (by omega), ← map_pow, ← Units.val_pow_eq_pow_val, ← hq,
        pow_card_eq_one, Units.val_one, map_one, MulChar.one_apply (Units.isUnit a)]
    · have h3 := DFunLike.congr_fun h (g : F)
      rw [hpowg, MulChar.one_apply g.isUnit] at h3
      exact hζ.pow_ne_one_of_pos_of_lt hm0.ne' hm h3
  · intro τ hτ
    obtain ⟨m, hm1, hmq, rfl⟩ := partB τ
    have e : ∀ x : F, (σ ^ m) x = σ (x ^ m) := fun x => by
      rw [MulChar.pow_apply' σ (by omega), map_pow]
    have hadd : ∀ a b : F, (a + b) ^ m = a ^ m + b ^ m := by
      intro a b
      apply toHom_injective v R hv hp F σ hσ
      have h3 := map_add (toHom v R hv hp F (σ ^ m) hτ) a b
      rw [toHom_apply, toHom_apply, toHom_apply, e, e, e] at h3
      rw [map_add, toHom_apply, toHom_apply, toHom_apply, h3]
    let α : F →+* F :=
      { toFun := fun x => x ^ m
        map_one' := one_pow m
        map_mul' := fun a b => mul_pow a b m
        map_zero' := zero_pow (by omega)
        map_add' := hadd }
    obtain ⟨n, hn, hα⟩ := ringHom_eq_frob_pow p F f hc α
    refine ⟨n, hn, ?_⟩
    apply MulChar.ext
    intro a
    rw [e, MulChar.pow_apply' σ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), ← map_pow]
    congr 1
    exact hα a
  · intro a b hab
    have h1 : σ a - σ b ∉ mIdeal v R hv := by
      intro hmem
      apply hab
      apply toHom_injective v R hv hp F σ hσ
      rw [toHom_apply, toHom_apply]
      exact Ideal.Quotient.eq.2 hmem
    rw [mem_mIdeal, not_lt] at h1
    exact le_antisymm (hv.map_le_one _) h1

end GlobalTheory.CompanionTheory.Ar.GR.FundGen
