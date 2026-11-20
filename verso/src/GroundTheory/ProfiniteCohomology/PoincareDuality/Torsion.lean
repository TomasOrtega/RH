import Mathlib
import GroundTheory.ProfiniteCohomology.TorsionDualFinite
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Function

variable {n : ℕ}

variable (n) in

noncomputable def zmodToQZ : ZMod n →+ QZ :=
  ZMod.lift n ⟨zmultiplesHom QZ (QZ.mk (1 / n)), by
    rw [zmultiplesHom_apply, ← QZ.mk_zsmul, QZ.mk_eq_zero_iff]
    by_cases hn : n = 0
    · exact ⟨0, by simp [hn]⟩
    · have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
      exact ⟨1, by rw [zsmul_eq_mul, Int.cast_natCast, mul_one_div, div_self hn', Int.cast_one]⟩⟩

/- English proof (translation)
Rewrite using `[zmodToQZ, ZMod.lift_coe, zmultiplesHom_apply, ← QZ.mk_zsmul, zsmul_eq_mul, mul_one_div]`.
-/
theorem zmodToQZ_intCast (m : ℤ) : zmodToQZ n (m : ZMod n) = QZ.mk (m / n) := by
  rw [zmodToQZ, ZMod.lift_coe, zmultiplesHom_apply, ← QZ.mk_zsmul, zsmul_eq_mul, mul_one_div]

variable [NeZero n]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Take `⟨m, rfl⟩` from `ZMod.intCast_surjective a`. Rewrite `ha` using `[zmodToQZ_intCast, QZ.mk_eq_zero_iff]`. Take `⟨z, hz⟩` from `ha`.

Establish `hn : (n : ℚ) ≠ 0` using `by exact_mod_cast NeZero.ne n`. Rewrite using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `⟨z, ?_⟩` and prove the remaining obligations. Establish `: (m : ℚ) = n * z`. Rewrite using `[hz]`.

Clear the denominators using the available nonvanishing facts. Conclude with `this` after adjusting the coercions.
-/
theorem zmodToQZ_injective : Injective (zmodToQZ n) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective a
  rw [zmodToQZ_intCast, QZ.mk_eq_zero_iff] at ha
  obtain ⟨z, hz⟩ := ha
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨z, ?_⟩
  have : (m : ℚ) = n * z := by
    rw [hz]
    field_simp
  exact_mod_cast this

/- English proof (translation)
Take `⟨q, rfl⟩` from `QZ.mk_surjective x`. Establish `h : QZ.mk ((n : ℤ) • q) = 0`. Rewrite using `[QZ.mk_zsmul, natCast_zsmul, hx]`. Take `⟨z, hz⟩` from `(QZ.mk_eq_zero_iff _).1 h`. Establish `hn : (n : ℚ) ≠ 0` using `by exact_mod_cast NeZero.ne n`.

Use `⟨(z : ZMod n), ?_⟩` and prove the remaining obligations. Rewrite using `[zmodToQZ_intCast, hz, zsmul_eq_mul]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_zmodToQZ_eq {x : QZ} (hx : n • x = 0) : ∃ a : ZMod n, zmodToQZ n a = x := by
  obtain ⟨q, rfl⟩ := QZ.mk_surjective x
  have h : QZ.mk ((n : ℤ) • q) = 0 := by
    rw [QZ.mk_zsmul, natCast_zsmul, hx]
  obtain ⟨z, hz⟩ := (QZ.mk_eq_zero_iff _).1 h
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  refine ⟨(z : ZMod n), ?_⟩
  rw [zmodToQZ_intCast, hz, zsmul_eq_mul]
  congr 1
  push_cast
  field_simp

section Lift

variable {A : Type*} [AddCommGroup A]

noncomputable def zmodOfQZ (f : A →+ QZ) (hf : ∀ a, n • f a = 0) : A →+ ZMod n where
  toFun a := Classical.choose (exists_zmodToQZ_eq (hf a))
  map_zero' := zmodToQZ_injective (by
    rw [Classical.choose_spec (exists_zmodToQZ_eq (hf 0)), map_zero, map_zero])
  map_add' a b := zmodToQZ_injective (by
    rw [Classical.choose_spec (exists_zmodToQZ_eq (hf (a + b))), map_add, map_add,
      Classical.choose_spec (exists_zmodToQZ_eq (hf a)),
      Classical.choose_spec (exists_zmodToQZ_eq (hf b))])

/- English proof (translation)
The claim follows from `Classical.choose_spec (exists_zmodToQZ_eq (hf a))`.
-/
theorem zmodToQZ_zmodOfQZ (f : A →+ QZ) (hf : ∀ a, n • f a = 0) (a : A) :
    zmodToQZ n (zmodOfQZ f hf a) = f a :=
  Classical.choose_spec (exists_zmodToQZ_eq (hf a))

end Lift

/- English proof (translation)
Take `⟨ψ₀, hψ₀⟩` from `QZ.exists_comp_eq_of_ker_le h ((zmodToQZ n).comp χ) fun b hb => by`. Rewrite `hb`, the goal using `[AddMonoidHom.mem_ker]`. Rewrite using `[AddMonoidHom.comp_apply, (AddMonoidHom.mem_ker).1 (hχ hb), map_zero]`. Establish `hψ₀' : ∀ c, n • ψ₀ c = 0` using `fun c => by rw [← map_nsmul, hC, map_zero]`. Use `⟨zmodOfQZ ψ₀ hψ₀', AddMonoidHom.ext fun b => zmodToQZ_injective ?_⟩` and prove the remaining obligations.

Rewrite using `[AddMonoidHom.comp_apply, zmodToQZ_zmodOfQZ]`. Conclude with `DFunLike.congr_fun hψ₀ b`.
-/
theorem zmod_exists_comp_eq_of_ker_le {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    (hC : ∀ c : C, n • c = 0) (h : B →+ C) (χ : B →+ ZMod n) (hχ : h.ker ≤ χ.ker) :
    ∃ ψ : C →+ ZMod n, ψ.comp h = χ := by
  obtain ⟨ψ₀, hψ₀⟩ := QZ.exists_comp_eq_of_ker_le h ((zmodToQZ n).comp χ) fun b hb => by
    rw [AddMonoidHom.mem_ker] at hb ⊢
    rw [AddMonoidHom.comp_apply, (AddMonoidHom.mem_ker).1 (hχ hb), map_zero]
  have hψ₀' : ∀ c, n • ψ₀ c = 0 := fun c => by rw [← map_nsmul, hC, map_zero]
  refine ⟨zmodOfQZ ψ₀ hψ₀', AddMonoidHom.ext fun b => zmodToQZ_injective ?_⟩
  rw [AddMonoidHom.comp_apply, zmodToQZ_zmodOfQZ]
  exact DFunLike.congr_fun hψ₀ b

/- English proof (translation)
Take `⟨f, hf⟩` from `QZ.exists_apply_ne_zero ha`. Establish `hf' : ∀ x, n • f x = 0` using `fun x => by rw [← map_nsmul, hA, map_zero]`. Use `⟨zmodOfQZ f hf', fun h => hf ?_⟩` and prove the remaining obligations. Rewrite using `[← zmodToQZ_zmodOfQZ f hf' a, h, map_zero]`.
-/
theorem zmod_exists_apply_ne_zero {A : Type*} [AddCommGroup A] (hA : ∀ a : A, n • a = 0)
    {a : A} (ha : a ≠ 0) : ∃ χ : A →+ ZMod n, χ a ≠ 0 := by
  obtain ⟨f, hf⟩ := QZ.exists_apply_ne_zero ha
  have hf' : ∀ x, n • f x = 0 := fun x => by rw [← map_nsmul, hA, map_zero]
  refine ⟨zmodOfQZ f hf', fun h => hf ?_⟩
  rw [← zmodToQZ_zmodOfQZ f hf' a, h, map_zero]

/- English proof (translation)
Introduce `_ _ h` and use `AddMonoidHom.ext fun a => zmodToQZ_injective (DFunLike.congr_fun h a)`.
-/
theorem comp_zmodToQZ_injective {A : Type*} [AddCommGroup A] :
    Injective fun χ : A →+ ZMod n => (zmodToQZ n).comp χ := fun _ _ h =>
  AddMonoidHom.ext fun a => zmodToQZ_injective (DFunLike.congr_fun h a)

instance finite_addMonoidHom_zmod {A : Type*} [AddCommGroup A] [Finite A] :
    Finite (A →+ ZMod n) :=
  Finite.of_injective _ comp_zmodToQZ_injective

/- English proof (translation)
The claim follows from `(Nat.card_le_card_of_injective _ comp_zmodToQZ_injective).trans QZ.card_hom_le`.
-/
theorem card_addMonoidHom_zmod_le {A : Type*} [AddCommGroup A] [Finite A] :
    Nat.card (A →+ ZMod n) ≤ Nat.card A :=
  (Nat.card_le_card_of_injective _ comp_zmodToQZ_injective).trans QZ.card_hom_le

/- English proof (translation)
Set `ψ : Y →+ (X →+ ZMod n)` to `{ toFun := fun y => t.comp (β.flip y) map_zero' := by ext; simp map_add' := fun y y' => by ext; simp }`. Set `φ : X →+ (Y →+ ZMod n)` to `{ toFun := fun x => t.comp (β x) map_zero' := by ext; simp map_add' := fun x x' => by ext; simp }`. Set `e : Y ≃+ (X →+ ZMod n)` to `AddEquiv.ofBijective ψ h`. Set `e' : (Y →+ ZMod n) ≃ ((X →+ ZMod n) →+ ZMod n)` to `{ toFun := fun f => f.comp e.symm.toAddMonoidHom invFun := fun g => g.comp e.toAddMonoidHom left_inv := fun f => by ext; simp right_inv := fun g => by ext; simp }`. Establish `: Finite (Y →+ ZMod n)` using `Finite.of_equiv _ e'.symm`.

Establish `hinj : Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Take `⟨χ, hχ⟩` from `zmod_exists_apply_ne_zero hX hne`.

Take `⟨y, hy⟩` from `h.2 χ`. Apply `hχ` to reduce the goal to its premises. Rewrite using `[← hy]`. Conclude with `DFunLike.congr_fun hx y`. Use `hinj.bijective_of_nat_card_le ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem bijective_of_bijective_flip {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Z] [Finite X] (hX : ∀ x : X, n • x = 0) (β : X →+ Y →+ Z) (t : Z →+ ZMod n)
    (h : Bijective fun y : Y => t.comp (β.flip y)) : Bijective fun x : X => t.comp (β x) := by
  let ψ : Y →+ (X →+ ZMod n) :=
    { toFun := fun y => t.comp (β.flip y)
      map_zero' := by ext; simp
      map_add' := fun y y' => by ext; simp }
  let φ : X →+ (Y →+ ZMod n) :=
    { toFun := fun x => t.comp (β x)
      map_zero' := by ext; simp
      map_add' := fun x x' => by ext; simp }
  let e : Y ≃+ (X →+ ZMod n) := AddEquiv.ofBijective ψ h
  let e' : (Y →+ ZMod n) ≃ ((X →+ ZMod n) →+ ZMod n) :=
    { toFun := fun f => f.comp e.symm.toAddMonoidHom
      invFun := fun g => g.comp e.toAddMonoidHom
      left_inv := fun f => by ext; simp
      right_inv := fun g => by ext; simp }
  have : Finite (Y →+ ZMod n) := Finite.of_equiv _ e'.symm
  have hinj : Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero hX hne
    obtain ⟨y, hy⟩ := h.2 χ
    apply hχ
    rw [← hy]
    exact DFunLike.congr_fun hx y
  refine hinj.bijective_of_nat_card_le ?_
  calc Nat.card (Y →+ ZMod n) = Nat.card ((X →+ ZMod n) →+ ZMod n) := Nat.card_congr e'
    _ ≤ Nat.card (X →+ ZMod n) := card_addMonoidHom_zmod_le
    _ ≤ Nat.card X := card_addMonoidHom_zmod_le

end GroundTheory.ProfCoh
