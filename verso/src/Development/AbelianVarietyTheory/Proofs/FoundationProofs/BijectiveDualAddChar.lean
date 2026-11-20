import Mathlib

namespace GlobalTheory.StandardAdditiveCharacter

/- English proof (translation)
Take `⟨i, -, hi⟩` from `(Complex.isPrimitiveRoot_exp n (NeZero.ne n)).eq_pow_of_pow_eq_one hz`. Use `⟨((i : ℤ) : ZMod n), ?_⟩` and prove the remaining obligations. Rewrite using `[ZMod.stdAddChar_coe, ← hi, ← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_stdAddChar_eq (n : ℕ) [NeZero n] (z : ℂ) (hz : z ^ n = 1) :
    ∃ j : ZMod n, ZMod.stdAddChar j = z := by
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).eq_pow_of_pow_eq_one hz
  refine ⟨((i : ℤ) : ZMod n), ?_⟩
  rw [ZMod.stdAddChar_coe, ← hi, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `φ ψ h`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `a`. Establish `h'` using `congr_arg (fun χ : AddChar A ℂ => χ a) h`.

Simplify using `only [AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe] at h'`. Conclude with `ZMod.injective_stdAddChar h'`. Introduce `ψ`. Establish `hroot : ∀ a : A, (ψ a) ^ n = 1`. Introduce `a`.

Rewrite using `[← AddChar.map_nsmul_eq_pow]`. Establish `h0 : n • a = 0`. Rewrite using `[← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]`. Rewrite using `[h0, AddChar.map_zero_eq_one]`. Use `choose j hj using fun a => exists_stdAddChar_eq n (ψ a) (hroot a)`.

Set `F : A →+ ZMod n` to `{ toFun := j map_zero' := ZMod.injective_stdAddChar (by simp [hj]) map_add' := fun a b => ZMod.injective_stdAddChar (by simp only [AddChar.map_add_eq_mul, hj]) }`. Use `⟨F.toZModLinearMap n, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Simplify using `[F, hj]`.
-/
theorem bijective_dual_addChar (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A]
    [Module (ZMod n) A] :
    Function.Bijective fun (φ : Module.Dual (ZMod n) A) ↦
      AddChar.compAddMonoidHom ZMod.stdAddChar (LinearMap.toAddMonoidHom φ) := by
  constructor
  · intro φ ψ h
    apply LinearMap.ext
    intro a
    have h' := congr_arg (fun χ : AddChar A ℂ => χ a) h
    simp only [AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe] at h'
    exact ZMod.injective_stdAddChar h'
  · intro ψ
    have hroot : ∀ a : A, (ψ a) ^ n = 1 := by
      intro a
      rw [← AddChar.map_nsmul_eq_pow]
      have h0 : n • a = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
      rw [h0, AddChar.map_zero_eq_one]
    choose j hj using fun a => exists_stdAddChar_eq n (ψ a) (hroot a)
    let F : A →+ ZMod n :=
      { toFun := j
        map_zero' := ZMod.injective_stdAddChar (by simp [hj])
        map_add' := fun a b => ZMod.injective_stdAddChar (by simp only [AddChar.map_add_eq_mul, hj]) }
    refine ⟨F.toZModLinearMap n, ?_⟩
    ext a
    simp [F, hj]

end GlobalTheory.StandardAdditiveCharacter
