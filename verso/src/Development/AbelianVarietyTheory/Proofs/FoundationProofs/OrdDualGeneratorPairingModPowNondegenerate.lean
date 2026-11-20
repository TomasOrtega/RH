import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DvdOfMemIk
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SelPerp

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `h1` using `h (red c n x)`. Rewrite `h1` using `[← map_mul, tbA_red, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]`. Rewrite using `[mul_comm]`. Conclude with `h1`.
-/
theorem tau_mul_dvd (c : Coef l) (n : ℕ) (b' : c.O)
    (h : ∀ a : Qn c n, tbA c n (a * red c n b') = 0) (x : c.O) :
    ∃ q : ℤ_[l], tau c (b' * x) = (l : ℤ_[l]) ^ n * q := by
  have h1 := h (red c n x)
  rw [← map_mul, tbA_red, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
  rw [mul_comm]
  exact h1

/- English proof (translation)
Take `⟨b', rfl⟩` from `red_surjective c n b`. Establish `hd` using `tau_mul_dvd c n b' h`. Establish `hl : ((l : ℤ_[l]) ^ n) ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`. Set `q : c.O → ℤ_[l]` to `fun x => Classical.choose (hd x)`. Establish `hq : ∀ x, tau c (b' * x) = (l : ℤ_[l]) ^ n * q x` using `fun x => Classical.choose_spec (hd x)`.

Set `g : c.O →ₗ[ℤ_[l]] ℤ_[l]` to `{ toFun := q map_add' := fun x y => by`. Apply `mul_left_cancel₀ hl` to reduce the goal to its premises. Rewrite using `[← hq, mul_add, map_add, hq, hq, mul_add]`. Use the proof step `map_smul' := fun r x => by`. Apply `mul_left_cancel₀ hl` to reduce the goal to its premises.

Rewrite using `[← hq, mul_smul_comm, map_smul, hq, RingHom.id_apply, smul_eq_mul, smul_eq_mul]`. Use `ring }`. Take `⟨a0, ha0⟩` from `(tau_spec c g).exists`. Set `f : c.O →ₗ[ℤ_[l]] ℤ_[l]` to `(tau c).comp (LinearMap.mulLeft ℤ_[l] b')`. Establish `e1 : ∀ x, f x = tau c (b' * x)` using `fun x => rfl`.

Establish `e2 : ∀ x, f x = tau c ((((l : ℤ_[l]) ^ n) • a0) * x)` using `fun x => by`. Rewrite using `[e1, hq, smul_mul_assoc, map_smul, smul_eq_mul]`. Use `congr 1`. Conclude with `ha0 x`. Establish `heq : b' = ((l : ℤ_[l]) ^ n) • a0` using `(tau_spec c f).unique e1 e2`.

Rewrite using `[heq, red_eq_zero_iff_mem]`. Conclude with `smul_mem_Ik c n (Ideal.mem_span_singleton_self _) a0`.
-/
theorem pair_nondeg (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (b : Qn c n)
    (h : ∀ a : Qn c n, GlobalTheory.Ord2.SelPerp.tbA c n (a * b) = 0) : b = 0 := by
  obtain ⟨b', rfl⟩ := red_surjective c n b
  have hd := tau_mul_dvd c n b' h
  have hl : ((l : ℤ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  let q : c.O → ℤ_[l] := fun x => Classical.choose (hd x)
  have hq : ∀ x, tau c (b' * x) = (l : ℤ_[l]) ^ n * q x := fun x => Classical.choose_spec (hd x)
  let g : c.O →ₗ[ℤ_[l]] ℤ_[l] :=
    { toFun := q
      map_add' := fun x y => by
        apply mul_left_cancel₀ hl
        rw [← hq, mul_add, map_add, hq, hq, mul_add]
      map_smul' := fun r x => by
        apply mul_left_cancel₀ hl
        rw [← hq, mul_smul_comm, map_smul, hq, RingHom.id_apply, smul_eq_mul, smul_eq_mul]
        ring }
  obtain ⟨a0, ha0⟩ := (tau_spec c g).exists
  let f : c.O →ₗ[ℤ_[l]] ℤ_[l] := (tau c).comp (LinearMap.mulLeft ℤ_[l] b')
  have e1 : ∀ x, f x = tau c (b' * x) := fun x => rfl
  have e2 : ∀ x, f x = tau c ((((l : ℤ_[l]) ^ n) • a0) * x) := fun x => by
    rw [e1, hq, smul_mul_assoc, map_smul, smul_eq_mul]
    congr 1
    exact ha0 x
  have heq : b' = ((l : ℤ_[l]) ^ n) • a0 := (tau_spec c f).unique e1 e2
  rw [heq, red_eq_zero_iff_mem]
  exact smul_mem_Ik c n (Ideal.mem_span_singleton_self _) a0

end GlobalTheory.Ord2.SelPerp

/- English proof (translation)
The claim follows from `GlobalTheory.Ord2.SelPerp.pair_nondeg`.
-/
example : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (b : Qn c n), (∀ a : Qn c n, GlobalTheory.Ord2.SelPerp.tbA c n (a * b) = 0) → b = 0 :=
  GlobalTheory.Ord2.SelPerp.pair_nondeg
