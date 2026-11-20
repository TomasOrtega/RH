import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory

namespace PDiv

/- English proof (translation)
Use `haveI := isHopfIdeal_kerIdeal_of_bialgHom k A C (ψ.comp φ)`. Use `haveI := isHopfIdeal_kerIdeal_of_bialgHom k B C φ`. Set `πA : A →ₐc[k] A ⧸ kerIdeal (ψ.comp φ)` to `Bialgebra.Quotient.mkBialgHom (kerIdeal (ψ.comp φ))`. Set `πB : B →ₐc[k] B ⧸ kerIdeal φ` to `Bialgebra.Quotient.mkBialgHom (kerIdeal φ)`. Establish `hπA : Function.Surjective πA` using `Ideal.Quotient.mk_surjective`.

Establish `hπB : Function.Surjective πB` using `Ideal.Quotient.mk_surjective`. Establish `hA : ∀ c, πA (ψ (φ c)) = algebraMap k _ (counit c)` using `(kerIdeal_le_ker_iff (ψ.comp φ) (πA : A →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))).1 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha`. Establish `h1 : kerIdeal φ ≤ RingHom.ker (πA.comp ψ : B →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))` using `(kerIdeal_le_ker_iff φ _).2 fun c => hA c`. Set `m' : (B ⧸ kerIdeal φ) →ₐc[k] A ⧸ kerIdeal (ψ.comp φ)` to `liftSurj πB hπB (πA.comp ψ) fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)`. Establish `hm' : ∀ b, m' (πB b) = πA (ψ b)` using `fun b => liftSurj_apply πB hπB (πA.comp ψ) (fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)) b`.

Set `q : A →ₐ[k] (A ⧸ kerIdeal (ψ.comp φ)) ⧸ kerIdeal m'` to `(Ideal.Quotient.mkₐ k (kerIdeal m')).comp (πA : A →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))`. Establish `hq : Function.Surjective q` using `Ideal.Quotient.mk_surjective.comp hπA`. Establish `h0` using `(kerIdeal_le_ker_iff m' (Ideal.Quotient.mkₐ k (kerIdeal m'))).1 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha`. Establish `h4 : kerIdeal ψ ≤ RingHom.ker q` using `(kerIdeal_le_ker_iff ψ q).2 fun b => by`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mkₐ k (kerIdeal m') (πA (ψ b)) = _`.

Rewrite using `[← hm', h0, CoalgHomClass.counit_comp_apply]`. Set `q'' : (A ⧸ kerIdeal ψ) →ₐ[k] (A ⧸ kerIdeal (ψ.comp φ)) ⧸ kerIdeal m'` to `Ideal.Quotient.liftₐ (kerIdeal ψ) q h4`. Establish `hq'' : Function.Surjective q''.toLinearMap` using `fun x => by`. Take `⟨a, rfl⟩` from `hq x`. Conclude with `⟨Ideal.Quotient.mk _ a, rfl⟩`.

Rewrite using `[finrank_eq_ker_mul_range k _ _ m']`. Conclude with `Nat.mul_le_mul (LinearMap.finrank_le_finrank_of_surjective hq'') (LinearMap.finrank_range_le _)`.
-/
theorem finrank_quot_kerIdeal_comp_le {k A B C : Type} [Field k] [CommRing A] [CommRing B]
    [CommRing C] [HopfAlgebra k A] [HopfAlgebra k B] [HopfAlgebra k C] [Module.Finite k A]
    [Module.Finite k B] (ψ : B →ₐc[k] A) (φ : C →ₐc[k] B) :
    Module.finrank k (A ⧸ kerIdeal (ψ.comp φ)) ≤
      Module.finrank k (A ⧸ kerIdeal ψ) * Module.finrank k (B ⧸ kerIdeal φ) := by
  haveI := isHopfIdeal_kerIdeal_of_bialgHom k A C (ψ.comp φ)
  haveI := isHopfIdeal_kerIdeal_of_bialgHom k B C φ
  let πA : A →ₐc[k] A ⧸ kerIdeal (ψ.comp φ) := Bialgebra.Quotient.mkBialgHom (kerIdeal (ψ.comp φ))
  let πB : B →ₐc[k] B ⧸ kerIdeal φ := Bialgebra.Quotient.mkBialgHom (kerIdeal φ)
  have hπA : Function.Surjective πA := Ideal.Quotient.mk_surjective
  have hπB : Function.Surjective πB := Ideal.Quotient.mk_surjective
  have hA : ∀ c, πA (ψ (φ c)) = algebraMap k _ (counit c) :=
    (kerIdeal_le_ker_iff (ψ.comp φ) (πA : A →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))).1
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h1 : kerIdeal φ ≤ RingHom.ker (πA.comp ψ : B →ₐ[k] A ⧸ kerIdeal (ψ.comp φ)) :=
    (kerIdeal_le_ker_iff φ _).2 fun c => hA c
  let m' : (B ⧸ kerIdeal φ) →ₐc[k] A ⧸ kerIdeal (ψ.comp φ) :=
    liftSurj πB hπB (πA.comp ψ) fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)
  have hm' : ∀ b, m' (πB b) = πA (ψ b) := fun b =>
    liftSurj_apply πB hπB (πA.comp ψ) (fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)) b
  let q : A →ₐ[k] (A ⧸ kerIdeal (ψ.comp φ)) ⧸ kerIdeal m' :=
    (Ideal.Quotient.mkₐ k (kerIdeal m')).comp (πA : A →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective.comp hπA
  have h0 := (kerIdeal_le_ker_iff m' (Ideal.Quotient.mkₐ k (kerIdeal m'))).1
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h4 : kerIdeal ψ ≤ RingHom.ker q := (kerIdeal_le_ker_iff ψ q).2 fun b => by
    change Ideal.Quotient.mkₐ k (kerIdeal m') (πA (ψ b)) = _
    rw [← hm', h0, CoalgHomClass.counit_comp_apply]
  let q'' : (A ⧸ kerIdeal ψ) →ₐ[k] (A ⧸ kerIdeal (ψ.comp φ)) ⧸ kerIdeal m' :=
    Ideal.Quotient.liftₐ (kerIdeal ψ) q h4
  have hq'' : Function.Surjective q''.toLinearMap := fun x => by
    obtain ⟨a, rfl⟩ := hq x
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  rw [finrank_eq_ker_mul_range k _ _ m']
  exact Nat.mul_le_mul (LinearMap.finrank_le_finrank_of_surjective hq'')
    (LinearMap.finrank_range_le _)

end PDiv

namespace Dieu

/- English proof (translation)
Introduce `p _ k _ _ G H K f g a b c ⟨N₁, h₁⟩ ⟨N₂, h₂⟩ ⟨N₃, h₃⟩`. Set `n` to `max N₁ (max N₂ N₃)`. Establish `e₁` using `h₁ n (le_max_left _ _)`. Establish `e₂` using `h₂ n (le_trans (le_max_left _ _) (le_max_right _ _))`. Establish `e₃` using `h₃ n (le_trans (le_max_right _ _) (le_max_right _ _))`.

Establish `hle` using `finrank_quot_kerIdeal_comp_le (f.app n) (g.app n)`. Rewrite `hle` using `[← comp_app, e₃, e₁, e₂, ← pow_add]`. Conclude with `(Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle`.
-/
theorem hasLogDeg_comp_le : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K) (a b c : ℕ),
    HasLogDeg f a → HasLogDeg g b → HasLogDeg (f ≫ g) c → c ≤ a + b := by
  intro p _ k _ _ G H K f g a b c ⟨N₁, h₁⟩ ⟨N₂, h₂⟩ ⟨N₃, h₃⟩
  let n := max N₁ (max N₂ N₃)
  have e₁ := h₁ n (le_max_left _ _)
  have e₂ := h₂ n (le_trans (le_max_left _ _) (le_max_right _ _))
  have e₃ := h₃ n (le_trans (le_max_right _ _) (le_max_right _ _))
  have hle := finrank_quot_kerIdeal_comp_le (f.app n) (g.app n)
  rw [← comp_app, e₃, e₁, e₂, ← pow_add] at hle
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle

end Dieu

end GlobalTheory
