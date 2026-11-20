import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard

namespace GlobalTheory.ZModDual

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem card_quot_ker_le (n : ℕ) [NeZero n] (A B : Type) [AddCommGroup A] [Module (ZMod n) A]
    [AddCommGroup B] [Module (ZMod n) B] [Finite B]
    (b : A →ₗ[ZMod n] B →ₗ[ZMod n] ZMod n) :
    Nat.card (A ⧸ LinearMap.ker b) ≤ Nat.card (B ⧸ LinearMap.ker b.flip) := by
  set K' := LinearMap.ker b.flip
  have : Finite (B ⧸ K') := Finite.of_surjective K'.mkQ K'.mkQ_surjective
  have : Finite (Module.Dual (ZMod n) B) :=
    Finite.of_injective (fun f : Module.Dual (ZMod n) B => (f : B → ZMod n)) DFunLike.coe_injective
  have hle : LinearMap.range b ≤ K'.dualAnnihilator := by
    rintro _ ⟨a, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    have := LinearMap.congr_fun (LinearMap.mem_ker.1 hy) a
    simpa using this
  calc Nat.card (A ⧸ LinearMap.ker b) = Nat.card (LinearMap.range b) :=
        Nat.card_congr (LinearMap.quotKerEquivRange b).toEquiv
    _ ≤ Nat.card K'.dualAnnihilator :=
        Nat.card_le_card_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ = Nat.card (Module.Dual (ZMod n) (B ⧸ K')) :=
        Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator K').toEquiv.symm
    _ = Nat.card (B ⧸ K') := card_dual_eq n (B ⧸ K')

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_ker_mul_card_eq (n : ℕ) [NeZero n] (A B : Type) [AddCommGroup A]
    [Module (ZMod n) A] [Finite A] [AddCommGroup B] [Module (ZMod n) B] [Finite B]
    (b : A →ₗ[ZMod n] B →ₗ[ZMod n] ZMod n) :
    Nat.card (LinearMap.ker b) * Nat.card B = Nat.card (LinearMap.ker b.flip) * Nat.card A := by
  have h1 := card_quot_ker_le n A B b
  have h2 := card_quot_ker_le n B A b.flip
  rw [LinearMap.flip_flip] at h2
  have heq : Nat.card (A ⧸ LinearMap.ker b) = Nat.card (B ⧸ LinearMap.ker b.flip) := le_antisymm h1 h2
  have eA := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker b)
  have eB := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker b.flip)
  rw [eA, eB, heq]
  ring

end GlobalTheory.ZModDual
