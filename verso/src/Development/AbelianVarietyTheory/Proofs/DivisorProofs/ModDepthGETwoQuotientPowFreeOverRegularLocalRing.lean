import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEThreeOfFreeRegularLocal
open IsLocalRing

namespace GlobalTheory

open Pointwise in

/- English proof (translation)
Introduce `R _ _ hd f hf hf0 B _ _ _ _ _ k hk`. Use `haveI : IsDomain R := GlobalTheory.isDomain_of_isRegularLocalRing R`. Establish `h3 : ReciprocityTheory.CA.ModDepthGE R B 3` using `GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing R hd B`. Establish `hfk0 : f ^ k ≠ 0` using `pow_ne_zero k hf0`. Establish `hfkm : f ^ k ∈ maximalIdeal R`.

Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le' hk`. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_left _ _ hf`. Establish `hreg : IsSMulRegular B (f ^ k)` using `smul_right_injective B hfk0`. Establish `h2 : ReciprocityTheory.CA.ModDepthGE R (QuotSMulTop (f ^ k) B) 2` using `ReciprocityTheory.CA.ModDepthGE.quotSMulTop hfkm hreg h3`.

Establish `hpow : (Ideal.span {f}).map (algebraMap R B) ^ k = (Ideal.span {f ^ k}).map (algebraMap R B)`. Rewrite using `[← Ideal.map_pow, Ideal.span_singleton_pow]`. Establish `heq : ((f ^ k) • (⊤ : Submodule R B)) = ((Ideal.span {f}).map (algebraMap R B) ^ k).restrictScalars R`. Rewrite using `[hpow]`. Use extensionality with `x`.

Simplify using `[Submodule.mem_smul_pointwise_iff_exists, Ideal.map_span, Ideal.mem_span_singleton', Algebra.smul_def, mul_comm]`. Set `e : QuotSMulTop (f ^ k) B ≃ₗ[R] (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k)` to `(Submodule.quotEquivOfEq _ _ heq).trans (Submodule.Quotient.restrictScalarsEquiv R ((Ideal.span {f}).map (algebraMap R B) ^ k))`. Conclude with `(ReciprocityTheory.CA.modDepthGE_congr e 2).mp h2`.
-/
theorem modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R,
      f ≠ 0 → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B]
      [Nontrivial B] (k : ℕ), 1 ≤ k →
      ReciprocityTheory.CA.ModDepthGE R (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) 2 := by
  intro R _ _ hd f hf hf0 B _ _ _ _ _ k hk
  haveI : IsDomain R := GlobalTheory.isDomain_of_isRegularLocalRing R
  have h3 : ReciprocityTheory.CA.ModDepthGE R B 3 :=
    GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing R hd B
  have hfk0 : f ^ k ≠ 0 := pow_ne_zero k hf0
  have hfkm : f ^ k ∈ maximalIdeal R := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [pow_succ]
    exact Ideal.mul_mem_left _ _ hf
  have hreg : IsSMulRegular B (f ^ k) := smul_right_injective B hfk0
  have h2 : ReciprocityTheory.CA.ModDepthGE R (QuotSMulTop (f ^ k) B) 2 :=
    ReciprocityTheory.CA.ModDepthGE.quotSMulTop hfkm hreg h3
  have hpow : (Ideal.span {f}).map (algebraMap R B) ^ k =
      (Ideal.span {f ^ k}).map (algebraMap R B) := by
    rw [← Ideal.map_pow, Ideal.span_singleton_pow]
  have heq : ((f ^ k) • (⊤ : Submodule R B)) =
      ((Ideal.span {f}).map (algebraMap R B) ^ k).restrictScalars R := by
    rw [hpow]
    ext x
    simp [Submodule.mem_smul_pointwise_iff_exists, Ideal.map_span, Ideal.mem_span_singleton',
      Algebra.smul_def, mul_comm]
  let e : QuotSMulTop (f ^ k) B ≃ₗ[R] (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) :=
    (Submodule.quotEquivOfEq _ _ heq).trans
      (Submodule.Quotient.restrictScalarsEquiv R ((Ideal.span {f}).map (algebraMap R B) ^ k))
  exact (ReciprocityTheory.CA.modDepthGE_congr e 2).mp h2

end GlobalTheory
