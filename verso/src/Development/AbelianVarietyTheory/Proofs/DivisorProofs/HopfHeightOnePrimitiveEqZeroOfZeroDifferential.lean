import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTopStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDiv.HeightOnePrim

/- English proof (translation)
Establish `hp` using `isPrimitiveElem_of_mem_ker (R := K) (A := CartierDual K H) (b := φ) hφ`. Establish `hmul : ∀ x y : H, φ (x * y) = φ x * counit (R` using `K) y + counit (R := K) x * φ y := by`. Introduce `x y`. Rewrite using `[← CartierDual.pair_comul_tmul, show comul φ = _ from hp, map_add, LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul, CartierDual.one_apply, CartierDual.one_apply]`. Rewrite `hb` using `[pow_two]`.

Use `Submodule.mul_induction_on hb (fun x hx y hy => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Establish `hx' : counit (R` using `K) x = 0 := hx`. Establish `hy' : counit (R` using `K) y = 0 := hy`. Rewrite using `[hmul, hx', hy', mul_zero, zero_mul, add_zero]`. Rewrite using `[map_add, hx, hy, add_zero]`.
-/
theorem apply_eq_zero_of_mem_sq {K H : Type} [Field K] [CommRing H] [HopfAlgebra K H]
    [IsCocomm K H] [Module.Finite K H] {φ : CartierDual K H} (hφ : cobOne K (CartierDual K H) φ = 0) {b : H}
    (hb : b ∈ augIdeal K H ^ 2) : φ b = 0 := by
  have hp := isPrimitiveElem_of_mem_ker (R := K) (A := CartierDual K H) (b := φ) hφ
  have hmul : ∀ x y : H, φ (x * y) = φ x * counit (R := K) y + counit (R := K) x * φ y := by
    intro x y
    rw [← CartierDual.pair_comul_tmul, show comul φ = _ from hp, map_add, LinearMap.add_apply,
      CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul, CartierDual.one_apply,
      CartierDual.one_apply]
  rw [pow_two] at hb
  refine Submodule.mul_induction_on hb (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · have hx' : counit (R := K) x = 0 := hx
    have hy' : counit (R := K) y = 0 := hy
    rw [hmul, hx', hy', mul_zero, zero_mul, add_zero]
  · rw [map_add, hx, hy, add_zero]

/- English proof (translation)
Introduce `p _ K H _ _ _ _ _ _ hpow b hb hd`. Establish `hcb : counit (R` using `K) b = 0 := (mulBy_of_cobOne_eq_zero hb 0).2`. Establish `hsq : b ∈ augIdeal K H ^ 2`. Use `(AugCot.d_eq_zero_iff (counitAlgHom K H) b).1 hd` as an intermediate fact. Simplify `this` using `[hcb]`.

Establish `hgen` using `GlobalTheory.T.cartierDual_height_one_adjoin_primitive_eq_top p K H hpow`. Establish `hall : ∀ φ : CartierDual K H, φ b = 0`. Introduce `φ`. Establish `hφ : φ ∈ Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0}`. Rewrite using `[hgen]`.

Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hφ using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact apply_eq_zero_of_mem_sq hx hsq`. Consider the case `algebraMap r`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`.

Express the relevant statement in the definitionally equal form `r • (1 : CartierDual K H) b = 0`. Rewrite using `[CartierDual.one_apply, hcb, smul_zero]`. Consider the case `add x y _ _ hx hy => rw [WithConv.ofConv_add, LinearMap.add_apply, hx, hy, add_zero]`. Consider the case `mul x y _ _ hx hy`. Use `evalAt_mul (R := K) (A := H) ⟨b, hb⟩ x y` as an intermediate fact.

Simplify using `only [CartierDual.evalAt_apply] at this`. Rewrite using `[this, hx, hy, smul_zero, smul_zero, add_zero]`. Conclude with `CartierDual.eq_of_forall_apply (R := K) fun φ => by rw [hall φ, map_zero]`.
-/
theorem eq_zero_of_cobOne_eq_zero_of_dUnit_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H]
    [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], (∀ a ∈ augIdeal K H, a ^ p = 0) →
    ∀ b : H, cobOne K H b = 0 → dUnit K b = 0 → b = 0 := by
  intro p _ K H _ _ _ _ _ _ hpow b hb hd
  have hcb : counit (R := K) b = 0 := (mulBy_of_cobOne_eq_zero hb 0).2
  have hsq : b ∈ augIdeal K H ^ 2 := by
    have := (AugCot.d_eq_zero_iff (counitAlgHom K H) b).1 hd
    simpa [hcb] using this
  have hgen := GlobalTheory.T.cartierDual_height_one_adjoin_primitive_eq_top p K H hpow
  have hall : ∀ φ : CartierDual K H, φ b = 0 := by
    intro φ
    have hφ : φ ∈ Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} := by
      rw [hgen]; trivial
    induction hφ using Algebra.adjoin_induction with
    | mem x hx => exact apply_eq_zero_of_mem_sq hx hsq
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      change r • (1 : CartierDual K H) b = 0
      rw [CartierDual.one_apply, hcb, smul_zero]
    | add x y _ _ hx hy => rw [WithConv.ofConv_add, LinearMap.add_apply, hx, hy, add_zero]
    | mul x y _ _ hx hy =>
      have := evalAt_mul (R := K) (A := H) ⟨b, hb⟩ x y
      simp only [CartierDual.evalAt_apply] at this
      rw [this, hx, hy, smul_zero, smul_zero, add_zero]
  exact CartierDual.eq_of_forall_apply (R := K) fun φ => by rw [hall φ, map_zero]

end GlobalTheory.PDiv.HeightOnePrim
