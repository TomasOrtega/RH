import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHopfAlgebraEqRangeMulKernelStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

/- English proof (translation)
Introduce `k _ A _ _ _ _ C _ _ _ _ f`. Prove the components needed by the constructor for the conclusion. Introduce `hf`. Rewrite using `[kerIdeal_of_surjective hf]`. Establish `hs : Function.Surjective (counitAlgHom k A)` using `fun c => ⟨algebraMap k A c, by simp⟩`.

Set `e : (A ⧸ augIdeal k A) ≃ₐ[k] k` to `Ideal.quotientKerAlgEquivOfSurjective hs`. Rewrite using `[e.toLinearEquiv.finrank_eq, Module.finrank_self]`. Introduce `h`. Establish `hL` using `GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel k A C f`. Rewrite `hL` using `[h, mul_one]`.

Establish `htop : LinearMap.range (f : C →ₐ[k] A).toLinearMap = ⊤` using `Submodule.eq_top_of_finrank_eq hL.symm`. Introduce `a`. Establish `ha : a ∈ LinearMap.range (f : C →ₐ[k] A).toLinearMap` using `htop ▸ Submodule.mem_top`. Take `⟨c, hc⟩` from `ha`. Conclude with `⟨c, hc⟩`.
-/
theorem surjective_iff_finrank_quot_kerIdeal_eq_one :
    ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A]
      [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
      [Module.Finite k C] (f : C →ₐc[k] A),
      Function.Surjective f ↔ Module.finrank k (A ⧸ kerIdeal f) = 1 := by
  intro k _ A _ _ _ _ C _ _ _ _ f
  constructor
  · intro hf
    rw [kerIdeal_of_surjective hf]
    have hs : Function.Surjective (counitAlgHom k A) := fun c =>
      ⟨algebraMap k A c, by simp⟩
    let e : (A ⧸ augIdeal k A) ≃ₐ[k] k := Ideal.quotientKerAlgEquivOfSurjective hs
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_self]
  · intro h
    have hL := GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel k A C f
    rw [h, mul_one] at hL
    have htop : LinearMap.range (f : C →ₐ[k] A).toLinearMap = ⊤ :=
      Submodule.eq_top_of_finrank_eq hL.symm
    intro a
    have ha : a ∈ LinearMap.range (f : C →ₐ[k] A).toLinearMap := htop ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := ha
    exact ⟨c, hc⟩

end GlobalTheory.Dieu
