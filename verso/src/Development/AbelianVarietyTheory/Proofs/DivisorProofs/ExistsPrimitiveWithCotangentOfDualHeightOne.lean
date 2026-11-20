import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTopStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition.

Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_primitive_dUnit_eq : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H],
    (∀ φ ∈ augIdeal K (CartierDual K H), φ ^ p = 0) →
    ∀ w : Cot K H, ∃ b : H, cobOne K H b = 0 ∧ dUnit K b = w := by
  intro p _ K H _ _ _ _ _ _ hnil w
  have hgen := GlobalTheory.T.cartierDual_height_one_adjoin_primitive_eq_top p K (CartierDual K H) hnil
  set e := CartierDual.bidual K H
  have hH : Algebra.adjoin K {b : H | cobOne K H b = 0} = ⊤ := by
    let f : CartierDual K (CartierDual K H) →ₐ[K] H :=
      ((e.symm : CartierDual K (CartierDual K H) →ₐc[K] H) : CartierDual K (CartierDual K H) →ₐ[K] H)
    have himg : f '' {φ | cobOne K (CartierDual K (CartierDual K H)) φ = 0} ⊆
        {b : H | cobOne K H b = 0} := by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [Set.mem_setOf_eq] at hφ ⊢
      show cobOne K H ((e.symm : CartierDual K (CartierDual K H) →ₐc[K] H) φ) = 0
      rw [← pullTwo_cobOne, hφ, map_zero]
    rw [eq_top_iff]
    intro x _
    refine Algebra.adjoin_mono himg ?_
    rw [Algebra.adjoin_image]
    refine ⟨e x, ?_, ?_⟩
    · rw [hgen]; trivial
    · exact e.symm_apply_apply x
  let P : Submodule K H := LinearMap.ker (cobOne K H)
  let S : Submodule K (Cot K H) := P.map (AugCot.d (counitAlgHom K H))
  have hS : ∀ a ∈ Algebra.adjoin K {b : H | cobOne K H b = 0}, dUnit K a ∈ S := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Submodule.mem_map_of_mem (p := P) hx
    | algebraMap r => rw [dUnit, AugCot.d_algebraMap]; exact S.zero_mem
    | add x y _ _ hx hy => rw [dUnit, map_add]; exact S.add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [dUnit, AugCot.d_mul]
      exact S.add_mem (S.smul_mem _ hy) (S.smul_mem _ hx)
  obtain ⟨a, rfl⟩ := AugCot.d_surjective (counitAlgHom K H) w
  obtain ⟨b, hb, hbd⟩ := hS a (by rw [hH]; trivial)
  exact ⟨b, hb, hbd⟩

end GlobalTheory.PDiv
