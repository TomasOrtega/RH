import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent

open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES

namespace PI.GreenLabelSurjWork

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
  (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem levi_mul (c : Fin s) (p q : parab K b) :
    levi K b c (p * q) = levi K b c p * levi K b c q := by
  apply Units.ext
  show blk K b c ((p.1 * q.1 : GL ι K) : Matrix ι ι K) = blk K b c p.1 * blk K b c q.1
  rw [Units.val_mul]
  exact blk_mul b c p.2.1 q.2.1

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem levi_one (c : Fin s) : levi K b c 1 = 1 := by
  apply Units.ext
  show blk K b c ((1 : GL ι K) : Matrix ι ι K) = 1
  rw [Units.val_one]
  exact Matrix.submatrix_one _ Subtype.val_injective

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem infl_mul (p q : parab K b) :
    infl K b lam (p * q) = infl K b lam p ∘ₗ infl K b lam q := by
  unfold infl
  rw [← PiTensorProduct.map_comp]
  congr 1
  funext c
  rw [levi_mul, map_mul]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem infl_one : infl K b lam 1 = LinearMap.id := by
  unfold infl
  simp only [levi_one, map_one]
  exact PiTensorProduct.map_id

/- English proof (translation)
Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_ne_zero_tensor (hl : ∀ c, Nontrivial (lam c)) :
    ∃ v : PiTensorProduct ℂ (fun c => (lam c : Type)), v ≠ 0 := by
  classical
  choose w hw using fun c => exists_ne (0 : lam c)
  have hφ : ∀ c, ∃ φ : Module.Dual ℂ (lam c), φ (w c) ≠ 0 := fun c => by
    by_contra hc
    push_neg at hc
    exact hw c ((Module.forall_dual_apply_eq_zero_iff ℂ (w c)).mp hc)
  choose φ hφ using hφ
  refine ⟨PiTensorProduct.tprod ℂ w, fun h0 => ?_⟩
  have h1 := PiTensorProduct.dualDistrib_apply φ w
  rw [show (⨂ₜ[ℂ] i, w i) = PiTensorProduct.tprod ℂ w from rfl, h0, map_zero] at h1
  exact (Finset.prod_ne_zero_iff.mpr (fun c _ => hφ c)) h1.symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem hcSpace_nontrivial (hl : ∀ c, Nontrivial (lam c)) : Nontrivial (hcSpace K b lam) := by
  classical
  obtain ⟨v, hv⟩ := exists_ne_zero_tensor b lam hl
  let f : GL ι K → PiTensorProduct ℂ (fun c => (lam c : Type)) := fun x =>
    if hx : x ∈ parab K b then infl K b lam ⟨x, hx⟩ v else 0
  have hf : f ∈ hcSpace K b lam := by
    show ∀ (p : parab K b) (x : GL ι K), f (p.1 * x) = infl K b lam p (f x)
    intro p x
    by_cases hx : x ∈ parab K b
    · have hpx : p.1 * x ∈ parab K b := mul_mem p.2 hx
      simp only [f, dif_pos hx, dif_pos hpx]
      rw [show (⟨p.1 * x, hpx⟩ : parab K b) = p * ⟨x, hx⟩ from rfl, infl_mul]
      rfl
    · have hpx : p.1 * x ∉ parab K b := fun h => hx (by
        have := mul_mem (inv_mem p.2) h
        rwa [inv_mul_cancel_left] at this)
      simp only [f, dif_neg hx, dif_neg hpx, map_zero]
  refine ⟨⟨⟨f, hf⟩, 0, fun h => hv ?_⟩⟩
  have h1 := congrFun (congrArg Subtype.val h) 1
  simp only [f, dif_pos (one_mem (parab K b))] at h1
  rw [show (⟨1, one_mem (parab K b)⟩ : parab K b) = 1 from rfl, infl_one] at h1
  exact h1

end PI.GreenLabelSurjWork
