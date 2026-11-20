import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraNormEqHomogeneousPolynomialInCoordinatesStatement
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem norm_surjective_of_norm_form {K L : Type} [Field K] [Field L] [Algebra K L] (hC : IsFirstChernClassOfLineBundle K) (m : ℕ) (hm0 : 0 < m)
    (B : Module.Basis (Fin m) K L) (f : MvPolynomial (Fin m) K) (hf : f.IsHomogeneous m)
    (hnorm : ∀ x : L, Algebra.norm K x = MvPolynomial.eval (fun i => B.repr x i) f)
    (hpow : ∀ a : K, Algebra.norm K (algebraMap K L a) = a ^ m)
    (b : K) : ∃ x : L, Algebra.norm K x = b := by
  let g : MvPolynomial (Fin (m + 1)) K :=
    MvPolynomial.rename Fin.succ f - MvPolynomial.C b * MvPolynomial.X 0 ^ m
  have hg : g.IsHomogeneous m := by
    refine (hf.rename_isHomogeneous).sub ?_
    have := (MvPolynomial.isHomogeneous_C (Fin (m + 1)) b).mul (MvPolynomial.isHomogeneous_X_pow (0 : Fin (m + 1)) m)
    rwa [zero_add] at this
  obtain ⟨y, hy0, hy⟩ := hC (m + 1) m g hg hm0 (Nat.lt_succ_self m)
  let x : L := B.equivFun.symm (fun i => y i.succ)
  have hrepr : ∀ i, B.repr x i = y i.succ := by
    intro i
    have h := congrFun (B.equivFun.apply_symm_apply (fun i => y i.succ)) i
    rw [Module.Basis.equivFun_apply] at h
    exact h
  have hev : Algebra.norm K x = b * y 0 ^ m := by
    have h1 := hy
    simp only [g, map_sub, map_mul, map_pow, MvPolynomial.eval_rename, MvPolynomial.eval_C,
      MvPolynomial.eval_X] at h1
    rw [hnorm]
    have e : (fun i => B.repr x i) = y ∘ Fin.succ := funext hrepr
    rw [e]; exact sub_eq_zero.mp h1
  have hnz : ∀ z : L, Algebra.norm K z = 0 → z = 0 := by
    intro z hz
    by_contra hz'
    have hu : IsUnit z := (isUnit_iff_ne_zero).mpr hz'
    exact (hu.map (Algebra.norm K)).ne_zero hz
  have hy00 : y 0 ≠ 0 := by
    intro h0
    apply hy0
    have hx : x = 0 := hnz x (by rw [hev, h0, zero_pow hm0.ne', mul_zero])
    funext i
    refine Fin.cases h0 (fun j => ?_) i
    have := hrepr j
    rw [hx, map_zero] at this
    simpa using this.symm
  refine ⟨x * algebraMap K L (y 0)⁻¹, ?_⟩
  rw [map_mul, hpow, hev, mul_assoc, ← mul_pow, mul_inv_cancel₀ hy00, one_pow, mul_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem norm_surjective_of_is_c1 : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], IsFirstChernClassOfLineBundle K →
    ∀ b : K, b ≠ 0 → ∃ x : L, Algebra.norm K x = b := by
  intro K L _ _ _ _ hC b _
  obtain ⟨f, hf, hnorm⟩ := GlobalTheory.T.algebraNorm_eq_homogeneous_polynomial_in_coordinates K L
  exact norm_surjective_of_norm_form hC _ Module.finrank_pos (Module.finBasis K L) f hf hnorm
    (fun a => Algebra.norm_algebraMap a) b

end GlobalTheory
