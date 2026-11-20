import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSubmoduleOfComplexPolyValuesMemStatement

noncomputable section

open Matrix GlobalTheory.TorFin Formalism.REAL

namespace GlobalTheory.CapFrame

variable {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A]

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Conclude with `Matrix.single_mul_single_of_ne a b c h 1 (c := (1 : ℂ))`.
-/
theorem single_mul_single_one (a b c d : Fin n) :
    (Matrix.single a b (1 : ℂ)) * Matrix.single c d 1 = if b = c then Matrix.single a d 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · exact Matrix.single_mul_single_of_ne a b c h 1 (c := (1 : ℂ))

/- English proof (translation)
Establish `h' : P' * P = 1` using `mul_eq_one_comm.mp h`. Introduce `a b c d`. Rewrite using `[← hρ]`. Establish `e : ∀ a b c d : Fin n, P * Matrix.single a b 1 * P' * (P * Matrix.single c d 1 * P') = P * (Matrix.single a b 1 * Matrix.single c d 1) * P'`. Introduce `a b c d`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e, e, single_mul_single_one, single_mul_single_one]`. Apply the tactic sequence `split_ifs <;> simp [eq_comm]`.
-/
theorem frame_glRel (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (hρ : IsLieRep ρ) (P P' : Matrix (Fin n) (Fin n) ℂ)
    (h : P * P' = 1) : GlRel (fun a b => ρ (P * Matrix.single a b 1 * P')) := by
  have h' : P' * P = 1 := mul_eq_one_comm.mp h
  intro a b c d
  rw [← hρ]
  have e : ∀ a b c d : Fin n, P * Matrix.single a b 1 * P' * (P * Matrix.single c d 1 * P') =
      P * (Matrix.single a b 1 * Matrix.single c d 1) * P' := by
    intro a b c d
    calc P * Matrix.single a b 1 * P' * (P * Matrix.single c d 1 * P')
        = P * Matrix.single a b 1 * (P' * P) * Matrix.single c d 1 * P' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, e, single_mul_single_one, single_mul_single_one]
  split_ifs <;> simp [eq_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']`.
-/
theorem conj_single (P0 Q0 : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    P0 * Matrix.single a b 1 * Q0 = ∑ c, ∑ d, (P0 c a * Q0 b d) • Matrix.single c d (1 : ℂ) := by
  ext i j
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

/- English proof (translation)
Unfold `qdet qminor`. Use `Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_` and prove the remaining obligations. Use `Subalgebra.list_prod_mem _ fun x hx => ?_` and prove the remaining obligations. Take `⟨k, rfl⟩` from `List.mem_ofFn.mp hx`. Unfold `Tm`.

Use `Subalgebra.add_mem _ ?_ (Algebra.subset_adjoin ⟨_, rfl⟩)` and prove the remaining obligations. Use `split_ifs`. Conclude with `Subalgebra.algebraMap_mem _ _`. Conclude with `Subalgebra.zero_mem _`.
-/
theorem qdet_frame_mem_adjoin (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (P P' : Matrix (Fin n) (Fin n) ℂ) (u : ℂ) :
    qdet (fun a b => ρ (P * Matrix.single a b 1 * P')) u ∈ Algebra.adjoin ℂ (Set.range ρ) := by
  unfold qdet qminor
  refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Tm
  refine Subalgebra.add_mem _ ?_ (Algebra.subset_adjoin ⟨_, rfl⟩)
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

/- English proof (translation)
Establish `h' : P' * P = 1` using `mul_eq_one_comm.mp h`. Use `mem_invAlg.mpr ⟨qdet_frame_mem_adjoin ρ P P' u, fun r g g' hg hr => ?_⟩` and prove the remaining obligations. Establish `hg' : g' * g = 1` using `mul_eq_one_comm.mp hg`. Rewrite using `[GlobalTheory.CapAdInv.qdet_semiconj _ (fun a b => ρ (g * (P * Matrix.single a b 1 * P') * g')) r (fun a b => hr _) u]`. Use `congr 1`.

Establish `hQP : (P' * g' * P) * (P' * g * P) = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← GlobalTheory.CapAdInv.qdet_ad _ (frame_glRel ρ hρ P P' h) (P' * g * P) (P' * g' * P) hQP u]`. Use `congr 1`. Use function extensionality and compare the values at `a b`.

Establish `e : g * (P * Matrix.single a b 1 * P') * g' = P * ((P' * g * P) * Matrix.single a b 1 * (P' * g' * P)) * P'`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h, Matrix.one_mul, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.

Rewrite using `[e, conj_single, Matrix.mul_sum, Matrix.sum_mul, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_sum, Matrix.sum_mul, map_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, map_smul]`.
-/
theorem qdet_frame_mem_invAlg (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (hρ : IsLieRep ρ) (P P' : Matrix (Fin n) (Fin n) ℂ)
    (h : P * P' = 1) (u : ℂ) : qdet (fun a b => ρ (P * Matrix.single a b 1 * P')) u ∈ invAlg ρ := by
  have h' : P' * P = 1 := mul_eq_one_comm.mp h
  refine mem_invAlg.mpr ⟨qdet_frame_mem_adjoin ρ P P' u, fun r g g' hg hr => ?_⟩
  have hg' : g' * g = 1 := mul_eq_one_comm.mp hg
  rw [GlobalTheory.CapAdInv.qdet_semiconj _ (fun a b => ρ (g * (P * Matrix.single a b 1 * P') * g')) r (fun a b => hr _) u]
  congr 1
  have hQP : (P' * g' * P) * (P' * g * P) = 1 := by
    calc (P' * g' * P) * (P' * g * P) = P' * g' * (P * P') * g * P := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.mul_one, Matrix.mul_assoc P' g' g, hg', Matrix.mul_one, h']
  rw [← GlobalTheory.CapAdInv.qdet_ad _ (frame_glRel ρ hρ P P' h) (P' * g * P) (P' * g' * P) hQP u]
  congr 1
  funext a b
  have e : g * (P * Matrix.single a b 1 * P') * g' = P * ((P' * g * P) * Matrix.single a b 1 * (P' * g' * P)) * P' := by
    calc g * (P * Matrix.single a b 1 * P') * g'
        = (P * P') * g * P * Matrix.single a b 1 * P' * g' * (P * P') := by
          rw [h, Matrix.one_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e, conj_single, Matrix.mul_sum, Matrix.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, map_smul]

end GlobalTheory.CapFrame

open GlobalTheory.CapFrame in

/- English proof (translation)
Introduce `n A _ _ ρ hρ P P' h`. Take `⟨c, hcn, hc⟩` from `GlobalTheory.qdet_polyMap_monic A n (fun a b => ρ (P * Matrix.single a b 1 * P'))`. Use `⟨c, hcn, fun k hk => ?_, hc⟩` and prove the remaining obligations. Establish `hS : ∀ u : ℂ, ∑ k ∈ Finset.range (n + 1), u ^ k • c k ∈ Subalgebra.toSubmodule (invAlg ρ)`. Introduce `u`.

Rewrite using `[← hc u]`. Conclude with `qdet_frame_mem_invAlg ρ hρ P P' h u`. Conclude with `GlobalTheory.T.coeff_mem_submodule_of_complex_poly_values_mem A (Subalgebra.toSubmodule (invAlg ρ)) (n + 1) c hS k (Nat.lt_succ_of_le hk)`.
-/
theorem GlobalTheory.qdet_frame_coeff_mem_invAlg : ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A]
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A), IsLieRep ρ → ∀ P P' : Matrix (Fin n) (Fin n) ℂ, P * P' = 1 →
    ∃ c : ℕ → A, c n = 1 ∧ (∀ k ≤ n, c k ∈ invAlg ρ) ∧
      ∀ u : ℂ, Formalism.REAL.qdet (fun a b => ρ (P * Matrix.single a b 1 * P')) u =
        ∑ k ∈ Finset.range (n + 1), u ^ k • c k := by
  intro n A _ _ ρ hρ P P' h
  obtain ⟨c, hcn, hc⟩ := GlobalTheory.qdet_polyMap_monic A n (fun a b => ρ (P * Matrix.single a b 1 * P'))
  refine ⟨c, hcn, fun k hk => ?_, hc⟩
  have hS : ∀ u : ℂ, ∑ k ∈ Finset.range (n + 1), u ^ k • c k ∈ Subalgebra.toSubmodule (invAlg ρ) := by
    intro u
    rw [← hc u]
    exact qdet_frame_mem_invAlg ρ hρ P P' h u
  exact GlobalTheory.T.coeff_mem_submodule_of_complex_poly_values_mem A (Subalgebra.toSubmodule (invAlg ρ)) (n + 1) c hS k (Nat.lt_succ_of_le hk)

end
