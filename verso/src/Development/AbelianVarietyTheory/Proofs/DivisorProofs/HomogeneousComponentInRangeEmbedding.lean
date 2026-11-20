import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.GradR

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem mR_isHomogeneous (P Q R : ℕ) (a : Fin P) (b : Fin Q) : (mR P Q R a b).IsHomogeneous 2 := by
  unfold mR
  exact IsHomogeneous.sum _ _ _ fun c _ => (isHomogeneous_X ℂ _).mul (isHomogeneous_X ℂ _)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Simplify to obtain the desired conclusion from the available facts.
-/
theorem detR_isHomogeneous (P Q R : ℕ) (h : P ≤ R) : (detR P Q R h).IsHomogeneous P := by
  unfold detR
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h1 : (∏ i : Fin P, (Matrix.of fun a c : Fin P =>
      (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)) (σ i) i).IsHomogeneous (∑ _i : Fin P, 1) :=
    IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X ℂ _
  have h0 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Pol P Q R 0).IsHomogeneous 0 := by
    have := isHomogeneous_C (Ix P Q × Ix R 0) (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)
    rwa [map_intCast] at this
  simpa using h0.mul h1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem embR_isHomogeneous (P Q R : ℕ) (h : P ≤ R) (k : ℕ) {G : Mdl P Q} {m : ℕ} (hG : G.IsHomogeneous m) :
    (embR P Q R h k G).IsHomogeneous (2 * m + P * k) :=
  (hG.aeval _ fun ab => mR_isHomogeneous P Q R ab.1 ab.2).mul ((detR_isHomogeneous P Q R h).pow k)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem homogeneousComponent_embR_mem (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (G : Mdl P Q) (n : ℕ) :
    homogeneousComponent n (embR P Q R h k G) ∈ LinearMap.range (embR P Q R h k) := by
  rw [← sum_homogeneousComponent G, map_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [homogeneousComponent_of_mem (embR_isHomogeneous P Q R h k (homogeneousComponent_isHomogeneous m G))]
  split_ifs
  · exact LinearMap.mem_range_self _ _
  · exact Submodule.zero_mem _

end GlobalTheory.CharPair.GradR
