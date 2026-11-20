import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.
-/
private theorem form_map' {A A' ι : Type} [CommRing A] [CommRing A'] [Fintype ι] (ρ : A →+* A') (c : ι → A) :
    (form c).map (MvPolynomial.map ρ) = form (fun k => ρ (c k)) := by
  unfold form
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  congr 2
  simp [map_sum, MvPolynomial.map_C, MvPolynomial.map_X]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem form_eval' {A ι : Type} [CommRing A] [Fintype ι] (x y : ι → A) :
    Polynomial.evalRingHom (∑ k, MvPolynomial.C (x k) * MvPolynomial.X k) (form y) =
      ∑ k, MvPolynomial.C (x k - y k) * MvPolynomial.X k := by
  unfold form
  show Polynomial.eval _ _ = _
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [map_sub, sub_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
-/
private theorem form_natDegree' {A ι : Type} [CommRing A] [Fintype ι] [Nontrivial A] (v : Multiset (ι → A)) :
    ((v.map form).prod).natDegree = v.card := by
  rw [Polynomial.natDegree_multiset_prod_of_monic]
  · simp only [Multiset.map_map, Function.comp_def, form, Polynomial.natDegree_X_sub_C]
    simp
  · intro f hf
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hf
    exact Polynomial.monic_X_sub_C _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.crystallineComparison.snBasic_of :
    SameNormBasic := by
  intro A ι _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A' _ ρ u u' h
    unfold SameNorm at h ⊢
    have e := congrArg (Polynomial.map (MvPolynomial.map ρ)) h
    simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, form_map'] at e
    simpa [Multiset.map_map, Function.comp_def] using e
  · intro x u u' h
    simp only [SameNorm, Multiset.map_cons, Multiset.prod_cons] at h ⊢
    exact (show (form x).Monic from Polynomial.monic_X_sub_C _).isRegular.left h
  · intro _ u u' h
    unfold SameNorm at h
    have e := congrArg Polynomial.natDegree h
    rwa [form_natDegree', form_natDegree'] at e
  · intro x u u' h hx
    unfold SameNorm at h
    have e := congrArg (Polynomial.evalRingHom (∑ k, MvPolynomial.C (x k) * MvPolynomial.X k)) h
    rw [map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map] at e
    simp only [Function.comp_def, form_eval'] at e
    rw [← e]
    apply Multiset.prod_eq_zero
    exact Multiset.mem_map.2 ⟨x, hx, by simp⟩
