import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.SemistableModel

def evalQ (O : Type) [CommRing O] (ϖ : O) :
    (MvPolynomial (Fin 1) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin 1 => (i : ℕ) < 1), MvPolynomial.X i) -
      MvPolynomial.C ϖ}) →+* O :=
  Ideal.Quotient.lift _ (MvPolynomial.aeval (fun _ : Fin 1 => ϖ) : MvPolynomial (Fin 1) O →ₐ[O] O).toRingHom (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    simp)

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.
-/
theorem evalQ_algebraMap (O : Type) [CommRing O] (ϖ : O) (o : O) :
    evalQ O ϖ (algebraMap O _ o) = o := by
  change evalQ O ϖ (Ideal.Quotient.mk _ (MvPolynomial.C o)) = o
  simp [evalQ]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem evalQ_bijective (O : Type) [CommRing O] (ϖ : O) : Function.Bijective (evalQ O ϖ) := by
  let I : Ideal (MvPolynomial (Fin 1) O) := Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin 1 => (i : ℕ) < 1), MvPolynomial.X i) -
      MvPolynomial.C ϖ}
  have key : (Ideal.Quotient.mkₐ O I) = (Algebra.ofId O _).comp (MvPolynomial.aeval fun _ : Fin 1 => ϖ) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    simp only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, MvPolynomial.aeval_X, Algebra.ofId_apply]
    change _ = Ideal.Quotient.mk I (MvPolynomial.C ϖ)
    rw [Ideal.Quotient.eq]
    apply Ideal.subset_span
    simp [I]
  refine ⟨fun a b hab => ?_, fun o => ⟨algebraMap O _ o, evalQ_algebraMap O ϖ o⟩⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have ha := AlgHom.congr_fun key a
  have hb := AlgHom.congr_fun key b
  simp only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, Algebra.ofId_apply] at ha hb
  change Ideal.Quotient.mk I a = Ideal.Quotient.mk I b
  rw [ha, hb]
  change (MvPolynomial.aeval fun _ : Fin 1 => ϖ) a = (MvPolynomial.aeval fun _ : Fin 1 => ϖ) b at hab
  rw [hab]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem isStrictlySemistable_base (O : Type) [CommRing O] (ϖ : O) :
    GlobalTheory.Et.IsStrictlySemistable ϖ (𝟙 (Spec (CommRingCat.of O))) := by
  intro x
  let T := ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of O))) ⊤ ⊤ le_top)
  have hT : Function.Bijective T.hom := by
    have : IsIso T := by
      have h1 : Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of O))) ⊤ ⊤ le_top = 𝟙 _ := by
        simp [Scheme.Hom.appLE]
      simp only [T, h1, Category.comp_id]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso T
  refine ⟨⊤, isAffineOpen_top _, trivial, 1, 1, le_rfl, le_rfl, T.hom.comp (evalQ O ϖ), ?_, ?_⟩
  · exact RingHom.Etale.of_bijective (hT.comp (evalQ_bijective O ϖ))
  · ext o
    simp [evalQ_algebraMap, T]

end GlobalTheory.SemistableModel
