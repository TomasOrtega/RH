import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem mem_span_X_of_pos {d n : ℕ} (hn : 0 < n) {f : MvPolynomial (Fin (d + 1)) ℂ}
    (hf : f.IsHomogeneous n) : f ∈ Ideal.span (Set.range (X : Fin (d + 1) → MvPolynomial _ ℂ)) := by
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro m hm
  by_contra! H
  obtain rfl : m = 0 := Finsupp.ext fun i => H i (Set.mem_univ i)
  have := hf (mem_support_iff.1 hm)
  simp only [map_zero] at this
  omega

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem iSup_chart_eq_top (d : ℕ) : ⨆ i, chart d i = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _
    ((HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun _ hn _ hf => mem_span_X_of_pos hn hf)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem inf_chart_eq (d : ℕ) (I : Finset (Fin (d + 1))) :
    I.inf (fun i => chart d i) = Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) (∏ i ∈ I, X i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.inf_insert, Finset.prod_insert ha, Proj.basicOpen_mul, ih]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem preimage_chart_cover : ∀ (d : ℕ) (Z : Scheme.{0}) (φ : Z ⟶ PSpace ℂ d) [IsAffineHom φ],
    (⨆ i, φ ⁻¹ᵁ chart d i) = ⊤ ∧
      ∀ I : Finset (Fin (d + 1)), I.Nonempty → IsAffineOpen (I.inf fun i => φ ⁻¹ᵁ chart d i) := by
  intro d Z φ _
  constructor
  · rw [← Scheme.Hom.preimage_iSup, iSup_chart_eq_top, Scheme.Hom.preimage_top]
  · intro I hI
    have key : (I.inf fun i => φ ⁻¹ᵁ chart d i) = φ ⁻¹ᵁ (I.inf fun i => chart d i) := by
      classical
      clear hI
      induction I using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.inf_insert, Finset.inf_insert, ih, Scheme.Hom.preimage_inf]
    rw [key, inf_chart_eq]
    have hdeg : (∏ i ∈ I, X i : MvPolynomial (Fin (d + 1)) ℂ) ∈ homogeneousSubmodule (Fin (d + 1)) ℂ I.card := by
      have := SetLike.prod_mem_graded (homogeneousSubmodule (Fin (d + 1)) ℂ) (fun _ => 1) (fun i => X i)
        (F := I) (fun i _ => X_mem_one d i)
      simpa using this
    exact (Proj.isAffineOpen_basicOpen _ _ hdeg (Finset.card_pos.2 hI)).preimage φ

end GlobalTheory.PD.XCover
