import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularPosDefAdjointActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmFieldTraceFormGramMatrixPosDefStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem unimodLattice_bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) :
    H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Use the polynomial consequences of the given equalities and inequalities. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem unimodLattice_bar_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.bar H.rt = -H.rt := by
  apply RingOfIntegers.ext
  rw [H.bar_eq]
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  have hsq : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
    simpa using this
  have hd : (7 : ℝ) ≤ H.d := by
    have := H.d_mod
    have : 7 ≤ H.d := by omega
    exact_mod_cast this
  set z := φ (H.rt : E) with hz
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp [pow_two] at hre him
  have hx : z.re = 0 := by
    have hm : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.1 hm with h | h
    · exact h
    · rw [h] at hre; nlinarith [sq_nonneg z.re]
  have key : starRingEnd ℂ z = -z := by apply Complex.ext <;> simp [hx]
  rw [hz] at key
  simpa using key

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem unimodLattice_w0_add {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have h1 := H.two_weight_eq_one_add_root
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar h1
    rw [map_mul, map_add, map_one, unimodLattice_bar_rt, map_ofNat] at this
    rw [this]; ring
  have h3 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, h1, h2]; ring
  exact mul_left_cancel₀ two_ne_zero h3

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem unimodLattice :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), 1 ≤ r ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit (W + W.transpose).det ∧ (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) ∧ W = (W + W.transpose) * ρ H.w0 := by
  intro E _ _ _ H
  obtain ⟨m, B0, ρ0, hm, hsym, hpd, hadj⟩ := GlobalTheory.T.exists_cmField_traceForm_gram_matrix_posDef E H
  obtain ⟨r, b, ρ, hr, hbs, hbpd, hbu, hbadj⟩ :=
    GlobalTheory.T.exists_unimodular_posDef_form_adjoint_rep_of_posDef (𝓞 E) (H.bar : 𝓞 E →+* 𝓞 E) (unimodLattice_bar_bar H) m B0 ρ0 hm hsym hpd hadj
  have hW : b * ρ H.w0 + (b * ρ H.w0).transpose = b := by
    rw [Matrix.transpose_mul, hbs, hbadj, ← Matrix.mul_add, ← map_add]
    erw [unimodLattice_w0_add H]
    rw [map_one, Matrix.mul_one]
  refine ⟨r, b * ρ H.w0, ρ, hr, ?_, ?_, ?_, ?_⟩
  · rw [hW]; exact hbpd
  · rw [hW]; exact hbu
  · intro a; rw [hW]; exact hbadj a
  · rw [hW]

end GlobalTheory.Mum
