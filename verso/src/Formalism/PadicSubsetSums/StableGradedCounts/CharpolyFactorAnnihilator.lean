import Formalism.PadicSubsetSums.CentralIdempotents.PrimitiveRootFifteenSubOneUnit

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem charpolyFactorAnnihilator : CharpolyFactorAnnihilator := by
  intro K V _ _ _ _ A B γ₀ γ c cγ t P hAB hA₀ hA hB₀ hB ht hchar
  classical
  let gA : Module.End K A := γ₀.restrict hA₀
  let gB : Module.End K B := c • LinearMap.id
  let e : (A × B) ≃ₗ[K] V := Submodule.prodEquivOfIsCompl A B hAB

  have hconj : e.conj (gA.prodMap gB) = γ₀ := by
    apply LinearMap.ext
    intro v
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    simp [e, gA, gB, Submodule.coe_prodEquivOfIsCompl', hB₀ b b.2]

  have hcB : gB.charpoly = (X - C c) ^ t := by
    rw [← LinearMap.charpoly_toMatrix gB (Module.finBasis K B)]
    have hm : LinearMap.toMatrix (Module.finBasis K B) (Module.finBasis K B) gB =
        Matrix.diagonal (fun _ => c) := by
      simp only [gB, map_smul, LinearMap.toMatrix_id]
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [hm, Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ht]
  have hPA : P = gA.charpoly := by
    have h1 : γ₀.charpoly = gA.charpoly * gB.charpoly := by
      rw [← hconj, LinearEquiv.charpoly_conj, LinearMap.charpoly_prodMap]
    rw [hchar, hcB] at h1
    exact mul_right_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero c)) h1

  have hrestr : ∀ (p : K[X]) (a : A), (aeval γ₀ p) (a : V) = ((aeval gA p) a : V) := by
    intro p
    induction p using Polynomial.induction_on with
    | C r => intro a; simp [Module.algebraMap_end_apply]
    | add p q hp hq => intro a; simp [hp, hq]
    | monomial n r ih =>
      intro a
      rw [pow_succ, ← mul_assoc, map_mul (aeval γ₀), map_mul (aeval gA), aeval_X, aeval_X,
        Module.End.mul_apply, Module.End.mul_apply]
      rw [show γ₀ (a : V) = ((gA a : A) : V) from rfl, ih]
  have h0 : aeval gA P = 0 := by
    rw [hPA]
    exact LinearMap.aeval_self_charpoly gA
  have hkill : ∀ w ∈ A, (aeval γ₀ P) w = 0 := by
    intro w hw
    have h2 := hrestr P ⟨w, hw⟩
    rw [h0] at h2
    simpa using h2
  apply LinearMap.ext
  intro v
  have hv : v ∈ A ⊔ B := by rw [hAB.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [Module.End.mul_apply, LinearMap.zero_apply, LinearMap.sub_apply,
    Module.algebraMap_end_apply]
  have h3 : γ (a + b) - cγ • (a + b) = γ a - cγ • a := by
    rw [map_add, hB b hb, smul_add]
    abel
  rw [h3]
  exact hkill _ (A.sub_mem (hA a ha) (A.smul_mem cγ ha))

end Formalism.IrreducibleCountingLemmas.Z
