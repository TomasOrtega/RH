import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitaryStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem IsU.transpose_mul_mul_map {R : Type} [CommRing R] {n : ℕ} {σ : R →+* R}
    {G γ : Matrix (Fin n) (Fin n) R} (h : IsU σ G γ) : γᵀ * G * γ.map σ = G := by
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  have h2 : hf σ G (Pi.single a 1) (Pi.single b 1) = G a b := by
    simp [hf, Pi.single_apply, apply_ite σ]
  rw [h2] at h1
  rw [← h1]
  simp only [hf, Matrix.mulVec_single_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.col_apply, Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem IsU.det_mul_conj_det {E : Type} [Field E] {n : ℕ} {σ : E →+* E}
    {G γ : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (h : IsU σ G γ) : γ.det * σ γ.det = 1 := by
  have h1 := congrArg Matrix.det h.transpose_mul_mul_map
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have h2 : (γ.map σ).det = σ γ.det := by
    rw [RingHom.map_det]; rfl
  rw [h2] at h1
  apply mul_left_cancel₀ hG
  linear_combination h1

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem IsU.nonsing_inv {E : Type} [Field E] {n : ℕ} {σ : E →+* E}
    {G γ : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (h : IsU σ G γ) : IsU σ G γ⁻¹ := by
  have hu : IsUnit γ.det := IsUnit.of_mul_eq_one _ (h.det_mul_conj_det hG)
  intro x y
  rw [← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec, Matrix.one_mulVec]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem tvGen_normal : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∀ γ, IsU σ G γ → γ.det * σ γ.det = 1 ∧ IsU σ G γ⁻¹) ∧ (∀ m ∈ TvGen σ G, IsU σ G m ∧ m.det = 1 ∧ m⁻¹ ∈ TvGen σ G ∧ ∀ γ, IsU σ G γ → ∃ m' ∈ TvGen σ G, γ * m = m' * γ ∧ ∃ m'' ∈ TvGen σ G, m * γ = γ * m'') := by
  intro E _ _ n σ G hG
  obtain ⟨-, -, hmul, hdet, hU, hconj, -, hUmul⟩ := GlobalTheory.T.transvection_identities_unitary E n σ G hG.invol hG.herm
  refine ⟨fun γ h => ⟨h.det_mul_conj_det hG.det_ne, h.nonsing_inv hG.det_ne⟩, ?_⟩
  have key : ∀ m ∈ TvGen σ G, IsU σ G m ∧ m.det = 1 ∧ m⁻¹ ∈ TvGen σ G ∧
      ∀ γ, IsU σ G γ → ∃ m' ∈ TvGen σ G, γ * m = m' * γ := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem m hm =>
      obtain ⟨x, t, hx, ht, rfl⟩ := hm
      refine ⟨hU x t (by rw [ht, hx]; simp), by rw [hdet, hx]; simp, ?_, ?_⟩
      · have h1 : tv σ G x t * tv σ G x (-t) = 1 := by
          rw [hmul, hx]
          ext a b
          simp [tv]
        rw [Matrix.inv_eq_right_inv h1]
        exact Submonoid.subset_closure ⟨x, -t, hx, by rw [map_neg]; linear_combination -ht, rfl⟩
      · intro γ hγ
        exact ⟨tv σ G (γ *ᵥ x) t, Submonoid.subset_closure ⟨_, t, by rw [hγ, hx], ht, rfl⟩,
          hconj γ x t hγ⟩
    | one =>
      refine ⟨fun x y => by simp, by simp, by rw [inv_one]; exact one_mem _, fun γ _ => ⟨1, one_mem _, by simp⟩⟩
    | mul a b _ _ ha hb =>
      obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
      refine ⟨hUmul _ _ ha1 hb1, by rw [Matrix.det_mul, ha2, hb2, one_mul], ?_, ?_⟩
      · rw [Matrix.mul_inv_rev]; exact mul_mem hb3 ha3
      · intro γ hγ
        obtain ⟨a', ha', ea⟩ := ha4 γ hγ
        obtain ⟨b', hb', eb⟩ := hb4 γ hγ
        exact ⟨a' * b', mul_mem ha' hb', by rw [← mul_assoc, ea, mul_assoc, eb, mul_assoc]⟩
  intro m hm
  obtain ⟨h1, h2, h3, h4⟩ := key m hm
  refine ⟨h1, h2, h3, fun γ hγ => ?_⟩
  obtain ⟨m', hm', e⟩ := h4 γ hγ
  obtain ⟨m'', hm'', e'⟩ := h4 γ⁻¹ (hγ.nonsing_inv hG.det_ne)
  have hu : IsUnit γ.det := IsUnit.of_mul_eq_one _ (hγ.det_mul_conj_det hG.det_ne)
  refine ⟨m', hm', e, m'', hm'', ?_⟩
  calc m * γ = γ * (γ⁻¹ * m) * γ := by
        rw [← mul_assoc, Matrix.mul_nonsing_inv _ hu, one_mul]
    _ = γ * m'' := by
        rw [e', mul_assoc, mul_assoc, Matrix.nonsing_inv_mul _ hu, mul_one]

end GlobalTheory.UTrans
