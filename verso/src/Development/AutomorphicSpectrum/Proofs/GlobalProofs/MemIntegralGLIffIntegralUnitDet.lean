import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormPropertiesStatement
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QLDet

variable {F : Type} [Field F]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem det_mem_of_isInt (O : Subring F) {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsInt O M) :
    M.det ∈ O := by
  let M' : Matrix (Fin n) (Fin n) O := fun a b => ⟨M a b, h a b⟩
  have hM : M = O.subtype.mapMatrix M' := by
    ext a b
    rfl
  rw [hM, ← RingHom.map_det]
  exact (M'.det).2

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem adjugate_isInt (O : Subring F) {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsInt O M) :
    IsInt O M.adjugate := by
  let M' : Matrix (Fin n) (Fin n) O := fun a b => ⟨M a b, h a b⟩
  have hM : M = O.subtype.mapMatrix M' := by
    ext a b
    rfl
  intro a b
  rw [hM, ← RingHom.map_adjugate]
  exact (M'.adjugate a b).2

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_GLint_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
    (hLF : LF O ϖ nrm q) (n : ℕ) (g : GL (Fin n) F) :
    g ∈ GLint O n ↔ (IsInt O (g : Matrix (Fin n) (Fin n) F) ∧
      nrm (g : Matrix (Fin n) (Fin n) F).det = 1) := by
  obtain ⟨-, -, hO, -, -, -, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties hLF
  have hdet : (g : Matrix (Fin n) (Fin n) F).det * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  constructor
  · intro hg
    obtain ⟨h1, h2⟩ : IsInt O (g : Matrix (Fin n) (Fin n) F) ∧
        IsInt O ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := hg
    refine ⟨h1, ?_⟩
    have a1 := (hO _).2 (det_mem_of_isInt O h1)
    have a2 := (hO _).2 (det_mem_of_isInt O h2)
    have hm : nrm (g : Matrix (Fin n) (Fin n) F).det *
        nrm ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
      rw [← map_mul, hdet, map_one]
    have p1 := nrm.nonneg (g : Matrix (Fin n) (Fin n) F).det
    have p2 := nrm.nonneg ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det
    nlinarith
  · rintro ⟨h1, h2⟩
    show IsInt O (g : Matrix (Fin n) (Fin n) F) ∧ IsInt O ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    refine ⟨h1, ?_⟩
    intro a b
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    apply O.mul_mem
    · apply (hO _).1
      rw [map_inv₀, h2, inv_one]
    · exact adjugate_isInt O h1 a b

end GlobalTheory.CompanionTheory.QLDet
