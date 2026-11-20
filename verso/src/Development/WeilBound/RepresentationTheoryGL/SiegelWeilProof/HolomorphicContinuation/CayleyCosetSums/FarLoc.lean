import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CurveGR
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockEqAdjoint
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IILeft
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.HermRealSmul
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContDiffOnSecondCayleyBlockEntries
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FactorL

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.FL

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw.LVs.II (cE cE_hasDerivAt0 cE_add cE_zero cE_continuous JJ_conjTranspose)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem JJ_mul_self : JJ n * JJ n = -1 := PositivityTheory.Rg.Sw.LVs.HolB.JJ_sq

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem JJ_inv : (JJ n)⁻¹ = -JJ n :=
  Matrix.inv_eq_right_inv (by rw [mul_neg, JJ_mul_self, neg_neg])

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sig_eq (X : M2 n) : sig X = JJ n * Xᴴ * JJ n := by
  simp only [sig, JJ_inv, neg_mul, neg_neg]

def IsLie (X : M2 n) : Prop := Xᴴ = JJ n * X * JJ n

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities.
-/
theorem isLie_first_direction (Z : M2 n) : IsLie (dir1 Z) := by
  unfold IsLie dir1
  rw [sig_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, JJ_conjTranspose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, JJ_mul_self]
  simp only [Matrix.mul_assoc, JJ_mul_self, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_one, Matrix.one_mul]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h2, add_comm]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem isLie_second_direction (Z : M2 n) : IsLie (dir2 Z) := by
  unfold IsLie dir2
  rw [sig_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, JJ_conjTranspose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, JJ_mul_self]
  simp only [Matrix.mul_assoc, JJ_mul_self, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_one, Matrix.one_mul]
  have h2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp [Complex.conj_I]
  rw [h2, neg_smul, ← smul_neg, neg_sub]

/- English proof (translation)
Split into cases according to the possible forms of the given data. A detailed English derivation is pending.
-/
theorem lie_dir (Z : M2 n) (b : Bool) : IsLie (if b then dir1 Z else dir2 Z) := by
  cases b
  · exact isLie_second_direction Z
  · exact isLie_first_direction Z

def Ju (n : ℕ) : (M2 n)ˣ where
  val := JJ n
  inv := -JJ n
  val_inv := by rw [mul_neg, JJ_mul_self, neg_neg]
  inv_val := by rw [neg_mul, JJ_mul_self, neg_neg]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem cE_conjTranspose {X : M2 n} (hX : IsLie X) (s : ℝ) : (cE X s)ᴴ = JJ n * cE X (-s) * -JJ n := by
  unfold cE
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial, hX]
  have h : s • (JJ n * X * JJ n) = (Ju n : M2 n) * ((-s) • X) * ((Ju n)⁻¹ : (M2 n)ˣ) := by
    simp only [Ju, Units.inv_mk, Units.val_mk, Matrix.mul_neg, Matrix.mul_smul, neg_smul]
    rw [Matrix.neg_mul, neg_neg, Matrix.smul_mul]
  rw [h, Matrix.exp_units_conj]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem inG_cE {X : M2 n} (hX : IsLie X) (s : ℝ) : InG (cE X s) := by
  unfold InG
  rw [cE_conjTranspose hX]
  calc JJ n * cE X (-s) * -JJ n * JJ n * cE X s = JJ n * (cE X (-s) * cE X s) := by
        simp only [Matrix.mul_assoc, Matrix.neg_mul, JJ_mul_self, neg_neg, Matrix.one_mul, Matrix.mul_neg]
    _ = JJ n := by rw [← cE_add, neg_add_cancel, cE_zero, Matrix.mul_one]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem cE_eq_exp (X : M2 n) (s : ℝ) : NormedSpace.exp ((s : ℂ) • X) = cE X s := by
  unfold cE; rw [Complex.coe_smul]

def gam {X : M2 n} (hX : IsLie X) (t : ℝ) : GR n :=
  ⟨⟨cE X t, cE X (-t), by rw [← cE_add, add_neg_cancel, cE_zero], by rw [← cE_add, neg_add_cancel, cE_zero]⟩,
    inG_cE hX t⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem curveGR' {X : M2 n} (hX : IsLie X) : Continuous (gam hX) ∧ gam hX 0 = 1 ∧
    (∀ s t, gam hX (s + t) = gam hX s * gam hX t) ∧ ∀ t, mR (gam hX t) = cE X t := by
  refine ⟨?_, ?_, ?_, fun t => rfl⟩
  · refine Continuous.subtype_mk ?_ _
    rw [Units.continuous_iff]
    exact ⟨cE_continuous X, (cE_continuous X).comp continuous_neg⟩
  · apply Subtype.ext; apply Units.ext; exact cE_zero X
  · intro s t; apply Subtype.ext; apply Units.ext; exact cE_add X s t

end PositivityTheory.Rg.Sw.HSt.FL

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt.FL

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem curveGR : CurveGR := by
  intro n Z b
  obtain ⟨h1, h2, h3, h4⟩ := curveGR' (lie_dir Z b)
  exact ⟨gam (lie_dir Z b), h1, h2, h3, fun t => by rw [h4, cE_eq_exp]⟩

end PositivityTheory.Rg.Sw.HSt
