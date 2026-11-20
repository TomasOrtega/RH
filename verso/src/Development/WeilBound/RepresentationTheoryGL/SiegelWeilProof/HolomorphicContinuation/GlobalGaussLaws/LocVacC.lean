import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacB

noncomputable section

open Matrix Filter Topology Polynomial
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {n : ℕ}

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem inG_JJ : InG (JJ n) := by
  unfold InG
  rw [JJ_conjTranspose, Matrix.mul_assoc, JJ_sq, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem nU_mul (b c : Matrix (Fin n) (Fin n) ℂ) : nU b * nU c = nU (b + c) := by
  simp [nU, fromBlocks_multiply, add_comm]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem nU_zero : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp [nU, fromBlocks_one]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (nU b) := by
  unfold InG; simp [nU, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, hb.eq]

def jjE : GR n := ⟨⟨JJ n, -JJ n, by rw [Matrix.mul_neg, JJ_sq, neg_neg], by rw [Matrix.neg_mul, JJ_sq, neg_neg]⟩, inG_JJ⟩

def nuE (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) : GR n :=
  ⟨⟨nU b, nU (-b), by rw [nU_mul, add_neg_cancel, nU_zero], by rw [nU_mul, neg_add_cancel, nU_zero]⟩, inG_nU hb⟩

def nbar (s : ℝ) : M2 n := fromBlocks 1 0 ((s : ℂ) • 1) 1

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem nbar_mul (s t : ℝ) : nbar (n := n) s * nbar t = nbar (s + t) := by
  simp [nbar, fromBlocks_multiply, add_smul, add_comm]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem nbar_zero : nbar (n := n) 0 = 1 := by simp [nbar, fromBlocks_one]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem inG_nbar (s : ℝ) : InG (nbar (n := n) s) := by
  unfold InG
  simp [nbar, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.conjTranspose_smul, Complex.conj_ofReal]

def nbE (s : ℝ) : GR n :=
  ⟨⟨nbar s, nbar (-s), by rw [nbar_mul, add_neg_cancel, nbar_zero], by rw [nbar_mul, neg_add_cancel, nbar_zero]⟩, inG_nbar s⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nbE_zero : nbE (n := n) 0 = 1 := Subtype.ext (Units.ext nbar_zero)

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem cont_nbar : Continuous (nbar (n := n)) := by
  unfold nbar
  exact Continuous.matrix_fromBlocks continuous_const continuous_const
    (Complex.continuous_ofReal.smul continuous_const) continuous_const

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem cont_nbE : Continuous (nbE (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.mpr ⟨cont_nbar, ?_⟩
  exact cont_nbar.comp continuous_neg

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem lower_left_block_mul_lowering (g : GR n) (s : ℝ) :
    (mR (g * nbE s)).toBlocks₂₁ = (mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂ := by
  rw [mR_mul]
  conv_lhs => rw [← fromBlocks_toBlocks (mR g)]
  show (fromBlocks _ _ _ _ * nbar s).toBlocks₂₁ = _
  simp [nbar, fromBlocks_multiply]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem finite_bad (g : GR n) :
    {s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0}.Finite := by
  set C := (mR g).toBlocks₂₁
  set D := (mR g).toBlocks₂₂
  set P : Polynomial ℂ := det (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C) with hP
  have hev : ∀ z : ℂ, P.eval z = (C + z • D).det := by
    intro z
    rw [hP, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hP0 : P ≠ 0 := by
    intro h0
    have hz := hev Complex.I
    rw [h0, Polynomial.eval_zero] at hz
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hz.symm
    apply hv
    apply vec_zero g (-Complex.I) (by simp) v
    have hm : (-Complex.I) • C + D = (-Complex.I) • (C + Complex.I • D) := by
      rw [smul_add, smul_smul]
      simp
    rw [hm, Matrix.vecMul_smul, hv0, smul_zero]
  apply ((P.roots.toFinset.finite_toSet).preimage Complex.ofReal_injective.injOn).subset
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP0,
    Polynomial.IsRoot, hev]
  exact hs

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem dense_cell : Dense {g : GR n | ((mR g).toBlocks₂₁).det ≠ 0} := by
  intro g
  have hT : Tendsto (fun s : ℝ => g * nbE s) (𝓝[≠] 0) (𝓝 g) := by
    have hc : Continuous fun s : ℝ => g * nbE s := continuous_const.mul cont_nbE
    have h := hc.tendsto 0
    rw [nbE_zero, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  have hfin := finite_bad g
  have hZ : IsClosed ({s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0} \ {0}) :=
    (hfin.subset Set.sdiff_subset).isClosed
  have h0 : (0 : ℝ) ∉ ({s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0} \ {0}) := by simp
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hZ.isOpen_compl.mem_nhds h0), self_mem_nhdsWithin] with s hs hs0
  show ((mR (g * nbE s)).toBlocks₂₁).det ≠ 0
  rw [lower_left_block_mul_lowering]
  intro hdet
  exact hs ⟨hdet, hs0⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem bigcell (g : GR n) (hγ : ((mR g).toBlocks₂₁).det ≠ 0) :
    ∃ (y h : GR n) (b : Matrix (Fin n) (Fin n) ℂ), (mR y).toBlocks₂₁ = 0 ∧ b.IsHermitian ∧ mR h = JJ n * nU b ∧
      g = y * h := by
  set C := (mR g).toBlocks₂₁ with hC
  set D := (mR g).toBlocks₂₂ with hD
  have hu : IsUnit C.det := isUnit_iff_ne_zero.mpr hγ
  have huH : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hγ)
  have hb : (C⁻¹ * D).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Dᴴ * Cᴴ⁻¹ = C⁻¹ * (C * Dᴴ) * Cᴴ⁻¹ := by rw [nonsing_inv_mul_cancel_left C _ hu]
      _ = C⁻¹ * (D * Cᴴ) * Cᴴ⁻¹ := by rw [hC, hD, lagr g]
      _ = C⁻¹ * D := by rw [← Matrix.mul_assoc, mul_nonsing_inv_cancel_right Cᴴ _ huH]
  refine ⟨g * (jjE * nuE (C⁻¹ * D) hb)⁻¹, jjE * nuE (C⁻¹ * D) hb, C⁻¹ * D, ?_, hb, ?_, by group⟩
  · have hinv : mR (jjE * nuE (C⁻¹ * D) hb)⁻¹ = nU (-(C⁻¹ * D)) * (-JJ n) := by
      rw [_root_.mul_inv_rev, mR_mul]
      rfl
    rw [mR_mul, hinv]
    conv_lhs => rw [← fromBlocks_toBlocks (mR g)]
    simp [nU, JJ, fromBlocks_multiply, fromBlocks_neg, ← hC, ← hD]
    rw [mul_nonsing_inv_cancel_left C D hu, neg_add_cancel]
  · rw [mR_mul]
    rfl

end PositivityTheory.Rg.Sw.Glob.Vac
