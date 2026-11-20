import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.DensStepOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryDense

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Matrix MvPolynomial
open scoped ComplexOrder
open Classical

namespace PI.UnitaryGroupMassFormula.HwConjInf

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

def coords (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) : InfinitePlace L × Fin n × Fin n → ℂ :=
  fun q => Y q.1 q.2.1 q.2.2

def Mx (w : InfinitePlace L) : Matrix (Fin n) (Fin n) (MvPolynomial (InfinitePlace L × Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => X (w, i, j)

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem eval_Mx (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace L) :
    (eval (coords Y)).mapMatrix (Mx w) = Y w := by
  ext i j
  simp [Mx, coords]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem eval_det_Mx (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace L) :
    eval (coords Y) (Mx w).det = (Y w).det := by
  rw [RingHom.map_det, eval_Mx]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem eval_det_one_add_Mx (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace L) :
    eval (coords Y) (1 + Mx w).det = (1 + Y w).det := by
  rw [RingHom.map_det, map_add, map_one, eval_Mx]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem eval_adj_Mx (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace L) (i j : Fin n) :
    eval (coords Y) ((Mx w).adjugate i j) = (Y w).adjugate i j := by
  have h := congrFun (congrFun (RingHom.map_adjugate (eval (coords Y)) (Mx w)) i) j
  rw [eval_Mx] at h
  simpa using h

def Dl (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) : ℂ := ∏ w, (Y w).det

def DlP : MvPolynomial (InfinitePlace L × Fin n × Fin n) ℂ := ∏ w, (Mx w).det

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem eval_DlP (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) : eval (coords Y) (DlP (L := L) (n := n)) = Dl Y := by
  simp [DlP, Dl, map_prod, eval_det_Mx]

/- English proof (translation)
Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem var_hom (v : (L →+* ℂ) × Fin n × Fin n) :
    ∃ N : MvPolynomial (InfinitePlace L × Fin n × Fin n) ℂ, ∀ Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ,
      (∀ w, (Y w).det ≠ 0) → Dl Y * repPt Y v = eval (coords Y) N := by
  obtain ⟨σ, i, j⟩ := v
  by_cases h : σ = (InfinitePlace.mk σ).embedding
  · refine ⟨X (InfinitePlace.mk σ, i, j) * DlP, fun Y _ => ?_⟩
    simp only [repPt, if_pos h, map_mul, eval_X, eval_DlP, coords]
    ring
  · refine ⟨(Mx (InfinitePlace.mk σ)).adjugate j i *
      ∏ w ∈ Finset.univ.erase (InfinitePlace.mk σ), (Mx w).det, fun Y hY => ?_⟩
    simp only [repPt, if_neg h, map_mul, map_prod, eval_adj_Mx, eval_det_Mx]
    rw [Matrix.inv_def, Matrix.smul_apply, Dl,
      ← Finset.mul_prod_erase Finset.univ (fun w => (Y w).det) (Finset.mem_univ (InfinitePlace.mk σ)),
      Ring.inverse_eq_inv', smul_eq_mul]
    have := hY (InfinitePlace.mk σ)
    field_simp

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hom_exists (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :
    ∃ (K : ℕ) (P : MvPolynomial (InfinitePlace L × Fin n × Fin n) ℂ), ∀ Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ,
      (∀ w, (Y w).det ≠ 0) → Dl Y ^ K * eval (repPt Y) F = eval (coords Y) P := by
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, fun Y _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨K1, P1, h1⟩ := hp
    obtain ⟨K2, P2, h2⟩ := hq
    refine ⟨K1 + K2, P1 * DlP ^ K2 + P2 * DlP ^ K1, fun Y hY => ?_⟩
    simp only [map_add, map_mul, map_pow, eval_DlP, ← h1 Y hY, ← h2 Y hY]
    ring
  | mul_X p v hp =>
    obtain ⟨K, P, h⟩ := hp
    obtain ⟨N, hN⟩ := var_hom (L := L) v
    refine ⟨K + 1, P * N, fun Y hY => ?_⟩
    rw [map_mul, map_mul, ← h Y hY, ← hN Y hY, eval_X]
    ring

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem repPt_of_InV [IsCMField L] (y : (L →+* ℂ) × Fin n × Fin n → ℂ) (hy : InV y) :
    repPt (fun w => Matrix.of fun i j => y (w.embedding, i, j)) = y ∧
      ∀ w : InfinitePlace L, (Matrix.of fun i j => y (w.embedding, i, j)).det ≠ 0 := by
  refine ⟨?_, fun w => ?_⟩
  · funext p
    obtain ⟨σ, i, j⟩ := p
    simp only [repPt]
    split_ifs with h
    · exact congrArg (fun s => y (s, i, j)) h.symm
    · have hc : σ = ComplexEmbedding.conjugate (InfinitePlace.mk σ).embedding := by
        rcases InfinitePlace.embedding_mk_eq σ with h' | h'
        · exact absurd h'.symm h
        · rw [h']; exact (star_star σ).symm
      obtain ⟨B, hB⟩ := hy (InfinitePlace.mk σ).embedding
      have hYB : (Matrix.of fun i j => y ((InfinitePlace.mk σ).embedding, i, j)) = (B : Matrix (Fin n) (Fin n) ℂ) := by
        ext a b; exact (hB a b).1
      rw [hYB, ← Matrix.coe_units_inv]
      conv_rhs => rw [hc]
      exact ((hB i j).2).symm
  · obtain ⟨B, hB⟩ := hy w.embedding
    have hYB : (Matrix.of fun i j => y (w.embedding, i, j)) = (B : Matrix (Fin n) (Fin n) ℂ) := by
      ext a b; exact (hB a b).1
    rw [hYB]
    exact (Matrix.isUnits_det_units B).ne_zero

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem density_second_bound : DensB := by
  intro L _ _ _ n F hF y hy
  obtain ⟨K, P, hP⟩ := hom_exists (L := L) F
  have hG : (∏ w, (1 + Mx (L := L) (n := n) w).det) * P = 0 := by
    apply productFramesDense_holds (InfinitePlace L) n (fun _ => 1) (fun _ => Matrix.PosDef.one)
    intro Y hY
    have hY' : ∀ w, (Y w)ᴴ * Y w = 1 := fun w => by simpa using hY w
    have hdet : ∀ w, (Y w).det ≠ 0 := fun w h0 => by
      have := congrArg Matrix.det (hY' w)
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    change eval (coords Y) _ = 0
    rw [map_mul, map_prod]
    simp only [eval_det_one_add_Mx]
    by_cases h1 : ∀ w, (1 + Y w).det ≠ 0
    · rw [← hP Y hdet, hF Y hY' h1]
      simp
    · push Not at h1
      obtain ⟨w, hw⟩ := h1
      rw [Finset.prod_eq_zero (Finset.mem_univ w) hw, zero_mul]
  have hne : (∏ w, (1 + Mx (L := L) (n := n) w).det) ≠ 0 := by
    intro h0
    have := congrArg (eval (coords (fun _ : InfinitePlace L => (0 : Matrix (Fin n) (Fin n) ℂ)))) h0
    rw [map_prod] at this
    simp only [eval_det_one_add_Mx, add_zero, Matrix.det_one, Finset.prod_const_one, map_zero] at this
    exact one_ne_zero this
  have hP0 : P = 0 := (mul_eq_zero.mp hG).resolve_left hne
  obtain ⟨hYy, hYdet⟩ := repPt_of_InV y hy
  have := hP _ hYdet
  rw [hP0, map_zero, hYy] at this
  exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun w _ => hYdet w))

end PI.UnitaryGroupMassFormula.HwConjInf
