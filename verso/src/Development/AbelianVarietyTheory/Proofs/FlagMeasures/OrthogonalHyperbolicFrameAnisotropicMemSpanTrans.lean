import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St
variable {D : D7}

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem crd_sum_smul (X : HidaSetting D) {ι : Type} [Fintype ι] (c : ι → X.B.I.E) (v : ι → (VS D).V) :
    X.crd (∑ k, X.ιE (c k) • v k) = fun i => ∑ k, c k * X.crd (v k) i := by
  funext i
  simp [HidaSetting.crd, crdOf, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem crd_injective (X : HidaSetting D) : Function.Injective X.crd := by
  intro v w h
  apply X.bas.repr.injective
  ext i
  have := congrFun h i
  simp only [HidaSetting.crd, crdOf] at this
  rw [X.ιE.symm.injective this]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem orth_mem_span_qFr : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    WittX X u wt → ∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) →
    (VS D).hT (X.zu u) y = 0 → ∃ d : Fin (D.R.N 0) → D.host.E, Fintype.linearCombination D.host.E (qFr wt) d = y := by
  intro D X u wt hw y hef hz
  classical
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hq, he, hf, hzc, -, -⟩ := qFrame_basis_gram D X u wt hw
  have hcol : ∀ k i, Q i k = X.crd (famQ X u wt k) i := by
    rintro (j | a | a | ⟨⟩) i
    · simp [famQ, hq]
    · simp [famQ, he, HidaSetting.eR]
    · simp [famQ, hf, HidaSetting.fR]
    · simp [famQ, hzc, HidaSetting.zR]
  set c := Qi *ᵥ X.crd y with hc
  have hy : y = ∑ k, X.ιE (c k) • famQ X u wt k := by
    apply crd_injective X
    rw [crd_sum_smul]
    have : Q *ᵥ c = X.crd y := by rw [hc, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    rw [← this]
    funext i
    simp only [Matrix.mulVec, dotProduct, hcol]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hy
  simp only [famQ, Sum.elim_inl, Sum.elim_inr, Fintype.univ_unit, Finset.sum_singleton] at hy
  have hqe : ∀ j b, (VS D).hT (X.eX b) (qFr wt j) = 0 := fun j b =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inl b))
  have hqf : ∀ j b, (VS D).hT (X.fY b) (qFr wt j) = 0 := fun j b =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inr (Sum.inl b)))
  have hqz : ∀ j, (VS D).hT (X.zu u) (qFr wt j) = 0 := fun j =>
    hT_symm_zero (hT_qFr_rest X u wt hw j (Sum.inr (Sum.inr ())))

  have c2 : ∀ b, X.ιE (c (Sum.inr (Sum.inr (Sum.inl b)))) = 0 := by
    intro b
    have h := (hef b).1
    rw [hy] at h
    simpa [map_add, map_sum, hqe, X.ee, X.ef, (X.zu_orth u b).1] using h
  have c1 : ∀ b, X.ιE (c (Sum.inr (Sum.inl b))) = 0 := by
    intro b
    have h := (hef b).2
    rw [hy] at h
    simpa [map_add, map_sum, hqf, X.ff, hT_fe, (X.zu_orth u b).2] using h
  have c3 : X.ιE (c (Sum.inr (Sum.inr (Sum.inr ())))) = 0 := by
    have h := hz
    rw [hy] at h
    simp [map_add, map_sum, hqz, hT_ze, hT_zf] at h
    rw [h.resolve_right (hT_zz_ne X u), map_zero]
  refine ⟨fun j => X.ιE (c (Sum.inl j)), ?_⟩
  rw [hy, Fintype.linearCombination_apply]
  simp [c1, c2, c3]

end GlobalTheory.St
