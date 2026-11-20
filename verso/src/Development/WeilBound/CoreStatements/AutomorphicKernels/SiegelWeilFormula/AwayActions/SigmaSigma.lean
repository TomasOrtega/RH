import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdDecomp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLocF
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemClosureHeckeSplitCongruenceOfFinPartOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBase
import Development.WeilBound.ThetaLifts.LatticeBasics.ConstIdele

noncomputable section

open scoped TensorProduct Matrix
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem cA_inclR (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  unfold cA inclR
  simp [Algebra.TensorProduct.includeRight_apply]

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
private theorem isHecke_div_and_resEtaPow_div (hcm : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  unfold IsCMExt at hcm
  obtain ⟨-, -, -, h⟩ := hcm
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  apply τ.injective
  rw [h, h, star_star]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately. Treat this case separately.

Treat this case separately.
-/
theorem cA_cA (hcm : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  have hσσ := isHecke_div_and_resEtaPow_div hcm
  unfold cA
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [hσσ]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Introduce a local definition for the expression. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem sigma_sigma' (hcm : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem isPair_and_isPair_of_isTriple (hcm : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  have hσσ := isHecke_div_and_resEtaPow_div hcm
  unfold IsCMExt at hcm
  obtain ⟨-, hE, -, h⟩ := hcm
  by_contra hne
  push Not at hne
  have hfix : ∀ x, σ x = x := by
    intro x
    by_contra hx
    apply hne (x - σ x) (sub_ne_zero.mpr (Ne.symm hx))
    rw [map_sub, hσσ]
    ring
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  have hc := hE.isComplex (InfinitePlace.mk τ)
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at hc
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  have hx := h τ x
  rw [hfix] at hx
  exact hx.symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Evaluate the numerical expressions.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem exists_trace_zero_generator_of_isCMExt (hcm : IsCMExt F E σ) :
    ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ ∧ ∀ e : E, ∃ s t : F, e = algebraMap F E s + t • δ := by
  obtain ⟨δ, hδ0, hδ⟩ := isPair_and_isPair_of_isTriple hcm
  have hrank : Module.finrank F E = 2 := by
    unfold IsCMExt at hcm
    exact hcm.2.2.1
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Algebra.smul_def, mul_one] at hst
    have h2 : algebraMap F E s - algebraMap F E t * δ = 0 := by
      have := congrArg σ hst
      rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hδ, map_zero] at this
      linear_combination this
    have hb : algebraMap F E t * δ = 0 := by
      have h3 : (2 : E) * (algebraMap F E t * δ) = 0 := by linear_combination hst - h2
      rcases mul_eq_zero.1 h3 with h | h
      · norm_num at h
      · exact h
    have ht : t = 0 := by
      rcases mul_eq_zero.1 hb with h | h
      · exact (map_eq_zero_iff _ (algebraMap F E).injective).1 h
      · exact absurd h hδ0
    subst ht
    refine ⟨?_, rfl⟩
    simpa using hst
  let bE := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hrank])
  refine ⟨δ, hδ0, hδ, fun e => ⟨bE.repr e 0, bE.repr e 1, ?_⟩⟩
  conv_lhs => rw [← bE.sum_repr e]
  simp [Fin.sum_univ_two, bE, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Extract witnesses or component facts from the available result. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the hypotheses and the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Evaluate the numerical expressions.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem sigma_fix (hcm : IsCMExt F E σ) (e : E) : σ e = e ↔ e ∈ (algebraMap F E).range := by
  obtain ⟨δ, hδ0, hδ, hdec⟩ := exists_trace_zero_generator_of_isCMExt hcm
  constructor
  · intro he
    obtain ⟨s, t, rfl⟩ := hdec e
    rw [Algebra.smul_def] at he ⊢
    rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hδ] at he
    have h3 : (2 : E) * (algebraMap F E t * δ) = 0 := by linear_combination -he
    have hb : algebraMap F E t * δ = 0 := by
      rcases mul_eq_zero.1 h3 with h | h
      · norm_num at h
      · exact h
    have ht : t = 0 := by
      rcases mul_eq_zero.1 hb with h | h
      · exact (map_eq_zero_iff _ (algebraMap F E).injective).1 h
      · exact absurd h hδ0
    exact ⟨s, by simp [ht]⟩
  · rintro ⟨f, rfl⟩
    exact σ.commutes f

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_delta (hcm : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨δ, h1, h2⟩ := Formalism.IndefR.Fin.U1.exists_delta σ (sigma_sigma' hcm) (sigma_fix hcm) hcm.2.2.1
  exact ⟨δ, h2, h1⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Proceed by induction.

Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Normalize the expressions using the abelian group laws.
-/
theorem nrm_exists (hcm : IsCMExt F E σ) (z : AE F E) : ∃ a : AF F, algebraMap (AF F) (AE F E) a = z * cA σ z := by
  obtain ⟨δ, hδ0, hδ, hdec⟩ := exists_trace_zero_generator_of_isCMExt hcm
  have hfixδ : σ (δ * δ) = δ * δ := by rw [map_mul, hδ, neg_mul_neg]
  obtain ⟨d, hd⟩ := (sigma_fix hcm (δ * δ)).1 hfixδ
  have hz : ∃ x y : AF F, z = x ⊗ₜ[F] (1 : E) + y ⊗ₜ[F] δ := by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul a e =>
      obtain ⟨s, t, rfl⟩ := hdec e
      refine ⟨s • a, t • a, ?_⟩
      simp only [TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
    | add x y hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, e, rfl⟩ := hy
      exact ⟨a + c, b + e, by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩
  obtain ⟨x, y, rfl⟩ := hz
  refine ⟨x * x - algebraMap F (AF F) d * (y * y), ?_⟩
  unfold cA
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, hδ, add_mul, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_neg, mul_neg]
  rw [Algebra.algebraMap_self, RingHom.id_apply, ← hd, Algebra.algebraMap_eq_smul_one (A := E) d,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm y x, sub_eq_add_neg,
    TensorProduct.add_tmul, TensorProduct.neg_tmul]
  abel

end PositivityTheory.SiegelWeilFormula.KAway

end
