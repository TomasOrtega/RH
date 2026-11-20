import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashRationalMatrixProperties

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.QAff

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rhom_eq (v : InfinitePlace F) (x : F) : rhom x v = reAt v x := (rfl)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the hypotheses and the conclusion using the stated equalities. Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem sum_reAt (x : F) : ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  have hv : ∀ v : InfinitePlace F, ((reAt v x : ℝ) : ℂ) = v.embedding x := fun v =>
    InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x
  rw [Complex.ofReal_sum, Complex.ofReal_ratCast]
  simp_rw [hv]
  rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ)]
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ x)
    (fun σ : F →ₐ[ℚ] ℂ => σ x) (fun _ => rfl)]
  symm
  refine Fintype.sum_equiv ((Equiv.subtypeUnivEquiv
    (fun φ : F →+* ℂ => IsTotallyReal.complexEmbedding_isReal φ)).symm.trans
    (InfinitePlace.mkReal.trans
      (Equiv.subtypeUnivEquiv (fun v : InfinitePlace F => IsTotallyReal.isReal v)))) _ _ ?_
  intro φ
  simp [InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem reAt_mul (v : InfinitePlace F) (x y : F) : reAt v (x * y) = reAt v x * reAt v y := by
  rw [← rhom_eq, ← rhom_eq, ← rhom_eq, map_mul, Pi.mul_apply]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem e00 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = reAt v (ε : F) :=
  rhom_eq v _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem e01 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = reAt v b :=
  rhom_eq v _

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem e10 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  simp [cmp, toInf, aff]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem e11 (ε : Fˣ) (b : F) (v : InfinitePlace F) :
    ((cmp v (toInf (aff ε b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by
  simp [cmp, toInf, aff]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem denom_aff (ε : Fˣ) (b : F) (v : InfinitePlace F) (w : ℂ) :
    UpperHalfPlane.denom (cmp v (toInf (aff ε b))) w = 1 := by
  rw [UpperHalfPlane.denom, e10, e11]; simp

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem act_aff (ε : Fˣ) (b : F) (hε : TP (ε : F)) (z : Hn F) (v : InfinitePlace F) :
    ((act (toInf (aff ε b)) z v : UpperHalfPlane) : ℂ) = (reAt v (ε : F) : ℂ) * (z v : ℂ) + (reAt v b : ℂ) := by
  have hd : 0 < ((Matrix.GeneralLinearGroup.det (cmp v (toInf (aff ε b))) : ℝˣ) : ℝ) := by
    simpa [Matrix.det_fin_two, e00, e01, e10, e11] using hε v
  simp only [act]
  rw [UpperHalfPlane.coe_smul_of_det_pos hd, denom_aff, div_one, UpperHalfPlane.num]
  simp [e00, e01]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ez_aff (ε : Fˣ) (b : F) (hε : TP (ε : F)) (z : Hn F) (η : F) :
    ez η (act (toInf (aff ε b)) z) = ez (η * ε) z * et (η * b) := by
  simp only [ez, et, act_aff ε b hε]
  rw [← Complex.exp_add, ← Complex.ofReal_ratCast, ← sum_reAt]
  congr 1
  simp only [reAt_mul]
  push_cast
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun v _ => ?_)
  ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem weightSlash_hilbertAffine_apply (k : ℕ) (f : Hn F → ℂ) (ε : Fˣ) (b : F) (z : Hn F) :
    sl0 k (toInf (aff ε b)) f z = f (act (toInf (aff ε b)) z) := by
  simp only [sl0, denom_aff, Finset.prod_const_one, inv_one, one_pow, one_mul]

omit [IsTotallyReal F] in
/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_den (x : F) : ∃ E : ℕ, 0 < E ∧ IsIntegral ℤ ((E : F) * x) := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  rw [Algebra.smul_def, algebraMap_int_eq, Int.coe_castRingHom] at hint
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rcases le_total 0 y with h | h
  · have e : ((y.natAbs : ℕ) : F) = (y : F) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg h]
    rw [e]
    exact hint
  · have e : ((y.natAbs : ℕ) : F) = -(y : F) := by
      rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos h, Int.cast_neg]
    rw [e, neg_mul]
    exact hint.neg

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem hasQ_aff : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ) (a : F → ℂ) (ε : Fˣ) (b : F),
    TP (ε : F) → HasQ f a → HasQ (sl0 k (toInf (aff ε b)) f) (fun ξ => a (ξ / ε) * et (ξ / ε * b)) := by
  intro F _ _ _ k f a ε b hε hf
  obtain ⟨⟨D, hD, hDa⟩, hsum⟩ := hf
  obtain ⟨E, hE, hEint⟩ := exists_den (ε : F)
  have hε0 : (ε : F) ≠ 0 := ε.ne_zero
  refine ⟨⟨D * E, by positivity, ?_⟩, ?_⟩
  · intro ξ hξ
    have ha : a (ξ / ε) ≠ 0 := fun h0 => hξ (by simp [h0])
    obtain ⟨h1, h2⟩ := hDa _ ha
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1
      · left
        rwa [div_eq_zero_iff, or_iff_left hε0] at h1
      · right
        intro v
        have hp := mul_pos (h1 v) (hε v)
        rwa [← reAt_mul, div_mul_cancel₀ _ hε0] at hp
    · have hm := h2.mul hEint
      have e : ((D * E : ℕ) : F) * ξ = ((D : F) * (ξ / ε)) * ((E : F) * ε) := by
        push_cast
        field_simp
      rw [e]
      exact hm
  · intro z
    have hs := hsum (act (toInf (aff ε b)) z)
    simp only [ez_aff ε b hε z] at hs
    rw [weightSlash_hilbertAffine_apply]
    have hc := (Equiv.hasSum_iff (Units.mulRight ε⁻¹)).mpr hs
    convert hc using 1
    funext ξ
    simp only [Function.comp_apply, Units.mulRight_apply, Units.val_inv_eq_inv_val]
    rw [← div_eq_mul_inv, div_mul_cancel₀ _ hε0]
    ring

end GlobalTheory.HilbertThetaSeries.QAff

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.hasQExpansion_affineTranslate_coeff : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ) (a : F → ℂ) (ε : Fˣ) (b : F), TP (ε : F) → HasQ f a → HasQ (sl0 k (toInf (aff ε b)) f) (fun ξ => a (ξ / ε) * et (ξ / ε * b)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.QAff.hasQ_aff | exact GlobalTheory.HilbertThetaSeries.QAff.hasQ_aff | (intros; apply GlobalTheory.HilbertThetaSeries.QAff.hasQ_aff <;> assumption)
