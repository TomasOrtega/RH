import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.OffUnitsLeUnitIdl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMInfinityComponentGlobalUnit

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep

namespace UpperTheory.Gal.TP.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
private theorem mk_emb_eq (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w)
    (v : InfinitePlace E) :
    InfinitePlace.mk (emb (v.comap (algebraMap (maximalRealSubfield E) E))).1 = v := by
  apply (IsCMField.equivInfinitePlace E).injective
  rw [IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply, InfinitePlace.comap_mk,
    (emb (v.comap (algebraMap (maximalRealSubfield E) E))).2, InfinitePlace.mk_embedding]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities.
-/
private theorem conj_div_norm {z : ℂ} (hz : z ≠ 0) :
    starRingEnd ℂ z / (‖starRingEnd ℂ z‖ : ℂ) = (z / (‖z‖ : ℂ))⁻¹ := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have hc : starRingEnd ℂ z * z = (‖z‖ : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  rw [RCLike.norm_conj, inv_div]
  field_simp
  rw [hc]

open Classical in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Simplify to obtain the desired conclusion from the available facts.

Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem muEmb : MuEmb := by
  intro E _ _ _ hU emb w₀ m hm
  let e : InfinitePlace E → ℤ := fun v =>
    if v.embedding = (emb (v.comap (algebraMap (maximalRealSubfield E) E))).1
    then m (v.comap (algebraMap (maximalRealSubfield E) E))
    else - m (v.comap (algebraMap (maximalRealSubfield E) E))
  have he : ∀ v, Odd (e v) := fun v => by
    by_cases h : v.embedding = (emb (v.comap (algebraMap (maximalRealSubfield E) E))).1
    · simpa [e, h] using hm _
    · simpa [e, h] using hm _
  obtain ⟨μ, hμ, hS⟩ := UpperTheory.ConvolutionTheory.D.muEx E hU {w₀} (Set.finite_singleton w₀) e he
  refine ⟨μ, hμ.1, hμ.2.1, fun k => ?_, hS w₀ rfl⟩
  have hk : ((μ.inf k : ℂˣ) : ℂ) = _ := GlobalTheory.BCT.inf_mu_unit E μ e hμ k
  rw [hk]
  refine Fintype.prod_equiv (IsCMField.equivInfinitePlace E) _ _ fun v => ?_
  rw [IsCMField.equivInfinitePlace_apply]
  have hmk := mk_emb_eq emb v
  have hor := InfinitePlace.mk_eq_iff.1 (hmk.trans (InfinitePlace.mk_embedding v).symm)
  by_cases h : v.embedding = (emb (v.comap (algebraMap (maximalRealSubfield E) E))).1
  · simp only [e, if_pos h]
    rw [← h]
  · have hc : (emb (v.comap (algebraMap (maximalRealSubfield E) E))).1 =
        ComplexEmbedding.conjugate v.embedding := by
      rcases hor with h' | h'
      · exact absurd h'.symm h
      · rw [← h']
        exact (star_star _).symm
    have hz : v.embedding (k : E) ≠ 0 := (map_ne_zero _).2 k.ne_zero
    simp only [e, if_neg h]
    rw [hc, ComplexEmbedding.conjugate_coe_eq, conj_div_norm hz, inv_zpow']

end UpperTheory.Gal.TP.Chr
