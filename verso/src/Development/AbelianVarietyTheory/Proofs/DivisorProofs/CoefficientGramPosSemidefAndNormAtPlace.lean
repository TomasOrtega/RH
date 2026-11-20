import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem pairVr_one_eq {E K : Type} [Field E] [Field K] [StarRing K] {ι : Type} [Fintype ι] (emb : ι → E →+* K) {n : ℕ}
    (lam : ι → DomWeight n) :
    pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) = pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) := by
  have e : gramKd emb (1 : Matrix (Fin n) (Fin n) E) = fun _ => 1 := by
    funext τ
    rw [gramKd, Matrix.map_one _ (map_zero _) (map_one _), inv_one, Matrix.transpose_one]
  rw [← e]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem gram_posSemidef_and_sqAt : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (emb : ι → E →+* K) (n : ℕ) (lam : ι → DomWeight n) (σ : K →+* ℂ), ((Matrix.of fun i j => pairVr emb lam 1 (bVV K lam i) (bVV K lam j)).map σ).PosSemidef ∧ ∀ x : Formalism.L2.DIV.VV K lam, (∑ i, ∑ j, starRingEnd ℂ ((InfinitePlace.mk σ).embedding ((bVV K lam).repr x i)) * (InfinitePlace.mk σ).embedding (pairVr emb lam 1 (bVV K lam i) (bVV K lam j)) * (InfinitePlace.mk σ).embedding ((bVV K lam).repr x j)).re = sqAt σ lam x := by
  intro E K _ _ _ _ _ ι _ emb n lam σ
  rw [pairVr_one_eq]
  refine ⟨?_, fun x => ?_⟩
  · simp only [GlobalTheory.PeriodClassSum.pairK_one_basis]
    exact (GlobalTheory.PeriodClassSum.gramB_posDef lam σ).posSemidef
  · unfold sqAt
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h, ← Complex.conj_re]
      simp only [map_sum, map_mul, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

end GlobalTheory.ColNorms
