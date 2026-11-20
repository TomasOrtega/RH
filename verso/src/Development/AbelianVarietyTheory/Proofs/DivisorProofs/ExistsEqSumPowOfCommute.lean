import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointsIntegralAlmostAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SepCommutant

/- English proof (translation)
Introduce `K _ n g t hs hc`. Establish `hm` using `GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute g t hs hc`. Rewrite `hm` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨p, rfl⟩` from `hm`. Use `set r := p %ₘ g.charpoly with hr`.

Establish `hmon : g.charpoly.Monic` using `Matrix.charpoly_monic g`. Establish `hae : aeval g p = aeval g r`. Conclude with `(Polynomial.aeval_modByMonic_eq_self_of_root (Matrix.aeval_self_charpoly g)).symm`. Establish `hdeg : r.degree < n`. Use `Polynomial.degree_modByMonic_lt p hmon` as an intermediate fact.

Rewrite `this` using `[Matrix.charpoly_degree_eq_dim, Fintype.card_fin]`. Then use the resulting hypothesis. Use `⟨fun i => r.coeff i, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `aeval g p = _`. Rewrite using `[hae, aeval_def, eval₂_eq_sum, ← Polynomial.sum_fin (fun e a => algebraMap K (Matrix (Fin n) (Fin n) K) a * g ^ e) (by simp) hdeg]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def]`.
-/
theorem exists_eq_sum_pow_of_commute :
    ∀ {K : Type} [Field K] {n : ℕ} (g t : Matrix (Fin n) (Fin n) K), g.charpoly.Separable →
    t * g = g * t → ∃ c : Fin n → K, t = ∑ i, c i • g ^ (i : ℕ) := by
  intro K _ n g t hs hc
  have hm := GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute g t hs hc
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
  obtain ⟨p, rfl⟩ := hm
  set r := p %ₘ g.charpoly with hr
  have hmon : g.charpoly.Monic := Matrix.charpoly_monic g
  have hae : aeval g p = aeval g r := by
    exact (Polynomial.aeval_modByMonic_eq_self_of_root (Matrix.aeval_self_charpoly g)).symm
  have hdeg : r.degree < n := by
    have := Polynomial.degree_modByMonic_lt p hmon
    rwa [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at this
  refine ⟨fun i => r.coeff i, ?_⟩
  change aeval g p = _
  rw [hae, aeval_def, eval₂_eq_sum, ← Polynomial.sum_fin (fun e a => algebraMap K (Matrix (Fin n) (Fin n) K) a * g ^ e) (by simp) hdeg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def]

end GlobalTheory.SepCommutant
