import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsDSSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Compact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Introduce `n ε lam hlam h hh hmax`. Take `⟨T⟩` from `HW.kType_exists ε lam hlam`. Distinguish the cases in `hpq : pOf ε = 0 ∨ qOf ε = 0`. Take `⟨σ, hDS, -⟩` from `isDS_compact hpq hlam T`. Conclude with `⟨T.V, inferInstance, inferInstance, σ, hDS⟩`.

Use `push_neg at hpq`. Establish `hq : 1 ≤ S7.q0 ε` using `by show 1 ≤ min (pOf ε) (qOf ε)`. Use linear arithmetic over natural numbers and integers. Establish `hgap : StdGap ε lam` using `⟨hlam.1, h, hh, (le_max_left _ _).trans_lt hmax⟩`. Establish `h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h`.

Establish `h16` using `(le_max_right _ _).trans_lt hmax`. Establish `hs : 0 ≤ Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ))` using `Real.sqrt_nonneg _`. Establish `hnq : 0 ≤ (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ)` using `by positivity`. Use `show 8 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) < h`. Use the polynomial consequences of the given equalities and inequalities.

Take `⟨Ψ, hP, -⟩` from `exists_isPsiFor (hS7 n) T hlam hh hq h8`. Conclude with `⟨_, inferInstance, inferInstance, sigLam ε Ψ T.w, isDS_sigLam hgap hP (HW.KType.w_ne_zero T)⟩`.
-/
theorem final_existsG_of (hS7 : ∀ m : ℕ, S7.PsiExistsStatement m) :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        max ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
          (16 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) +
            8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ))) < h →
        ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
          (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ := by
  intro n ε lam hlam h hh hmax
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  by_cases hpq : pOf ε = 0 ∨ qOf ε = 0
  · obtain ⟨σ, hDS, -⟩ := isDS_compact hpq hlam T
    exact ⟨T.V, inferInstance, inferInstance, σ, hDS⟩
  · push_neg at hpq
    have hq : 1 ≤ S7.q0 ε := by
      show 1 ≤ min (pOf ε) (qOf ε)
      omega
    have hgap : StdGap ε lam := ⟨hlam.1, h, hh, (le_max_left _ _).trans_lt hmax⟩
    have h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h := by
      have h16 := (le_max_right _ _).trans_lt hmax
      have hs : 0 ≤ Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ)) := Real.sqrt_nonneg _
      have hnq : 0 ≤ (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) := by positivity
      show 8 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) < h
      nlinarith
    obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor (hS7 n) T hlam hh hq h8
    exact ⟨_, inferInstance, inferInstance, sigLam ε Ψ T.w, isDS_sigLam hgap hP (HW.KType.w_ne_zero T)⟩

end ReciprocityTheory.ChartRestriction.DS
