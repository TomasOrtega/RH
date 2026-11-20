import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeOrthogonalSumStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeFullRankSublatticeStatement

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.FlagPair

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.Ar.FlagPair.IsOrthFull at h`. Take `⟨hort, hcard⟩` from `h`. Take `⟨hdeg, hrk⟩` from `GlobalTheory.T.normalized_degree_orthogonal_sum K E (Ψ ⊕ Ψ) A.part hort`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hdeg, Fintype.sum_sum_type]`.

Both sides reduce to the same expression. Establish `hW : ∀ τ, E.rank (A.part (Sum.inl τ)) = j` using `fun τ => by show E.rank ((A.W τ).F (Fin.last j)) = j`. Rewrite using `[(A.W τ).rank (Fin.last j), Fin.val_last]`. Establish `hS : ∀ τ, E.rank (A.part (Sum.inr τ)) = k` using `fun τ => by show E.rank ((A.S τ).F (Fin.last k)) = k`. Rewrite using `[(A.S τ).rank (Fin.last k), Fin.val_last]`.

Rewrite using `[hrk, Fintype.sum_sum_type, ← hcard]`. Simplify using `only [hW, hS, Finset.sum_const, Finset.card_univ, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iSup_part_degree_rank {K : Type} [Field K] [NumberField K] {E : HermitianBundle.{0} K}
    {Ψ : Type} [Fintype Ψ] {j k : ℕ} (A : FlagPair E Ψ j k) (h : A.IsOrthFull) :
    E.normDegree (⨆ a, A.part a) =
        ∑ τ, E.normDegree (A.W τ).top + ∑ τ, E.normDegree (A.S τ).top ∧
      E.rank (⨆ a, A.part a) = Module.finrank (𝓞 K) E.carrier := by
  unfold GlobalTheory.CompanionTheory.Ar.FlagPair.IsOrthFull at h
  obtain ⟨hort, hcard⟩ := h
  obtain ⟨hdeg, hrk⟩ := GlobalTheory.T.normalized_degree_orthogonal_sum K E (Ψ ⊕ Ψ) A.part hort
  refine ⟨?_, ?_⟩
  · rw [hdeg, Fintype.sum_sum_type]
    rfl
  · have hW : ∀ τ, E.rank (A.part (Sum.inl τ)) = j := fun τ => by
      show E.rank ((A.W τ).F (Fin.last j)) = j
      rw [(A.W τ).rank (Fin.last j), Fin.val_last]
    have hS : ∀ τ, E.rank (A.part (Sum.inr τ)) = k := fun τ => by
      show E.rank ((A.S τ).F (Fin.last k)) = k
      rw [(A.S τ).rank (Fin.last k), Fin.val_last]
    rw [hrk, Fintype.sum_sum_type, ← hcard]
    simp only [hW, hS, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring

/- English proof (translation)
Introduce `K _ _ E Ψ _ j k A h`. Take `⟨hdeg, hrk⟩` from `iSup_part_degree_rank A h`. Take `⟨hle, hge⟩` from `GlobalTheory.T.normalized_degree_full_rank_sublattice K E (⨆ a, A.part a) hrk`. Establish `hflat : ∑ τ, A.flatDeg τ = ∑ τ, E.normDegree (A.W τ).top - ∑ τ, E.normDegree (A.S τ).top`. Simplify using `only [GlobalTheory.CompanionTheory.Ar.FlagPair.flatDeg, Finset.sum_sub_distrib]`.

Rewrite `hle` using `[hdeg]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hflat, Finset.sum_neg_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `d hd hsub`.

Establish `hb` using `hge d hd hsub`. Rewrite `hb` using `[hdeg]`. Rewrite using `[hflat, Finset.sum_neg_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem two_sum_neg_degree_W : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ j k), A.IsOrthFull →
    -E.normDegree ⊤ - ∑ τ, A.flatDeg τ ≤ 2 * ∑ τ, -E.normDegree (A.W τ).top ∧
      ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ ⨆ a, A.part a) →
        2 * ∑ τ, -E.normDegree (A.W τ).top ≤
          -E.normDegree ⊤ - ∑ τ, A.flatDeg τ +
            Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  intro K _ _ E Ψ _ j k A h
  obtain ⟨hdeg, hrk⟩ := iSup_part_degree_rank A h
  obtain ⟨hle, hge⟩ := GlobalTheory.T.normalized_degree_full_rank_sublattice K E (⨆ a, A.part a) hrk
  have hflat : ∑ τ, A.flatDeg τ =
      ∑ τ, E.normDegree (A.W τ).top - ∑ τ, E.normDegree (A.S τ).top := by
    simp only [GlobalTheory.CompanionTheory.Ar.FlagPair.flatDeg, Finset.sum_sub_distrib]
  rw [hdeg] at hle
  refine ⟨?_, ?_⟩
  · rw [hflat, Finset.sum_neg_distrib]
    linarith
  · intro d hd hsub
    have hb := hge d hd hsub
    rw [hdeg] at hb
    rw [hflat, Finset.sum_neg_distrib]
    linarith

end GlobalTheory.CompanionTheory.Ar.FlagPair
