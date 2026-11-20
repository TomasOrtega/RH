import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockEOfIsBlockSum

noncomputable section

namespace GlobalTheory.AmbBlockDecomp

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

/- English proof (translation)
Use `split_ifs with h`. Take `⟨n, rfl⟩ : ∃ n : ℕ, a = n` from `⟨a.toNat, (Int.toNat_of_nonneg h.1).symm⟩`. Rewrite using `[Finset.sum_eq_single (n + 1)]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Rewrite using `[if_neg]`. Use linear arithmetic over natural numbers and integers. Introduce `hn`. It suffices to derive a contradiction. Apply `hn` to reduce the goal to its premises.

Rewrite using `[Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `c hc`. Rewrite `hc` using `[Finset.mem_Icc]`.

Rewrite using `[if_neg]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_ind_block (t : ℕ) (a : ℤ) :
    (∑ c ∈ Finset.Icc 1 t, (if a = (c : ℤ) - 1 then (1 : ℤ) else 0)) =
      if 0 ≤ a ∧ a < t then 1 else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = n := ⟨a.toNat, (Int.toNat_of_nonneg h.1).symm⟩
    rw [Finset.sum_eq_single (n + 1)]
    · simp
    · intro b _ hb
      rw [if_neg]
      omega
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_Icc]
      omega
  · apply Finset.sum_eq_zero
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [if_neg]
    omega

/- English proof (translation)
Introduce `D i r ρ π hD _ _ _ w hw C τ`. Establish `hB : GlobalTheory.PtCore.BlockE D i r ρ π` using `GlobalTheory.BlockEnl.blockE_of_isBlockSum D i r ρ π (by`. Take `⟨e, he⟩` from `hD`. Conclude with `⟨e, fun g u => he g u⟩)`. Take `⟨h1, h2⟩` from `hB w hw C.LL C.le τ`.

Establish `hl : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), TruncatedSeriesCountingIdentities.locC C M = GlobalTheory.PtCore.locE D i w hw C.LL C.le M` using `fun _ => rfl`. Simplify using `only [hl]`. Use `⟨fun a => ?_, fun c hc a => h2 c hc a⟩` and prove the remaining obligations. Rewrite using `[h1 a]`. Use `congr 1`.

Rewrite using `[Finset.sum_congr rfl (fun c hc => h2 c hc a)]`. Conclude with `(sum_ind_block D.R.t a).symm`.
-/
theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i),
    TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambBlock (D := D) i r ρ π := by
  intro D i r ρ π hD _ _ _ w hw C τ
  have hB : GlobalTheory.PtCore.BlockE D i r ρ π :=
    GlobalTheory.BlockEnl.blockE_of_isBlockSum D i r ρ π (by
      obtain ⟨e, he⟩ := hD
      exact ⟨e, fun g u => he g u⟩)
  obtain ⟨h1, h2⟩ := hB w hw C.LL C.le τ
  have hl : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)),
      TruncatedSeriesCountingIdentities.locC C M = GlobalTheory.PtCore.locE D i w hw C.LL C.le M := fun _ => rfl
  simp only [hl]
  refine ⟨fun a => ?_, fun c hc a => h2 c hc a⟩
  rw [h1 a]
  congr 1
  rw [Finset.sum_congr rfl (fun c hc => h2 c hc a)]
  exact (sum_ind_block D.R.t a).symm

end GlobalTheory.AmbBlockDecomp
