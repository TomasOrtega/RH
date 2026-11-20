import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

/- English proof (translation)
Take `⟨-, -, -, hSb, hSσ, -⟩` from `S.hyp.1`. Establish `hWb` using `(S.W H).emb_bij`. Establish `hWσ` using `(S.W H).emb_σ`. Establish `key : ∀ j, (S.W H).emb ((Equiv.ofBijective _ hWb).symm j) = j` using `Equiv.ofBijective_apply_symm_apply _ hWb`. Use `⟨fun i => (Equiv.ofBijective _ hWb).symm (S.emb i), (Equiv.ofBijective _ hWb).symm.bijective.comp hSb, fun i => key _, fun i => hWb.1 ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sub_add_cancel, key]`. Use `_ = (S.W H).emb ((Equiv.ofBijective _ hWb).symm (S.emb i) - 1) := by`. Rewrite using `[← hWσ ((Equiv.ofBijective _ hWb).symm (S.emb i) - 1), sub_add_cancel]`.
-/
theorem exists_letter_bijection {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) :
    ∃ τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K)),
      Function.Bijective τ ∧ (∀ i, (S.W H).emb (τ i) = S.emb i) ∧ ∀ i, τ (i - 1) = τ i - 1 := by
  obtain ⟨-, -, -, hSb, hSσ, -⟩ := S.hyp.1
  have hWb := (S.W H).emb_bij
  have hWσ := (S.W H).emb_σ
  have key : ∀ j, (S.W H).emb ((Equiv.ofBijective _ hWb).symm j) = j :=
    Equiv.ofBijective_apply_symm_apply _ hWb
  refine ⟨fun i => (Equiv.ofBijective _ hWb).symm (S.emb i),
    (Equiv.ofBijective _ hWb).symm.bijective.comp hSb, fun i => key _, fun i => hWb.1 ?_⟩
  calc (S.W H).emb ((Equiv.ofBijective _ hWb).symm (S.emb (i - 1)))
      = S.emb (i - 1) := key _
    _ = (S.emb (i - 1 + 1)).comp (P.PD S.K).σ := (hSσ _).symm
    _ = ((S.W H).emb ((Equiv.ofBijective _ hWb).symm (S.emb i))).comp (P.PD S.K).σ := by
        rw [sub_add_cancel, key]
    _ = (S.W H).emb ((Equiv.ofBijective _ hWb).symm (S.emb i) - 1) := by
        rw [← hWσ ((Equiv.ofBijective _ hWb).symm (S.emb i) - 1), sub_add_cancel]

end GlobalTheory.RedFun
