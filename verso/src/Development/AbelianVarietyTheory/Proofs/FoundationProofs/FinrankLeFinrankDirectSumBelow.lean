import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSsIdxInjective
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

/- English proof (translation)
Take `⟨b, ⟨hli, hb, -⟩, -⟩` from `sSBasis K N N lam.natW`. Establish `: Finite (ssIdx N N lam.natW)` using `(sSIdxFinite N N _).to_subtype`. Use `Fintype.ofFinite (ssIdx N N lam.natW)` as an intermediate fact. Unfold `nablaSq`. Rewrite using `[← hb, finrank_span_eq_card hli, Nat.card_eq_fintype_card]`.
-/
theorem finrank_nablaSq_eq_card (K : Type) [Field K] (N : ℕ) (lam : DomWeight N) :
    Module.finrank K (nablaSq K N lam) = Nat.card (ssIdx N N lam.natW) := by
  obtain ⟨b, ⟨hli, hb, -⟩, -⟩ := sSBasis K N N lam.natW
  have : Finite (ssIdx N N lam.natW) := (sSIdxFinite N N _).to_subtype
  have := Fintype.ofFinite (ssIdx N N lam.natW)
  unfold nablaSq
  rw [← hb, finrank_span_eq_card hli, Nat.card_eq_fintype_card]

/- English proof (translation)
Take `⟨F, hF⟩` from `GlobalTheory.Branching.exists_ssIdx_injective n N h lam`. Use `Fintype.ofFinite (Below h lam)` as an intermediate fact. Establish `: ∀ mu : Below h lam, Finite (ssIdx n n mu.1.natW)` using `fun mu => (sSIdxFinite n n _).to_subtype`. Rewrite using `[Module.finrank_directSum, finrank_nablaSq_eq_card]`. Simplify using `only [finrank_nablaSq_eq_card]`.

Rewrite using `[← Nat.card_sigma]`. Conclude with `Nat.card_le_card_of_injective F hF`.
-/
theorem finrank_le_finrank_directSum_below (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) :
    Module.finrank ℂ (nablaSq ℂ N lam) ≤ Module.finrank ℂ (⨁ mu : Below h lam, nablaSq ℂ n mu.1) := by
  obtain ⟨F, hF⟩ := GlobalTheory.Branching.exists_ssIdx_injective n N h lam
  have := Fintype.ofFinite (Below h lam)
  have : ∀ mu : Below h lam, Finite (ssIdx n n mu.1.natW) := fun mu => (sSIdxFinite n n _).to_subtype
  rw [Module.finrank_directSum, finrank_nablaSq_eq_card]
  simp only [finrank_nablaSq_eq_card]
  rw [← Nat.card_sigma]
  exact Nat.card_le_card_of_injective F hF

end GlobalTheory.Branching
