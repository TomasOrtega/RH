import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WspOrth

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Unfold `trOn`. Use `split_ifs with h`. Establish `: Subsingleton (⊥ : Submodule ℂ V)` using `inferInstance`. Establish `h0 : L.restrict h = 0` using `Subsingleton.elim _ _`. Rewrite using `[h0, map_zero]`.

Both sides reduce to the same expression.
-/
private theorem trOn_bot' {V : Type} [AddCommGroup V] [Module ℂ V] (L : V →ₗ[ℂ] V) :
    trOn (⊥ : Submodule ℂ V) L = 0 := by
  unfold trOn
  split_ifs with h
  · have : Subsingleton (⊥ : Submodule ℂ V) := inferInstance
    have h0 : L.restrict h = 0 := Subsingleton.elim _ _
    rw [h0, map_zero]
  · rfl

/- English proof (translation)
Simplify using `[cf, ex, AddMonoidAlgebra.coeff, Finsupp.finset_sum_apply, Finsupp.single_apply]`.
-/
private theorem cf_sum {n : ℕ} (s : Finset (Wt n)) (g : Wt n → ℂ) (μ : Wt n) :
    cf (∑ x ∈ s, g x • ex x) μ = if μ ∈ s then g μ else 0 := by
  classical
  simp [cf, ex, AddMonoidAlgebra.coeff, Finsupp.finset_sum_apply, Finsupp.single_apply]

/- English proof (translation)
Introduce `n V _ _ F hF S hS hSt B`. Take `⟨s, hs, -, -⟩` from `wtDec n V F hF S hS hSt`. Use `⟨∑ μ ∈ s, trOn (wsp F μ ⊓ S) B • ex μ, fun μ => ?_⟩` and prove the remaining obligations. Rewrite using `[cf_sum]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Rewrite using `[hs μ h, trOn_bot']`.
-/
theorem UpperTheory.RealTr.chEx :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ B, ∃ c, IsCh F S B c := by
  intro n V _ _ F hF S hS hSt B
  obtain ⟨s, hs, -, -⟩ := wtDec n V F hF S hS hSt
  refine ⟨∑ μ ∈ s, trOn (wsp F μ ⊓ S) B • ex μ, fun μ => ?_⟩
  rw [cf_sum]
  split_ifs with h
  · rfl
  · rw [hs μ h, trOn_bot']
