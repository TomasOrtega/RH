import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTmulOneOfFrobFixedOfMemFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingsRegularPhiSurjectiveFil
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.FundSeq

/- English proof (translation)
Introduce `l _ P AI hT K LL _ _ V _ _ _ _`. Take `⟨-, h1, h2⟩` from `GlobalTheory.MemLoc.tied_regular_and_onto l P AI hT`. Establish `hA : ∀ u : V ⊗[ℚ_[l]] P.R.B, ∃ x : V ⊗[ℚ_[l]] P.R.B, x - φVB (P.PD K) (LL` using `LL) (V := V) x = u := by`. Introduce `u`. Proceed by induction on `u using TensorProduct.induction_on with`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul v b`. Take `⟨x, hx⟩` from `h1 b`. Use `⟨v ⊗ₜ x, ?_⟩` and prove the remaining obligations. Establish `: φVB (P.PD K) (LL` using `LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).φ x := rfl`.

Rewrite using `[this, P.PD_φ, ← TensorProduct.tmul_sub, hx]`. Consider the case `add u u' hu hu'`. Take `⟨x, hx⟩` from `hu`. Take `⟨x', hx'⟩` from `hu'`. Use `⟨x + x', ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, ← hx, ← hx']`. Normalize the expressions using the abelian group laws. Establish `hB : ∀ w : V ⊗[ℚ_[l]] P.R.BdR, ∃ x : V ⊗[ℚ_[l]] P.R.B, φVB (P.PD K) (LL` using `LL) (V := V) x = x ∧ ιV (P.PD K) (LL := LL) (V := V) x - w ∈ FilV (P.PD K) (LL := LL) (V := V) 0 := by`. Introduce `w`. Proceed by induction on `w using TensorProduct.induction_on with`.

Consider the case `zero => exact ⟨0, by simp, by simp⟩`. Consider the case `tmul v b`. Take `⟨x, hx, hx'⟩` from `h2 K b`. Use `⟨v ⊗ₜ x, ?_, ?_⟩` and prove the remaining obligations. Establish `: φVB (P.PD K) (LL` using `LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).φ x := rfl`.

Rewrite using `[this, P.PD_φ, hx]`. Establish `: ιV (P.PD K) (LL` using `LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).ι x := rfl`. Rewrite using `[this, P.PD_ι, ← TensorProduct.tmul_sub]`. Conclude with `⟨v ⊗ₜ ⟨P.ιB x - b, hx'⟩, rfl⟩`. Consider the case `add w w' hw hw'`.

Take `⟨x, hx, hy⟩` from `hw`. Take `⟨x', hx', hy'⟩` from `hw'`. Use `⟨x + x', by rw [map_add, hx, hx'], ?_⟩` and prove the remaining obligations. Use `Submodule.add_mem _ hy hy'` as an intermediate fact. Rewrite using `[map_add]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Use `⟨fun u w => ?_, fun x hx hF => GlobalTheory.exists_tmul_one_of_frob_fixed_of_mem_fil_zero (P.PD K) x hx hF⟩` and prove the remaining obligations. Take `⟨x₀, hx₀⟩` from `hA u`. Take `⟨x₁, hx₁, hy⟩` from `hB (w - ιV (P.PD K) (LL := LL) (V := V) x₀)`.

Use `⟨x₀ + x₁, _, hy, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hx₁, ← hx₀]`. Normalize the expressions using the abelian group laws. Rewrite using `[map_add]`. Normalize the expressions using the abelian group laws.
-/
theorem tensor_fundamental_sequence :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V], (∀ (u : V ⊗[ℚ_[l]] P.R.B) (w : V ⊗[ℚ_[l]] P.R.BdR), ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := LL) (V := V) 0 ∧ x - φVB (P.PD K) (LL := LL) (V := V) x = u ∧ ιV (P.PD K) (LL := LL) (V := V) x - y = w) ∧ ∀ x : V ⊗[ℚ_[l]] P.R.B, φVB (P.PD K) (LL := LL) (V := V) x = x → ιV (P.PD K) (LL := LL) (V := V) x ∈ FilV (P.PD K) (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
  intro l _ P AI hT K LL _ _ V _ _ _ _
  obtain ⟨-, h1, h2⟩ := GlobalTheory.MemLoc.tied_regular_and_onto l P AI hT
  have hA : ∀ u : V ⊗[ℚ_[l]] P.R.B, ∃ x : V ⊗[ℚ_[l]] P.R.B,
      x - φVB (P.PD K) (LL := LL) (V := V) x = u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul v b =>
      obtain ⟨x, hx⟩ := h1 b
      refine ⟨v ⊗ₜ x, ?_⟩
      have : φVB (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).φ x := rfl
      rw [this, P.PD_φ, ← TensorProduct.tmul_sub, hx]
    | add u u' hu hu' =>
      obtain ⟨x, hx⟩ := hu
      obtain ⟨x', hx'⟩ := hu'
      refine ⟨x + x', ?_⟩
      rw [map_add, ← hx, ← hx']
      abel
  have hB : ∀ w : V ⊗[ℚ_[l]] P.R.BdR, ∃ x : V ⊗[ℚ_[l]] P.R.B,
      φVB (P.PD K) (LL := LL) (V := V) x = x ∧
        ιV (P.PD K) (LL := LL) (V := V) x - w ∈ FilV (P.PD K) (LL := LL) (V := V) 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul v b =>
      obtain ⟨x, hx, hx'⟩ := h2 K b
      refine ⟨v ⊗ₜ x, ?_, ?_⟩
      · have : φVB (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).φ x := rfl
        rw [this, P.PD_φ, hx]
      · have : ιV (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).ι x := rfl
        rw [this, P.PD_ι, ← TensorProduct.tmul_sub]
        exact ⟨v ⊗ₜ ⟨P.ιB x - b, hx'⟩, rfl⟩
    | add w w' hw hw' =>
      obtain ⟨x, hx, hy⟩ := hw
      obtain ⟨x', hx', hy'⟩ := hw'
      refine ⟨x + x', by rw [map_add, hx, hx'], ?_⟩
      have := Submodule.add_mem _ hy hy'
      rw [map_add]
      convert this using 1
      abel
  refine ⟨fun u w => ?_, fun x hx hF =>
    GlobalTheory.exists_tmul_one_of_frob_fixed_of_mem_fil_zero (P.PD K) x hx hF⟩
  obtain ⟨x₀, hx₀⟩ := hA u
  obtain ⟨x₁, hx₁, hy⟩ := hB (w - ιV (P.PD K) (LL := LL) (V := V) x₀)
  refine ⟨x₀ + x₁, _, hy, ?_, ?_⟩
  · rw [map_add, hx₁, ← hx₀]
    abel
  · rw [map_add]
    abel

end GlobalTheory.FundSeq
