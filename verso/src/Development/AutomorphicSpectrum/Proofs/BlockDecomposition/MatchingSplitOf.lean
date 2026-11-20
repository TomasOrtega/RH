import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSphNe

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
open PositivityTheory.Rg.BcB.F.Eig (lconv)
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace GlobalTheory.CompanionTheory.MatchPowers

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem isLevel_KL (n : ℕ) (w : Pl E) : IsLevel (MonoidHom.id _) (KL n w) (KL n w) :=
  ⟨GlobalTheory.CompanionTheory.SphLine.isOpen_KL n w, le_rfl, fun _ h => h⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isHecke_lpow_KL {n : ℕ} {w : Pl E} {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) (j : ℕ) :
    IsHecke (KL n w) (lpow (KL n w) f j) :=
  GlobalTheory.CompanionTheory.UnitaryWord.isHecke_lpow GlobalTheory.CompanionTheory.LocHecke.locAlg (isLevel_KL n w) hf j

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem matchSplitOf : MatchSplitOf := by
  intro hM3 hCt E _ _ _ n a ha w hw μ hμ f hf k hk
  have hc : ∀ j : ℕ, ctMu (Nat.add_sub_cancel' ha) w μ (lpow (KL n w) f j) =
      Nat.rec (ctMu (Nat.add_sub_cancel' ha) w μ (lone (KL n w)))
        (fun _ g => mconv (ctMu (Nat.add_sub_cancel' ha) w μ f) g) j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have h := hCt E n a ha w hw μ hμ f _ hf (isHecke_lpow_KL hf j)
      rw [ih] at h
      exact h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := hM3 E n a ha w hw μ (KL n w) (isLevel_KL n w) _ (isHecke_lpow_KL hf (j + 1))
  rw [hc (j + 1)] at h
  exact h

end GlobalTheory.CompanionTheory.MatchPowers

end
