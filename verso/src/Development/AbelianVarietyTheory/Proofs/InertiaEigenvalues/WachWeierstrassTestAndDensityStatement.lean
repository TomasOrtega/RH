import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NL.WDiv.weierstrass_dense` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWachWeierstrassTestAndDensity.lean&line=284#L284)
-/
theorem _root_.GlobalTheory.T.wachWeierstrass_test_and_density : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; (∀ (k : ℕ) (a : AA K LL), (∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → a ∈ van W i ζ k) → W.Q ^ k ∣ a) ∧ (∀ (k : ℕ) (a : AA K LL), (∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 → a ∈ van W i ζ k) → W.X ^ k ∣ a) ∧ (∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ (f : PowerSeries ↥LL.1) (m : ℕ), ∃ (a : AA K LL) (c : ↥LL.1), c ≠ 0 ∧ PowerSeries.X ^ m ∣ c • W.lev i ζ a - f) ∧ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∀ (f : PowerSeries ↥LL.1) (m : ℕ), ∃ (a : AA K LL) (c : ↥LL.1), c ≠ 0 ∧ PowerSeries.X ^ m ∣ c • W.lev i ζ a - f ∧ ∀ (i' : Let K) (ζ' : ↥LL.1), IsPrimitiveRoot ζ' (l ^ s) → (i', ζ') ≠ (i, ζ) → a ∈ van W i' ζ' m := by
  first | exact @GlobalTheory.NL.WDiv.weierstrass_dense | exact GlobalTheory.NL.WDiv.weierstrass_dense | (intros; apply GlobalTheory.NL.WDiv.weierstrass_dense <;> assumption)
