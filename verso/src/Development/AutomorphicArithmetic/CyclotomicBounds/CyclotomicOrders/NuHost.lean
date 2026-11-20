import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuRecord

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

namespace UpperTheory.KStar

/- English proof (translation)
Unfold `TwistedPlaces.nuL`. Rewrite using `[dif_pos (D.ntw.lPrime i).out]`. Both sides reduce to the same expression.
-/
theorem nu_eq_nuL {D : D7} (i : D.ntw.Tw) : (BlochKatoReduction.Gen.nu D.ntw i : ℝ) = TwistedPlaces.nuL D (D.ntw.l i) := by
  unfold TwistedPlaces.nuL
  rw [dif_pos (D.ntw.lPrime i).out]
  rfl

def nuBudget (D : D7) : ℝ := Real.log (D.host.QS : ℝ) + Real.log ((D.R.t * D.R.r : ℕ) : ℝ)

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨k, rfl⟩ : ∃ k, l = D.host.g k := by`. Break down `Finset.mem_insert.1 h with h | h` into its components or cases. Conclude with `⟨0, h⟩`. Conclude with `⟨1, Finset.mem_singleton.1 h⟩`. Use `haveI := Fact.mk (D.host.g_prime k)`.

Unfold `TwistedPlaces.nuL`. Rewrite using `[dif_pos (D.host.g_prime k), Nat.cast_eq_zero]`. Conclude with `UpperTheory.Mu.nu_eq_zero_of_split D.host D.nd.Om _ (D.nd.g_split k)`.
-/
theorem nuL_eq_zero_of_g (D : D7) (l : ℕ) (h : l ∈ TwistedPlaces.gset D) (_h2 : l ≠ 2) : TwistedPlaces.nuL D l = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, l = D.host.g k := by
    rcases Finset.mem_insert.1 h with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, Finset.mem_singleton.1 h⟩
  haveI := Fact.mk (D.host.g_prime k)
  unfold TwistedPlaces.nuL
  rw [dif_pos (D.host.g_prime k), Nat.cast_eq_zero]
  exact UpperTheory.Mu.nu_eq_zero_of_split D.host D.nd.Om _ (D.nd.g_split k)

/- English proof (translation)
Unfold `TwistedPlaces.nuL`. Use `split_ifs with hl`. Use `haveI := Fact.mk hl`. Rewrite using `[Nat.cast_eq_zero]`. Conclude with `UpperTheory.Mu.nu_eq_zero_of_qd D.host D.nd.Om l h`.

Both sides reduce to the same expression.
-/
theorem nuL_eq_zero_of_qd (D : D7) (l : ℕ) (h : l = D.host.q ∨ l = D.host.d) : TwistedPlaces.nuL D l = 0 := by
  unfold TwistedPlaces.nuL
  split_ifs with hl
  · haveI := Fact.mk hl
    rw [Nat.cast_eq_zero]
    exact UpperTheory.Mu.nu_eq_zero_of_qd D.host D.nd.Om l h
  · rfl

/- English proof (translation)
The claim follows from `UpperTheory.Mu.sum_nu_le D.host D.nd.Om (TwistedPlaces.nuL D) (fun _ hl => dif_pos hl.out) S hS`.
-/
theorem sum_nuL_le (D : D7) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    ∑ l ∈ S, TwistedPlaces.nuL D l * Real.log l ≤ nuBudget D :=
  UpperTheory.Mu.sum_nu_le D.host D.nd.Om (TwistedPlaces.nuL D) (fun _ hl => dif_pos hl.out) S hS

/- English proof (translation)
The claim follows from `UpperTheory.Mu.budget_le D.host`.
-/
theorem nuBudget_le (D : D7) : nuBudget D ≤ 2 * Real.log D.R.n + Real.log D.R.t + Real.log D.R.r :=
  UpperTheory.Mu.budget_le D.host

end UpperTheory.KStar
