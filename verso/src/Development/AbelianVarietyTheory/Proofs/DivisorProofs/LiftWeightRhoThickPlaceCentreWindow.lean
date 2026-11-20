import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Lift

variable {D : D7}

/- English proof (translation)
Establish `hmem : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces`. Simplify `hτ` using `[wts]`. Establish `hm2` using `D.R.two_le_m`. Establish `hj` using `j.2`. Establish `h1` using `L.win_thick ((j : ℕ) + 1) (by omega) (by omega) τ hmem`.

Establish `h2` using `L.win_thick D.R.m (by omega) le_rfl τ hmem`. Establish `hc` using `c_le L j τ hv`. Establish `hb : (parOf L j).b = L.sc.b` using `rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (parOf L j).b ≤ wj D ((j : ℕ) + 1) τ ∧ wj D ((j : ℕ) + 1) τ ≤ (parOf L j).b + L.etaSz + 1`.

Rewrite using `[hb]`. Conclude with `h1`. Establish `hfl : ((wts L j).xp τ : ℝ) ≤ cT j τ + L.Sc` using `by show ((⌊cT j τ + L.Sc⌋ : ℤ) : ℝ) ≤ cT j τ + L.Sc`. Conclude with `Int.floor_le _`. Establish `hc' : cT j τ ≤ wj D D.R.m τ + ((D.R.t : ℝ) - 1) / 2` using `hc`.

Establish `ht : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`. Use `show ((wts L j).xp τ : ℝ) ≤ (parOf L j).b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1`. Rewrite using `[hb]`. Combine the linear relations using `[h2.2]`.
-/
theorem thick_of_mem (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (hv : ValsAt L j τ)
    (hτ : τ ∈ (wts L j).T2) :
    (parOf L j).Thick ((wts L j).e τ) ∧ ((wts L j).xp τ : ℝ) ≤ (parOf L j).h := by
  have hmem : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces := by
    simpa [wts] using hτ
  have hm2 := D.R.two_le_m
  have hj := j.2
  have h1 := L.win_thick ((j : ℕ) + 1) (by omega) (by omega) τ hmem
  have h2 := L.win_thick D.R.m (by omega) le_rfl τ hmem
  have hc := c_le L j τ hv
  have hb : (parOf L j).b = L.sc.b := rfl
  refine ⟨?_, ?_⟩
  · show (parOf L j).b ≤ wj D ((j : ℕ) + 1) τ ∧ wj D ((j : ℕ) + 1) τ ≤ (parOf L j).b + L.etaSz + 1
    rw [hb]; exact h1
  · have hfl : ((wts L j).xp τ : ℝ) ≤ cT j τ + L.Sc := by
      show ((⌊cT j τ + L.Sc⌋ : ℤ) : ℝ) ≤ cT j τ + L.Sc
      exact Int.floor_le _
    have hc' : cT j τ ≤ wj D D.R.m τ + ((D.R.t : ℝ) - 1) / 2 := hc
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    show ((wts L j).xp τ : ℝ) ≤ (parOf L j).b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1
    rw [hb]
    linarith [h2.2]

end GlobalTheory.ExpTie.Lift

end
