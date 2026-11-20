import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.RowA

/- English proof (translation)
Establish `h1 : 1 ≤ Formalism.MainNotions.TwistedPlaces.hB L` using `Formalism.MainNotions.TwistedPlaces.one_le_hB L`. Use `set h := Formalism.MainNotions.TwistedPlaces.hB L with hh`. Establish `hl' : (5 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Establish `hl1 : (1 : ℝ) < l` using `by linarith`.

Use `set a : ℝ := ((hN L : ℕ) : ℝ) with ha`. Establish `ha0 : 0 ≤ a` using `Nat.cast_nonneg _`. Establish `haN : a ≤ h` using `Nat.floor_le (by linarith)`. Establish `hlog1 : 0 ≤ Real.logb l (a + a + 1)` using `Real.logb_nonneg hl1 (by linarith)`. Establish `hlh : 0 ≤ Real.logb l h` using `Real.logb_nonneg hl1 h1`.

Establish `hlog2 : Real.logb l (a + a + 1) ≤ 1 + Real.logb l h`. Establish `hle : a + a + 1 ≤ l * h` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.logb_mul hl0.ne' (by linarith), Real.logb_self_eq_one hl1]`. Establish `hdiv : (a + a) / l ≤ 2 * (h / l)`.

Rewrite using `[mul_div_assoc']`. Conclude with `div_le_div_of_nonneg_right (by linarith) hl0.le`. Establish `hhl : 0 ≤ h / l` using `div_nonneg (by linarith) hl0.le`. Establish `hY : 1 ≤ 1 + h / l + Real.logb l h` using `by linarith`. Establish `hin : 1 + (a + a) / l + (1 + Real.logb l (a + a + 1)) ≤ 3 * (1 + h / l + Real.logb l h)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnn : 0 ≤ CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1)))`. Apply `mul_nonneg hCA` to reduce the goal to its premises. Establish `: 0 ≤ (a + a) / l` using `div_nonneg (by linarith) hl0.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hceil : (eA L CA l : ℝ) < CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) + 1`. Unfold `eA`. Use `push_cast`. Conclude with `Nat.ceil_lt_add_one hnn`. Establish `harg : CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) ≤ CA * (3 * (1 + h / l + Real.logb l h))` using `mul_le_mul_of_nonneg_left hin hCA`.

Establish `hE : (eA L CA l : ℝ) ≤ (3 * CA + 1) * (1 + h / l + Real.logb l h)` using `by nlinarith`. Unfold `Formalism.MainNotions.TwistedPlaces.eP`. Rewrite using `[← hh]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem two_eA_le {D : D7} (L : SizeData₂ D) {CA C : ℝ} (hCA : 0 ≤ CA) (hC : 2 * (3 * CA + 1) ≤ C)
    {l : ℕ} (hl : 5 ≤ l) : 2 * (eA L CA l : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.eP L C l := by
  have h1 : 1 ≤ Formalism.MainNotions.TwistedPlaces.hB L := Formalism.MainNotions.TwistedPlaces.one_le_hB L
  set h := Formalism.MainNotions.TwistedPlaces.hB L with hh
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0 : ℝ) < l := by linarith
  have hl1 : (1 : ℝ) < l := by linarith
  set a : ℝ := ((hN L : ℕ) : ℝ) with ha
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have haN : a ≤ h := Nat.floor_le (by linarith)
  have hlog1 : 0 ≤ Real.logb l (a + a + 1) := Real.logb_nonneg hl1 (by linarith)
  have hlh : 0 ≤ Real.logb l h := Real.logb_nonneg hl1 h1
  have hlog2 : Real.logb l (a + a + 1) ≤ 1 + Real.logb l h := by
    have hle : a + a + 1 ≤ l * h := by nlinarith
    calc Real.logb l (a + a + 1) ≤ Real.logb l (l * h) :=
          Real.logb_le_logb_of_le hl1 (by linarith) hle
      _ = 1 + Real.logb l h := by
          rw [Real.logb_mul hl0.ne' (by linarith), Real.logb_self_eq_one hl1]
  have hdiv : (a + a) / l ≤ 2 * (h / l) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hl0.le
  have hhl : 0 ≤ h / l := div_nonneg (by linarith) hl0.le
  have hY : 1 ≤ 1 + h / l + Real.logb l h := by linarith
  have hin : 1 + (a + a) / l + (1 + Real.logb l (a + a + 1)) ≤ 3 * (1 + h / l + Real.logb l h) := by
    linarith
  have hnn : 0 ≤ CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) := by
    apply mul_nonneg hCA
    have : 0 ≤ (a + a) / l := div_nonneg (by linarith) hl0.le
    linarith
  have hceil : (eA L CA l : ℝ) < CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) + 1 := by
    unfold eA
    push_cast
    exact Nat.ceil_lt_add_one hnn
  have harg : CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) ≤
      CA * (3 * (1 + h / l + Real.logb l h)) := mul_le_mul_of_nonneg_left hin hCA
  have hE : (eA L CA l : ℝ) ≤ (3 * CA + 1) * (1 + h / l + Real.logb l h) := by nlinarith
  unfold Formalism.MainNotions.TwistedPlaces.eP
  rw [← hh]
  nlinarith

/- English proof (translation)
Introduce `D L P HW X R C hD hR i _htw hcond`. Take `⟨h5, hsp, _, _⟩` from `hcond`. Take `⟨_, _, _, hCA, hC1, _, _, _, _, _, hCC⟩` from `hR`. Establish `hl0 : D.nd.l i ≠ 0` using `by omega`. Establish `hfin` using `FamilyRepresentationConstants.placesOver_finite D.host.E (D.nd.l i) hl0`.

Establish `he` using `two_eA_le L hCA hCC h5`. Establish `heP : 0 ≤ Formalism.MainNotions.TwistedPlaces.eP L C (D.nd.l i)` using `Formalism.MainNotions.TwistedPlaces.eP_nonneg L (by linarith) _`. Unfold `TwistedPlaces.sumOver`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `lam _`. Establish `hk : (0 : ℝ) ≤ 2 * (TwistedPlaces.nLam D lam : ℝ) * D.R.m + 1` using `by positivity`. Establish `hconst : (fun π => X.len0 i π lam) = fun _ => ((lenA i (X.dc i) (eA L R.CA (D.nd.l i)) lam : ℚ) : ℝ)`. Use function extensionality and compare the values at `π`. Rewrite using `[hD.len0S i hsp π lam, hD.eS i hsp]`.

Use `show 2 * KillingConditions.supZ i (fun π => X.len0 i π lam) ≤ _`. Rewrite using `[hconst]`. Unfold `KillingConditions.supZ`. Use `split_ifs with hne`. Rewrite using `[Finset.sup'_const]`.

Unfold `lenA`. Use `split_ifs`. Use `push_cast`. Establish `: (TwistedPlaces.nLam D lam : ℝ) = (locDeg D.host.E lam : ℝ)` using `rfl`. Rewrite using `[← this]`.

Use the polynomial consequences of the given equalities and inequalities. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.admA L (tabX L X) C := by
  intro D L P HW X R C hD hR i _htw hcond
  obtain ⟨h5, hsp, _, _⟩ := hcond
  obtain ⟨_, _, _, hCA, hC1, _, _, _, _, _, hCC⟩ := hR
  have hl0 : D.nd.l i ≠ 0 := by omega
  have hfin := FamilyRepresentationConstants.placesOver_finite D.host.E (D.nd.l i) hl0
  have he := two_eA_le L hCA hCC h5
  have heP : 0 ≤ Formalism.MainNotions.TwistedPlaces.eP L C (D.nd.l i) := Formalism.MainNotions.TwistedPlaces.eP_nonneg L (by linarith) _
  unfold TwistedPlaces.sumOver
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro lam _
  have hk : (0 : ℝ) ≤ 2 * (TwistedPlaces.nLam D lam : ℝ) * D.R.m + 1 := by positivity
  have hconst : (fun π => X.len0 i π lam) =
      fun _ => ((lenA i (X.dc i) (eA L R.CA (D.nd.l i)) lam : ℚ) : ℝ) := by
    funext π
    rw [hD.len0S i hsp π lam, hD.eS i hsp]
  show 2 * KillingConditions.supZ i (fun π => X.len0 i π lam) ≤ _
  rw [hconst]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    unfold lenA
    split_ifs
    · push_cast
      have : (TwistedPlaces.nLam D lam : ℝ) = (locDeg D.host.E lam : ℝ) := rfl
      rw [← this]
      nlinarith
    · push_cast; nlinarith
  · nlinarith

end GlobalTheory.NLink.RowA
