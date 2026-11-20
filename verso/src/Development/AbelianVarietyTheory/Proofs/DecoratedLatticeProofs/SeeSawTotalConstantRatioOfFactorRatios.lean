import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioParts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRootOfSUnitRatioUpToRootOfUnityClosureLaws
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

/- English proof (translation)
Introduce `D c v 𝒯 t w S s₀ hIs hCV hkap hcG hscK hTQ hcP n hn s`. Take `⟨hrefl, hmul, -, hprod⟩` from `GlobalTheory.Fam.unitRatio_laws (S s)`. Establish `split : ∀ (f : ℕ → ℂ) (k : ℕ), ∏ j ∈ Finset.range (2 * k), f j = ∏ i ∈ Finset.range k, (f (2 * i) * f (2 * i + 1))`. Introduce `f k`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih, Finset.prod_range_succ, mul_assoc]`. Establish `hIs' : ∀ s j, j < D.R.m → (t s).cI j ≠ 0` using `fun s j hj => (hIs s).cI j hj`. Establish `hκ : ∀ i, i < n → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ s, (t s).cV (2 * i) = κ * ((w s).sc (2 * i) * (w s).sc (2 * i + 1)) * (w s).cQ (2 * i) * v.cG (2 * i) * (w s).cT (2 * i)`.

Introduce `i hi`. Distinguish the cases in `hlast : i + 1 = n`. Use `⟨1, one_ne_zero, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[one_mul]`. Conclude with `(hCV s).2 (2 * i) (by omega)`.

Conclude with `⟨v.kap (2 * i) (n - i - 2) (by omega), hkap _ _ _, fun s => (hCV s).1 (2 * i) (n - i - 2) (by omega)⟩`. Establish `hB : ∀ i, i < n → UnitRatio (S s) ((t s).cV (2 * i) * (t s).cK (2 * i) * (t s).cK (2 * i + 1) / ((t s).cI (2 * i) * (t s).cI (2 * i + 1))) ((t s₀).cV (2 * i) * (t s₀).cK (2 * i) * (t s₀).cK (2 * i + 1) / ((t s₀).cI (2 * i) * (t s₀).cI (2 * i + 1)))`. Introduce `i hi`. Take `⟨κ, hκ0, hκs⟩` from `hκ i hi`. Establish `hK0 : κ * v.cG (2 * i) ≠ 0` using `mul_ne_zero hκ0 (hcG _)`.

Establish `hform : ∀ s', (t s').cV (2 * i) * (t s').cK (2 * i) * (t s').cK (2 * i + 1) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1)) = κ * v.cG (2 * i) * ((w s').sc (2 * i) * (w s').sc (2 * i + 1) * (w s').cT (2 * i) * ((w s').cQ (2 * i) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1))) * ((t …`. Introduce `s'`. Rewrite using `[hκs s']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hform s, hform s₀]`.

Establish `hsc1` using `(hscK s (2 * i) (by omega)).1`. Establish `hsc2` using `(hscK s (2 * i + 1) (by omega)).1`. Establish `homogComponent_comm_first_action` using `(hscK s (2 * i) (by omega)).2`. Establish `homogComponent_comm_second_action` using `(hscK s (2 * i + 1) (by omega)).2`. Establish `hcT` using `(hTQ s (2 * i) (n - i - 1) (by omega)).1`.

Establish `hcQ` using `(hTQ s (2 * i) (n - i - 1) (by omega)).2`. Conclude with `(hmul _ _ _ _ (hrefl _ hK0) (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ hsc1 hsc2).1 hcT).1 hcQ).1 (hmul _ _ _ _ homogComponent_comm_first_action homogComponent_comm_second_action).1).1).1`. Establish `hq : ∀ s', (t s').cTop n / (t s').cBot = (∏ i ∈ Finset.range n, ((t s').cV (2 * i) * (t s').cK (2 * i) * (t s').cK (2 * i + 1) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1)))) * (t s').cP`. Introduce `s'`. Unfold `Tup.cTop Tup.cBot`.

Rewrite using `[← hn, split (fun j => (t s').cI j) n, Finset.prod_div_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hall : UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot)`. Rewrite using `[hq s, hq s₀]`. Conclude with `(hmul _ _ _ _ (hprod ℕ (Finset.range n) _ _ fun i hi => hB i (Finset.mem_range.mp hi)) (hcP s)).1`.

Establish `hbot : (t s).cBot ≠ 0`. Unfold `Tup.cBot`. Conclude with `Finset.prod_ne_zero_iff.mpr fun j hj => hIs' s j (Finset.mem_range.mp hj)`. Establish `hne` using `(hmul _ _ _ _ hall hall).2.2`. Use `⟨fun h0 => hne ?_, hbot, hall⟩` and prove the remaining obligations.

Rewrite using `[h0, zero_div]`.
-/
theorem ratio_total_unitRatio_of_parts : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)) (S : 𝒯 → ℕ → Prop) (s₀ : 𝒯), (∀ s, (t s).Is) → (∀ s, CVEq v (w s)) → (∀ j σ h, v.kap j σ h ≠ 0) → (∀ j, v.cG j ≠ 0) → (∀ s j, j < D.R.m → UnitRatio (S s) ((w s).sc j) ((w s₀).sc j) ∧ UnitRatio (S s) ((t s).cK j) ((t s₀).cK j)) → (∀ s j ρ, j + 2 * ρ + 2 = D.R.m → UnitRatio (S s) ((w s).cT j) ((w s₀).cT j) ∧ UnitRatio (S s) ((w s).cQ j / ((t s).cI j * (t s).cI (j + 1))) ((w s₀).cQ j / ((t s₀).cI j * (t s₀).cI (j + 1)))) → (∀ s, UnitRatio (S s) (t s).cP (t s₀).cP) → ∀ n, 2 * n = D.R.m → ∀ s, (t s).cTop n ≠ 0 ∧ (t s).cBot ≠ 0 ∧ UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot) := by
  intro D c v 𝒯 t w S s₀ hIs hCV hkap hcG hscK hTQ hcP n hn s
  obtain ⟨hrefl, hmul, -, hprod⟩ := GlobalTheory.Fam.unitRatio_laws (S s)
  have split : ∀ (f : ℕ → ℂ) (k : ℕ), ∏ j ∈ Finset.range (2 * k), f j =
      ∏ i ∈ Finset.range k, (f (2 * i) * f (2 * i + 1)) := by
    intro f k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
        Finset.prod_range_succ, mul_assoc]
  have hIs' : ∀ s j, j < D.R.m → (t s).cI j ≠ 0 := fun s j hj => (hIs s).cI j hj
  have hκ : ∀ i, i < n → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ s, (t s).cV (2 * i) =
      κ * ((w s).sc (2 * i) * (w s).sc (2 * i + 1)) * (w s).cQ (2 * i) * v.cG (2 * i) * (w s).cT (2 * i) := by
    intro i hi
    by_cases hlast : i + 1 = n
    · refine ⟨1, one_ne_zero, fun s => ?_⟩
      rw [one_mul]
      exact (hCV s).2 (2 * i) (by omega)
    · exact ⟨v.kap (2 * i) (n - i - 2) (by omega), hkap _ _ _, fun s => (hCV s).1 (2 * i) (n - i - 2) (by omega)⟩
  have hB : ∀ i, i < n → UnitRatio (S s)
      ((t s).cV (2 * i) * (t s).cK (2 * i) * (t s).cK (2 * i + 1) / ((t s).cI (2 * i) * (t s).cI (2 * i + 1)))
      ((t s₀).cV (2 * i) * (t s₀).cK (2 * i) * (t s₀).cK (2 * i + 1) / ((t s₀).cI (2 * i) * (t s₀).cI (2 * i + 1))) := by
    intro i hi
    obtain ⟨κ, hκ0, hκs⟩ := hκ i hi
    have hK0 : κ * v.cG (2 * i) ≠ 0 := mul_ne_zero hκ0 (hcG _)
    have hform : ∀ s', (t s').cV (2 * i) * (t s').cK (2 * i) * (t s').cK (2 * i + 1) /
        ((t s').cI (2 * i) * (t s').cI (2 * i + 1)) =
        κ * v.cG (2 * i) *
          ((w s').sc (2 * i) * (w s').sc (2 * i + 1) * (w s').cT (2 * i) *
            ((w s').cQ (2 * i) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1))) *
            ((t s').cK (2 * i) * (t s').cK (2 * i + 1))) := by
      intro s'
      rw [hκs s']
      ring
    rw [hform s, hform s₀]
    have hsc1 := (hscK s (2 * i) (by omega)).1
    have hsc2 := (hscK s (2 * i + 1) (by omega)).1
    have homogComponent_comm_first_action := (hscK s (2 * i) (by omega)).2
    have homogComponent_comm_second_action := (hscK s (2 * i + 1) (by omega)).2
    have hcT := (hTQ s (2 * i) (n - i - 1) (by omega)).1
    have hcQ := (hTQ s (2 * i) (n - i - 1) (by omega)).2
    exact (hmul _ _ _ _ (hrefl _ hK0)
      (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ hsc1 hsc2).1 hcT).1 hcQ).1
        (hmul _ _ _ _ homogComponent_comm_first_action homogComponent_comm_second_action).1).1).1
  have hq : ∀ s', (t s').cTop n / (t s').cBot = (∏ i ∈ Finset.range n,
      ((t s').cV (2 * i) * (t s').cK (2 * i) * (t s').cK (2 * i + 1) / ((t s').cI (2 * i) * (t s').cI (2 * i + 1)))) *
      (t s').cP := by
    intro s'
    unfold Tup.cTop Tup.cBot
    rw [← hn, split (fun j => (t s').cI j) n, Finset.prod_div_distrib]
    ring
  have hall : UnitRatio (S s) ((t s).cTop n / (t s).cBot) ((t s₀).cTop n / (t s₀).cBot) := by
    rw [hq s, hq s₀]
    exact (hmul _ _ _ _ (hprod ℕ (Finset.range n) _ _ fun i hi => hB i (Finset.mem_range.mp hi)) (hcP s)).1
  have hbot : (t s).cBot ≠ 0 := by
    unfold Tup.cBot
    exact Finset.prod_ne_zero_iff.mpr fun j hj => hIs' s j (Finset.mem_range.mp hj)
  have hne := (hmul _ _ _ _ hall hall).2.2
  refine ⟨fun h0 => hne ?_, hbot, hall⟩
  rw [h0, zero_div]

end GlobalTheory.SeeSaw
