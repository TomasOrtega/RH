import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LatCoordA
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LatCoordB
import Formalism.PairingDivisors.PairingDivisorProofs.ValAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Take `⟨s, hs, hs'⟩` from `hx`. Take `⟨t, ht, ht'⟩` from `hy`. Use `⟨s * t, by rw [map_mul, hs, ht], ?_⟩` and prove the remaining obligations. Break down `hs' with h0 | h1` into its components or cases. Use `left`.

Simplify using `[h0]`. Break down `ht' with h0 | h2` into its components or cases. Use `left`. Simplify using `[h0]`. Distinguish the cases in `hs0 : s = 0`.

Use `left`. Simplify using `[hs0]`. Distinguish the cases in `ht0 : t = 0`. Use `left`. Simplify using `[ht0]`.

Use `right`. Rewrite using `[Formalism.DivisionValues.ValuationRepresentative.vw_mul w s t hs0 ht0]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem lossLe_mul_wild_jets {D : D7} (w : PlL D) {x y : ℂ} {a b : ℝ}
    (hx : LossLe w x a) (hy : LossLe w y b) : LossLe w (x * y) (a + b) := by
  obtain ⟨s, hs, hs'⟩ := hx
  obtain ⟨t, ht, ht'⟩ := hy
  refine ⟨s * t, by rw [map_mul, hs, ht], ?_⟩
  rcases hs' with h0 | h1
  · left; simp [h0]
  rcases ht' with h0 | h2
  · left; simp [h0]
  by_cases hs0 : s = 0
  · left; simp [hs0]
  by_cases ht0 : t = 0
  · left; simp [ht0]
  right
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w s t hs0 ht0]
  push_cast
  linarith
/- English proof (translation)
Take `⟨s, hs, hs'⟩` from `hx`. Take `⟨t, ht, ht'⟩` from `hy`. Use `⟨s + t, by rw [map_add, hs, ht], ?_⟩` and prove the remaining obligations. Distinguish the cases in `hs0 : s = 0`. Substitute `hs0` using the available equality.

Simplify using `using ht'`. Distinguish the cases in `ht0 : t = 0`. Substitute `ht0` using the available equality. Simplify using `using hs'`. Distinguish the cases in `hst : s + t = 0`.

Use `left`. Conclude with `hst`. Use `right`. Establish `h1 : -a ≤ (vw w s : ℝ)` using `hs'.resolve_left hs0`. Establish `h2 : -a ≤ (vw w t : ℝ)` using `ht'.resolve_left ht0`.

Establish `h3` using `Formalism.PairingDivisionLocalBalance.vw_add w s t hs0 ht0 hst`. Establish `h4 : ((min (vw w s) (vw w t) : ℤ) : ℝ) ≤ (vw w (s + t) : ℝ)` using `by exact_mod_cast h3`. Rewrite `h4` using `[Int.cast_min]`. Conclude with `le_trans (le_min h1 h2) h4`.
-/
private theorem lossLe_add {D : D7} (w : PlL D) {x y : ℂ} {a : ℝ}
    (hx : LossLe w x a) (hy : LossLe w y a) : LossLe w (x + y) a := by
  obtain ⟨s, hs, hs'⟩ := hx
  obtain ⟨t, ht, ht'⟩ := hy
  refine ⟨s + t, by rw [map_add, hs, ht], ?_⟩
  by_cases hs0 : s = 0
  · subst hs0; simpa using ht'
  by_cases ht0 : t = 0
  · subst ht0; simpa using hs'
  by_cases hst : s + t = 0
  · left; exact hst
  right
  have h1 : -a ≤ (vw w s : ℝ) := hs'.resolve_left hs0
  have h2 : -a ≤ (vw w t : ℝ) := ht'.resolve_left ht0
  have h3 := Formalism.PairingDivisionLocalBalance.vw_add w s t hs0 ht0 hst
  have h4 : ((min (vw w s) (vw w t) : ℤ) : ℝ) ≤ (vw w (s + t) : ℝ) := by exact_mod_cast h3
  rw [Int.cast_min] at h4
  exact le_trans (le_min h1 h2) h4
/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨0, by simp, Or.inl rfl⟩`. Consider the case `insert j S hj ih`. Rewrite using `[Finset.sum_insert hj]`. Conclude with `lossLe_add w (hg j (Finset.mem_insert_self j S)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))`.
-/
private theorem lossLe_finset_sum {D : D7} (w : PlL D) {ι : Type*} (S : Finset ι) (g : ι → ℂ) {a : ℝ}
    (hg : ∀ i ∈ S, LossLe w (g i) a) : LossLe w (∑ i ∈ S, g i) a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp, Or.inl rfl⟩
  | insert j S hj ih =>
    rw [Finset.sum_insert hj]
    exact lossLe_add w (hg j (Finset.mem_insert_self j S))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `D n n' lam lam' w l hl hlw Λ Λ' hΛ hΛ' f c hf a v hv`. Apply `UpperTheory.WildA.latCoordB D lam' w l hl hlw Λ' hΛ' (a + c) (f v)` to reduce the goal to its premises. Introduce `i`. Establish `hv'` using `UpperTheory.WildA.latCoordA D lam w l hl hlw Λ hΛ a v hv`. Establish `hsum` using `(bVV ℂ lam).sum_repr v`.

Establish `hrepr : (bVV ℂ lam').repr (f v) i = ∑ j, (bVV ℂ lam).repr v j * (bVV ℂ lam').repr (f (bVV ℂ lam j)) i`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sum, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]`.

Rewrite using `[hrepr]`. Conclude with `lossLe_finset_sum w _ _ fun j _ => lossLe_mul_wild_jets w (hv' j) (hf i j)`.
-/
theorem UpperTheory.WildA.matLat :
    ∀ (D : D7) {n n' : ℕ} (lam : D.what₂.Tau → DomWeight n) (lam' : D.what₂.Tau → DomWeight n') (w : PlL D) (l : ℕ), l.Prime →
      (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)),
      Formalism.MainNotions.TaylorLogMetric.EqAt D l Λ (Formalism.MainNotions.StandardLatticesGL3.stdL D n) → Formalism.MainNotions.TaylorLogMetric.EqAt D l Λ' (Formalism.MainNotions.StandardLatticesGL3.stdL D n') →
      ∀ (f : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (c : ℝ), (∀ i j, LossLe w ((bVV ℂ lam').repr (f (bVV ℂ lam j)) i) c) →
      ∀ (a : ℝ) (v : VV ℂ lam), InLat lam w a Λ v → InLat lam' w (a + c) Λ' (f v) := by
  intro D n n' lam lam' w l hl hlw Λ Λ' hΛ hΛ' f c hf a v hv
  apply UpperTheory.WildA.latCoordB D lam' w l hl hlw Λ' hΛ' (a + c) (f v)
  intro i
  have hv' := UpperTheory.WildA.latCoordA D lam w l hl hlw Λ hΛ a v hv
  have hsum := (bVV ℂ lam).sum_repr v
  have hrepr : (bVV ℂ lam').repr (f v) i =
      ∑ j, (bVV ℂ lam).repr v j * (bVV ℂ lam').repr (f (bVV ℂ lam j)) i := by
    calc (bVV ℂ lam').repr (f v) i
        = (bVV ℂ lam').repr (f (∑ j, (bVV ℂ lam).repr v j • bVV ℂ lam j)) i := by rw [hsum]
      _ = _ := by
        rw [map_sum, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [hrepr]
  exact lossLe_finset_sum w _ _ fun j _ => lossLe_mul_wild_jets w (hv' j) (hf i j)
