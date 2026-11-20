import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.SqTop

open Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

/- English proof (translation)
Introduce `D T L sc G μ₀ hL t i j P hP`. Establish `hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0`. Simplify using `only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hP`. Conclude with `⟨hP.1.resolve_left hP.2, hP.2⟩`. Establish `hxi : ¬ (L.xiH t).UnrAt P` using `(hL.Q_ram t P).2 (Or.inl hP'.1)`.

Establish `hS1 : P.under (𝓞 D.host.F) ∉ S1 D` using `fun h => by`. Establish `e` using `G.pl.w_Q t P hP'.1 h`. Use `hP'.2 ?_` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))`.

Establish `hS0 : P.under (𝓞 D.host.F) ∉ G.pl.S0` using `fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t P hP'.1) hS1`. Establish `a1 : 1 ≤ D.R.m - i` using `by have := i.2; omega`. Establish `a2 : D.R.m - i ≤ D.R.m` using `by omega`. Establish `hmu : (L.C.mu0 j).UnrAt P` using `(L.C.isMu0 j).unr P fun k hk => hS1 ((S1_mem_OmF D).2 ?_)`. Establish `hchi : (G.ch.chiH (D.R.m - i)).UnrAt P` using `G.ch.unr _ a1 a2 P hS0`.

Introduce `hnu`. Apply `hxi` to reduce the goal to its premises. Establish `e : L.xiH t = nuH G t i j * (L.C.mu0 j)⁻¹ * G.ch.chiH (D.R.m - i)`. Rewrite using `[nuH]`. Establish `key : ∀ {M : Type} [CommGroup M] (a x c : M), x = a * x / c * a⁻¹ * c` using `fun a x c => by`.

Rewrite using `[div_mul_eq_mul_div, div_mul_cancel, mul_comm a x, mul_inv_cancel_right]`. Conclude with `key _ _ _`. Rewrite using `[e]`. Conclude with `(hnu.mul hmu.inv).mul hchi`. Establish `: ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal` using `by show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal`.

Rewrite using `[map_natCast]`. Conclude with `hk`. Use `fin_cases k`. Conclude with `Or.inl this`. Conclude with `Or.inr (Or.inl this)`.
-/
theorem nuH_not_unrAt_twPl : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i j : Fin D.R.m), ∀ P ∈ GlobalTheory.SqTop.twPl G t, ¬ (GlobalTheory.FunObj.SqNum.nuH G t i j).UnrAt P := by
  intro D T L sc G μ₀ hL t i j P hP
  classical
  have hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0 := by
    simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hP
    exact ⟨hP.1.resolve_left hP.2, hP.2⟩
  have hxi : ¬ (L.xiH t).UnrAt P := (hL.Q_ram t P).2 (Or.inl hP'.1)
  have hS1 : P.under (𝓞 D.host.F) ∉ S1 D := fun h => by
    have e := G.pl.w_Q t P hP'.1 h
    refine hP'.2 ?_
    rw [e]
    exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
  have hS0 : P.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h =>
    (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t P hP'.1) hS1
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr P fun k hk => hS1 ((S1_mem_OmF D).2 ?_)
  · have hchi : (G.ch.chiH (D.R.m - i)).UnrAt P := G.ch.unr _ a1 a2 P hS0
    intro hnu
    apply hxi
    have e : L.xiH t = nuH G t i j * (L.C.mu0 j)⁻¹ * G.ch.chiH (D.R.m - i) := by
      rw [nuH]
      have key : ∀ {M : Type} [CommGroup M] (a x c : M), x = a * x / c * a⁻¹ * c := fun a x c => by
        rw [div_mul_eq_mul_div, div_mul_cancel, mul_comm a x, mul_inv_cancel_right]
      exact key _ _ _
    rw [e]
    exact (hnu.mul hmu.inv).mul hchi
  · have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
      rw [map_natCast]; exact hk
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)

end GlobalTheory.SqTop
