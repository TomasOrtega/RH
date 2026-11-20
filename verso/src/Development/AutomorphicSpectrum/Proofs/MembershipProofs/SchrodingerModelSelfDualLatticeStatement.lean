import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SchrodingerModelSelfDualLattice
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMembershipProofs%2FSchrodingerModelSelfDualLattice.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.indicator_in_schrodinger_span : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {κ : Type} [Fintype κ] (v : Rˣ), GoodChar ψ O u → (v : R) ∈ O → (Set.indicator {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} fun _ => (1 : ℂ)) ∈ Submodule.span ℂ {f : (κ → R) → ℂ | ∃ y : κ → R, f = schr ψ (0, y) (Set.indicator {x : κ → R | ∀ i, x i ∈ O} fun _ => (1 : ℂ))} := by
  first | exact @GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span | exact GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span | (intros; apply GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span <;> assumption)
