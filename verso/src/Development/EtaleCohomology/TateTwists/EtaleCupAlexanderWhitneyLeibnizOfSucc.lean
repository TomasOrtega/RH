import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizEvalDegreeZero

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

/- English proof (translation)
Introduce `R _ E K k γ γ' H`. Apply `Cochain.ext` to reduce the goal to its premises. Introduce `p q hpq`. Distinguish the cases in `hp : ∃ N : ℕ, -(N : ℤ) = p`. Take `⟨N, rfl⟩` from `hp`.

Rewrite using `[← cancel_epi (chainsXIso R E N).inv]`. Apply `Sheaf.hom_ext` to reduce the goal to its premises. Apply `sheafify_hom_ext _ _ _ (Sheaf.cond _)` to reduce the goal to its premises. Use extensionality with `U : 2`. Apply `ModuleCat.free_hom_ext` to reduce the goal to its premises.

Introduce `x`. Conclude with `H N q hpq U.unop x.down`. Establish `hz : IsZero (((chains R).obj E).X p)` using `HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => hp ⟨i, by`. Establish `e : ComplexShape.embeddingDownNat.f i = -(i : ℤ)` using `rfl`. Use the proof step `omega⟩)`.

Conclude with `hz.eq_of_src _ _`.
-/
theorem awleib_ext_pf : EtaleSimplicialCochainEqOfEvaluationsAgree := by
  intro R _ E K k γ γ' H
  apply Cochain.ext
  intro p q hpq
  by_cases hp : ∃ N : ℕ, -(N : ℤ) = p
  · obtain ⟨N, rfl⟩ := hp
    rw [← cancel_epi (chainsXIso R E N).inv]
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ (Sheaf.cond _)
    ext U : 2
    apply ModuleCat.free_hom_ext
    intro x
    exact H N q hpq U.unop x.down
  · have hz : IsZero (((chains R).obj E).X p) :=
      HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => hp ⟨i, by
        have e : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
        omega⟩)
    exact hz.eq_of_src _ _

/- English proof (translation)
The claim follows from `etale_cup_alexanderWhitney_leibniz_of_ext_and_succ awleib_ext_pf hs`.
-/
theorem etale_cup_alexanderWhitney_leibniz_of_succ (hs : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree) : EtaleAlexanderWhitneyCupLeibnizRule :=
  etale_cup_alexanderWhitney_leibniz_of_ext_and_succ awleib_ext_pf hs

end LateralTheory.EtaleFoundations
