import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridNuUnitTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondESupConj
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section

namespace GlobalTheory.BotPairSmall.CondXi

open GlobalTheory.Mem.Col2.SplitChar

/- English proof (translation)
Distinguish the cases in `hW : PP ∈ G.pl.W0`. Take `⟨v, hv, rfl⟩` from `Finset.mem_image.1 hW`. Unfold `modT`. Use `(Ideal.mul_le_inf.trans inf_le_left).trans ?_` and prove the remaining obligations. Establish `h1 : condE G.pl ≤ (G.pl.w v).asIdeal ^ condExp G.pl v` using `Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)`.

Use `h1.trans (Ideal.pow_le_self ?_)` and prove the remaining obligations. Apply the tactic sequence `unfold condExp; split_ifs <;> omega`. Establish `hT : PP ∈ twPl G t`. Unfold `twPl`. Rewrite using `[Finset.mem_filter]`.

Conclude with `⟨by unfold GlobalTheory.FunObj.locPl; exact Finset.mem_union_right _ hq, hW⟩`. Unfold `modT`. Conclude with `(Ideal.mul_le_inf.trans inf_le_right).trans (Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hT))`.
-/
theorem modT_le {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T)
    {PP : HeightOneSpectrum (𝓞 D.host.E)} (hq : PP ∈ L.Q t) : modT G t ≤ PP.asIdeal := by
  classical
  by_cases hW : PP ∈ G.pl.W0
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hW
    unfold modT
    refine (Ideal.mul_le_inf.trans inf_le_left).trans ?_
    have h1 : condE G.pl ≤ (G.pl.w v).asIdeal ^ condExp G.pl v :=
      Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
    refine h1.trans (Ideal.pow_le_self ?_)
    unfold condExp; split_ifs <;> omega
  · have hT : PP ∈ twPl G t := by
      unfold twPl
      rw [Finset.mem_filter]
      exact ⟨by unfold GlobalTheory.FunObj.locPl; exact Finset.mem_union_right _ hq, hW⟩
    unfold modT
    exact (Ideal.mul_le_inf.trans inf_le_right).trans (Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hT))

/- English proof (translation)
Use `show Ideal.map _ _ ≤ _`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Take `⟨c', hc', e⟩` from `h x hx`. Rewrite using `[Ideal.mem_comap]`.

Use `hc'` and compare the differences between its conclusion and the goal. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[e, Formalism.BasicNotions.bridge_star_holds]`. Both sides reduce to the same expression.
-/
theorem conj_smul_le_of_isConjPl {D : D7} {PP' PP : HeightOneSpectrum (𝓞 D.host.E)}
    (h : Formalism.IndefR.Lev.IsConjPl PP' PP) : D.host.conj • PP'.asIdeal ≤ PP.asIdeal := by
  show Ideal.map _ _ ≤ _
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  obtain ⟨c', hc', e⟩ := h x hx
  rw [Ideal.mem_comap]
  convert hc'
  apply RingOfIntegers.ext
  rw [e, Formalism.BasicNotions.bridge_star_holds]
  rfl

open Formalism.L2.Host in

/- English proof (translation)
Introduce `D T L sc μ₀ hL G t u hu hc`. Use `GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (L.xiH t).2.1 (finIdl D u) (finIdl_unit hu) (fun w => by rw [finIdl_fst]; rfl) fun PP x hx => ?_` and prove the remaining obligations. Establish `hunit : IsUnitAt PP x`. Unfold `IsUnitAt`. Rewrite using `[hx]`.

Conclude with `finIdl_unit hu PP`. Use `show (L.xiH t).loc PP x = 1`. Distinguish the cases in `hr : (L.xiH t).UnrAt PP`. Conclude with `hr x hunit`. Establish `hle : modT G t * D.host.conj • modT G t ≤ PP.asIdeal ^ (1 : ℕ)`.

Rewrite using `[pow_one]`. Break down `(hL.Q_ram t PP).1 hr with hq | ⟨PP', hq, hcj⟩` into its components or cases. Conclude with `(Ideal.mul_le_inf.trans inf_le_left).trans (modT_le G t hq)`. Conclude with `(Ideal.mul_le_inf.trans inf_le_right).trans ((Ideal.map_mono (modT_le G t hq)).trans (conj_smul_le_of_isConjPl hcj))`. Use `hL.xi_tame t PP x hunit ?_` and prove the remaining obligations.

Rewrite using `[hx, vl_sub_one]`. Conclude with `GlobalTheory.BotPairSmall.CondNu.vl_le_of_mem_hatId hle hc`.
-/
theorem xiH_eq_one_of_cong : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (t : T) (u : (AE D)ˣ), IntU D u → (u : AE D) - 1 ∈ hatId D (modT G t * D.host.conj • modT G t) → (L.xiH t).1 (finIdl D u) = 1 := by
  intro D T L sc μ₀ hL G t u hu hc
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (L.xiH t).2.1 (finIdl D u) (finIdl_unit hu)
    (fun w => by rw [finIdl_fst]; rfl) fun PP x hx => ?_
  have hunit : IsUnitAt PP x := by
    unfold IsUnitAt
    rw [hx]
    exact finIdl_unit hu PP
  show (L.xiH t).loc PP x = 1
  by_cases hr : (L.xiH t).UnrAt PP
  · exact hr x hunit
  have hle : modT G t * D.host.conj • modT G t ≤ PP.asIdeal ^ (1 : ℕ) := by
    rw [pow_one]
    rcases (hL.Q_ram t PP).1 hr with hq | ⟨PP', hq, hcj⟩
    · exact (Ideal.mul_le_inf.trans inf_le_left).trans (modT_le G t hq)
    · exact (Ideal.mul_le_inf.trans inf_le_right).trans
        ((Ideal.map_mono (modT_le G t hq)).trans (conj_smul_le_of_isConjPl hcj))
  refine hL.xi_tame t PP x hunit ?_
  rw [hx, vl_sub_one]
  exact GlobalTheory.BotPairSmall.CondNu.vl_le_of_mem_hatId hle hc

end GlobalTheory.BotPairSmall.CondXi

end
