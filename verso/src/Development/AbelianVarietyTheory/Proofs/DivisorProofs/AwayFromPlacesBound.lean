import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

namespace TwistAwayFromPlace
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.DivisionValues (vw lw)
open GlobalTheory.SumSize

namespace GlobalTheory.CompanionTheory.Twist

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Host in

/- English proof (translation)
Introduce `_`. Use `⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ w PP hP => ?_⟩⟩⟩` and prove the remaining obligations. Establish `hr : ¬ (R.xiH (R.mu w)).UnrAt PP` using `(s.core.lev.Q_ram (R.mu w) PP).2 (Or.inl hP)`. Distinguish the cases in `hw : w ∈ R.twPl`. Take `⟨ψ, Q, hψ, e⟩` from `s.mu_on w hw`.

Establish `e' : R.xiH (R.mu w) = R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ` using `e`. Distinguish the cases in `hd : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt PP`. Use `Or.inr fun l hl h1 h2 => hr fun x hx => ?_` and prove the remaining obligations. Establish `hp : Formalism.EigenvalueLevelCeiling.plc w = l`. Conclude with `((Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime w) hl).1 ((ringChar.spec _ l).1 (by simpa using Ideal.Quotient.eq_zero_iff_mem.2 h2)))`.

Establish `a1` using `hd x hx`. Establish `a2` using `hψ.atl PP (hp ▸ h1) x`. Rewrite using `[e']`. Express the relevant statement in the definitionally equal form `(R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc PP x * ψ.loc PP x = 1`. Rewrite using `[a1, a2, mul_one]`.

Use `Or.inl (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_)))` and prove the remaining obligations. Establish `key : ∀ p : ℕ, OverP D.host p PP → (p : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal` using `fun p hp => by`. Express the relevant statement in the definitionally equal form `algebraMap _ (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ PP.asIdeal`. Rewrite using `[map_natCast]` and apply the resulting hypothesis. Unfold `CharFrame.delAt at hd`.

Use `split_ifs at hd`. Conclude with `Or.inr (Or.inr (Or.inr (key _ (by by_contra h; exact hd (R.C.isDel'.unr PP h)))))`. Conclude with `Or.inr (Or.inr (Or.inl (key _ (by by_contra h; exact hd (R.C.isDel.unr PP h)))))`. Establish `e : R.mu w = A.μ0` using `s.mu_off w hw`. Use `absurd (fun x _ => ?_) hr` and prove the remaining obligations.

Rewrite using `[e, show R.xiH A.μ0 = 1 from s.core.lev.xi_base]`. Both sides reduce to the same expression.
-/
theorem away_k : GlobalTheory.FunPr.Hypotheses₂ → AwayK := by
  intro _
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ w PP hP => ?_⟩⟩⟩
  have hr : ¬ (R.xiH (R.mu w)).UnrAt PP := (s.core.lev.Q_ram (R.mu w) PP).2 (Or.inl hP)
  by_cases hw : w ∈ R.twPl
  · obtain ⟨ψ, Q, hψ, e⟩ := s.mu_on w hw
    have e' : R.xiH (R.mu w) = R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ := e
    by_cases hd : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt PP
    · refine Or.inr fun l hl h1 h2 => hr fun x hx => ?_
      have hp : Formalism.EigenvalueLevelCeiling.plc w = l := by
        exact ((Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime w) hl).1
          ((ringChar.spec _ l).1 (by simpa using Ideal.Quotient.eq_zero_iff_mem.2 h2)))
      have a1 := hd x hx
      have a2 := hψ.atl PP (hp ▸ h1) x
      rw [e']
      change (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc PP x * ψ.loc PP x = 1
      rw [a1, a2, mul_one]
    · refine Or.inl (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_)))
      have key : ∀ p : ℕ, OverP D.host p PP → (p : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal := fun p hp => by
        change algebraMap _ (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ PP.asIdeal
        rwa [map_natCast]
      unfold CharFrame.delAt at hd
      split_ifs at hd
      · exact Or.inr (Or.inr (Or.inr (key _ (by by_contra h; exact hd (R.C.isDel'.unr PP h)))))
      · exact Or.inr (Or.inr (Or.inl (key _ (by by_contra h; exact hd (R.C.isDel.unr PP h)))))
  · have e : R.mu w = A.μ0 := s.mu_off w hw
    refine absurd (fun x _ => ?_) hr
    rw [e, show R.xiH A.μ0 = 1 from s.core.lev.xi_base]
    rfl

end GlobalTheory.CompanionTheory.Twist

end

end

end TwistAwayFromPlace
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
/- English proof (translation)
Apply the tactic sequence `first | exact @TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.away_k | exact TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.away_k | (intros; apply TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.away_k <;> assumption)`.
-/
theorem _root_.GlobalTheory.Adopt.away_from_places_bound : GlobalTheory.FunPr.Hypotheses₂ → AwayK := by
  first | exact @TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.away_k | exact TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.away_k | (intros; apply TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.away_k <;> assumption)

end
