import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
namespace GlobalTheory.CovTop.Sizes
/- English proof (translation)
Introduce `M`. Use `⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ => ?_⟩⟩` and prove the remaining obligations. Take `⟨x0, hx0⟩` from `eventually_scale he (22 + |Fm.Ct|) M`. Establish `hez : 0 < Fm.ez` using `div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)`. Take `⟨x2, hx2⟩` from `Filter.eventually_atTop.1 ((tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 5)).eventually_ge_atTop 5)`.

Use `⟨22 + |Fm.Ct|, by positivity, max x0 x2, fun x hx hle ι p _ _ => ?_⟩` and prove the remaining obligations. Take `⟨a1, a2, a3, a4, -, a6⟩` from `hx0 x ((le_max_left _ _).trans hle)`. Establish `a5 : 5 ≤ x ^ (Fm.ez / 5)` using `hx2 x ((le_max_right _ _).trans hle)`. Establish `hsz : (Fm.L x ι).sc.ez = Fm.ez` using `Fm.toFamCore.L_ez x ι`. Establish `hsx : (Fm.L x ι).sc.x = x` using `Fm.L_x x ι hx`.

Establish `hse : (Fm.L x ι).sc.eps = eps` using `Fm.L_eps x ι`. Establish `hsL : (Fm.L x ι).sc.L = x ^ eps` using `by unfold Scale.L; rw [hsx, hse]`. Establish `hg : ∀ k, Real.log ((Fm.D x ι).host.g k) ≤ 9 * (Fm.L x ι).sc.L + 1` using `fun k => by`. Establish `hlo : 0 < ((((Fm.D x ι).host.g k : ℕ)) : ℝ)` using `by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos`. Use `(Real.log_le_iff_le_exp hlo).2 ((hF.1.2.2.2.2.2.2.2.2 x hx ι).2.2.1 k)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `hostNum_of_sizes (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) hg ?_ ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[Fm.Ct_eq]`. Combine the linear relations using `[le_abs_self Fm.Ct]`. Rewrite using `[hsL]` and apply the resulting hypothesis.

Rewrite using `[hsL]` and apply the resulting hypothesis. Rewrite using `[hsx]` and apply the resulting hypothesis. Unfold `Scale.b`. Rewrite using `[hsL, hsx]` and apply the resulting hypothesis. Rewrite using `[hsx, hsz]` and apply the resulting hypothesis.

Rewrite using `[hsx]` and apply the resulting hypothesis.
-/
theorem hostN_alt : ∀ M : ℝ, _root_.GlobalTheory.CovTop.HostNAlt M := by
  intro M
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := eventually_scale he (22 + |Fm.Ct|) M
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  obtain ⟨x2, hx2⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 5)).eventually_ge_atTop 5)
  refine ⟨22 + |Fm.Ct|, by positivity, max x0 x2, fun x hx hle ι p _ _ => ?_⟩
  obtain ⟨a1, a2, a3, a4, -, a6⟩ := hx0 x ((le_max_left _ _).trans hle)
  have a5 : 5 ≤ x ^ (Fm.ez / 5) := hx2 x ((le_max_right _ _).trans hle)
  have hsz : (Fm.L x ι).sc.ez = Fm.ez := Fm.toFamCore.L_ez x ι
  have hsx : (Fm.L x ι).sc.x = x := Fm.L_x x ι hx
  have hse : (Fm.L x ι).sc.eps = eps := Fm.L_eps x ι
  have hsL : (Fm.L x ι).sc.L = x ^ eps := by unfold Scale.L; rw [hsx, hse]
  have hg : ∀ k, Real.log ((Fm.D x ι).host.g k) ≤ 9 * (Fm.L x ι).sc.L + 1 := fun k => by
    have hlo : 0 < ((((Fm.D x ι).host.g k : ℕ)) : ℝ) := by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos
    have := (Real.log_le_iff_le_exp hlo).2 ((hF.1.2.2.2.2.2.2.2.2 x hx ι).2.2.1 k)
    linarith
  refine hostNum_of_sizes (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) hg ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Fm.Ct_eq]; linarith [le_abs_self Fm.Ct]
  · rwa [hsL]
  · rwa [hsL]
  · rwa [hsx]
  · unfold Scale.b; rwa [hsL, hsx]
  · rwa [hsx, hsz]
  · rwa [hsx]
end GlobalTheory.CovTop.Sizes
end
end
