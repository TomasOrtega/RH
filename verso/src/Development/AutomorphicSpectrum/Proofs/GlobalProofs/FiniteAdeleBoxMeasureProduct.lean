import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

/- English proof (translation)
Introduce `F _ _ ψ hψ v t`. Take `⟨hc, -, -⟩` from `(GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ).1 v`. Establish `hU : {x : Fv F v | ‖psiV F ψ v x - 1‖ < 1 / 2} ∈ nhds (0 : Fv F v)`. Establish `hcont : Continuous fun x : Fv F v => ‖psiV F ψ v x - 1‖` using `(hc.sub continuous_const).norm`. Use `(isOpen_lt hcont continuous_const).mem_nhds ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `‖psiV F ψ v 0 - 1‖ < 1 / 2`. Rewrite using `[psiV_zero, sub_self, norm_zero]`. Evaluate the numerical expressions. Take `⟨m, hm⟩` from `GlobalTheory.CompanionTheory.SW.PiV.exists_ball_subset _ hU`. Establish `triv : ∀ x ∈ GlobalTheory.CompanionTheory.SW.PiV.ball v m, psiV F ψ v x = 1` using `fun x hx => char_eq_one_of_near (GlobalTheory.CompanionTheory.SW.PiV.ball v m) (psiV F ψ v) (psiV_zero ψ v) (psiV_add ψ v) (fun z hz => hm hz) hx`.

Take `⟨n, hn⟩` from `GlobalTheory.CompanionTheory.SW.PiV.exists_mem_ball t`. Use `filter_upwards [Filter.eventually_ge_atTop (n - m).toNat] with k hk s hs`. Apply `triv` to reduce the goal to its premises. Rewrite using `[GlobalTheory.CompanionTheory.SW.PiV.mem_ball, map_mul]`. Establish `hs' : Valued.v s ≤ WithZero.exp (-(k : ℤ))` using `(GlobalTheory.CompanionTheory.SW.PiV.mem_ball _ _).1 hs`.

Establish `hn' : Valued.v t ≤ WithZero.exp n` using `(GlobalTheory.CompanionTheory.SW.PiV.mem_ball _ _).1 hn`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eventually_mem_annV_ball : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v), ∀ᶠ k : ℕ in Filter.atTop, t ∈ annV ψ v (GlobalTheory.CompanionTheory.SW.PiV.ball v (-(k : ℤ)) : Set (Fv F v)) := by
  intro F _ _ ψ hψ v t
  obtain ⟨hc, -, -⟩ := (GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ).1 v
  have hU : {x : Fv F v | ‖psiV F ψ v x - 1‖ < 1 / 2} ∈ nhds (0 : Fv F v) := by
    have hcont : Continuous fun x : Fv F v => ‖psiV F ψ v x - 1‖ := (hc.sub continuous_const).norm
    refine (isOpen_lt hcont continuous_const).mem_nhds ?_
    change ‖psiV F ψ v 0 - 1‖ < 1 / 2
    rw [psiV_zero, sub_self, norm_zero]
    norm_num
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.SW.PiV.exists_ball_subset _ hU
  have triv : ∀ x ∈ GlobalTheory.CompanionTheory.SW.PiV.ball v m, psiV F ψ v x = 1 := fun x hx =>
    char_eq_one_of_near (GlobalTheory.CompanionTheory.SW.PiV.ball v m) (psiV F ψ v) (psiV_zero ψ v) (psiV_add ψ v)
      (fun z hz => hm hz) hx
  obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.SW.PiV.exists_mem_ball t
  filter_upwards [Filter.eventually_ge_atTop (n - m).toNat] with k hk s hs
  apply triv
  rw [GlobalTheory.CompanionTheory.SW.PiV.mem_ball, map_mul]
  have hs' : Valued.v s ≤ WithZero.exp (-(k : ℤ)) := (GlobalTheory.CompanionTheory.SW.PiV.mem_ball _ _).1 hs
  have hn' : Valued.v t ≤ WithZero.exp n := (GlobalTheory.CompanionTheory.SW.PiV.mem_ball _ _).1 hn
  calc Valued.v s * Valued.v t ≤ WithZero.exp (-(k : ℤ)) * WithZero.exp n := mul_le_mul' hs' hn'
    _ = WithZero.exp (-(k : ℤ) + n) := (WithZero.exp_add _ _).symm
    _ ≤ WithZero.exp m := WithZero.exp_le_exp.2 (by omega)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
