import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.SlashAddSmulPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertHolomorphicUnnormalizedSlashOfPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertModerateGrowthUnnormalizedSlash
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.QExpansionLinearCombination
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsOrbitAverageOfSeedPowersWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsDifferentGeneratorTotallyPositiveTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Gl2AdelicDoubleCosetDecompositionTotallyReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.SystemCuspInfinityComponentCongrOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.FormSystemOfFinitelyManyStabilizerForms
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsIsHolAdelicLiftOfEvenWeightSystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsSeedThetaLatticeFixedPointFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsAdelicFourierExpansionOfLift
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

/- English proof (translation)
Take `⟨b, hb, hs⟩` from `hg`. Establish `h1` using `(hasQ_lin F _ _ b b 1 hb hb).2.2.2`. Establish `h2` using `(hasQ_lin F _ _ _ _ 1 hb h1).1`. Establish `e : (g - 1 + fun _ : Hn F => (1 : ℂ)) = g` using `by funext z; simp`. Rewrite `h2` using `[e]`.

Use `⟨_, h2, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using (hs 0).trans_lt hr`. Simplify using `using (hs 1).trans_lt hr`.
-/
theorem hasQ_of_small_sub_one {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ)
    {r : ℝ} (hr : r < 1) {g : Hn F → ℂ} (hg : Small ι r (g - 1)) :
    ∃ a, HasQ g a ∧ ‖ι.symm (a 0) - 1‖ < 1 ∧ ‖ι.symm (a 1)‖ < 1 := by
  classical
  obtain ⟨b, hb, hs⟩ := hg
  have h1 := (hasQ_lin F _ _ b b 1 hb hb).2.2.2
  have h2 := (hasQ_lin F _ _ _ _ 1 hb h1).1
  have e : (g - 1 + fun _ : Hn F => (1 : ℂ)) = g := by funext z; simp
  rw [e] at h2
  refine ⟨_, h2, ?_, ?_⟩
  · simpa using (hs 0).trans_lt hr
  · simpa using (hs 1).trans_lt hr

/- English proof (translation)
Introduce `F _ _ _ p _ hp2 ι`. Establish `hp : p.Prime` using `Fact.out`. Take `⟨δ, hδ⟩` from `(GlobalTheory.T.exists_different_generator_totallyPositive_translate F p hp).1`. Take `⟨θ, hθ⟩` from `GlobalTheory.T.exists_seed_theta_lattice_fixedPointFree F p ι hp2 δ hδ`. Take `⟨Y, hY, hrep⟩` from `GlobalTheory.T.gl2_adelic_double_coset_decomposition_totally_real F p hp δ hδ`.

Establish `hav : ∀ y : (Af F)ˣ, ∃ N : ℕ, y ∈ Y → ∀ M : ℕ, p ^ N ∣ M → ∃ f : Hn F → ℂ, Comp ι δ ((p - 1) * M) (aff y 0) f`. Introduce `y`. Distinguish the cases in `hy : y ∈ Y`. Take `⟨N, hN⟩` from `GlobalTheory.T.exists_orbit_average_of_seed_powers_weight F p ι hp2 δ hδ θ hθ y (hY y hy)`. Conclude with `⟨N, fun _ => hN⟩`.

Conclude with `⟨0, fun h => absurd h hy⟩`. Use `choose n hn using hav`. Use `⟨Y.sup n, fun k _ hk => ?_⟩` and prove the remaining obligations. Take `⟨m, rfl⟩` from `hk`. Rewrite using `[mul_assoc]`.

Use `set k := (p - 1) * (p ^ Y.sup n * m) with hkdef`. Establish `hf : ∀ y : (Af F)ˣ, ∃ f : Hn F → ℂ, y ∈ Y → Comp ι δ k (aff y 0) f`. Introduce `y`. Distinguish the cases in `hy : y ∈ Y`. Take `⟨f, hf⟩` from `hn y hy (p ^ Y.sup n * m) ((pow_dvd_pow p (Finset.le_sup hy)).mul_right m)`.

Conclude with `⟨f, fun _ => hf⟩`. Conclude with `⟨0, fun h => absurd h hy⟩`. Use `choose f hf using hf`. Take `⟨Ψ, hΨ, hval⟩` from `GlobalTheory.T.form_system_of_finitely_many_stabilizer_forms F k Y (fun y => ((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ) • f y) hrep (fun y hy => ⟨(HolKeep.main F k _ _ _ (hf y hy).hol (hf y hy).hol).2.1, (Growth.gr_closed F k _ _ _ (hf y hy).gr (hf y hy).gr).2.1, fun γ hγ => by rw [(slas …`. Establish `hev : Even k` using `(hp.even_sub_one hp2).mul_right _`.

Take `⟨φ, hl, hφ⟩` from `GlobalTheory.T.exists_isHol_adelic_lift_of_even_weight_system F k hev Ψ hΨ`. Establish `hlt : (p : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)`. Establish `hone : ∀ y : (Af F)ˣ, ∃ a, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) a ∧ ‖ι.symm (a 0) - 1‖ < 1 ∧ ‖ι.symm (a 1)‖ < 1`. Introduce `y`. Take `⟨γ, z, hγ, y', hy', u, hu, h1, h2⟩` from `hval (aff y 0)`.

Conclude with `hasQ_of_small_sub_one ι hlt (GlobalTheory.T.system_cusp_infinity_component_congr_one F p ι hp2 δ hδ k (dvd_mul_right _ _) Ψ hΨ y y' z (f y') (hY y' hy') (hf y' hy').one γ u hγ hu h1 h2)`. Use `choose a ha h0 h1 using hone`. Take `⟨c, hc, hc'⟩` from `GlobalTheory.T.exists_adelic_fourier_expansion_of_lift F k Ψ φ.1 a hΨ hl ha`. Use `⟨φ, fun y => a y 0, c, hφ, hc, h0, fun 𝔪 h𝔪 => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hc' 𝔪 h𝔪`.

Rewrite using `[hy]`. Conclude with `h1 y`.
-/
theorem hilbertOne : UpperTheory.V.Published.HilbertOne := by
  intro F _ _ _ p _ hp2 ι
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨δ, hδ⟩ := (GlobalTheory.T.exists_different_generator_totallyPositive_translate F p hp).1
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_seed_theta_lattice_fixedPointFree F p ι hp2 δ hδ
  obtain ⟨Y, hY, hrep⟩ := GlobalTheory.T.gl2_adelic_double_coset_decomposition_totally_real F p hp δ hδ
  have hav : ∀ y : (Af F)ˣ, ∃ N : ℕ, y ∈ Y → ∀ M : ℕ, p ^ N ∣ M → ∃ f : Hn F → ℂ, Comp ι δ ((p - 1) * M) (aff y 0) f := by
    intro y
    by_cases hy : y ∈ Y
    · obtain ⟨N, hN⟩ := GlobalTheory.T.exists_orbit_average_of_seed_powers_weight F p ι hp2 δ hδ θ hθ y (hY y hy)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose n hn using hav
  refine ⟨Y.sup n, fun k _ hk => ?_⟩
  obtain ⟨m, rfl⟩ := hk
  rw [mul_assoc]
  set k := (p - 1) * (p ^ Y.sup n * m) with hkdef
  have hf : ∀ y : (Af F)ˣ, ∃ f : Hn F → ℂ, y ∈ Y → Comp ι δ k (aff y 0) f := by
    intro y
    by_cases hy : y ∈ Y
    · obtain ⟨f, hf⟩ := hn y hy (p ^ Y.sup n * m) ((pow_dvd_pow p (Finset.le_sup hy)).mul_right m)
      exact ⟨f, fun _ => hf⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose f hf using hf
  obtain ⟨Ψ, hΨ, hval⟩ := GlobalTheory.T.form_system_of_finitely_many_stabilizer_forms F k Y (fun y => ((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ) • f y) hrep (fun y hy =>
    ⟨(HolKeep.main F k _ _ _ (hf y hy).hol (hf y hy).hol).2.1, (Growth.gr_closed F k _ _ _ (hf y hy).gr (hf y hy).gr).2.1,
      fun γ hγ => by rw [(slash_add_smul_pow F k 0 _ _ (f y) _).2.2.2.2.1, (hf y hy).inv γ hγ]⟩)
  have hev : Even k := (hp.even_sub_one hp2).mul_right _
  obtain ⟨φ, hl, hφ⟩ := GlobalTheory.T.exists_isHol_adelic_lift_of_even_weight_system F k hev Ψ hΨ
  have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hone : ∀ y : (Af F)ˣ, ∃ a, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) a ∧
      ‖ι.symm (a 0) - 1‖ < 1 ∧ ‖ι.symm (a 1)‖ < 1 := by
    intro y
    obtain ⟨γ, z, hγ, y', hy', u, hu, h1, h2⟩ := hval (aff y 0)
    exact hasQ_of_small_sub_one ι hlt
      (GlobalTheory.T.system_cusp_infinity_component_congr_one F p ι hp2 δ hδ k (dvd_mul_right _ _) Ψ hΨ y y' z (f y') (hY y' hy') (hf y' hy').one γ u hγ hu h1 h2)
  choose a ha h0 h1 using hone
  obtain ⟨c, hc, hc'⟩ := GlobalTheory.T.exists_adelic_fourier_expansion_of_lift F k Ψ φ.1 a hΨ hl ha
  refine ⟨φ, fun y => a y 0, c, hφ, hc, h0, fun 𝔪 h𝔪 => ?_⟩
  obtain ⟨y, hy⟩ := hc' 𝔪 h𝔪
  rw [hy]
  exact h1 y

end GlobalTheory.HilbertThetaSeries
