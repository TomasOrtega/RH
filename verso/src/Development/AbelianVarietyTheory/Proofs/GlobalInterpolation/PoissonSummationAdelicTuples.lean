import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuouStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicFourierSeriesOfSummableCoefficientsStatement
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.PoissonSum

/- English proof (translation)
The claim follows from `(Module.finBasis ℚ F).equivFun.injective.countable`.
-/
theorem countable_F (F : Type) [Field F] [NumberField F] : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `l`. Simplify using `[rat]`.
-/
theorem rat_add (ξ η : Fin N → F) : (rat (ξ + η) : Fin N → AF F) = rat ξ + rat η := by
  funext l; simp [rat]

/- English proof (translation)
Use function extensionality and compare the values at `l`. Simplify using `[rat]`.
-/
theorem rat_neg (ξ : Fin N → F) : (rat (-ξ) : Fin N → AF F) = -rat ξ := by
  funext l; simp [rat]

/- English proof (translation)
Simplify using `only [Bd, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun l _ => by simp only [Pi.add_apply]; ring`.
-/
theorem Bd_add_left (a : Fin N → F) (u v w : Fin N → AF F) :
    Bd (AF F) a (u + v) w = Bd (AF F) a u w + Bd (AF F) a v w := by
  simp only [Bd, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by simp only [Pi.add_apply]; ring

/- English proof (translation)
Simplify using `only [Bd, ← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun l _ => by simp only [Pi.neg_apply]; ring`.
-/
theorem Bd_neg_right (a : Fin N → F) (u w : Fin N → AF F) :
    Bd (AF F) a u (-w) = -Bd (AF F) a u w := by
  simp only [Bd, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun l _ => by simp only [Pi.neg_apply]; ring

/- English proof (translation)
Simplify using `[Bd]`.
-/
theorem Bd_zero_left (a : Fin N → F) (w : Fin N → AF F) : Bd (AF F) a 0 w = 0 := by
  simp [Bd]

/- English proof (translation)
Simplify using `[Bd, rat, map_sum, map_mul]`.
-/
theorem Bd_rat (a : Fin N → F) (ξ η : Fin N → F) :
    Bd (AF F) a (rat ξ) (rat η) = algebraMap F (AF F) (Bd F a ξ η) := by
  simp [Bd, rat, map_sum, map_mul]

/- English proof (translation)
Unfold `Bd`. Conclude with `continuous_finsetSum _ fun l _ => (continuous_const.mul (continuous_apply l)).mul continuous_const`.
-/
theorem continuous_Bd_right (a : Fin N → F) (w : Fin N → AF F) :
    Continuous fun u : Fin N → AF F => Bd (AF F) a u w := by
  unfold Bd
  exact continuous_finsetSum _ fun l _ => (continuous_const.mul (continuous_apply l)).mul continuous_const

end GlobalTheory.SWQ.PoissonSum

open GlobalTheory.SWQ.PoissonSum in
/- English proof (translation)
Introduce `F _ _ N ψ lam ν a hC Φ hΦ hFΦ`. Use `haveI := countable_F F`. Establish `hψ` using `hC.2.1`. Take `⟨hHaar, hmem, hinj, -, D, hDm, hD, hD1⟩` from `GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hC.2.2.2.1`. Use `haveI := hHaar`.

Take `⟨hint, hsum, hcont⟩` from `GlobalTheory.T.rapidDecay_adelic_integrable_periodisation_continuous F N hC.1 Φ hΦ`. Take `⟨-, hsumF, -⟩` from `GlobalTheory.T.rapidDecay_adelic_integrable_periodisation_continuous F N hC.1 _ hFΦ`. Use `set P : (Fin N → AF F) → ℂ := fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u) with hP`. Establish `hper : ∀ ξ u, P (rat ξ + u) = P u`. Introduce `ξ u`.

Simplify using `only [hP]`. Use `Eq.trans (tsum_congr fun η => ?_) ((Equiv.addRight ξ).tsum_eq (fun η => Φ (rat η + u)))` and prove the remaining obligations. Simplify using `[rat_add, add_assoc]`. Establish `hcoef : ∀ ξ, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = Fo ψ ν a Φ (rat (-ξ))`. Introduce `ξ`.

Use `set G := AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))`. Set `e : (Fin N → F) ≃ G` to `Equiv.ofBijective (fun η => ⟨rat η, (hmem _).2 ⟨η, rfl⟩⟩) ⟨fun η η' h => hinj (congrArg Subtype.val h), fun γ => by`. Take `⟨η, hη⟩` from `(hmem γ.1).1 γ.2`. Conclude with `⟨η, Subtype.ext hη.symm⟩⟩`. Use `haveI : Countable G := e.surjective.countable`.

Use `set g : (Fin N → AF F) → ℂ := fun u => Φ u * ψ (-(Bd (AF F) a u (rat ξ))) with hg`. Establish `hgc : Continuous g` using `hΦ.1.mul (hψ.1.comp (continuous_Bd_right a (rat ξ)).neg)`. Establish `hgn : ∀ u, ‖g u‖ = ‖Φ u‖` using `fun u => by simp [hg, hψ.2.1]`. Establish `hgi : Integrable g (muV N ν)` using `(hint _ hHaar).norm.mono' hgc.aestronglyMeasurable (Eventually.of_forall fun u => (hgn u).le)`. Establish `hshift : ∀ η u, g (rat η + u) = Φ (rat η + u) * ψ (-(Bd (AF F) a u (rat ξ)))`.

Introduce `η u`. Simplify using `only [hg, Bd_add_left, Bd_rat, neg_add, AddChar.map_add_eq_mul, ← map_neg, hψ.2.2.1, one_mul]`. Establish `hFo : Fo ψ ν a Φ (rat (-ξ)) = ∫ u, g u ∂(muV N ν)`. Simplify using `only [Fo, hg, rat_neg, Bd_neg_right]`. Rewrite using `[hFo, hD.integral_eq_tsum'' g hgi, ← e.tsum_eq]`.

Establish `hvadd : ∀ η u, (e η +ᵥ u : Fin N → AF F) = rat η + u` using `fun η u => rfl`. Repeatedly rewrite using `[hvadd, hshift]`. Simplify using `only [hP]`. Repeatedly rewrite using `[← tsum_mul_right]`. Use `integral_tsum (fun η => ?_) ?_` and prove the remaining obligations.

Conclude with `((hΦ.1.comp (continuous_const.add continuous_id)).mul (hψ.1.comp (continuous_Bd_right a (rat ξ)).neg)).aestronglyMeasurable`. Establish `hl` using `hD.lintegral_eq_tsum'' (fun u => ‖Φ u‖ₑ)`. Rewrite `hl` using `[← e.tsum_eq]`. Rewrite `hl` using `[hvadd]`. Establish `hfin : ∫⁻ u, ‖Φ u‖ₑ ∂(muV N ν) ≠ ∞` using `(hint _ hHaar).2.ne`.

Simplify using `only [← ofReal_norm_eq_enorm] at hl ⊢`. Simplify using `only [norm_mul, hψ.2.1, mul_one]`. Rewrite using `[← hl]`. Simplify `hfin` using `[ofReal_norm_eq_enorm]`. Establish `hsc : Summable (fun ξ : Fin N → F => ‖Fo ψ ν a Φ (rat (-ξ))‖)`.

Establish `h` using `hsumF 0`. Simplify using `only [add_zero] at h`. Conclude with `(Equiv.neg (Fin N → F)).summable_iff.2 h`. Establish `key` using `GlobalTheory.T.adelic_fourierSeries_of_summable_coefficients F N ψ lam ν a hC D hD hD1 P _ hcont hper hcoef hsc 0`. Establish `h0 : P 0 = th Φ` using `by simp [hP, th]`.

Rewrite `key` using `[h0]`. Rewrite using `[key, th]`. Use `((Equiv.neg (Fin N → F)).tsum_eq (fun ξ => Fo ψ ν a Φ (rat ξ))).symm.trans (tsum_congr fun ξ => ?_)` and prove the remaining obligations. Simplify using `[Bd_zero_left]`.
-/
theorem GlobalTheory.SWQ.poisson_summation : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → Decay (Fo ψ ν a Φ) → th (Fo ψ ν a Φ) = th Φ := by
  intro F _ _ N ψ lam ν a hC Φ hΦ hFΦ
  haveI := countable_F F
  have hψ := hC.2.1
  obtain ⟨hHaar, hmem, hinj, -, D, hDm, hD, hD1⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hC.2.2.2.1
  haveI := hHaar
  obtain ⟨hint, hsum, hcont⟩ := GlobalTheory.T.rapidDecay_adelic_integrable_periodisation_continuous F N hC.1 Φ hΦ
  obtain ⟨-, hsumF, -⟩ := GlobalTheory.T.rapidDecay_adelic_integrable_periodisation_continuous F N hC.1 _ hFΦ
  set P : (Fin N → AF F) → ℂ := fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u) with hP
  have hper : ∀ ξ u, P (rat ξ + u) = P u := by
    intro ξ u
    simp only [hP]
    refine Eq.trans (tsum_congr fun η => ?_) ((Equiv.addRight ξ).tsum_eq (fun η => Φ (rat η + u)))
    simp [rat_add, add_assoc]
  have hcoef : ∀ ξ, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = Fo ψ ν a Φ (rat (-ξ)) := by
    intro ξ
    set G := AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))
    let e : (Fin N → F) ≃ G := Equiv.ofBijective (fun η => ⟨rat η, (hmem _).2 ⟨η, rfl⟩⟩)
      ⟨fun η η' h => hinj (congrArg Subtype.val h), fun γ => by
        obtain ⟨η, hη⟩ := (hmem γ.1).1 γ.2
        exact ⟨η, Subtype.ext hη.symm⟩⟩
    haveI : Countable G := e.surjective.countable
    set g : (Fin N → AF F) → ℂ := fun u => Φ u * ψ (-(Bd (AF F) a u (rat ξ))) with hg
    have hgc : Continuous g :=
      hΦ.1.mul (hψ.1.comp (continuous_Bd_right a (rat ξ)).neg)
    have hgn : ∀ u, ‖g u‖ = ‖Φ u‖ := fun u => by simp [hg, hψ.2.1]
    have hgi : Integrable g (muV N ν) :=
      (hint _ hHaar).norm.mono' hgc.aestronglyMeasurable (Eventually.of_forall fun u => (hgn u).le)
    have hshift : ∀ η u, g (rat η + u) = Φ (rat η + u) * ψ (-(Bd (AF F) a u (rat ξ))) := by
      intro η u
      simp only [hg, Bd_add_left, Bd_rat, neg_add, AddChar.map_add_eq_mul, ← map_neg, hψ.2.2.1, one_mul]
    have hFo : Fo ψ ν a Φ (rat (-ξ)) = ∫ u, g u ∂(muV N ν) := by
      simp only [Fo, hg, rat_neg, Bd_neg_right]
    rw [hFo, hD.integral_eq_tsum'' g hgi, ← e.tsum_eq]
    have hvadd : ∀ η u, (e η +ᵥ u : Fin N → AF F) = rat η + u := fun η u => rfl
    simp_rw [hvadd, hshift]
    simp only [hP]
    simp_rw [← tsum_mul_right]
    refine integral_tsum (fun η => ?_) ?_
    · exact ((hΦ.1.comp (continuous_const.add continuous_id)).mul
        (hψ.1.comp (continuous_Bd_right a (rat ξ)).neg)).aestronglyMeasurable
    · have hl := hD.lintegral_eq_tsum'' (fun u => ‖Φ u‖ₑ)
      rw [← e.tsum_eq] at hl
      simp_rw [hvadd] at hl
      have hfin : ∫⁻ u, ‖Φ u‖ₑ ∂(muV N ν) ≠ ∞ := (hint _ hHaar).2.ne
      simp only [← ofReal_norm_eq_enorm] at hl ⊢
      simp only [norm_mul, hψ.2.1, mul_one]
      rw [← hl]
      simpa [ofReal_norm_eq_enorm] using hfin
  have hsc : Summable (fun ξ : Fin N → F => ‖Fo ψ ν a Φ (rat (-ξ))‖) := by
    have h := hsumF 0
    simp only [add_zero] at h
    exact (Equiv.neg (Fin N → F)).summable_iff.2 h
  have key := GlobalTheory.T.adelic_fourierSeries_of_summable_coefficients F N ψ lam ν a hC D hD hD1 P _ hcont hper hcoef hsc 0
  have h0 : P 0 = th Φ := by simp [hP, th]
  rw [h0] at key
  rw [key, th]
  refine ((Equiv.neg (Fin N → F)).tsum_eq (fun ξ => Fo ψ ν a Φ (rat ξ))).symm.trans (tsum_congr fun ξ => ?_)
  simp [Bd_zero_left]
