import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.RepresentativeL2

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {Γ : Subgroup G} [Countable Γ] {μ : Measure G} {𝓕 : Set G}

/- English proof (translation)
The claim follows from `measurable_quotient_mk''`.
-/
theorem meas_mk : Measurable (Quotient.mk (QuotientGroup.rightRel Γ)) := measurable_quotient_mk''

/- English proof (translation)
Establish `h1` using `ae_of_ae_map (meas_mk (Γ := Γ)).aemeasurable hp`. Rewrite `h1` using `[ae_iff, Measure.restrict_apply₀' h.nullMeasurableSet]`. Rewrite using `[ae_iff]`. Use `h.measure_zero_of_invariant _ (fun g => ?_) h1` and prove the remaining obligations. Use extensionality with `x`.

Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Establish `: (Quotient.mk (QuotientGroup.rightRel Γ) (g⁻¹ • x)) = Quotient.mk _ x`. Use `Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)` and prove the remaining obligations. Simplify using `[Subgroup.smul_def]`. Simplify using `only [Set.mem_setOf_eq, this]`.
-/
theorem ae_up [μ.IsMulLeftInvariant] (h : IsFundamentalDomain Γ 𝓕 μ) {p : Quotient (QuotientGroup.rightRel Γ) → Prop}
    (hp : ∀ᵐ q ∂((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))), p q) :
    ∀ᵐ x ∂μ, p (Quotient.mk _ x) := by
  have h1 := ae_of_ae_map (meas_mk (Γ := Γ)).aemeasurable hp
  rw [ae_iff, Measure.restrict_apply₀' h.nullMeasurableSet] at h1
  rw [ae_iff]
  refine h.measure_zero_of_invariant _ (fun g => ?_) h1
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have : (Quotient.mk (QuotientGroup.rightRel Γ) (g⁻¹ • x)) = Quotient.mk _ x := by
    refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
    simp [Subgroup.smul_def]
  simp only [Set.mem_setOf_eq, this]

end General

/- English proof (translation)
Introduce `D V μ 𝓕 ρ hp hr`. Take `⟨-, -, -, hB, hT, -, hC⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V`. Use `haveI := hp.haar`. Use `haveI := hp.right`. Establish `hm : Measurable (autMk V)` using `meas_mk`.

Use `haveI : IsFiniteMeasure (nuQ V μ 𝓕) := ⟨by`. Rewrite using `[nuQ, Measure.map_apply hm MeasurableSet.univ]`. Simplify `hp.fin⟩` using `[lt_top_iff_ne_top]`. Establish `up : ∀ {p : AutQ V → Prop}, (∀ᵐ q ∂(nuQ V μ 𝓕), p q) → ∀ᵐ x ∂μ, p (autMk V x)` using `fun h => ae_up hp.fd h`. Use `⟨fun φ hφ hinv ⟨C, hC⟩ => ?_, fun F ψ ψ' h h' e e' => ?_, fun F F' ψ e e' => ?_, fun F ψ g e => ?_, fun F F' ψ ψ' a e e' => ?_, fun F F' ψ ψ' e e' => ?_⟩` and prove the remaining obligations.

Set `f : AutQ V → ℂ` to `Quotient.lift φ fun a b hab => by`. Use `hinv _ (QuotientGroup.rightRel_apply.1 hab) a` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_right]`. Conclude with `this.symm`. Establish `hf : Measurable f` using `measurable_from_quotient.2 hφ.measurable`.

Establish `hL : MemLp f 2 (nuQ V μ 𝓕)` using `MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun q => by`. Proceed by induction on `q using Quotient.inductionOn with`. Consider the case `h x => exact hC x)`. Conclude with `⟨hL.toLp f, up hL.coeFn_toLp⟩`. Use `(h.ae_eq_iff_eq μ h').1 ?_ filter_upwards [e, e'] with x h1 h2` and prove the remaining obligations.

Rewrite using `[← h1, h2]`. Use `Lp.ext ?_` and prove the remaining obligations. Use `(ae_map_iff hm.aemeasurable ((Lp.stronglyMeasurable F).measurableSet_eq_fun (Lp.stronglyMeasurable F'))).2 (ae_restrict_of_ae ?_)` and prove the remaining obligations. Use `filter_upwards [e, e'] with x h1 h2`. Rewrite using `[h1, h2]`.

Establish `e2` using `(measurePreserving_mul_right μ g).quasiMeasurePreserving.ae e filter_upwards [hr.val g F, e2] with x h1 h2`. Rewrite using `[h1, h2]`. Both sides reduce to the same expression. Use `filter_upwards [up (Lp.coeFn_add (a • F) F'), up (Lp.coeFn_smul a F), e, e'] with x h1 h2 h3 h4`. Rewrite using `[h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]`.

Both sides reduce to the same expression. Establish `hI : Integrable (fun q => ⟪F q, F' q⟫_ℂ) (nuQ V μ 𝓕)` using `L2.integrable_inner F F'`. Establish `hae : (fun x => ⟪F (autMk V x), F' (autMk V x)⟫_ℂ) =ᵐ[μ.restrict 𝓕] fun x => star (ψ x) * ψ' x`. Use `ae_restrict_of_ae ?_` and prove the remaining obligations. Use `filter_upwards [e, e'] with x h1 h2`.

Rewrite using `[h1, h2]`. Simplify using `[mul_comm]`. Use `⟨((integrable_map_measure hI.aestronglyMeasurable hm.aemeasurable).1 hI).congr hae, ?_⟩` and prove the remaining obligations. Rewrite using `[L2.inner_def, ← integral_congr_ae hae]`. Conclude with `integral_map hm.aemeasurable hI.aestronglyMeasurable`.
-/
theorem repr_properties : ∀ (D : D7) (V : HSp D), ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → (∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → ∃ F, Repr V μ 𝓕 F φ) ∧ (∀ F ψ ψ', Continuous ψ → Continuous ψ' → Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F ψ' → ψ = ψ') ∧ (∀ F F' ψ, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ → F = F') ∧ (∀ F ψ g, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 (ρ g F) (rTr V g ψ)) ∧ (∀ F F' ψ ψ' (a : ℂ), Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → Repr V μ 𝓕 (a • F + F') (a • ψ + ψ')) ∧ ∀ F F' ψ ψ', Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → IntegrableOn (fun x => star (ψ x) * ψ' x) 𝓕 μ ∧ ⟪F, F'⟫_ℂ = ∫ x in 𝓕, star (ψ x) * ψ' x ∂μ := by
  intro D V μ 𝓕 ρ hp hr
  obtain ⟨-, -, -, hB, hT, -, hC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hp.haar
  haveI := hp.right
  have hm : Measurable (autMk V) := meas_mk
  haveI : IsFiniteMeasure (nuQ V μ 𝓕) := ⟨by
    rw [nuQ, Measure.map_apply hm MeasurableSet.univ]
    simpa [lt_top_iff_ne_top] using hp.fin⟩
  have up : ∀ {p : AutQ V → Prop}, (∀ᵐ q ∂(nuQ V μ 𝓕), p q) → ∀ᵐ x ∂μ, p (autMk V x) := fun h => ae_up hp.fd h
  refine ⟨fun φ hφ hinv ⟨C, hC⟩ => ?_, fun F ψ ψ' h h' e e' => ?_, fun F F' ψ e e' => ?_, fun F ψ g e => ?_,
    fun F F' ψ ψ' a e e' => ?_, fun F F' ψ ψ' e e' => ?_⟩
  · let f : AutQ V → ℂ := Quotient.lift φ fun a b hab => by
      have := hinv _ (QuotientGroup.rightRel_apply.1 hab) a
      rw [inv_mul_cancel_right] at this
      exact this.symm
    have hf : Measurable f := measurable_from_quotient.2 hφ.measurable
    have hL : MemLp f 2 (nuQ V μ 𝓕) :=
      MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun q => by
        induction q using Quotient.inductionOn with
        | h x => exact hC x)
    exact ⟨hL.toLp f, up hL.coeFn_toLp⟩
  · refine (h.ae_eq_iff_eq μ h').1 ?_
    filter_upwards [e, e'] with x h1 h2
    rw [← h1, h2]
  · refine Lp.ext ?_
    refine (ae_map_iff hm.aemeasurable
      ((Lp.stronglyMeasurable F).measurableSet_eq_fun (Lp.stronglyMeasurable F'))).2 (ae_restrict_of_ae ?_)
    filter_upwards [e, e'] with x h1 h2
    rw [h1, h2]
  · have e2 := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae e
    filter_upwards [hr.val g F, e2] with x h1 h2
    rw [h1, h2]; rfl
  · filter_upwards [up (Lp.coeFn_add (a • F) F'), up (Lp.coeFn_smul a F), e, e'] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]; rfl
  · have hI : Integrable (fun q => ⟪F q, F' q⟫_ℂ) (nuQ V μ 𝓕) := L2.integrable_inner F F'
    have hae : (fun x => ⟪F (autMk V x), F' (autMk V x)⟫_ℂ) =ᵐ[μ.restrict 𝓕] fun x => star (ψ x) * ψ' x := by
      refine ae_restrict_of_ae ?_
      filter_upwards [e, e'] with x h1 h2
      rw [h1, h2]
      simp [mul_comm]
    refine ⟨((integrable_map_measure hI.aestronglyMeasurable hm.aemeasurable).1 hI).congr hae, ?_⟩
    rw [L2.inner_def, ← integral_congr_ae hae]
    exact integral_map hm.aemeasurable hI.aestronglyMeasurable

end GlobalTheory.HolDict.RepresentativeL2
