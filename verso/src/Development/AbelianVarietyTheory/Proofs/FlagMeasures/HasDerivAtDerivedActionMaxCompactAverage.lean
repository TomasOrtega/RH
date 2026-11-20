import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

/- English proof (translation)
Establish `hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ` using `hσ'`. Take `⟨hprob, hK0, -, -⟩` from `hμ`. Establish `hKc` using `isCompact_KH k r`. Establish `hae : ∀ᵐ g ∂μ, g ∈ GlobalTheory.ThA.KH k r` using `mem_ae_iff.2 hK0`. Establish `hres : μ.restrict (GlobalTheory.ThA.KH k r) = μ` using `Measure.restrict_eq_self_of_ae_mem hae`.

Establish `hint : ∀ D' : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), (∀ Y ∈ D', Formalism.MainNotions.S.InLieHpk k r Y) → Integrable (fun g => φ g • Formalism.MainNotions.S.dsigW (k` using `k) (r := r) σ D' (σ g v)) μ := by`. Introduce `D' hD'`. Establish `h1 : ContinuousOn (fun g => φ g • Formalism.MainNotions.S.dsigW (k` using `k) (r := r) σ D' (σ g v)) (GlobalTheory.ThA.KH k r) := hφ.continuousOn.smul ((Formalism.MainNotions.LowestKTypeMultiplicity.orbit_cont hσ hv D' hD').mono Set.inter_subset_left)`. Establish `h2 : IntegrableOn (fun g => φ g • Formalism.MainNotions.S.dsigW (k` using `k) (r := r) σ D' (σ g v)) (GlobalTheory.ThA.KH k r) μ := h1.integrableOn_compact hKc`. Rewrite `h2` using `[IntegrableOn, hres]`. Then use the resulting hypothesis.

Establish `hXD : ∀ Y ∈ X :: D, Formalism.MainNotions.S.InLieHpk k r Y`. Introduce `Y hY`. Break down `List.mem_cons.1 hY with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `hX`.

Conclude with `hD Y h`. Establish `hexp` using `Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX`. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ) (x₀ := (0 : ℝ)) (F := fun (t : ℝ) g => σ (NormedSpace.exp ((t : ℂ) • X)) (φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v))) (F' := fun (t : ℝ) g => σ (NormedSpace.exp ((t : ℂ) • X)) (φ g • Formal …`. Establish `hsm` using `Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv hg.1`. Establish `h0` using `(Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hsm D hD hX).const_smul (φ g)`.

Establish `h1` using `((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0`. Rewrite `h1` using `[← sub_self t]`. Establish `h2` using `h1.comp_sub_const t t`. Simplify using `only [map_smul]`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `s`. Establish `e : NormedSpace.exp ((s : ℂ) • X) = NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((s - t : ℝ) : ℂ) • X)`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _), ← add_smul]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hσ.1.2 _ (hexp t) _ (hexp (s - t))]`. Simplify using `only [Function.comp, Pi.smul_apply, ContinuousLinearMap.coe_restrictScalars', map_smul]`. Both sides reduce to the same expression. Use the proof step `simp)`.

Establish `h3` using `key.2`. Simplify using `only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, one_apply_eq_self] at h3`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`. Conclude with `((σ _).integral_comp_comm (hint D hD)).symm`.
-/
theorem hasDerivAt_exp_integral_dsigW (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ) (v : H)
    (D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hσ' : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hμ : GlobalTheory.KFinAvg.IsHaarKH k r μ)
    (hφ : Continuous φ) (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v)
    (hD : ∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) (hX : Formalism.MainNotions.S.InLieHpk k r X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X))
        (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ))
      (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v) ∂μ) 0 := by
  have hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ := hσ'
  obtain ⟨hprob, hK0, -, -⟩ := hμ
  have hKc := isCompact_KH k r
  have hae : ∀ᵐ g ∂μ, g ∈ GlobalTheory.ThA.KH k r := mem_ae_iff.2 hK0
  have hres : μ.restrict (GlobalTheory.ThA.KH k r) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hint : ∀ D' : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      (∀ Y ∈ D', Formalism.MainNotions.S.InLieHpk k r Y) →
      Integrable (fun g => φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D' (σ g v)) μ := by
    intro D' hD'
    have h1 : ContinuousOn (fun g => φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D' (σ g v)) (GlobalTheory.ThA.KH k r) :=
      hφ.continuousOn.smul ((Formalism.MainNotions.LowestKTypeMultiplicity.orbit_cont hσ hv D' hD').mono Set.inter_subset_left)
    have h2 : IntegrableOn (fun g => φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D' (σ g v)) (GlobalTheory.ThA.KH k r) μ :=
      h1.integrableOn_compact hKc
    rwa [IntegrableOn, hres] at h2
  have hXD : ∀ Y ∈ X :: D, Formalism.MainNotions.S.InLieHpk k r Y := by
    intro Y hY
    rcases List.mem_cons.1 hY with h | h
    · rw [h]; exact hX
    · exact hD Y h
  have hexp := Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ) (x₀ := (0 : ℝ))
    (F := fun (t : ℝ) g => σ (NormedSpace.exp ((t : ℂ) • X))
      (φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v)))
    (F' := fun (t : ℝ) g => σ (NormedSpace.exp ((t : ℂ) • X))
      (φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v)))
    (bound := fun g => ‖φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v)‖) (s := Set.univ)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      ((σ (NormedSpace.exp ((t : ℂ) • X))).integrable_comp (hint D hD)).aestronglyMeasurable)
    ((σ _).integrable_comp (hint D hD))
    ((σ _).integrable_comp (hint _ hXD)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g t _ => (hσ.2.1 _ (hexp t) _).le)
    (hint _ hXD).norm
    (by
      filter_upwards [hae] with g hg t _
      have hsm := Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv hg.1
      have h0 := (Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hsm D hD hX).const_smul (φ g)
      have h1 := ((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
      rw [← sub_self t] at h1
      have h2 := h1.comp_sub_const t t
      simp only [map_smul]
      convert h2 using 1
      · funext s
        have e : NormedSpace.exp ((s : ℂ) • X) =
            NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((s - t : ℝ) : ℂ) • X) := by
          rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _), ← add_smul]
          congr 2
          push_cast; ring
        rw [e, hσ.1.2 _ (hexp t) _ (hexp (s - t))]
        simp only [Function.comp, Pi.smul_apply, ContinuousLinearMap.coe_restrictScalars', map_smul]
        rfl
      · simp)
  have h3 := key.2
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, one_apply_eq_self] at h3
  convert h3 using 1
  funext t
  exact ((σ _).integral_comp_comm (hint D hD)).symm

end GlobalTheory.KFinAvg
