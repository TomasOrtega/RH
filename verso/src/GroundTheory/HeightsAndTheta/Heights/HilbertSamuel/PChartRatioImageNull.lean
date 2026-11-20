import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartImageNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

/- English proof (translation)
Set `E : ((Σ _ : Fin e, Fin 2) → ℝ) ≃L[ℝ] (Fin e → ℂ)` to `(Pi.basis (fun _ : Fin e => Complex.basisOneI)).equivFun.symm.toContinuousLinearEquiv`. Establish `hcard : Fintype.card (Σ _ : Fin e, Fin 2) = 2 * e`. Simplify using `[Fintype.card_sigma, mul_comm]`. Establish `hT : volume (E ⁻¹' S) = 0`. Rewrite using `[← hausdorffMeasure_pi_real, hcard]`.

Establish `h` using `hausdorffMeasure_of_dimH_lt (s := E ⁻¹' S) (d := ((2 * e : ℕ) : ℝ≥0)) (by`. Rewrite using `[ContinuousLinearEquiv.dimH_preimage]`. Simplify using `using hS)`. Simplify using `using h`. Establish `: (Measure.map E volume).IsAddHaarMeasure` using `E.isAddHaarMeasure_map volume`.

Establish `hac : (volume : Measure (Fin e → ℂ)) ≪ Measure.map E volume` using `Measure.absolutelyContinuous_isAddHaarMeasure _ _`. Apply `hac` to reduce the goal to its premises. Conclude with `(E.toHomeomorph.toMeasurableEquiv.map_apply S).trans hT`.
-/
theorem ChartRatioImageNull.volume_eq_zero_of_dimH_lt {e : ℕ} {S : Set (Fin e → ℂ)}
    (hS : dimH S < 2 * (e : ℝ≥0∞)) : volume S = 0 := by
  let E : ((Σ _ : Fin e, Fin 2) → ℝ) ≃L[ℝ] (Fin e → ℂ) :=
    (Pi.basis (fun _ : Fin e => Complex.basisOneI)).equivFun.symm.toContinuousLinearEquiv
  have hcard : Fintype.card (Σ _ : Fin e, Fin 2) = 2 * e := by
    simp [Fintype.card_sigma, mul_comm]
  have hT : volume (E ⁻¹' S) = 0 := by
    rw [← hausdorffMeasure_pi_real, hcard]
    have h := hausdorffMeasure_of_dimH_lt (s := E ⁻¹' S) (d := ((2 * e : ℕ) : ℝ≥0)) (by
      rw [ContinuousLinearEquiv.dimH_preimage]
      simpa using hS)
    simpa using h
  have : (Measure.map E volume).IsAddHaarMeasure := E.isAddHaarMeasure_map volume
  have hac : (volume : Measure (Fin e → ℂ)) ≪ Measure.map E volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply hac
  exact (E.toHomeomorph.toMeasurableEquiv.map_apply S).trans hT

/- English proof (translation)
Introduce `K _ ι _ J e Ψ hdim`. Use `set S := {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ J, Ψ (segre z) 0 ≠ 0 ∧ (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)} with hSdef`. Distinguish the cases in `hJ : J = ⊤`. Establish `hS : S = ∅`. Use extensionality with `y`.

Simplify using `only [hSdef, mem_ofPred_eq, mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨z, hz, -⟩`. Establish `h1` using `hz 1 (hJ ▸ Submodule.mem_top)`. Simplify using `at h1`. Rewrite using `[hS, measure_empty]`.

Establish `: Nontrivial (MvPolynomial (Σ k, ι k) ℂ ⧸ J)` using `Ideal.Quotient.nontrivial_iff.mpr hJ`. Establish `h0` using `ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Σ k, ι k) ℂ ⧸ J)`. Choose the witnesses or unpack the hypotheses as in `⟨m, rfl⟩ : ∃ m, e = m + 1 := by`. Break down `e with _ | m` into its components or cases. Conclude with `absurd (h0.trans_lt hdim) (by simp)`.

Conclude with `⟨m, rfl⟩`. Establish `hle : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) ≤ (m : WithBot ℕ∞)`. Break down `hx : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) with _ | x` into its components or cases. Conclude with `bot_le`. Rewrite `hdim` using `[hx]`.

Establish `hx' : x < (m : ℕ∞) + 1`. Establish `h5 : ((x : WithBot ℕ∞)) < (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)` using `hdim`. Establish `h6` using `WithBot.coe_lt_coe.1 h5`. Conclude with `h6` after adjusting the coercions. Conclude with `WithBot.coe_le_coe.2 ((ENat.lt_add_one_iff (ENat.natCast_ne_top m)).1 hx')`.

Set `eqv : (Σ k, ι k) ≃ Fin (Fintype.card (Σ k, ι k))` to `Fintype.equivFin _`. Set `J' : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)` to `J.map (rename eqv)`. Establish `hdim' : ringKrullDim (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J') ≤ (m : WithBot ℕ∞)`. Rewrite using `[← ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv J J' (renameEquiv ℂ eqv).toRingEquiv rfl)]`. Conclude with `hle`.

Establish `hV'` using `GroundTheory.Heights₂.Heights.ZeroLocusDimH.full _ m J' hdim'`. Set `L : ((Σ k, ι k) → ℂ) ≃L[ℂ] (Fin (Fintype.card (Σ k, ι k)) → ℂ)` to `(LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) eqv).toContinuousLinearEquiv`. Establish `hVsub : zeroLocus ℂ J ⊆ L ⁻¹' {x | ∀ q ∈ J', eval x q = 0}`. Introduce `z hz q hq`. Establish `hJle : J ≤ (RingHom.ker (eval (L z))).comap (rename eqv)`.

Introduce `p hp`. Simplify using `only [Ideal.mem_comap, RingHom.mem_ker, eval_rename]`. Establish `h2 : (L z) ∘ eqv = z`. Use function extensionality and compare the values at `i`. Simplify using `[L]`.

Rewrite using `[h2]`. Simplify `hz p hp` using `[MvPolynomial.coe_aeval_eq_eval]`. Conclude with `Ideal.map_le_iff_le_comap.mpr hJle hq`. Establish `hV : dimH (zeroLocus ℂ J : Set ((Σ k, ι k) → ℂ)) ≤ 2 * (m : ℝ≥0∞)` using `(dimH_mono hVsub).trans ((L.dimH_preimage _).le.trans hV')`. Set `G : ((Σ k, ι k) → ℂ) → (Fin (m + 1) → ℂ)` to `fun z j => (Ψ (segre z) 0)⁻¹ * Ψ (segre z) j.succ`.

Set `U` to `{z : (Σ k, ι k) → ℂ | Ψ (segre z) 0 ≠ 0}`. Establish `hSsub : S ⊆ G '' (zeroLocus ℂ J ∩ U)`. Introduce and unpack `y ⟨z, hz, hz0, hy⟩`. Use `⟨z, ⟨hz, hz0⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`.

Establish `h3` using `congrFun hy j.succ`. Simplify `h3.symm` using `[G]`. Establish `hsmooth : ContDiff ℂ ⊤ (fun z : (Σ k, ι k) → ℂ => Ψ (segre z))`. Establish `h1 : ContDiff ℂ ⊤ (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ)`. Apply `contDiff_pi.2` to reduce the goal to its premises.

Introduce `i`. Conclude with `contDiff_prod (fun k _ => contDiff_apply ℂ ℂ _)`. Conclude with `(LinearMap.toContinuousLinearMap Ψ).contDiff.comp h1`. Establish `hc : ∀ i, ContDiff ℂ ⊤ (fun z : (Σ k, ι k) → ℂ => Ψ (segre z) i)` using `fun i => (contDiff_apply ℂ ℂ i).comp hsmooth`. Establish `hG : ∀ z ∈ U, ContDiffAt ℂ 1 G z`.

Introduce `z hz`. Apply `contDiffAt_pi.2` to reduce the goal to its premises. Introduce `j`. Conclude with `(((hc 0).contDiffAt.inv hz).mul (hc j.succ).contDiffAt).of_le le_top`. Establish `hGdim : dimH (G '' (zeroLocus ℂ J ∩ U)) ≤ dimH (zeroLocus ℂ J ∩ U)`.

Apply `dimH_image_le_of_locally_lipschitzOn` to reduce the goal to its premises. Introduce `z hz`. Take `⟨C, t, ht, hlip⟩` from `(hG z hz.2).exists_lipschitzOnWith`. Conclude with `⟨C, t, mem_nhdsWithin_of_mem_nhds ht, hlip⟩`. Apply `ChartRatioImageNull.volume_eq_zero_of_dimH_lt` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Establish `h4 : 2 * m < 2 * (m + 1)` using `by omega`. Conclude with `h4` after adjusting the coercions.
-/
theorem ChartRatioImageNull.proof : ChartRatioImageNull.Statement := by
  intro K _ ι _ J e Ψ hdim
  classical
  set S := {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ J, Ψ (segre z) 0 ≠ 0 ∧
    (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)} with hSdef
  by_cases hJ : J = ⊤
  · have hS : S = ∅ := by
      ext y
      simp only [hSdef, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨z, hz, -⟩
      have h1 := hz 1 (hJ ▸ Submodule.mem_top)
      simp at h1
    rw [hS, measure_empty]
  have : Nontrivial (MvPolynomial (Σ k, ι k) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Σ k, ι k) ℂ ⧸ J)
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := by
    rcases e with _ | m
    · exact absurd (h0.trans_lt hdim) (by simp)
    · exact ⟨m, rfl⟩
  have hle : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) ≤ (m : WithBot ℕ∞) := by
    rcases hx : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) with _ | x
    · exact bot_le
    · rw [hx] at hdim
      have hx' : x < (m : ℕ∞) + 1 := by
        have h5 : ((x : WithBot ℕ∞)) < (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := hdim
        have h6 := WithBot.coe_lt_coe.1 h5
        exact_mod_cast h6
      exact WithBot.coe_le_coe.2 ((ENat.lt_add_one_iff (ENat.natCast_ne_top m)).1 hx')

  let eqv : (Σ k, ι k) ≃ Fin (Fintype.card (Σ k, ι k)) := Fintype.equivFin _
  let J' : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) := J.map (rename eqv)
  have hdim' : ringKrullDim (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J') ≤ (m : WithBot ℕ∞) := by
    rw [← ringKrullDim_eq_of_ringEquiv
      (Ideal.quotientEquiv J J' (renameEquiv ℂ eqv).toRingEquiv rfl)]
    exact hle
  have hV' := GroundTheory.Heights₂.Heights.ZeroLocusDimH.full _ m J' hdim'
  let L : ((Σ k, ι k) → ℂ) ≃L[ℂ] (Fin (Fintype.card (Σ k, ι k)) → ℂ) :=
    (LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) eqv).toContinuousLinearEquiv
  have hVsub : zeroLocus ℂ J ⊆ L ⁻¹' {x | ∀ q ∈ J', eval x q = 0} := by
    intro z hz q hq
    have hJle : J ≤ (RingHom.ker (eval (L z))).comap (rename eqv) := by
      intro p hp
      simp only [Ideal.mem_comap, RingHom.mem_ker, eval_rename]
      have h2 : (L z) ∘ eqv = z := by
        funext i; simp [L]
      rw [h2]
      simpa [MvPolynomial.coe_aeval_eq_eval] using hz p hp
    exact Ideal.map_le_iff_le_comap.mpr hJle hq
  have hV : dimH (zeroLocus ℂ J : Set ((Σ k, ι k) → ℂ)) ≤ 2 * (m : ℝ≥0∞) :=
    (dimH_mono hVsub).trans ((L.dimH_preimage _).le.trans hV')

  let G : ((Σ k, ι k) → ℂ) → (Fin (m + 1) → ℂ) := fun z j => (Ψ (segre z) 0)⁻¹ * Ψ (segre z) j.succ
  let U := {z : (Σ k, ι k) → ℂ | Ψ (segre z) 0 ≠ 0}
  have hSsub : S ⊆ G '' (zeroLocus ℂ J ∩ U) := by
    rintro y ⟨z, hz, hz0, hy⟩
    refine ⟨z, ⟨hz, hz0⟩, ?_⟩
    funext j
    have h3 := congrFun hy j.succ
    simpa [G] using h3.symm
  have hsmooth : ContDiff ℂ ⊤ (fun z : (Σ k, ι k) → ℂ => Ψ (segre z)) := by
    have h1 : ContDiff ℂ ⊤ (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) := by
      apply contDiff_pi.2
      intro i
      exact contDiff_prod (fun k _ => contDiff_apply ℂ ℂ _)
    exact (LinearMap.toContinuousLinearMap Ψ).contDiff.comp h1
  have hc : ∀ i, ContDiff ℂ ⊤ (fun z : (Σ k, ι k) → ℂ => Ψ (segre z) i) :=
    fun i => (contDiff_apply ℂ ℂ i).comp hsmooth
  have hG : ∀ z ∈ U, ContDiffAt ℂ 1 G z := by
    intro z hz
    apply contDiffAt_pi.2
    intro j
    exact (((hc 0).contDiffAt.inv hz).mul (hc j.succ).contDiffAt).of_le le_top
  have hGdim : dimH (G '' (zeroLocus ℂ J ∩ U)) ≤ dimH (zeroLocus ℂ J ∩ U) := by
    apply dimH_image_le_of_locally_lipschitzOn
    intro z hz
    obtain ⟨C, t, ht, hlip⟩ := (hG z hz.2).exists_lipschitzOnWith
    exact ⟨C, t, mem_nhdsWithin_of_mem_nhds ht, hlip⟩
  apply ChartRatioImageNull.volume_eq_zero_of_dimH_lt
  calc dimH S ≤ dimH (G '' (zeroLocus ℂ J ∩ U)) := dimH_mono hSsub
    _ ≤ dimH (zeroLocus ℂ J ∩ U) := hGdim
    _ ≤ dimH (zeroLocus ℂ J : Set ((Σ k, ι k) → ℂ)) := dimH_mono inter_subset_left
    _ ≤ 2 * (m : ℝ≥0∞) := hV
    _ < 2 * ((m + 1 : ℕ) : ℝ≥0∞) := by
      have h4 : 2 * m < 2 * (m + 1) := by omega
      exact_mod_cast h4

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
