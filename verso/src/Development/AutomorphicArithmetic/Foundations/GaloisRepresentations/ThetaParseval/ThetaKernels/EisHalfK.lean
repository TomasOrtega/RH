import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHalfHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisHalfKAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSeriesAbsoluteConvergence
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSeriesLeftInvariance

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)
namespace GlobalTheory.CompanionTheory.SiegelEisHalf
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n Y r' s' hB hn hY χ _ c _ b K a hb hK ha s₁ f hf`. Take `⟨Ê, t, hsum, hhol⟩` from `_root_.GlobalTheory.T.eisenstein_series_absolute_convergence F E σ B n Y r' s' hB hn hY b K a hb hK ha χ s₁ f hf`. Take `⟨t₀, hmod⟩` from `_root_.GlobalTheory.T.eisenstein_series_left_invariance F E σ B n Y r' s' hB hn hY b K a hb hK ha χ s₁ f hf`. Take `⟨t', ht, ht₀⟩ : ∃ t' : ℝ, t ≤ t' ∧ t₀ ≤ t'` from `⟨max t t₀, le_max_left _ _, le_max_right _ _⟩`. Establish `hsum' : ∀ s : ℂ, t' < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)` using `fun s hs => hsum s (lt_of_le_of_lt ht hs)`.

Take `⟨hmem, hcont, hbd⟩` from `hmod t' Ê ht₀ hsum'`. Set `v : ℂ → modFun σ Y` to `fun s => if h : t' < s.re then ⟨fun x => Ê s x, hmem s h⟩ else 0`. Establish `hv : ∀ s : ℂ, t' < s.re → ∀ x, (v s).1 x = Ê s x`. Introduce `s h x`. Simplify using `only [v, dif_pos h]`.

Use `⟨t', v, fun s h x => by rw [hv s h x]; exact hsum' s h x, ?_⟩` and prove the remaining obligations. Establish `hS : IsOpen {s : ℂ | t' < s.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Use `GlobalTheory.CompanionTheory.WeakHolo.wholo_growForms v hS ?_ ?_ ?_` and prove the remaining obligations. Introduce `x`. Conclude with `((hhol x).mono fun s hs => lt_of_le_of_lt ht hs).congr fun s hs => hv s hs x`.

Use `hcont.congr ?_` and prove the remaining obligations. Introduce and unpack `⟨s, x⟩ ⟨hs, -⟩`. Conclude with `hv s hs x`. Introduce `Q hQ hQc`. Break down `Q.eq_empty_or_nonempty with rfl | hne` into its components or cases.

Conclude with `⟨0, 0, by simp⟩`. Take `⟨z₁, hz₁, hmin⟩` from `hQc.exists_isMinOn hne Complex.continuous_re.continuousOn`. Take `⟨z₂, -, hmax⟩` from `hQc.exists_isMaxOn hne Complex.continuous_re.continuousOn`. Take `⟨C, N, h⟩` from `hbd z₁.re z₂.re (hQ hz₁)`. Use `⟨C, N, fun s hs x => ?_⟩` and prove the remaining obligations.

Rewrite using `[hv s (hQ hs) x]`. Conclude with `h s (hmin hs) (hmax hs) x`.
-/
theorem eisHalf_k : _root_.SiegelEisensteinSeries.EisHalf_k := by
  intro F E _ _ _ _ _ σ B n Y r' s' hB hn hY χ _ c _ b K a hb hK ha s₁ f hf
  obtain ⟨Ê, t, hsum, hhol⟩ := _root_.GlobalTheory.T.eisenstein_series_absolute_convergence F E σ B n Y r' s' hB hn hY b K a hb hK ha χ s₁ f hf
  obtain ⟨t₀, hmod⟩ := _root_.GlobalTheory.T.eisenstein_series_left_invariance F E σ B n Y r' s' hB hn hY b K a hb hK ha χ s₁ f hf
  obtain ⟨t', ht, ht₀⟩ : ∃ t' : ℝ, t ≤ t' ∧ t₀ ≤ t' := ⟨max t t₀, le_max_left _ _, le_max_right _ _⟩
  have hsum' : ∀ s : ℂ, t' < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x) :=
    fun s hs => hsum s (lt_of_le_of_lt ht hs)
  obtain ⟨hmem, hcont, hbd⟩ := hmod t' Ê ht₀ hsum'
  classical
  let v : ℂ → modFun σ Y := fun s => if h : t' < s.re then ⟨fun x => Ê s x, hmem s h⟩ else 0
  have hv : ∀ s : ℂ, t' < s.re → ∀ x, (v s).1 x = Ê s x := by
    intro s h x
    simp only [v, dif_pos h]
  refine ⟨t', v, fun s h x => by rw [hv s h x]; exact hsum' s h x, ?_⟩
  have hS : IsOpen {s : ℂ | t' < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine GlobalTheory.CompanionTheory.WeakHolo.wholo_growForms v hS ?_ ?_ ?_
  · intro x
    exact ((hhol x).mono fun s hs => lt_of_le_of_lt ht hs).congr fun s hs => hv s hs x
  · refine hcont.congr ?_
    rintro ⟨s, x⟩ ⟨hs, -⟩
    exact hv s hs x
  · intro Q hQ hQc
    rcases Q.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, 0, by simp⟩
    obtain ⟨z₁, hz₁, hmin⟩ := hQc.exists_isMinOn hne Complex.continuous_re.continuousOn
    obtain ⟨z₂, -, hmax⟩ := hQc.exists_isMaxOn hne Complex.continuous_re.continuousOn
    obtain ⟨C, N, h⟩ := hbd z₁.re z₂.re (hQ hz₁)
    refine ⟨C, N, fun s hs x => ?_⟩
    rw [hv s (hQ hs) x]
    exact h s (hmin hs) (hmax hs) x
end GlobalTheory.CompanionTheory.SiegelEisHalf
end
end
