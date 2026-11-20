import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [IsTotallyReal F] in

/- English proof (translation)
Introduce `M r ha D La g x hD hx hx0 hmin`. Use `set c : InfinitePlace E → ℝ := fun w => (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re with hc`. Establish `hcpos : ∀ w, 0 < c w` using `h₄ M g x hx0`. Establish `hdeg : finrank ℚ E = 2 * finrank ℚ F`. Rewrite using `[← Module.finrank_mul_finrank ℚ F E, Algebra.IsQuadraticExtension.finrank_eq_two F E, mul_comm]`.

Establish `hlen : ∀ a : E, M.len (invApply g (vecAt v (a • x))) ^ 2 = ∑ w, c w * ‖w.embedding a‖ ^ 2`. Introduce `a`. Rewrite using `[h₃ M g x a]`. Conclude with `Finset.sum_congr rfl fun w _ => mul_comm _ _`. Establish `hlen1 : M.len (invApply g (vecAt v x)) ^ 2 = ∑ w, c w`.

Use `hlen 1` as an intermediate fact. Simplify using `using this`. Establish `hsub : intSubgroup E ≤ lineCoeffs La x`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `hD.isLattice.smul_mem a x hx`.

Establish `hfg : (lineCoeffs La x).FG` using `h₂ La x hD.isLattice.fg hx0`. Establish `hmin' : ∀ a ∈ lineCoeffs La x, a ≠ 0 → ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2`. Introduce `a haA ha0`. Establish `hax : a • x ∈ La` using `haA`. Establish `hax0 : a • x ≠ 0` using `smul_ne_zero ha0 hx0`.

Establish `hle` using `hmin (a • x) hax hax0`. Rewrite using `[← hlen1, ← hlen a]`. Conclude with `pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2`. Take `⟨a, hali, habs⟩` from `ha`. Establish `ha' : ∃ b : Fin (finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (b i : E)) ∧ ∀ i (σ : E →+* ℂ), ‖σ (b i)‖ ≤ r` using `⟨a ∘ Fin.cast hdeg, hali.comp _ (Fin.cast_injective hdeg), fun i σ => habs _ σ⟩`.

Establish `key` using `h₅ c hcpos (lineCoeffs La x) hsub hfg hmin' r ha'`. Rewrite using `[h₁ La x hx0]`. Rewrite `key` using `[hdeg]`. Move the coercions through the operations in `at key`. Conclude with `key`.
-/
theorem ShortestVectorIndex.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : LineIndexCoeffs.Statement (E := E) W) (h₂ : LineCoeffsFG.Statement (E := E) W)
    (h₃ : WeightedLenSmul.Statement h v) (h₄ : WeightPos.Statement h v)
    (h₅ : WeightedIndexBound.Statement E) : ShortestVectorIndex.Statement h v := by
  intro M r ha D La g x hD hx hx0 hmin
  set c : InfinitePlace E → ℝ := fun w =>
    (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re with hc
  have hcpos : ∀ w, 0 < c w := h₄ M g x hx0
  have hdeg : finrank ℚ E = 2 * finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F E, Algebra.IsQuadraticExtension.finrank_eq_two F E,
      mul_comm]

  have hlen : ∀ a : E, M.len (invApply g (vecAt v (a • x))) ^ 2 =
      ∑ w, c w * ‖w.embedding a‖ ^ 2 := by
    intro a
    rw [h₃ M g x a]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have hlen1 : M.len (invApply g (vecAt v x)) ^ 2 = ∑ w, c w := by
    have := hlen 1
    simpa using this
  have hsub : intSubgroup E ≤ lineCoeffs La x := by
    rintro _ ⟨a, rfl⟩
    exact hD.isLattice.smul_mem a x hx
  have hfg : (lineCoeffs La x).FG := h₂ La x hD.isLattice.fg hx0
  have hmin' : ∀ a ∈ lineCoeffs La x, a ≠ 0 →
      ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2 := by
    intro a haA ha0
    have hax : a • x ∈ La := haA
    have hax0 : a • x ≠ 0 := smul_ne_zero ha0 hx0
    have hle := hmin (a • x) hax hax0
    rw [← hlen1, ← hlen a]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  obtain ⟨a, hali, habs⟩ := ha
  have ha' : ∃ b : Fin (finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (b i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (b i)‖ ≤ r :=
    ⟨a ∘ Fin.cast hdeg, hali.comp _ (Fin.cast_injective hdeg), fun i σ => habs _ σ⟩
  have key := h₅ c hcpos (lineCoeffs La x) hsub hfg hmin' r ha'
  rw [h₁ La x hx0]
  rw [hdeg] at key
  push_cast at key
  exact key

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
