import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisLocallyMonomialStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
open Filter Topology

noncomputable section

namespace GlobalTheory.PMon.Gauss

/- English proof (translation)
Unfold `gC`. Use `split_ifs with h`. Establish `hN` using `Classical.choose_spec h set N := Classical.choose h`. Establish `hm` using `hN.2.2.2.1 ((l : Formalism.Per.Acris l)) 0`. Establish `hl : N (l : Formalism.Per.Acris l) = ρ`.

Use `hN.2.2.2.2 (l : Formalism.Per.Ainf l)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Rewrite using `[this]`. Conclude with `GlobalTheory.GaussSlope.gauss_l l h0`. Rewrite `hm` using `[mul_zero, hl]`.

Establish `: (1 - ρ) * N 0 = 0` using `by linarith`. Break down `mul_eq_zero.1 this with h' | h'` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h'`. Both sides reduce to the same expression.
-/
theorem gC_zero_of_lt_one (l : ℕ) [Fact l.Prime] {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    gC l ρ (0 : Formalism.Per.Acris l) = 0 := by
  unfold gC
  split_ifs with h
  · have hN := Classical.choose_spec h
    set N := Classical.choose h
    have hm := hN.2.2.2.1 ((l : Formalism.Per.Acris l)) 0
    have hl : N (l : Formalism.Per.Acris l) = ρ := by
      have := hN.2.2.2.2 (l : Formalism.Per.Ainf l)
      rw [map_natCast] at this
      rw [this]
      exact GlobalTheory.GaussSlope.gauss_l l h0
    rw [mul_zero, hl] at hm
    have : (1 - ρ) * N 0 = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  · rfl

/- English proof (translation)
Establish `hl0 : (0 : ℝ) < (l : ℝ)⁻¹`. Establish `: (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Check the signs of the components of the expression. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality.

Use `(continuousOn_const (c := (0 : ℝ))).congr fun ρ hρ => ?_` and prove the remaining obligations. Conclude with `gC_zero_of_lt_one l (hl0.le.trans hρ.1) hρ.2`. Introduce `ρ₀ hρ₀`. Establish `hpos : 0 < ρ₀` using `hl0.trans_le hρ₀.1`. Take `⟨⟨c, k, ρ₂, -, h02, -, hR⟩, hL⟩` from `GlobalTheory.T.gaussNormAcris_locally_monomial l x hx ρ₀ hρ₀.1 hρ₀.2`.

Establish `hS : Set.Ico (l : ℝ)⁻¹ 1 = (Set.Ico (l : ℝ)⁻¹ 1 ∩ Set.Iic ρ₀) ∪ (Set.Ico (l : ℝ)⁻¹ 1 ∩ Set.Ici ρ₀)`. Use extensionality with `y`. Simplify using `only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Break down `le_total y ρ₀ with h | h` into its components or cases. Conclude with `Or.inl ⟨hy, h⟩`. Conclude with `Or.inr ⟨hy, h⟩`. Apply the tactic sequence `rintro (h | h) <;> exact h.1`. Rewrite using `[ContinuousWithinAt, hS, ← ContinuousWithinAt, continuousWithinAt_union]`.

Prove the components needed by the constructor for the conclusion. Break down `eq_or_lt_of_le hρ₀.1 with heq | hlt` into its components or cases. Use `(continuousWithinAt_singleton (f := fun ρ => gC l ρ x) (x := ρ₀)).mono ?_` and prove the remaining obligations. Introduce and unpack `y ⟨hy1, hy2⟩`. Conclude with `le_antisymm hy2 (heq ▸ hy1.1)`.

Take `⟨c', k', ρ₁, -, -, h10, hL'⟩` from `hL hlt`. Establish `hg : ContinuousWithinAt (fun ρ : ℝ => c' * ρ ^ k') (Set.Iic ρ₀) ρ₀` using `(continuousAt_const.mul (continuousAt_zpow₀ ρ₀ k' (Or.inl hpos.ne'))).continuousWithinAt`. Establish `hg' : ContinuousWithinAt (fun ρ => gC l ρ x) (Set.Icc ρ₁ ρ₀) ρ₀` using `(hg.mono Set.Icc_subset_Iic_self).congr (fun y hy => hL' y hy) (hL' ρ₀ ⟨h10.le, le_rfl⟩)`. Conclude with `(hg'.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE h10)).mono Set.inter_subset_right`. Establish `hg : ContinuousWithinAt (fun ρ : ℝ => c * ρ ^ k) (Set.Ici ρ₀) ρ₀` using `(continuousAt_const.mul (continuousAt_zpow₀ ρ₀ k (Or.inl hpos.ne'))).continuousWithinAt`.

Establish `hg' : ContinuousWithinAt (fun ρ => gC l ρ x) (Set.Icc ρ₀ ρ₂) ρ₀` using `(hg.mono Set.Icc_subset_Ici_self).congr (fun y hy => hR y hy) (hR ρ₀ ⟨le_rfl, h02.le⟩)`. Conclude with `(hg'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE h02)).mono Set.inter_subset_right`.
-/
theorem continuousOn_gC (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) :
    ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) := by
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  by_cases hx : x = 0
  · subst hx
    refine (continuousOn_const (c := (0 : ℝ))).congr fun ρ hρ => ?_
    exact gC_zero_of_lt_one l (hl0.le.trans hρ.1) hρ.2
  intro ρ₀ hρ₀
  have hpos : 0 < ρ₀ := hl0.trans_le hρ₀.1
  obtain ⟨⟨c, k, ρ₂, -, h02, -, hR⟩, hL⟩ := GlobalTheory.T.gaussNormAcris_locally_monomial l x hx ρ₀ hρ₀.1 hρ₀.2
  have hS : Set.Ico (l : ℝ)⁻¹ 1 = (Set.Ico (l : ℝ)⁻¹ 1 ∩ Set.Iic ρ₀) ∪ (Set.Ico (l : ℝ)⁻¹ 1 ∩ Set.Ici ρ₀) := by
    ext y
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici]
    constructor
    · intro hy
      rcases le_total y ρ₀ with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (h | h) <;> exact h.1
  rw [ContinuousWithinAt, hS, ← ContinuousWithinAt, continuousWithinAt_union]
  constructor
  · rcases eq_or_lt_of_le hρ₀.1 with heq | hlt
    · refine (continuousWithinAt_singleton (f := fun ρ => gC l ρ x) (x := ρ₀)).mono ?_
      rintro y ⟨hy1, hy2⟩
      exact le_antisymm hy2 (heq ▸ hy1.1)
    · obtain ⟨c', k', ρ₁, -, -, h10, hL'⟩ := hL hlt
      have hg : ContinuousWithinAt (fun ρ : ℝ => c' * ρ ^ k') (Set.Iic ρ₀) ρ₀ :=
        (continuousAt_const.mul (continuousAt_zpow₀ ρ₀ k' (Or.inl hpos.ne'))).continuousWithinAt
      have hg' : ContinuousWithinAt (fun ρ => gC l ρ x) (Set.Icc ρ₁ ρ₀) ρ₀ :=
        (hg.mono Set.Icc_subset_Iic_self).congr (fun y hy => hL' y hy) (hL' ρ₀ ⟨h10.le, le_rfl⟩)
      exact (hg'.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE h10)).mono Set.inter_subset_right
  · have hg : ContinuousWithinAt (fun ρ : ℝ => c * ρ ^ k) (Set.Ici ρ₀) ρ₀ :=
      (continuousAt_const.mul (continuousAt_zpow₀ ρ₀ k (Or.inl hpos.ne'))).continuousWithinAt
    have hg' : ContinuousWithinAt (fun ρ => gC l ρ x) (Set.Icc ρ₀ ρ₂) ρ₀ :=
      (hg.mono Set.Icc_subset_Ici_self).congr (fun y hy => hR y hy) (hR ρ₀ ⟨le_rfl, h02.le⟩)
    exact (hg'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE h02)).mono Set.inter_subset_right

/- English proof (translation)
Introduce `l _ x` and use `continuousOn_gC l x`.
-/
theorem continuousOn_gC_target :
    ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) :=
  fun l _ x => continuousOn_gC l x

end GlobalTheory.PMon.Gauss

end
