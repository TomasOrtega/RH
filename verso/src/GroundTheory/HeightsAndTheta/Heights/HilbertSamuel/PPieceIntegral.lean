import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClopenDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IntNumOffBlocks
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

/- English proof (translation)
Unfold `ptsIntegral ptsIntegralAt`. Use `split_ifs with hΨ`. Establish `hd : ∀ y w, sheetDensity P hΨ.choose φ g y w = sheetDensity P hΨ.choose φ g' y w`. Introduce `y w`. Unfold `sheetDensity`.

Use `split_ifs with hγ`. Rewrite using `[hg _ hγ.choose_spec.2.self_of_nhds.2.1]`. Both sides reduce to the same expression. Simplify using `only [hd]`. Both sides reduce to the same expression.
-/
theorem ptsIntegral_congr_integrand {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) {g g' : ((Σ k, ι k) → ℂ) → ℝ}
    (hg : ∀ z ∈ mcPts P, g z = g' z) : ptsIntegral P φ g = ptsIntegral P φ g' := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · have hd : ∀ y w, sheetDensity P hΨ.choose φ g y w = sheetDensity P hΨ.choose φ g' y w := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1]
      · rfl
    simp only [hd]
  · rfl

/- English proof (translation)
Introduce `K _ _ ι _ P e L I hP hL hPI hopen`. Use `set Z : Set ((Σ k, ι k) → ℂ) := {z | ∀ f ∈ I, eval z f = 0} with hZ`. Use `set A := Z ∩ mcPts P with hA`. Establish `h1 : ptsIntegral P (pot L) (Z.indicator fun _ => (1 : ℝ)) = ptsIntegral P (pot L) (A.indicator fun _ => (1 : ℝ))`. Use `ptsIntegral_congr_integrand P _ fun z hz => ?_` and prove the remaining obligations.

Distinguish the cases in `hzZ : z ∈ Z`. Rewrite using `[Set.indicator_of_mem hzZ, Set.indicator_of_mem (show z ∈ A from ⟨hzZ, hz⟩)]`. Rewrite using `[Set.indicator_of_notMem hzZ, Set.indicator_of_notMem fun h' => hzZ h'.1]`. Establish `hZc : IsClosed Z`. Establish `hZi : Z = ⋂ f ∈ I, {z | eval z f = 0}`.

Use extensionality with `z`. Simplify using `[hZ]`. Rewrite using `[hZi]`. Conclude with `isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const`. Establish `hcl : IsClopen (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' A)`.

Prove the components needed by the constructor for the conclusion. Establish `hpre : (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' A) = (↑) ⁻¹' Z`. Use extensionality with `⟨z, hz⟩`. Simplify using `[hA]`. Rewrite using `[hpre]`.

Conclude with `hZc.preimage continuous_subtype_val`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce and unpack `⟨z, hz⟩ ⟨hzZ, -⟩`. Rewrite using `[nhds_subtype]`. Conclude with `((hopen z hz hzZ).comap Subtype.val).mono fun y hy => ⟨hy y.2, y.2⟩`.

Establish `hAeq : A = zeroLocus ℂ I ∩ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}`. Use extensionality with `z`. Simplify using `only [hA, hZ, mcPts, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_zeroLocus_iff, aeval_eq_eval]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz, hU, -⟩`.

Conclude with `⟨hz, hU⟩`. Introduce and unpack `⟨hz, hU⟩`. Conclude with `⟨hz, hU, fun f hf => hz _ (hPI (Ideal.mem_map_of_mem _ hf))⟩`. Rewrite using `[h1, h K ι P e L A hP hL Set.inter_subset_right hcl, intNum_radical_eq_offBlocks, hAeq]`.
-/
theorem PieceIntegral.proof (h : ClopenDegree.Statement) : PieceIntegral.Statement := by
  intro K _ _ ι _ P e L I hP hL hPI hopen
  set Z : Set ((Σ k, ι k) → ℂ) := {z | ∀ f ∈ I, eval z f = 0} with hZ
  set A := Z ∩ mcPts P with hA
  have h1 : ptsIntegral P (pot L) (Z.indicator fun _ => (1 : ℝ)) =
      ptsIntegral P (pot L) (A.indicator fun _ => (1 : ℝ)) := by
    refine ptsIntegral_congr_integrand P _ fun z hz => ?_
    by_cases hzZ : z ∈ Z
    · rw [Set.indicator_of_mem hzZ, Set.indicator_of_mem (show z ∈ A from ⟨hzZ, hz⟩)]
    · rw [Set.indicator_of_notMem hzZ, Set.indicator_of_notMem fun h' => hzZ h'.1]
  have hZc : IsClosed Z := by
    have hZi : Z = ⋂ f ∈ I, {z | eval z f = 0} := by
      ext z
      simp [hZ]
    rw [hZi]
    exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const
  have hcl : IsClopen (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' A) := by
    constructor
    · have hpre : (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' A) = (↑) ⁻¹' Z := by
        ext ⟨z, hz⟩
        simp [hA]
      rw [hpre]
      exact hZc.preimage continuous_subtype_val
    · rw [isOpen_iff_mem_nhds]
      rintro ⟨z, hz⟩ ⟨hzZ, -⟩
      rw [nhds_subtype]
      exact ((hopen z hz hzZ).comap Subtype.val).mono fun y hy => ⟨hy y.2, y.2⟩
  have hAeq : A = zeroLocus ℂ I ∩ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp only [hA, hZ, mcPts, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_zeroLocus_iff, aeval_eq_eval]
    constructor
    · rintro ⟨hz, hU, -⟩
      exact ⟨hz, hU⟩
    · rintro ⟨hz, hU⟩
      exact ⟨hz, hU, fun f hf => hz _ (hPI (Ideal.mem_map_of_mem _ hf))⟩
  rw [h1, h K ι P e L A hP hL Set.inter_subset_right hcl, intNum_radical_eq_offBlocks, hAeq]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
