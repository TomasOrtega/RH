import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PKerUnif

/- English proof (translation)
Unfold `MainStatements.WeightKernel.ker`. Apply `tsum_eq_sum` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[Set.Finite.mem_toFinset]`. Distinguish the cases in `h1 : c i x = 0`.

Simplify using `[h1]`. Establish `h2 : q i x ∉ C` using `fun h => hi ⟨h1, h⟩`. Simplify using `[hφ _ h2]`.
-/
theorem ker_eq_sum {H Ω I : Type} (c : I → Ω → ℂ) (q : I → Ω → H) (φ : H → ℂ) (C : Set H) (x : Ω)
    (hf : {i | c i x ≠ 0 ∧ q i x ∈ C}.Finite) (hφ : ∀ y ∉ C, φ y = 0) :
    MainStatements.WeightKernel.ker c q φ x = ∑ i ∈ hf.toFinset, c i x * φ (q i x) := by
  unfold MainStatements.WeightKernel.ker
  apply tsum_eq_sum
  intro i hi
  rw [Set.Finite.mem_toFinset] at hi
  by_cases h1 : c i x = 0
  · simp [h1]
  · have h2 : q i x ∉ C := fun h => hi ⟨h1, h⟩
    simp [hφ _ h2]

end MainStatements.WeightKernel.PKerUnif

open MainStatements.WeightKernel.PKerUnif in
/- English proof (translation)
Introduce `hS hCG H _ _ _ _ _ _ _ _ n ι hι Ω I _ _ m _ c q hker P _ _ _ W p K C hW hp hK hC hvan`. Take `⟨M, hM⟩` from `((hC.image hι.continuous).prod (hK.image hp)).exists_bound_of_continuousOn hW.continuous.continuousOn`. Establish `hMb : ∀ y ∈ C, ∀ k ∈ K, ‖W (matCoord ι y, p k)‖ ≤ M` using `fun y hy k hk => hM _ (Set.mk_mem_prod ⟨y, hy, rfl⟩ ⟨k, hk, rfl⟩)`. Take `⟨R, hR⟩` from `(hC.image hι.continuous).isBounded.subset_closedBall (0 : Mx n)`. Take `⟨Bd, hBd⟩` from `hCG Ω K m (fun (k : K) x => ker c q (fun y => W (matCoord ι y, p k)) x) (by`.

Introduce `x`. Use `⟨∑ i ∈ (hker.fin x C hC).toFinset, ‖c i x‖ * M, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[ker_eq_sum c q _ C x (hker.fin x C hC) (fun y hy => hvan k k.2 y hy)]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_left (hMb _ ((Set.Finite.mem_toFinset _).1 hi).2 _ k.2) (norm_nonneg _)) (by`. Introduce `a ha`. Establish `hz : ∀ y ∉ C, ∑' k : K, a k * W (matCoord ι y, p k) = 0`. Introduce `y hy`. Establish `: ∀ k : K, a k * W (matCoord ι y, p k) = 0` using `fun k => by rw [hvan k.1 k.2 y hy, mul_zero]`.

Simplify using `[this]`. Set `bump : ContDiffBump (0 : Mx n)` to `⟨max R 0 + 1, max R 0 + 2, add_pos_of_nonneg_of_pos (le_max_right _ _) one_pos, by linarith⟩`. Take `⟨Φ, hΦs, hΦ⟩` from `hS (Mx n) P W hW (p '' K) (Metric.closedBall 0 (max R 0 + 2)) (hK.image hp) (isCompact_closedBall _ _) K (fun k => p k.1) (fun k => ⟨k.1, k.2, rfl⟩) a ha`. Establish `hψ : (fun y => ∑' k : K, a k * W (matCoord ι y, p k)) ∈ CcMat ι`. Use `⟨HasCompactSupport.intro hC fun y hy => hz y hy, fun z => Complex.ofRealCLM (bump z) * Φ z, (Complex.ofRealCLM.contDiff.comp bump.contDiff).mul hΦs, fun y => ?_⟩` and prove the remaining obligations.

Simplify using `only [Complex.ofRealCLM_apply]`. Distinguish the cases in `hy : y ∈ C`. Establish `hin : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 1)` using `Metric.closedBall_subset_closedBall (by linarith [le_max_left R 0]) (hR ⟨y, hy, rfl⟩)`. Establish `hin2 : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 2)` using `Metric.closedBall_subset_closedBall (by linarith [le_max_left R 0]) (hR ⟨y, hy, rfl⟩)`. Establish `h1 : bump (matCoord ι y) = 1` using `bump.one_of_mem_closedBall hin`.

Rewrite using `[h1, hΦ _ hin2]`. Simplify using the standard rewrite rules. Distinguish the cases in `hb : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 2)`. Rewrite using `[hΦ _ hb]`. Simplify using `[hz y hy]`.

Establish `h0 : bump (matCoord ι y) = 0` using `image_eq_zero_of_notMem_tsupport (by rw [bump.tsupport_eq]; exact hb)`. Simplify using `[h0, hz y hy]`. Use `(hker.int _ hψ).congr (ae_of_all m fun x => ?_)` and prove the remaining obligations. Establish `hf` using `hker.fin x C hC`. Establish `hs : ∀ i ∈ hf.toFinset, Summable (fun k : K => a k * W (matCoord ι (q i x), p k))`.

Introduce `i hi`. Establish `hq` using `((Set.Finite.mem_toFinset _).1 hi).2`. Use `Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (ha.mul_right M))` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hMb _ hq _ k.2) (norm_nonneg _)`.

Establish `hu : ∀ k : K, ker c q (fun y => W (matCoord ι y, p k)) x = ∑ i ∈ hf.toFinset, c i x * W (matCoord ι (q i x), p k)` using `fun k => ker_eq_sum c q _ C x hf (fun y hy => hvan k k.2 y hy)`. Use `symm`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `k`.

Rewrite using `[hu k, Finset.mul_sum]`. Use `congr 1`. Use extensionality with `i`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ i ∈ hf.toFinset, ∑' k : K, c i x * (a k * W (matCoord ι (q i x), p k)) := Summable.tsum_finsetSum fun i hi => (hs i hi).mul_left _`.

Use `_ = ∑ i ∈ hf.toFinset, c i x * ∑' k : K, a k * W (matCoord ι (q i x), p k) := by`. Use `congr 1`. Use extensionality with `i`. Rewrite using `[tsum_mul_left]`. Use `_ = ker c q (fun y => ∑' k : K, a k * W (matCoord ι y, p k)) x := (ker_eq_sum c q _ C x hf hz).symm)`.

Conclude with `⟨Bd, fun k hk => hBd ⟨k, hk⟩⟩`.
-/
theorem MainStatements.WeightKernel.kerUnif : SmoothSum → ClosedGraph → KerUnif := by
  intro hS hCG H _ _ _ _ _ _ _ _ n ι hι Ω I _ _ m _ c q hker P _ _ _ W p K C hW hp hK hC hvan
  obtain ⟨M, hM⟩ := ((hC.image hι.continuous).prod (hK.image hp)).exists_bound_of_continuousOn
    hW.continuous.continuousOn
  have hMb : ∀ y ∈ C, ∀ k ∈ K, ‖W (matCoord ι y, p k)‖ ≤ M := fun y hy k hk =>
    hM _ (Set.mk_mem_prod ⟨y, hy, rfl⟩ ⟨k, hk, rfl⟩)
  obtain ⟨R, hR⟩ := (hC.image hι.continuous).isBounded.subset_closedBall (0 : Mx n)
  obtain ⟨Bd, hBd⟩ := hCG Ω K m (fun (k : K) x => ker c q (fun y => W (matCoord ι y, p k)) x) (by
    intro x
    refine ⟨∑ i ∈ (hker.fin x C hC).toFinset, ‖c i x‖ * M, fun k => ?_⟩
    rw [ker_eq_sum c q _ C x (hker.fin x C hC) (fun y hy => hvan k k.2 y hy)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hMb _ ((Set.Finite.mem_toFinset _).1 hi).2 _ k.2) (norm_nonneg _)) (by
    intro a ha
    have hz : ∀ y ∉ C, ∑' k : K, a k * W (matCoord ι y, p k) = 0 := by
      intro y hy
      have : ∀ k : K, a k * W (matCoord ι y, p k) = 0 := fun k => by rw [hvan k.1 k.2 y hy, mul_zero]
      simp [this]
    let bump : ContDiffBump (0 : Mx n) :=
      ⟨max R 0 + 1, max R 0 + 2, add_pos_of_nonneg_of_pos (le_max_right _ _) one_pos, by linarith⟩
    obtain ⟨Φ, hΦs, hΦ⟩ := hS (Mx n) P W hW (p '' K) (Metric.closedBall 0 (max R 0 + 2)) (hK.image hp)
      (isCompact_closedBall _ _) K (fun k => p k.1) (fun k => ⟨k.1, k.2, rfl⟩) a ha
    have hψ : (fun y => ∑' k : K, a k * W (matCoord ι y, p k)) ∈ CcMat ι := by
      refine ⟨HasCompactSupport.intro hC fun y hy => hz y hy, fun z => Complex.ofRealCLM (bump z) * Φ z,
        (Complex.ofRealCLM.contDiff.comp bump.contDiff).mul hΦs, fun y => ?_⟩
      simp only [Complex.ofRealCLM_apply]
      by_cases hy : y ∈ C
      · have hin : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 1) :=
          Metric.closedBall_subset_closedBall (by linarith [le_max_left R 0]) (hR ⟨y, hy, rfl⟩)
        have hin2 : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 2) :=
          Metric.closedBall_subset_closedBall (by linarith [le_max_left R 0]) (hR ⟨y, hy, rfl⟩)
        have h1 : bump (matCoord ι y) = 1 := bump.one_of_mem_closedBall hin
        rw [h1, hΦ _ hin2]
        simp
      · by_cases hb : matCoord ι y ∈ Metric.closedBall (0 : Mx n) (max R 0 + 2)
        · rw [hΦ _ hb]
          simp [hz y hy]
        · have h0 : bump (matCoord ι y) = 0 :=
            image_eq_zero_of_notMem_tsupport (by rw [bump.tsupport_eq]; exact hb)
          simp [h0, hz y hy]
    refine (hker.int _ hψ).congr (ae_of_all m fun x => ?_)
    have hf := hker.fin x C hC
    have hs : ∀ i ∈ hf.toFinset, Summable (fun k : K => a k * W (matCoord ι (q i x), p k)) := by
      intro i hi
      have hq := ((Set.Finite.mem_toFinset _).1 hi).2
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (ha.mul_right M))
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hMb _ hq _ k.2) (norm_nonneg _)
    have hu : ∀ k : K, ker c q (fun y => W (matCoord ι y, p k)) x
        = ∑ i ∈ hf.toFinset, c i x * W (matCoord ι (q i x), p k) :=
      fun k => ker_eq_sum c q _ C x hf (fun y hy => hvan k k.2 y hy)
    symm
    calc ∑' k : K, a k * ker c q (fun y => W (matCoord ι y, p k)) x
        = ∑' k : K, ∑ i ∈ hf.toFinset, c i x * (a k * W (matCoord ι (q i x), p k)) := by
          congr 1; ext k; rw [hu k, Finset.mul_sum]; congr 1; ext i; ring
      _ = ∑ i ∈ hf.toFinset, ∑' k : K, c i x * (a k * W (matCoord ι (q i x), p k)) :=
          Summable.tsum_finsetSum fun i hi => (hs i hi).mul_left _
      _ = ∑ i ∈ hf.toFinset, c i x * ∑' k : K, a k * W (matCoord ι (q i x), p k) := by
          congr 1; ext i; rw [tsum_mul_left]
      _ = ker c q (fun y => ∑' k : K, a k * W (matCoord ι y, p k)) x :=
          (ker_eq_sum c q _ C x hf hz).symm)
  exact ⟨Bd, fun k hk => hBd ⟨k, hk⟩⟩

end
