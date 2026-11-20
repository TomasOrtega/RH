import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PSmoothSum

/- English proof (translation)
Conclude with `le_top` after adjusting the coercions.
-/
lemma le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

end MainStatements.WeightKernel.PSmoothSum

namespace MainStatements.WeightKernel

open PSmoothSum in
/- English proof (translation)
Introduce `X P _ _ _ _ _ _ W hW K B hK hB I p hp a ha`. Take `⟨R, hR⟩` from `hB.isBounded.subset_closedBall (0 : X)`. Set `φ : ContDiffBump (0 : X)` to `⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩`. Set `G : X × P → ℂ` to `fun q => ((φ q.1 : ℝ) : ℂ) * W q`. Establish `hG : ContDiff ℝ ∞ G` using `(Complex.ofRealCLM.contDiff.comp (φ.contDiff.comp contDiff_fst)).mul hW`.

Establish `hsupp : tsupport G ⊆ tsupport φ ×ˢ univ`. Use `closure_minimal ?_ ((isClosed_tsupport _).prod isClosed_univ)` and prove the remaining obligations. Introduce `q hq`. Use `⟨subset_tsupport _ ?_, mem_univ _⟩` and prove the remaining obligations. Introduce `h0`.

Apply `hq` to reduce the goal to its premises. Simplify using `[G, h0]`. Establish `hcpt : IsCompact (tsupport φ ×ˢ K)` using `φ.hasCompactSupport.isCompact.prod hK`. Establish `hbound : ∀ k : ℕ, ∃ M : ℝ, ∀ x : X, ∀ y ∈ K, ‖iteratedFDeriv ℝ k G (x, y)‖ ≤ M`. Introduce `k`.

Take `⟨M, hM⟩` from `hcpt.exists_bound_of_continuousOn (hG.continuous_iteratedFDeriv (le_infty k)).continuousOn`. Use `⟨max M 0, fun x y hy => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ tsupport φ`. Conclude with `(by simpa using hM (x, y) ⟨hx, hy⟩ : _ ≤ M).trans (le_max_left _ _)`. Establish `: (x, y) ∉ tsupport G` using `fun h => hx (hsupp h).1`.

Establish `h0 : iteratedFDeriv ℝ k G (x, y) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `this (support_iteratedFDeriv_subset k hne)`. Simplify using `[h0]`. Use `choose M hM using hbound`.

Set `L : X →L[ℝ] X × P` to `ContinuousLinearMap.inl ℝ X P`. Establish `hpart : ∀ (y : P) (k : ℕ) (x : X), y ∈ K → ‖iteratedFDeriv ℝ k (fun z => G (z, y)) x‖ ≤ M k * ‖L‖ ^ k`. Introduce `y k x hy`. Establish `heq : (fun z => G (z, y)) = (fun q => G (q + (0, y))) ∘ L`. Use function extensionality and compare the values at `z`.

Simplify using `[L]`. Establish `hGt : ContDiff ℝ ∞ (fun q => G (q + (0, y)))` using `hG.comp (contDiff_id.add contDiff_const)`. Rewrite using `[heq, L.iteratedFDeriv_comp_right hGt x (le_infty k)]`. Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[iteratedFDeriv_comp_add_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.

Establish `hxy : L x + (0, y) = (x, y)` using `by simp [L]`. Rewrite using `[hxy]`. Conclude with `mul_le_mul_of_nonneg_right (hM k x y hy) (pow_nonneg (norm_nonneg _) _)`. Use `⟨fun x => ∑' i, a i * G (x, p i), ?_, ?_⟩` and prove the remaining obligations. Use `contDiff_tsum (N := (⊤ : ℕ∞)) (v := fun k i => ‖a i‖ * (M k * ‖L‖ ^ k)) ?_ ?_ ?_` and prove the remaining obligations.

Introduce `i`. Conclude with `contDiff_const.mul (hG.comp (contDiff_id.prodMk contDiff_const))`. Introduce `k _`. Conclude with `ha.mul_right _`. Introduce `k i x _`.

Establish `hci : ContDiffAt ℝ k (fun z => G (z, p i)) x` using `((hG.comp (contDiff_id.prodMk contDiff_const)).of_le (le_infty k)).contDiffAt`. Use `iteratedFDeriv_const_smul_apply' (a := a i) hci` as an intermediate fact. Simplify using `only [smul_eq_mul] at this`. Rewrite using `[this]`. Conclude with `(norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hpart (p i) k x (hp i)) (norm_nonneg _))`.

Introduce `x hx`. Establish `hx' : dist x 0 ≤ R` using `hR hx`. Establish `h1 : φ x = 1` using `φ.one_of_mem_closedBall (by show dist x 0 ≤ max R 0 + 1`. Combine the linear relations using `[le_max_left R 0])`. Simplify using `[G, h1]`.
-/
theorem smoothSum : SmoothSum := by
  intro X P _ _ _ _ _ _ W hW K B hK hB I p hp a ha
  obtain ⟨R, hR⟩ := hB.isBounded.subset_closedBall (0 : X)
  let φ : ContDiffBump (0 : X) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  let G : X × P → ℂ := fun q => ((φ q.1 : ℝ) : ℂ) * W q
  have hG : ContDiff ℝ ∞ G :=
    (Complex.ofRealCLM.contDiff.comp (φ.contDiff.comp contDiff_fst)).mul hW
  have hsupp : tsupport G ⊆ tsupport φ ×ˢ univ := by
    refine closure_minimal ?_ ((isClosed_tsupport _).prod isClosed_univ)
    intro q hq
    refine ⟨subset_tsupport _ ?_, mem_univ _⟩
    intro h0
    apply hq
    simp [G, h0]
  have hcpt : IsCompact (tsupport φ ×ˢ K) := φ.hasCompactSupport.isCompact.prod hK
  have hbound : ∀ k : ℕ, ∃ M : ℝ, ∀ x : X, ∀ y ∈ K, ‖iteratedFDeriv ℝ k G (x, y)‖ ≤ M := by
    intro k
    obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn
      (hG.continuous_iteratedFDeriv (le_infty k)).continuousOn
    refine ⟨max M 0, fun x y hy => ?_⟩
    by_cases hx : x ∈ tsupport φ
    · exact (by simpa using hM (x, y) ⟨hx, hy⟩ : _ ≤ M).trans (le_max_left _ _)
    · have : (x, y) ∉ tsupport G := fun h => hx (hsupp h).1
      have h0 : iteratedFDeriv ℝ k G (x, y) = 0 := by
        by_contra hne
        exact this (support_iteratedFDeriv_subset k hne)
      simp [h0]
  choose M hM using hbound
  let L : X →L[ℝ] X × P := ContinuousLinearMap.inl ℝ X P
  have hpart : ∀ (y : P) (k : ℕ) (x : X), y ∈ K →
      ‖iteratedFDeriv ℝ k (fun z => G (z, y)) x‖ ≤ M k * ‖L‖ ^ k := by
    intro y k x hy
    have heq : (fun z => G (z, y)) = (fun q => G (q + (0, y))) ∘ L := by
      funext z
      simp [L]
    have hGt : ContDiff ℝ ∞ (fun q => G (q + (0, y))) := hG.comp (contDiff_id.add contDiff_const)
    rw [heq, L.iteratedFDeriv_comp_right hGt x (le_infty k)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [iteratedFDeriv_comp_add_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hxy : L x + (0, y) = (x, y) := by simp [L]
    rw [hxy]
    exact mul_le_mul_of_nonneg_right (hM k x y hy) (pow_nonneg (norm_nonneg _) _)
  refine ⟨fun x => ∑' i, a i * G (x, p i), ?_, ?_⟩
  · refine contDiff_tsum (N := (⊤ : ℕ∞)) (v := fun k i => ‖a i‖ * (M k * ‖L‖ ^ k)) ?_ ?_ ?_
    · intro i
      exact contDiff_const.mul (hG.comp (contDiff_id.prodMk contDiff_const))
    · intro k _
      exact ha.mul_right _
    · intro k i x _
      have hci : ContDiffAt ℝ k (fun z => G (z, p i)) x :=
        ((hG.comp (contDiff_id.prodMk contDiff_const)).of_le (le_infty k)).contDiffAt
      have := iteratedFDeriv_const_smul_apply' (a := a i) hci
      simp only [smul_eq_mul] at this
      rw [this]
      exact (norm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hpart (p i) k x (hp i)) (norm_nonneg _))
  · intro x hx
    have hx' : dist x 0 ≤ R := hR hx
    have h1 : φ x = 1 := φ.one_of_mem_closedBall (by
      show dist x 0 ≤ max R 0 + 1
      linarith [le_max_left R 0])
    simp [G, h1]

end MainStatements.WeightKernel
