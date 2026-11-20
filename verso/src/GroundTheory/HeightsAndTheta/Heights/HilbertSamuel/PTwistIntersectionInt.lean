import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersectionInt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersection
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

namespace TwistIntersectionInt

/- English proof (translation)
Introduce `K _ ι _ Ω _ F _ _ _ y D A B II Λ _ hII hP hbir hA hBa hB hΛ hex hloc`. Establish `hI : IsIntersectionFamily (II K ι)` using `hII K ι`. Establish `hC : IsSmoothHerm (A.tensor B)` using `hA.mul hB`. Establish `hopen : IsOpen {u : (Σ k, ι k) → ℂ | ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0}`. Simplify using `only [Set.ofPred_forall, Set.ofPred_exists]`.

Conclude with `isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const`. Establish `hCloc : ∀ z ∈ mcPts (mCoordIdeal y), ∃ c : ℝ, ∀ᶠ u in 𝓝 z, Real.log ((A.tensor B).h u) = Real.log (A.h u) + c`. Introduce `z hz`. Take `⟨sg, hsg, -⟩` from `hex z hz`. Use `⟨Real.log (Λ sg), ?_⟩` and prove the remaining obligations.

Use `filter_upwards [hloc z hz sg hsg, hopen.mem_nhds hz.1] with u hu hu'`. Use `show Real.log (A.h u * B.h u) = _`. Rewrite using `[hu, Real.log_mul (A.pos u hu').ne' (hΛ sg).ne']`. Set `L : Finset (Fin (D + 1)) → Fin (D + 1) → HermLine ι` to `fun S i => if i ∈ S then A.tensor B else A`. Establish `hLs : ∀ S i, IsSmoothHerm (L S i)`.

Introduce `S i`. Simplify using `only [L]`. Use `split_ifs`. Use `exacts [hC, hA]`. Establish `hLpot : ∀ S i, ∀ z ∈ mcPts (mCoordIdeal y), ∃ c : ℝ, ∀ᶠ u in 𝓝 z, Real.log ((L S i).h u) = Real.log (A.h u) + c`.

Introduce `S i z hz`. Simplify using `only [L]`. Use `split_ifs`. Conclude with `hCloc z hz`. Conclude with `⟨0, Eventually.of_forall fun u => by rw [add_zero]⟩`.

Establish `step : ∀ (S : Finset (Fin (D + 1))) (j : Fin (D + 1)), j ∉ S → II K ι (mCoordIdeal y) (D + 1) (L (insert j S)) = II K ι (mCoordIdeal y) (D + 1) (L S) + -ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1)`. Introduce `S j hj`. Use `set σ : Equiv.Perm (Fin (D + 1)) := Equiv.swap j (Fin.last D) with hσ`. Use `set M : Fin D → HermLine ι := Fin.init (L S ∘ σ) with hMdef`. Establish `hσl : σ (Fin.last D) = j` using `Equiv.swap_apply_right _ _`.

Establish `hne : ∀ i : Fin D, σ (Fin.castSucc i) ≠ j`. Introduce `i h'`. Rewrite `h'` using `[← hσl]`. Conclude with `(Fin.castSucc_lt_last i).ne (σ.injective h')`. Establish `hM : Fin.init (L (insert j S) ∘ σ) = M`.

Use function extensionality and compare the values at `i`. Simplify using `only [hMdef, Fin.init, Function.comp, L, Finset.mem_insert, hne i, false_or]`. Establish `e0 : L S ∘ σ = Fin.snoc M A`. Establish `h0` using `Fin.snoc_init_self (q := L S ∘ σ)`. Establish `hl : (L S ∘ σ) (Fin.last D) = A` using `by simp [L, hσl, hj]`.

Rewrite `h0` using `[hl]`. Conclude with `h0.symm`. Establish `e1 : L (insert j S) ∘ σ = Fin.snoc M (A.tensor B)`. Establish `h0` using `Fin.snoc_init_self (q := L (insert j S) ∘ σ)`. Establish `hl : (L (insert j S) ∘ σ) (Fin.last D) = A.tensor B` using `by simp [L, hσl]`.

Rewrite `h0` using `[hl, hM]`. Conclude with `h0.symm`. Establish `hMs : ∀ i, IsSmoothHerm (M i)` using `fun i => hLs S _`. Establish `hint : ptsIntegral (mCoordIdeal y) (pot M) (logNorm B 1) = ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1)` using `TwistIntersection.ptsIntegral_add_locConst _ (fun i z hz => hLpot S (σ (Fin.castSucc i)) z hz) _`. Rewrite using `[← hI.1 _ (D + 1) (L (insert j S)) σ hP (hLs _), ← hI.1 _ (D + 1) (L S) σ hP (hLs S), e0, e1, hI.2.1 _ D M A B hP hMs hA hB, TwistIntersection.I_snoc_degZero hI hP hMs hB hBa, hint]`.

Establish `hall : ∀ S : Finset (Fin (D + 1)), II K ι (mCoordIdeal y) (D + 1) (L S) = II K ι (mCoordIdeal y) (D + 1) (L ∅) + S.card * -ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1)`. Introduce `S`. Use `Finset.induction_on S (by simp) ?_` and prove the remaining obligations. Introduce `j S hj ih`. Rewrite using `[step S j hj, ih, Finset.card_insert_of_notMem hj]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hL0 : L ∅ = fun _ => A`. Use function extensionality and compare the values at `i`. Simplify using `[L]`.

Establish `hLu : L Finset.univ = fun _ => A.tensor B`. Use function extensionality and compare the values at `i`. Simplify using `[L]`. Establish `hw : ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → logNorm B 1 =ᶠ[𝓝 z] fun _ => (fun sg => -Real.log (Λ sg)) sg`. Introduce `z hz sg hsg`.

Use `filter_upwards [hloc z hz sg hsg] with u hu`. Simplify using `[logNorm, hu, Real.log_inv]`. Establish `hpc` using `hPc K ι Ω F y D (fun _ => A) (fun sg => -Real.log (Λ sg)) (logNorm B 1) hP hbir (fun _ => hA) hex hw`. Establish `hg : ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (fun _ => 1) = (genDeg (mCoordIdeal y) D A.a : ℝ)`. Rewrite using `[hDG K ι (mCoordIdeal y) D (fun _ => A) hP (fun _ => hA)]`.

Unfold `genDeg`. Reduce the equality to equality of the corresponding arguments. Use `hall Finset.univ` as an intermediate fact. Rewrite `this` using `[hL0, hLu, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[this, hpc, hg, Finset.sum_neg_distrib]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem proof (hPc : EmbeddingPieces.Statement) (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    TwistIntersectionInt.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D A B II Λ _ hII hP hbir hA hBa hB hΛ hex hloc
  classical
  have hI : IsIntersectionFamily (II K ι) := hII K ι
  have hC : IsSmoothHerm (A.tensor B) := hA.mul hB
  have hopen : IsOpen {u : (Σ k, ι k) → ℂ | ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hCloc : ∀ z ∈ mcPts (mCoordIdeal y), ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, Real.log ((A.tensor B).h u) = Real.log (A.h u) + c := by
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    refine ⟨Real.log (Λ sg), ?_⟩
    filter_upwards [hloc z hz sg hsg, hopen.mem_nhds hz.1] with u hu hu'
    show Real.log (A.h u * B.h u) = _
    rw [hu, Real.log_mul (A.pos u hu').ne' (hΛ sg).ne']
  let L : Finset (Fin (D + 1)) → Fin (D + 1) → HermLine ι := fun S i => if i ∈ S then A.tensor B else A
  have hLs : ∀ S i, IsSmoothHerm (L S i) := by
    intro S i
    dsimp only [L]
    split_ifs
    exacts [hC, hA]
  have hLpot : ∀ S i, ∀ z ∈ mcPts (mCoordIdeal y), ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, Real.log ((L S i).h u) = Real.log (A.h u) + c := by
    intro S i z hz
    dsimp only [L]
    split_ifs
    · exact hCloc z hz
    · exact ⟨0, Eventually.of_forall fun u => by rw [add_zero]⟩
  have step : ∀ (S : Finset (Fin (D + 1))) (j : Fin (D + 1)), j ∉ S →
      II K ι (mCoordIdeal y) (D + 1) (L (insert j S)) = II K ι (mCoordIdeal y) (D + 1) (L S) +
        -ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) := by
    intro S j hj
    set σ : Equiv.Perm (Fin (D + 1)) := Equiv.swap j (Fin.last D) with hσ
    set M : Fin D → HermLine ι := Fin.init (L S ∘ σ) with hMdef
    have hσl : σ (Fin.last D) = j := Equiv.swap_apply_right _ _
    have hne : ∀ i : Fin D, σ (Fin.castSucc i) ≠ j := by
      intro i h'
      rw [← hσl] at h'
      exact (Fin.castSucc_lt_last i).ne (σ.injective h')
    have hM : Fin.init (L (insert j S) ∘ σ) = M := by
      funext i
      simp only [hMdef, Fin.init, Function.comp, L, Finset.mem_insert, hne i, false_or]
    have e0 : L S ∘ σ = Fin.snoc M A := by
      have h0 := Fin.snoc_init_self (q := L S ∘ σ)
      have hl : (L S ∘ σ) (Fin.last D) = A := by simp [L, hσl, hj]
      rw [hl] at h0
      exact h0.symm
    have e1 : L (insert j S) ∘ σ = Fin.snoc M (A.tensor B) := by
      have h0 := Fin.snoc_init_self (q := L (insert j S) ∘ σ)
      have hl : (L (insert j S) ∘ σ) (Fin.last D) = A.tensor B := by simp [L, hσl]
      rw [hl, hM] at h0
      exact h0.symm
    have hMs : ∀ i, IsSmoothHerm (M i) := fun i => hLs S _
    have hint : ptsIntegral (mCoordIdeal y) (pot M) (logNorm B 1) =
        ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) :=
      TwistIntersection.ptsIntegral_add_locConst _ (fun i z hz => hLpot S (σ (Fin.castSucc i)) z hz) _
    rw [← hI.1 _ (D + 1) (L (insert j S)) σ hP (hLs _), ← hI.1 _ (D + 1) (L S) σ hP (hLs S), e0, e1,
      hI.2.1 _ D M A B hP hMs hA hB, TwistIntersection.I_snoc_degZero hI hP hMs hB hBa, hint]
  have hall : ∀ S : Finset (Fin (D + 1)), II K ι (mCoordIdeal y) (D + 1) (L S) =
      II K ι (mCoordIdeal y) (D + 1) (L ∅) +
        S.card * -ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) := by
    intro S
    refine Finset.induction_on S (by simp) ?_
    intro j S hj ih
    rw [step S j hj, ih, Finset.card_insert_of_notMem hj]
    push_cast
    ring
  have hL0 : L ∅ = fun _ => A := by
    funext i
    simp [L]
  have hLu : L Finset.univ = fun _ => A.tensor B := by
    funext i
    simp [L]
  have hw : ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
      logNorm B 1 =ᶠ[𝓝 z] fun _ => (fun sg => -Real.log (Λ sg)) sg := by
    intro z hz sg hsg
    filter_upwards [hloc z hz sg hsg] with u hu
    simp [logNorm, hu, Real.log_inv]
  have hpc := hPc K ι Ω F y D (fun _ => A) (fun sg => -Real.log (Λ sg)) (logNorm B 1) hP hbir
    (fun _ => hA) hex hw
  have hg : ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (fun _ => 1) =
      (genDeg (mCoordIdeal y) D A.a : ℝ) := by
    rw [hDG K ι (mCoordIdeal y) D (fun _ => A) hP (fun _ => hA)]
    unfold genDeg
    congr
  have := hall Finset.univ
  rw [hL0, hLu, Finset.card_univ, Fintype.card_fin] at this
  rw [this, hpc, hg, Finset.sum_neg_distrib]
  push_cast
  ring

end TwistIntersectionInt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
