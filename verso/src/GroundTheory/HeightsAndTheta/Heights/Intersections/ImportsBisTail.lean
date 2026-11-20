import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtraAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerBis
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerSide
import GroundTheory.HeightsAndTheta.Heights.Intersections.XcNotMemOfIsRelevant
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ P f g a x hP hf hg hfP hgP hx`. Establish `: P.IsPrime` using `hP.2.1.1`. Set `t : Ideal (MRing ι) → MRing ι` to `fun W => if h : IsRelevant W then ∏ k, (X ⟨k, (h k).choose⟩ : MRing ι) ^ a k else 1`. Establish `ht : ∀ W : Ideal (MRing ι), W.IsPrime → IsRelevant W → IsMultiHomog (t W) a ∧ t W ∉ W`. Introduce `W hWp hW`.

Simplify using `only [t, dif_pos hW]`. Use `⟨AvoidRing.isMultiHomog_coordProd _ _, fun hmem => ?_⟩` and prove the remaining obligations. Take `⟨k, -, hk⟩` from `hWp.prod_mem_iff.mp hmem`. Conclude with `(hW k).choose_spec (hWp.mem_of_pow_mem _ hk)`. Establish `hne : ∀ W : Ideal (MRing ι), P ≤ W → t W ∉ W → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) ≠ 0`.

Introduce `W hPW htW h0`. Rewrite `h0` using `[IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `htW (hPW h0)`. Set `y : MRing ι → Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)` to `fun s W => algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) / algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W))`. Establish `hdata : ∀ (s : MRing ι), ∀ W ∈ divSupp P s, P ≤ W ∧ W.IsPrime ∧ IsMultiHomog (t W) a ∧ t W ∉ W ∧ ∀ s' : MRing ι, y s' W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P …`.

Introduce `s W hW`. Establish `hPW : P ≤ W` using `le_trans le_sup_left hW.1.1.2`. Take `⟨h1, h2⟩` from `ht W hW.1.1.1 hW.2`. Conclude with `⟨hPW, hW.1.1.1, h1, h2, fun s' => div_mul_cancel₀ _ (hne W hPW h2)⟩`. Establish `term : ∀ s : MRing ι, IsMultiHomog s a → s ∉ P → ∀ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) * (if IsHorizontal W then 0 else (geoNum 0 W (fun j => ((Fin.elim0 : Fin 0 → HermLine ι) j).a) : ℝ) * Real.log (charOf W)) = Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y s …`.

Introduce `s hs hsP W hW`. Establish `hA : IsSectionOn P (HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun k => (a k : ℤ))) s` using `⟨a, fun _ => rfl, hs, hsP⟩`. Rewrite using `[if_neg (not_isHorizontal_of_dimOne arithVarZero hP hA hW)]`. Take `⟨-, -, hta, htW, hy⟩` from `hdata s W hW`. Take `⟨hyW, hm⟩` from `hD K ι P s (t W) a W (y s W) hP.2.1 hs hsP hW hta htW (hy s)`.

Establish `hy0 : y s W ≠ 0`. Introduce `h0`. Establish `h1` using `hy s`. Rewrite `h1` using `[h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hsP h1`.

Rewrite using `[hm]`. Conclude with `hC K ι P s a W _ (y s W) hP hs hsP hW hyW hy0`. Establish `hvert : ∀ s : MRing ι, IsMultiHomog s a → s ∉ P → vertR P (Fin.elim0 : Fin 0 → HermLine ι) s = ∑ᶠ W ∈ divSupp P s, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y s W)))`. Introduce `s hs hsP`. Unfold `vertR`.

Conclude with `finsum_mem_congr rfl fun W hW => term s hs hsP W hW`. Rewrite using `[hvert f hf hfP, hvert g hg hgP]`. Use `hL K ι P f g a x t (y f) (y g) hP hf hg hfP hgP hx fun W hW => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨-, -, hta, htW, hy⟩ : P ≤ W ∧ W.IsPrime ∧ IsMultiHomog (t W) a ∧ t W ∉ W ∧ _ := by`. Break down `hW with hW | hW` into its components or cases.

Conclude with `hdata f W hW`. Conclude with `hdata g W hW`. Conclude with `⟨hta, htW, hy f, hy g⟩`.
-/
theorem VerticalEmbedding.proof (hD : regularityDehomogenization_holds.Statement) (hC : regularityLocalCardinality_holds.Statement) (hL : RegularityLocalProduct.Statement) :
    VerticalEmbedding.Statement := by
  classical
  intro K _ ι _ P f g a x hP hf hg hfP hgP hx
  have : P.IsPrime := hP.2.1.1

  let t : Ideal (MRing ι) → MRing ι := fun W =>
    if h : IsRelevant W then ∏ k, (X ⟨k, (h k).choose⟩ : MRing ι) ^ a k else 1
  have ht : ∀ W : Ideal (MRing ι), W.IsPrime → IsRelevant W → IsMultiHomog (t W) a ∧ t W ∉ W := by
    intro W hWp hW
    simp only [t, dif_pos hW]
    refine ⟨AvoidRing.isMultiHomog_coordProd _ _, fun hmem => ?_⟩
    obtain ⟨k, -, hk⟩ := hWp.prod_mem_iff.mp hmem
    exact (hW k).choose_spec (hWp.mem_of_pow_mem _ hk)
  have hne : ∀ W : Ideal (MRing ι), P ≤ W → t W ∉ W →
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) ≠ 0 := by
    intro W hPW htW h0
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact htW (hPW h0)

  let y : MRing ι → Ideal (MRing ι) → FractionRing (MRing ι ⧸ P) := fun s W =>
    algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) /
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W))
  have hdata : ∀ (s : MRing ι), ∀ W ∈ divSupp P s, P ≤ W ∧ W.IsPrime ∧ IsMultiHomog (t W) a ∧ t W ∉ W ∧
      ∀ s' : MRing ι, y s' W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s') := by
    intro s W hW
    have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
    obtain ⟨h1, h2⟩ := ht W hW.1.1.1 hW.2
    exact ⟨hPW, hW.1.1.1, h1, h2, fun s' => div_mul_cancel₀ _ (hne W hPW h2)⟩

  have term : ∀ s : MRing ι, IsMultiHomog s a → s ∉ P → ∀ W ∈ divSupp P s,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
          (if IsHorizontal W then 0 else
            (geoNum 0 W (fun j => ((Fin.elim0 : Fin 0 → HermLine ι) j).a) : ℝ) * Real.log (charOf W)) =
        Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y s W))) := by
    intro s hs hsP W hW
    have hA : IsSectionOn P (HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun k => (a k : ℤ))) s :=
      ⟨a, fun _ => rfl, hs, hsP⟩
    rw [if_neg (not_isHorizontal_of_dimOne arithVarZero hP hA hW)]
    obtain ⟨-, -, hta, htW, hy⟩ := hdata s W hW
    obtain ⟨hyW, hm⟩ := hD K ι P s (t W) a W (y s W) hP.2.1 hs hsP hW hta htW (hy s)
    have hy0 : y s W ≠ 0 := by
      intro h0
      have h1 := hy s
      rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact hsP h1
    rw [hm]
    exact hC K ι P s a W _ (y s W) hP hs hsP hW hyW hy0
  have hvert : ∀ s : MRing ι, IsMultiHomog s a → s ∉ P →
      vertR P (Fin.elim0 : Fin 0 → HermLine ι) s =
        ∑ᶠ W ∈ divSupp P s, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y s W))) := by
    intro s hs hsP
    unfold vertR
    exact finsum_mem_congr rfl fun W hW => term s hs hsP W hW
  rw [hvert f hf hfP, hvert g hg hgP]
  refine hL K ι P f g a x t (y f) (y g) hP hf hg hfP hgP hx fun W hW => ?_
  obtain ⟨-, -, hta, htW, hy⟩ : P ≤ W ∧ W.IsPrime ∧ IsMultiHomog (t W) a ∧ t W ∉ W ∧ _ := by
    rcases hW with hW | hW
    · exact hdata f W hW
    · exact hdata g W hW
  exact ⟨hta, htW, hy f, hy g⟩

end

end GroundTheory.Heights₂.Heights.Inter
