import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h : (fun u ↦ evalCone (z u) (C a)) = fun _ ↦ ((a : ℤ) : ℂ)`. Use function extensionality and compare the values at `u`. Rewrite using `[evalCone, eval₂_C]`.

Simplify using the standard rewrite rules. Rewrite using `[h]`. Conclude with `analyticAt_const`. Consider the case `add p q hp hq`. Establish `h : (fun u ↦ evalCone (z u) (p + q)) = fun u ↦ evalCone (z u) p + evalCone (z u) q`.

Use function extensionality and compare the values at `u`. Simplify using `[evalCone]`. Rewrite using `[h]`. Conclude with `hp.add hq`. Consider the case `mul_X p v hp`.

Establish `h : (fun u ↦ evalCone (z u) (p * X v)) = fun u ↦ evalCone (z u) p * z u v.1 v.2`. Use function extensionality and compare the values at `u`. Simplify using `[evalCone]`. Rewrite using `[h]`. Conclude with `hp.mul (hz v.1 v.2)`.
-/
theorem analyticAt_evalCone_comp {ι : Type} [Fintype ι] {n : ι → ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (z : E → Cone n ℂ) (u₀ : E) (hz : ∀ k i, AnalyticAt ℂ (fun u ↦ z u k i) u₀)
    (f : MvPolynomial (Coord n) ℤ) : AnalyticAt ℂ (fun u ↦ evalCone (z u) f) u₀ := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h : (fun u ↦ evalCone (z u) (C a)) = fun _ ↦ ((a : ℤ) : ℂ) := by
      funext u; rw [evalCone, eval₂_C]; simp
    rw [h]; exact analyticAt_const
  | add p q hp hq =>
    have h : (fun u ↦ evalCone (z u) (p + q)) = fun u ↦ evalCone (z u) p + evalCone (z u) q := by
      funext u; simp [evalCone]
    rw [h]; exact hp.add hq
  | mul_X p v hp =>
    have h : (fun u ↦ evalCone (z u) (p * X v)) = fun u ↦ evalCone (z u) p * z u v.1 v.2 := by
      funext u; simp [evalCone]
    rw [h]; exact hp.mul (hz v.1 v.2)

/- English proof (translation)
Introduce `ι _ _ n P D N hN d g hg r G δ hG e γ u₀ hγ hev`. Establish `hw₀ : γ u₀ ∈ D.extPoints` using `hev.self_of_nhds`. Take `⟨hz₀, la₀, hla₀, hrel₀⟩` from `(hPts ι n P D d g hg).2 _ hw₀`. Use `choose c hc using fun k ↦ Function.ne_iff.mp (hz₀.1 k)`. Establish `hm₀ : evalCone (D.basePart₂ (γ u₀)) (chartMonomial c d) ≠ 0`.

Simplify using `only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)`. Take `⟨j, hj⟩` from `Function.ne_iff.mp (hw₀.1 none)`. Establish `hj' : D.newPart (γ u₀) j ≠ 0` using `hj`. Establish `hg₀ : evalCone (D.basePart₂ (γ u₀)) (g c j) ≠ 0`.

Introduce `h0`. Apply `hj'` to reduce the goal to its premises. Rewrite using `[hrel₀ c hm₀ j, h0, mul_zero, zero_div]`. Establish `hco : ∀ (o : Option ι) (i : Fin (D.extSizes o + 1)), AnalyticAt ℂ (fun u ↦ γ u o i) u₀` using `fun o i ↦ ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (D.extSizes o + 1) ↦ ℂ) i).analyticAt _).comp (((ContinuousLinearMap.proj (R := ℂ) (φ := fun o ↦ Fin (D.extSizes o + 1) → ℂ) o).analyticAt _).comp hγ)`. Establish `hold : ∀ f, AnalyticAt ℂ (fun u ↦ evalCone (D.basePart₂ (γ u)) f) u₀` using `analyticAt_evalCone_comp (fun u ↦ D.basePart₂ (γ u)) u₀ fun k i ↦ hco (some k) i`.

Establish `hM` using `hold (chartMonomial c d)`. Establish `hG'` using `hold (g c j)`. Establish `hnew : AnalyticAt ℂ (fun u ↦ D.newPart (γ u) j) u₀` using `hco none j`. Use `⟨fun u ↦ D.newPart (γ u) j * evalCone (D.basePart₂ (γ u)) (chartMonomial c d) / evalCone (D.basePart₂ (γ u)) (g c j), (hnew.mul hM).div hG' hg₀, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[hrel₀ c hm₀ j]`. Clear the denominators using the available nonvanishing facts. Conclude with `hla₀`. Use `filter_upwards [hev, hM.continuousAt.eventually_ne hm₀, hG'.continuousAt.eventually_ne hg₀] with u hu hmu hgu`. Take `⟨_, la, _, hrel⟩` from `(hPts ι n P D d g hg).2 _ hu`.

Establish `hla : D.newPart (γ u) j * evalCone (D.basePart₂ (γ u)) (chartMonomial c d) / evalCone (D.basePart₂ (γ u)) (g c j) = la`. Rewrite using `[hrel c hmu j]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hla]`. Conclude with `(hMet ι n P D N hN d g hg r G δ hG).2 _ hu c la hmu (hrel c hmu)`.
-/
theorem PlurisubharmonicMetric.proof (hPts : ConePoints.Statement) (hMet : ChartMetric.Statement) : PlurisubharmonicMetric.Statement := by
  intro ι _ _ n P D N hN d g hg r G δ hG e γ u₀ hγ hev
  have hw₀ : γ u₀ ∈ D.extPoints := hev.self_of_nhds
  obtain ⟨hz₀, la₀, hla₀, hrel₀⟩ := (hPts ι n P D d g hg).2 _ hw₀

  choose c hc using fun k ↦ Function.ne_iff.mp (hz₀.1 k)
  have hm₀ : evalCone (D.basePart₂ (γ u₀)) (chartMonomial c d) ≠ 0 := by
    simp only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)

  obtain ⟨j, hj⟩ := Function.ne_iff.mp (hw₀.1 none)
  have hj' : D.newPart (γ u₀) j ≠ 0 := hj
  have hg₀ : evalCone (D.basePart₂ (γ u₀)) (g c j) ≠ 0 := by
    intro h0
    apply hj'
    rw [hrel₀ c hm₀ j, h0, mul_zero, zero_div]

  have hco : ∀ (o : Option ι) (i : Fin (D.extSizes o + 1)), AnalyticAt ℂ (fun u ↦ γ u o i) u₀ :=
    fun o i ↦ ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (D.extSizes o + 1) ↦ ℂ) i).analyticAt _).comp
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun o ↦ Fin (D.extSizes o + 1) → ℂ) o).analyticAt _).comp hγ)
  have hold : ∀ f, AnalyticAt ℂ (fun u ↦ evalCone (D.basePart₂ (γ u)) f) u₀ :=
    analyticAt_evalCone_comp (fun u ↦ D.basePart₂ (γ u)) u₀ fun k i ↦ hco (some k) i
  have hM := hold (chartMonomial c d)
  have hG' := hold (g c j)
  have hnew : AnalyticAt ℂ (fun u ↦ D.newPart (γ u) j) u₀ := hco none j
  refine ⟨fun u ↦ D.newPart (γ u) j * evalCone (D.basePart₂ (γ u)) (chartMonomial c d) /
      evalCone (D.basePart₂ (γ u)) (g c j), (hnew.mul hM).div hG' hg₀, ?_, ?_⟩
  · simp only
    rw [hrel₀ c hm₀ j]
    field_simp
    exact hla₀
  · filter_upwards [hev, hM.continuousAt.eventually_ne hm₀, hG'.continuousAt.eventually_ne hg₀]
      with u hu hmu hgu
    obtain ⟨_, la, _, hrel⟩ := (hPts ι n P D d g hg).2 _ hu
    have hla : D.newPart (γ u) j * evalCone (D.basePart₂ (γ u)) (chartMonomial c d) /
        evalCone (D.basePart₂ (γ u)) (g c j) = la := by
      rw [hrel c hmu j]
      field_simp
    rw [hla]
    exact (hMet ι n P D N hN d g hg r G δ hG).2 _ hu c la hmu (hrel c hmu)

end

end GroundTheory.Heights₂.Heights
