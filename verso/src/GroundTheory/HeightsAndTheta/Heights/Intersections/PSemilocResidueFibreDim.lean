import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocResidueFibreDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTail
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 PointVertical

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G'`. Establish `hsW : s ∈ W` using `hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))`. Establish `hsW' : rename v s ∈ W'`. Establish `h : s ∈ imageZ v W'` using `hW'.2.2 ▸ hsW`. Conclude with `h`.

Establish `hD' : W' ∈ divSupp P' (rename v s)` using `((hFD K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W').1 ⟨hW', hsW'⟩).1`. Establish `hsec' : IsSectionOn P' (HermLine.sqMetric (ι` using `ι') (Function.extend κ α 0)) (rename v s) := ⟨Function.extend κ α 0, fun _ => rfl, isMultiHomog_rename hv hs, hsP⟩`. Establish `hsec : IsSectionOn (imageZ v P') (HermLine.sqMetric (ι` using `ι) α) s := ⟨α, fun _ => rfl, hs, hsP⟩`. Establish `hA'` using `divSuppArith K' ι' P' n _ _ W' hP' hsec' hD'`. Establish `hA` using `divSuppArith K ι (imageZ v P') n _ _ W hZ hsec hW`.

Establish `hdW : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)`. Distinguish the cases in `hh : IsHorizontal W`. Conclude with `(hA.1 hh).2.2.2`. Conclude with `(hA.2 hh).2.2`. Distinguish the cases in `hh' : IsHorizontal W'`.

Establish `hh : IsHorizontal W`. Unfold `IsHorizontal at hh' ⊢`. Rewrite using `[← hh', ← hW'.2.2]`. Use extensionality with `z`. Simplify using `[imageZ, Ideal.mem_comap]`.

Establish `hW'a : IsArithVar W' (n + 0)` using `hA'.1 hh'`. Establish `hWa : IsArithVar (imageZ v W') n` using `hW'.2.2 ▸ hA.1 hh`. Conclude with `hDim K ι K' ι' κ v W' n 0 G' hv hW'a hWa`. Take `⟨hW'm, hpr, hdW'⟩` from `hA'.2 hh' set p := charOf W' with hpdef`. Establish `: Fact p.Prime` using `⟨hpr⟩`.

Establish `hpW' : ((p : ℕ) : MRing ι') ∈ W'` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W'`. Establish `hpW : ((p : ℕ) : MRing ι) ∈ W`. Rewrite using `[← hW'.2.2]`. Use `show rename v ((p : ℕ) : MRing ι) ∈ W'`. Simplify using `using hpW'`.

Establish `hWm : IsMultiProjPrime W` using `hW'.2.2 ▸ isMultiProjPrime_imageZ hv hW'm`. Establish `hWp : IsProjVarF (W'.map (red p)) n` using `⟨isMultiProjPrime_red p hW'm hpW', by rw [ringKrullDim_red p hpW', hdW']⟩`. Establish `hVi : IsProjVarF (imageVar (ZMod p) v (W'.map (red p))) n`. Rewrite using `[imageVar_red p v hpW', hW'.2.2]`. Conclude with `⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hdW]⟩`.

Conclude with `hAI K ι K' ι' κ v p W' n hv hpW' hWp hVi G'`.
-/
theorem SemilocResidueFibreDim.proof (hFD : FibreDivSupp.Statement) (hDim : FibreDimStatement)
    (hAI : FibreDimensionZero.Statement) : SemilocResidueFibreDim.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G'
  classical
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hsW' : rename v s ∈ W' := by
    have h : s ∈ imageZ v W' := hW'.2.2 ▸ hsW
    exact h
  have hD' : W' ∈ divSupp P' (rename v s) := ((hFD K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W').1 ⟨hW', hsW'⟩).1
  have hsec' : IsSectionOn P' (HermLine.sqMetric (ι := ι') (Function.extend κ α 0)) (rename v s) :=
    ⟨Function.extend κ α 0, fun _ => rfl, isMultiHomog_rename hv hs, hsP⟩
  have hsec : IsSectionOn (imageZ v P') (HermLine.sqMetric (ι := ι) α) s := ⟨α, fun _ => rfl, hs, hsP⟩
  have hA' := divSuppArith K' ι' P' n _ _ W' hP' hsec' hD'
  have hA := divSuppArith K ι (imageZ v P') n _ _ W hZ hsec hW
  have hdW : ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    by_cases hh : IsHorizontal W
    · exact (hA.1 hh).2.2.2
    · exact (hA.2 hh).2.2
  by_cases hh' : IsHorizontal W'
  · have hh : IsHorizontal W := by
      unfold IsHorizontal at hh' ⊢
      rw [← hh', ← hW'.2.2]
      ext z
      simp [imageZ, Ideal.mem_comap]
    have hW'a : IsArithVar W' (n + 0) := hA'.1 hh'
    have hWa : IsArithVar (imageZ v W') n := hW'.2.2 ▸ hA.1 hh
    exact hDim K ι K' ι' κ v W' n 0 G' hv hW'a hWa
  · obtain ⟨hW'm, hpr, hdW'⟩ := hA'.2 hh'
    set p := charOf W' with hpdef
    have : Fact p.Prime := ⟨hpr⟩
    have hpW' : ((p : ℕ) : MRing ι') ∈ W' := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W'
    have hpW : ((p : ℕ) : MRing ι) ∈ W := by
      rw [← hW'.2.2]
      show rename v ((p : ℕ) : MRing ι) ∈ W'
      simpa using hpW'
    have hWm : IsMultiProjPrime W := hW'.2.2 ▸ isMultiProjPrime_imageZ hv hW'm
    have hWp : IsProjVarF (W'.map (red p)) n :=
      ⟨isMultiProjPrime_red p hW'm hpW', by rw [ringKrullDim_red p hpW', hdW']⟩
    have hVi : IsProjVarF (imageVar (ZMod p) v (W'.map (red p))) n := by
      rw [imageVar_red p v hpW', hW'.2.2]
      exact ⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hdW]⟩
    exact hAI K ι K' ι' κ v p W' n hv hpW' hWp hVi G'

end GroundTheory.Heights₂.Heights.Inter
