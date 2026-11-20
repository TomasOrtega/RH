import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontalMult
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AevalChartSubstMemOfMemBlowUpOf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW`. Establish `hPp : P.IsPrime` using `hP.multiProj.isPrime`. Establish `hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes`. Unfold `divCycle at hW`. Use `split_ifs at hW with h`.

Conclude with `h.1`. Conclude with `absurd rfl hW`. Take `⟨hWp, hBW, hWrel⟩` from `le_and_isRelevant_of_divCycle_ne_zero hW`. Use `set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀`. Take `⟨hW₀p, hPW₀, hrel₀, -⟩` from `comap_liftForm_facts hWp hBW hWrel`.

Establish `hϖW₀ : (C ϖ : MRing ι O) ∉ W₀` using `by rw [Ideal.mem_comap, liftForm_C]; exact hϖW`. Take `⟨j₀, hj₀⟩` from `hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀`. Use `choose v w hv hvw using hj₀`. Establish `huj₀ : u j₀ ∉ P`. Introduce `h`.

Take `⟨j, hj⟩` from `hex`. Establish `h1 : v j * u j ∈ P`. Use `P.add_mem (hvw j) (P.mul_mem_left (w j) h)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Conclude with `hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))`.

Choose the witnesses or unpack the hypotheses as in `⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧ ∀ j, u₀ * u j - u j₀ * a j ∈ P := by`. Use `hW₀p` as an intermediate fact. Use `⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j', fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩` and prove the remaining obligations. Establish `e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') = (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀)`. Rewrite using `[← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `P.mul_mem_left _ (hvw j)`. Establish `hu₀P : u₀ ∉ P` using `fun h => hu₀W (hPW₀ h)`. Establish `ha₀ : a j₀ ∉ W₀`.

Introduce `h`. Establish `h1 : u j₀ * (u₀ - a j₀) ∈ P`. Use `hrelP j₀` as an intermediate fact. Rewrite `this` using `[show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring]`. Then use the resulting hypothesis. Establish `h2 : u₀ - a j₀ ∈ W₀` using `hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)`.

Conclude with `hu₀W (by simpa using W₀.add_mem h2 h)`. Establish `hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u`. Introduce `j`. Apply `mem_blowUpOf_of_sub` to reduce the goal to its premises. Establish `e : u₀ * (u j * a j₀ - u j₀ * a j) = a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀)` using `by ring`.

Establish `h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P`. Rewrite using `[e]`. Conclude with `P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))`. Conclude with `(hPp.mem_or_mem h1).resolve_left hu₀P`. Establish `hxW : liftForm x ∈ W` using `hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`.

Use `⟨⟨hW₀p, sup_le hPW₀ ((Ideal.span_singleton_le_iff_mem _).mpr hxW)⟩, fun P' hP' hP'W₀ => ?_⟩` and prove the remaining obligations. Use `hP'.1` as an intermediate fact. Establish `hxP' : x ∈ P'` using `hP'.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))`. Set `Q'` to `(Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P').comap (aeval (R := O) (chartSubst a))`. Establish `hQ'p : Q'.IsPrime` using `Ideal.comap_isPrime _ _`.

Establish `hBQ' : blowUpOf P u ⊔ Ideal.span {liftForm x} ≤ Q'`. Use `sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)` and prove the remaining obligations. Conclude with `Ideal.map_mono (le_sup_left.trans hP'.2) (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)`. Rewrite using `[Ideal.mem_comap, aeval_chartSubst_liftForm]`. Conclude with `Ideal.mem_map_of_mem _ hxP'`.

Establish `hQ'W : Q' ≤ W` using `fun G hG => mem_of_aeval_chartSubst_mem hWp hP'W₀ j₀ ha₀ (fun j => hBW (hrelB j)) hG`. Establish `hWQ' : W ≤ Q'` using `hmin.2 ⟨hQ'p, hBQ'⟩ hQ'W`. Introduce `p hp`. Establish `h5 : Polynomial.C p ∈ Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P'`. Rewrite using `[← aeval_chartSubst_liftForm a p]`.

Conclude with `hWQ' hp`. Simplify using `using Ideal.mem_map_C_iff.mp h5 0`.
-/
theorem BlowUpHorizontalMinimal.full : BlowUpHorizontalMinimal.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  obtain ⟨hWp, hBW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀
  obtain ⟨hW₀p, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hWrel
  have hϖW₀ : (C ϖ : MRing ι O) ∉ W₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖW
  obtain ⟨j₀, hj₀⟩ := hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀
  choose v w hv hvw using hj₀

  have huj₀ : u j₀ ∉ P := by
    intro h
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have := P.add_mem (hvw j) (P.mul_mem_left (w j) h)
      rwa [sub_add_cancel] at this
    exact hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))

  obtain ⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧
      ∀ j, u₀ * u j - u j₀ * a j ∈ P := by
    have := hW₀p
    refine ⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j',
      fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩
    have e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') =
        (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀) := by
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]; ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hu₀P : u₀ ∉ P := fun h => hu₀W (hPW₀ h)
  have ha₀ : a j₀ ∉ W₀ := by
    intro h
    have h1 : u j₀ * (u₀ - a j₀) ∈ P := by
      have := hrelP j₀
      rwa [show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring] at this
    have h2 : u₀ - a j₀ ∈ W₀ := hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)
    exact hu₀W (by simpa using W₀.add_mem h2 h)

  have hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u := by
    intro j
    apply mem_blowUpOf_of_sub
    have e : u₀ * (u j * a j₀ - u j₀ * a j) =
        a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀) := by ring
    have h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P := by
      rw [e]; exact P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))
    exact (hPp.mem_or_mem h1).resolve_left hu₀P

  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine ⟨⟨hW₀p, sup_le hPW₀ ((Ideal.span_singleton_le_iff_mem _).mpr hxW)⟩, fun P' hP' hP'W₀ => ?_⟩
  have := hP'.1
  have hxP' : x ∈ P' := hP'.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))

  let Q' := (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P').comap
    (aeval (R := O) (chartSubst a))
  have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hBQ' : blowUpOf P u ⊔ Ideal.span {liftForm x} ≤ Q' := by
    refine sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact Ideal.map_mono (le_sup_left.trans hP'.2)
        (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
    · rw [Ideal.mem_comap, aeval_chartSubst_liftForm]
      exact Ideal.mem_map_of_mem _ hxP'
  have hQ'W : Q' ≤ W := fun G hG =>
    mem_of_aeval_chartSubst_mem hWp hP'W₀ j₀ ha₀ (fun j => hBW (hrelB j)) hG

  have hWQ' : W ≤ Q' := hmin.2 ⟨hQ'p, hBQ'⟩ hQ'W
  intro p hp
  have h5 : Polynomial.C p ∈ Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P' := by
    rw [← aeval_chartSubst_liftForm a p]
    exact hWQ' hp
  simpa using Ideal.mem_map_C_iff.mp h5 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
