import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Set `ψ : Ideal B → ℕ∞` to `fun P => if h : P.IsMaximal then (haveI := h.isPrime Ring.ord (Localization.AtPrime P) (algebraMap B (Localization.AtPrime P) θ) * Module.length O (B ⧸ P)) else 0`. Combine the equalities or inequalities in the displayed calculation. Use `finsum_congr fun 𝔓 => ?_` and prove the remaining obligations. Rewrite using `[finsum_eq_if]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Establish `hu : IsUnit (algebraMap B (Localization.AtPrime 𝔓.asIdeal) θ)` using `IsLocalization.map_units (M := 𝔓.asIdeal.primeCompl) (Localization.AtPrime 𝔓.asIdeal) ⟨θ, h⟩`. Rewrite using `[Ring.ord_of_isUnit hu, zero_mul]`. Use `_ = ∑ᶠ P ∈ {P : Ideal B | P.IsMaximal ∧ θ ∈ P}, ψ P := finsum_mem_eq_of_bijOn MaximalSpectrum.asIdeal ⟨fun 𝔓 h => ⟨𝔓.isMaximal, h⟩, fun a _ b _ h => MaximalSpectrum.ext h, fun P hP => ⟨⟨P, hP.1⟩, hP.2, rfl⟩⟩ (fun 𝔓 _ => by simp only [ψ, dif_pos 𝔓.isMaximal])`. Use `_ = ∑ᶠ i ∈ (S : Set ι), ψ (c i) := (finsum_mem_eq_of_bijOn c hc fun _ _ => rfl).symm`.

Use `_ = ∑ i ∈ S, ψ (c i) := finsum_mem_coe_finset _ _`. Use `_ = ∑ i ∈ S, m i := Finset.sum_congr rfl fun i hi => by`. Establish `hmax : (c i).IsMaximal` using `(hc.mapsTo (Finset.mem_coe.mpr hi)).1`. Simplify using `only [ψ, dif_pos hmax]`. Conclude with `hm i hi hmax.isPrime`.
-/
theorem finsum_maximalSpectrum_ord_eq_sum {O B ι : Type*} [CommRing O] [CommRing B] [Algebra O B] (θ : B)
    (S : Finset ι) (c : ι → Ideal B) (hc : Set.BijOn c ↑S {P | P.IsMaximal ∧ θ ∈ P}) (m : ι → ℕ∞)
    (hm : ∀ i ∈ S, ∀ _ : (c i).IsPrime,
      Ring.ord (Localization.AtPrime (c i)) (algebraMap B _ θ) * Module.length O (B ⧸ c i) = m i) :
    ∑ᶠ 𝔓 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) * Module.length O (B ⧸ 𝔓.asIdeal) =
      ∑ i ∈ S, m i := by
  classical
  let ψ : Ideal B → ℕ∞ := fun P => if h : P.IsMaximal then
    (haveI := h.isPrime
     Ring.ord (Localization.AtPrime P) (algebraMap B (Localization.AtPrime P) θ) * Module.length O (B ⧸ P))
    else 0
  calc ∑ᶠ 𝔓 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) * Module.length O (B ⧸ 𝔓.asIdeal)
      = ∑ᶠ 𝔓 ∈ {𝔓 : MaximalSpectrum B | θ ∈ 𝔓.asIdeal},
          Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) *
            Module.length O (B ⧸ 𝔓.asIdeal) := by
        refine finsum_congr fun 𝔓 => ?_
        rw [finsum_eq_if]
        split_ifs with h
        · rfl
        · have hu : IsUnit (algebraMap B (Localization.AtPrime 𝔓.asIdeal) θ) :=
            IsLocalization.map_units (M := 𝔓.asIdeal.primeCompl) (Localization.AtPrime 𝔓.asIdeal) ⟨θ, h⟩
          rw [Ring.ord_of_isUnit hu, zero_mul]
    _ = ∑ᶠ P ∈ {P : Ideal B | P.IsMaximal ∧ θ ∈ P}, ψ P :=
        finsum_mem_eq_of_bijOn MaximalSpectrum.asIdeal
          ⟨fun 𝔓 h => ⟨𝔓.isMaximal, h⟩, fun a _ b _ h => MaximalSpectrum.ext h,
            fun P hP => ⟨⟨P, hP.1⟩, hP.2, rfl⟩⟩
          (fun 𝔓 _ => by simp only [ψ, dif_pos 𝔓.isMaximal])
    _ = ∑ᶠ i ∈ (S : Set ι), ψ (c i) := (finsum_mem_eq_of_bijOn c hc fun _ _ => rfl).symm
    _ = ∑ i ∈ S, ψ (c i) := finsum_mem_coe_finset _ _
    _ = ∑ i ∈ S, m i := Finset.sum_congr rfl fun i hi => by
        have hmax : (c i).IsMaximal := (hc.mapsTo (Finset.mem_coe.mpr hi)).1
        simp only [ψ, dif_pos hmax]
        exact hm i hi hmax.isPrime

/- English proof (translation)
Introduce `F _ _ n e I f t u q p _ hI hf hu hq hp hqt`. Establish `hpt : specFirst f t ∉ p`. Rewrite using `[hp, Ideal.mem_span_singleton]`. Conclude with `hqt`. Establish `: Module.Finite (Localization.AtPrime p) (ChartLoc I t e p)` using `h₃ F n e I f t p hI hf hpt`.

Rewrite using `[h₄ (Localization.AtPrime p) (ChartLoc I t e p) (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))]`. Use `finsum_maximalSpectrum_ord_eq_sum _ _ (chartIdeal I t e p) ?_ _ ?_` and prove the remaining obligations. Establish `h` using `h₅ F n e I f t u q p hI hf hu hq hp hqt`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `W`.

Simplify using the standard rewrite rules. Introduce `W hW _`. Take `⟨hWs, hWq⟩` from `Finset.mem_filter.mp hW`. Establish `hrel : W ∈ relComps (I ⊔ Ideal.span {linForm u})`. Rewrite `hWs` using `[Finsupp.mem_support_iff]`.

Assume the negation of the conclusion as `h`. Conclude with `hWs (by simp [divCycle, fundCycle, Finsupp.onFinset_apply, h])`. Establish `hqW : q ∈ incIdeal W e` using `hWq ▸ Ideal.mem_span_singleton_self q`. Establish `htW : linForm t ∉ W` using `fun h => by`. Establish `hIW : I ≤ W` using `le_trans le_sup_left hrel.1.1.2`.

Use `h₂ F n e I W f t hf hIW h` as an intermediate fact. Rewrite `this` using `[← hWq, Ideal.mem_span_singleton]`. Conclude with `hqt this`. Take `⟨_, hord⟩` from `h₆ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW`. Establish `hlen` using `h₇ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW`.

Establish `hdiv : divCycle I u W = localMult (I ⊔ Ideal.span {linForm u}) W`. Simplify using `[divCycle, fundCycle, Finsupp.onFinset_apply, hrel]`. Rewrite using `[hlen, mul_one, hdiv]`. Conclude with `hord`.
-/
theorem ChartLength.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartFinite.Statement) (h₄ : LengthFiniteAlgebra.Statement) (h₅ : ChartMaxIdeals.Statement)
    (h₆ : ChartLocalOrder.Statement) (h₇ : ChartResidueDegree.Statement) : ChartLength.Statement := by
  intro F _ _ n e I f t u q p _ hI hf hu hq hp hqt
  classical

  have hpt : specFirst f t ∉ p := by
    rw [hp, Ideal.mem_span_singleton]
    exact hqt
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₃ F n e I f t p hI hf hpt
  rw [h₄ (Localization.AtPrime p) (ChartLoc I t e p)
    (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))]
  refine finsum_maximalSpectrum_ord_eq_sum _ _ (chartIdeal I t e p) ?_ _ ?_
  · have h := h₅ F n e I f t u q p hI hf hu hq hp hqt
    convert h using 1
    ext W
    simp
  · intro W hW _
    obtain ⟨hWs, hWq⟩ := Finset.mem_filter.mp hW
    have hrel : W ∈ relComps (I ⊔ Ideal.span {linForm u}) := by
      rw [Finsupp.mem_support_iff] at hWs
      by_contra h
      exact hWs (by simp [divCycle, fundCycle, Finsupp.onFinset_apply, h])
    have hqW : q ∈ incIdeal W e := hWq ▸ Ideal.mem_span_singleton_self q
    have htW : linForm t ∉ W := fun h => by
      have hIW : I ≤ W := le_trans le_sup_left hrel.1.1.2
      have := h₂ F n e I W f t hf hIW h
      rw [← hWq, Ideal.mem_span_singleton] at this
      exact hqt this
    obtain ⟨_, hord⟩ := h₆ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW
    have hlen := h₇ F n e I W f t u q p hI hf hu hq hp hqt hrel hqW htW
    have hdiv : divCycle I u W = localMult (I ⊔ Ideal.span {linForm u}) W := by
      simp [divCycle, fundCycle, Finsupp.onFinset_apply, hrel]
    rw [hlen, mul_one, hdiv]
    exact hord

end

end GroundTheory.Heights₂.Heights
