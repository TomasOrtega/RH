import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX

noncomputable section

open PowerSeries GlobalTheory.NB.LT

namespace GlobalTheory.NB.LT

open scoped PowerSeries.WithPiTopology in

/- English proof (translation)
Set `: WithIdeal O` to `⟨I⟩`. Establish `hI : IsAdic I` using `rfl`. Take `⟨h1, h2⟩` from `hI.isAdicComplete_iff.mp h`. Establish `ha : PowerSeries.HasEval c` using `WithIdeal.isTopologicallyNilpotent_of_mem hc`. Establish `hC : PowerSeries.HasEval (C c : O⟦X⟧)` using `ha.map (φ := (C : O →+* O⟦X⟧)) PowerSeries.WithPiTopology.continuous_C`.

Establish `: IsLinearTopology O⟦X⟧ O⟦X⟧` using `inferInstance`. Establish `hX : PowerSeries.HasEval (X + C c : O⟦X⟧)` using `PowerSeries.HasEval.X.add hC`. Establish `: ContinuousSMul O O⟦X⟧` using `⟨by`. Establish `: (fun p : O × O⟦X⟧ => p.1 • p.2) = fun p => C p.1 * p.2`. Use function extensionality and compare the values at `p`.

Rewrite using `[smul_eq_C_mul]`. Rewrite using `[this]`. Conclude with `(PowerSeries.WithPiTopology.continuous_C.comp continuous_fst).mul continuous_snd⟩`. Use `⟨PowerSeries.aeval hX, ?_⟩` and prove the remaining obligations. Rewrite using `[PowerSeries.coe_aeval, PowerSeries.eval₂_X]`.
-/
theorem exists_algHom_X_add_C {O : Type} [CommRing O] (I : Ideal O) [h : IsAdicComplete I O]
    (c : O) (hc : c ∈ I) : ∃ t : O⟦X⟧ →ₐ[O] O⟦X⟧, t X = X + C c := by
  let : WithIdeal O := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨h1, h2⟩ := hI.isAdicComplete_iff.mp h
  have ha : PowerSeries.HasEval c := WithIdeal.isTopologicallyNilpotent_of_mem hc
  have hC : PowerSeries.HasEval (C c : O⟦X⟧) :=
    ha.map (φ := (C : O →+* O⟦X⟧)) PowerSeries.WithPiTopology.continuous_C
  have : IsLinearTopology O⟦X⟧ O⟦X⟧ :=
    inferInstance
  have hX : PowerSeries.HasEval (X + C c : O⟦X⟧) := PowerSeries.HasEval.X.add hC
  have : ContinuousSMul O O⟦X⟧ := ⟨by
    have : (fun p : O × O⟦X⟧ => p.1 • p.2) = fun p => C p.1 * p.2 := by
      funext p; rw [smul_eq_C_mul]
    rw [this]
    exact (PowerSeries.WithPiTopology.continuous_C.comp continuous_fst).mul continuous_snd⟩
  refine ⟨PowerSeries.aeval hX, ?_⟩
  rw [PowerSeries.coe_aeval, PowerSeries.eval₂_X]

/- English proof (translation)
Introduce `O _ I _ c hc`. Take `⟨s, hs⟩` from `exists_algHom_X_add_C I c hc`. Take `⟨t, ht⟩` from `exists_algHom_X_add_C I (-c) (neg_mem hc)`. Establish `hC : ∀ (u : O⟦X⟧ →ₐ[O] O⟦X⟧) (a : O), u (C a) = C a` using `fun u a => u.commutes a`. Establish `h1 : (s.comp t) X = X`.

Rewrite using `[AlgHom.comp_apply, ht, map_add, hs, hC, map_neg]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (t.comp s) X = X`. Rewrite using `[AlgHom.comp_apply, hs, map_add, ht, hC, map_neg]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `⟨AlgEquiv.ofAlgHom s t (algHom_ext_X _ _ h1 (by rw [h1])) (algHom_ext_X _ _ h2 (by rw [h2])), hs⟩`.
-/
theorem exists_algEquiv_X_add_C : ∀ {O : Type} [CommRing O] (I : Ideal O) [IsAdicComplete I O] (c : O), c ∈ I → ∃ lev : O⟦X⟧ ≃ₐ[O] O⟦X⟧, lev X = X + C c := by
  intro O _ I _ c hc
  obtain ⟨s, hs⟩ := exists_algHom_X_add_C I c hc
  obtain ⟨t, ht⟩ := exists_algHom_X_add_C I (-c) (neg_mem hc)
  have hC : ∀ (u : O⟦X⟧ →ₐ[O] O⟦X⟧) (a : O), u (C a) = C a := fun u a => u.commutes a
  have h1 : (s.comp t) X = X := by
    rw [AlgHom.comp_apply, ht, map_add, hs, hC, map_neg]; ring
  have h2 : (t.comp s) X = X := by
    rw [AlgHom.comp_apply, hs, map_add, ht, hC, map_neg]; ring
  exact ⟨AlgEquiv.ofAlgHom s t (algHom_ext_X _ _ h1 (by rw [h1])) (algHom_ext_X _ _ h2 (by rw [h2])), hs⟩

end GlobalTheory.NB.LT
