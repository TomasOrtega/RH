import Mathlib
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep

/- English proof (translation)
The claim follows from `h.nullMeasurableSet.congr hst.symm ae_covers := by have hall : ∀ᵐ x ∂μ, ∀ g : Γ, (g • x ∈ t) = (g • x ∈ s) := by rw [ae_all_iff] intro g exact (measurePreserving_smul g μ).quasiMeasurePreserving.ae_eq hst filter_upwards [h.ae_covers, hall] with x ⟨g, hg⟩ hx exact ⟨g, by rw [hx g] …`.
-/
theorem isFundamentalDomain_of_ae_eq {Γ X : Type} [Group Γ] [Countable Γ] [MeasurableSpace X]
    [MulAction Γ X] [MeasurableConstSMul Γ X] {μ : Measure X} [SMulInvariantMeasure Γ X μ]
    {s t : Set X} (h : IsFundamentalDomain Γ s μ) (hst : t =ᵐ[μ] s) :
    IsFundamentalDomain Γ t μ where
  nullMeasurableSet := h.nullMeasurableSet.congr hst.symm
  ae_covers := by
    have hall : ∀ᵐ x ∂μ, ∀ g : Γ, (g • x ∈ t) = (g • x ∈ s) := by
      rw [ae_all_iff]
      intro g
      exact (measurePreserving_smul g μ).quasiMeasurePreserving.ae_eq hst
    filter_upwards [h.ae_covers, hall] with x ⟨g, hg⟩ hx
    exact ⟨g, by rw [hx g]; exact hg⟩
  aedisjoint a b hab := by
    have key : ∀ c : Γ, (c • t : Set X) =ᵐ[μ] (c • s : Set X) := fun c => by
      rw [← Set.preimage_smul_inv, ← Set.preimage_smul_inv]
      exact (measurePreserving_smul c⁻¹ μ).quasiMeasurePreserving.preimage_ae_eq hst
    exact (h.aedisjoint hab).congr (key a) (key b)

variable {S X : Type} [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X]
  [MeasurableSMul₂ S X]

/- English proof (translation)
Use `set W' := toMeasurable μ W`. Establish `hW'm : MeasurableSet W'` using `measurableSet_toMeasurable μ W`. Establish `hW'0 : μ W' = 0` using `by rw [measure_toMeasurable]; exact hW`. Establish `hQ : MeasurableSet {p : X × S | p.2 • p.1 ∈ W'}` using `hW'm.preimage (measurable_snd.smul measurable_fst)`. Establish `h0 : μ.prod ν {p : X × S | p.2 • p.1 ∈ W'} = 0`.

Rewrite using `[Measure.prod_apply_symm hQ]`. Establish `: ∀ s : S, μ ((fun x => (x, s)) ⁻¹' {p : X × S | p.2 • p.1 ∈ W'}) = 0` using `fun s => by`. Express the relevant statement in the definitionally equal form `μ ((fun x => s • x) ⁻¹' W') = 0`. Rewrite using `[measure_preimage_smul]`. Conclude with `hW'0`.

Conclude with `(lintegral_congr this).trans lintegral_zero`. Establish `h1` using `(Measure.measure_prod_null hQ).1 h0`. Use `filter_upwards [h1] with y hy`. Conclude with `measure_mono_null (fun s hs => subset_toMeasurable μ W hs) hy`.
-/
theorem ae_measure_setOf_smul_mem_eq_zero (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] {W : Set X} (hW : μ W = 0) :
    ∀ᵐ y ∂μ, ν {s | s • y ∈ W} = 0 := by
  set W' := toMeasurable μ W
  have hW'm : MeasurableSet W' := measurableSet_toMeasurable μ W
  have hW'0 : μ W' = 0 := by rw [measure_toMeasurable]; exact hW
  have hQ : MeasurableSet {p : X × S | p.2 • p.1 ∈ W'} :=
    hW'm.preimage (measurable_snd.smul measurable_fst)
  have h0 : μ.prod ν {p : X × S | p.2 • p.1 ∈ W'} = 0 := by
    rw [Measure.prod_apply_symm hQ]
    have : ∀ s : S, μ ((fun x => (x, s)) ⁻¹' {p : X × S | p.2 • p.1 ∈ W'}) = 0 := fun s => by
      change μ ((fun x => s • x) ⁻¹' W') = 0
      rw [measure_preimage_smul]; exact hW'0
    exact (lintegral_congr this).trans lintegral_zero
  have h1 := (Measure.measure_prod_null hQ).1 h0
  filter_upwards [h1] with y hy
  exact measure_mono_null (fun s hs => subset_toMeasurable μ W hs) hy

end GlobalTheory.CovolIndep
