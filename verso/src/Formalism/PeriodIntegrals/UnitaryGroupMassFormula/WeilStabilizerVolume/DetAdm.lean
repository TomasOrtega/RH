import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DetAdmC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.NuInvSt

noncomputable section

namespace PI.VolStabW.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabW.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabW
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported

/- English proof (translation)
Set `ι` to `Fin a × Fin M × Fin (Module.finrank F E)`. Set `Ψ` to `psiH F E a M`. Set `Ψm` to `Ψ.toMeasurableEquiv`. Establish `hfin : ∀ ν : Measure (Fin a → Fin M → AF F ⊗[F] E), (∀ K, IsCompact K → ν K < ⊤) → ∀ K, IsCompact K → ν.map Ψm K < ⊤`. Introduce `ν hν K hK`.

Rewrite using `[Ψm.map_apply]`. Conclude with `hν _ (Ψ.isCompact_preimage.2 hK)`. It suffices to establish `hμ : ν1.map Ψm = ν2.map Ψm by`. Rewrite using `[← Ψm.map_symm_map (μ := ν1), ← Ψm.map_symm_map (μ := ν2), hμ]`. Use `set μ1 := ν1.map Ψm with hμ1`.

Use `set μ2 := ν2.map Ψm with hμ2`. Establish `hbox : ∀ D, IsBoxD D → ∀ U : Set (ι → Ainf F), MeasurableSet U → μ1 (U ×ˢ boxS D) = μ2 (U ×ˢ boxS D)`. Introduce `D hD`. Set `ρ` to `fun μ : Measure ((ι → Ainf F) × (ι → Af F)) => (μ.restrict (univ ×ˢ boxS D)).map Prod.fst`. Establish `hβ : MeasurableSet (boxS D)` using `(isCompact_boxS hD).isClosed.measurableSet`.

Establish `hρ : ∀ μ U, MeasurableSet U → ρ μ U = μ (U ×ˢ boxS D)`. Introduce `μ U hU`. Simplify using `only [ρ]`. Rewrite using `[Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU)]`. Use `congr 1`.

Use extensionality with `p`. Simplify using the standard rewrite rules. Establish `hint : ∀ μ (f : C_c(ι → Ainf F, ℝ)), ∫ x, f x ∂(ρ μ) = ∫ p, f p.1 * (boxS D).indicator (fun _ => (1 : ℝ)) p.2 ∂μ`. Introduce `μ f`. Simplify using `only [ρ]`.

Rewrite using `[integral_map measurable_fst.aemeasurable (map_continuous f).aestronglyMeasurable, ← integral_indicator (MeasurableSet.univ.prod hβ)]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Distinguish the cases in `hp : p.2 ∈ boxS D`. Rewrite using `[Set.indicator_of_mem (mk_mem_prod (mem_univ p.1) hp : p ∈ univ ×ˢ boxS D), Set.indicator_of_mem hp, mul_one]`.

Rewrite using `[Set.indicator_of_notMem (fun h' => hp h'.2), Set.indicator_of_notMem hp, mul_zero]`. Establish `hfc : ∀ μ : Measure ((ι → Ainf F) × (ι → Af F)), (∀ K, IsCompact K → μ K < ⊤) → IsFiniteMeasureOnCompacts (ρ μ)` using `fun μ hμ => ⟨fun K hK => by`. Rewrite using `[hρ μ K hK.measurableSet]`. Conclude with `hμ _ (hK.prod (isCompact_boxS hD))⟩`. Use `hfc μ1 (hfin ν1 h1)` as an intermediate fact.

Use `hfc μ2 (hfin ν2 h2)` as an intermediate fact. Establish `hρeq : ρ μ1 = ρ μ2` using `Measure.ext_of_integral_eq_on_compactlySupported fun f => by`. Rewrite using `[hint, hint, hμ1, hμ2, integral_map_equiv, integral_map_equiv]`. Conclude with `key_int ν1 ν2 h hD f`. Introduce `U hU`.

Rewrite using `[← hρ μ1 U hU, ← hρ μ2 U hU, hρeq]`. Take `⟨bs, hbs, hbU⟩` from `boxes_seq (F := F) (ι := ι)`. Use `Measure.ext_of_generateFrom_of_iUnion (image2 (· ×ˢ ·) {U : Set (ι → Ainf F) | MeasurableSet U} (boxes F ι)) (fun n => compactCovering (ι → Ainf F) n.unpair.1 ×ˢ bs n.unpair.2) ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← generateFrom_prod_eq isCountablySpanning_measurableSet ⟨bs, hbs, hbU⟩, generateFrom_boxes, MeasurableSpace.generateFrom_measurableSet]`. Introduce and unpack `_ ⟨U, hU, β, hβ, rfl⟩ _ ⟨U', hU', β', hβ', rfl⟩ _`.

Rewrite using `[prod_inter_prod]`. Establish `hU2 : MeasurableSet U` using `hU`. Establish `hU2' : MeasurableSet U'` using `hU'`. Conclude with `mem_image2_of_mem (hU2.inter hU2') (boxes_inter hβ hβ')`. Use `eq_univ_of_forall fun p => mem_iUnion.2 ?_` and prove the remaining obligations.

Establish `h1' : p.1 ∈ ⋃ m, compactCovering (ι → Ainf F) m`. Rewrite using `[iUnion_compactCovering]`. Discharge the goal by the elementary cases of `trivial`. Establish `h2' : p.2 ∈ ⋃ n, bs n`. Rewrite using `[hbU]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨m, hm⟩` from `mem_iUnion.1 h1'`. Take `⟨n, hn⟩` from `mem_iUnion.1 h2'`. Use `⟨Nat.pair m n, ?_⟩` and prove the remaining obligations. Simplify using `only [Nat.unpair_pair]`.

Conclude with `⟨hm, hn⟩`. Introduce `n`. Conclude with `mem_image2_of_mem (show MeasurableSet (compactCovering (ι → Ainf F) n.unpair.1) from (isCompact_compactCovering _ _).measurableSet) (hbs _)`. Introduce `n`. Take `⟨D, hD, e⟩` from `hbs n.unpair.2`.

Rewrite using `[e]`. Conclude with `(hfin ν1 h1 _ ((isCompact_compactCovering _ _).prod (isCompact_boxS hD))).ne`. Introduce and unpack `_ ⟨U, hU, β, ⟨D, hD, rfl⟩, rfl⟩`. Conclude with `hbox D hD U hU`.
-/
theorem detAdm_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {a M : ℕ} (ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (h1 : ∀ K, IsCompact K → ν1 K < ⊤) (h2 : ∀ K, IsCompact K → ν2 K < ⊤)
    (h : ∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2) : ν1 = ν2 := by
  classical
  let ι := Fin a × Fin M × Fin (Module.finrank F E)
  let Ψ := psiH F E a M
  let Ψm := Ψ.toMeasurableEquiv
  have hfin : ∀ ν : Measure (Fin a → Fin M → AF F ⊗[F] E), (∀ K, IsCompact K → ν K < ⊤) →
      ∀ K, IsCompact K → ν.map Ψm K < ⊤ := by
    intro ν hν K hK
    rw [Ψm.map_apply]
    exact hν _ (Ψ.isCompact_preimage.2 hK)
  suffices hμ : ν1.map Ψm = ν2.map Ψm by
    rw [← Ψm.map_symm_map (μ := ν1), ← Ψm.map_symm_map (μ := ν2), hμ]
  set μ1 := ν1.map Ψm with hμ1
  set μ2 := ν2.map Ψm with hμ2

  have hbox : ∀ D, IsBoxD D → ∀ U : Set (ι → Ainf F), MeasurableSet U →
      μ1 (U ×ˢ boxS D) = μ2 (U ×ˢ boxS D) := by
    intro D hD
    let ρ := fun μ : Measure ((ι → Ainf F) × (ι → Af F)) =>
      (μ.restrict (univ ×ˢ boxS D)).map Prod.fst
    have hβ : MeasurableSet (boxS D) := (isCompact_boxS hD).isClosed.measurableSet
    have hρ : ∀ μ U, MeasurableSet U → ρ μ U = μ (U ×ˢ boxS D) := by
      intro μ U hU
      simp only [ρ]
      rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU)]
      congr 1
      ext p
      simp
    have hint : ∀ μ (f : C_c(ι → Ainf F, ℝ)), ∫ x, f x ∂(ρ μ) =
        ∫ p, f p.1 * (boxS D).indicator (fun _ => (1 : ℝ)) p.2 ∂μ := by
      intro μ f
      simp only [ρ]
      rw [integral_map measurable_fst.aemeasurable (map_continuous f).aestronglyMeasurable,
        ← integral_indicator (MeasurableSet.univ.prod hβ)]
      congr 1
      funext p
      by_cases hp : p.2 ∈ boxS D
      · rw [Set.indicator_of_mem (mk_mem_prod (mem_univ p.1) hp : p ∈ univ ×ˢ boxS D),
          Set.indicator_of_mem hp, mul_one]
      · rw [Set.indicator_of_notMem (fun h' => hp h'.2), Set.indicator_of_notMem hp, mul_zero]
    have hfc : ∀ μ : Measure ((ι → Ainf F) × (ι → Af F)), (∀ K, IsCompact K → μ K < ⊤) →
        IsFiniteMeasureOnCompacts (ρ μ) := fun μ hμ =>
      ⟨fun K hK => by
        rw [hρ μ K hK.measurableSet]
        exact hμ _ (hK.prod (isCompact_boxS hD))⟩
    have := hfc μ1 (hfin ν1 h1)
    have := hfc μ2 (hfin ν2 h2)
    have hρeq : ρ μ1 = ρ μ2 := Measure.ext_of_integral_eq_on_compactlySupported fun f => by
      rw [hint, hint, hμ1, hμ2, integral_map_equiv, integral_map_equiv]
      exact key_int ν1 ν2 h hD f
    intro U hU
    rw [← hρ μ1 U hU, ← hρ μ2 U hU, hρeq]

  obtain ⟨bs, hbs, hbU⟩ := boxes_seq (F := F) (ι := ι)
  refine Measure.ext_of_generateFrom_of_iUnion
    (image2 (· ×ˢ ·) {U : Set (ι → Ainf F) | MeasurableSet U} (boxes F ι))
    (fun n => compactCovering (ι → Ainf F) n.unpair.1 ×ˢ bs n.unpair.2) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← generateFrom_prod_eq isCountablySpanning_measurableSet ⟨bs, hbs, hbU⟩,
      generateFrom_boxes, MeasurableSpace.generateFrom_measurableSet]
  · rintro _ ⟨U, hU, β, hβ, rfl⟩ _ ⟨U', hU', β', hβ', rfl⟩ _
    rw [prod_inter_prod]
    have hU2 : MeasurableSet U := hU
    have hU2' : MeasurableSet U' := hU'
    exact mem_image2_of_mem (hU2.inter hU2') (boxes_inter hβ hβ')
  · refine eq_univ_of_forall fun p => mem_iUnion.2 ?_
    have h1' : p.1 ∈ ⋃ m, compactCovering (ι → Ainf F) m := by
      rw [iUnion_compactCovering]
      trivial
    have h2' : p.2 ∈ ⋃ n, bs n := by
      rw [hbU]
      trivial
    obtain ⟨m, hm⟩ := mem_iUnion.1 h1'
    obtain ⟨n, hn⟩ := mem_iUnion.1 h2'
    refine ⟨Nat.pair m n, ?_⟩
    simp only [Nat.unpair_pair]
    exact ⟨hm, hn⟩
  · intro n
    exact mem_image2_of_mem (show MeasurableSet (compactCovering (ι → Ainf F) n.unpair.1) from
      (isCompact_compactCovering _ _).measurableSet) (hbs _)
  · intro n
    obtain ⟨D, hD, e⟩ := hbs n.unpair.2
    rw [e]
    exact (hfin ν1 h1 _ ((isCompact_compactCovering _ _).prod (isCompact_boxS hD))).ne
  · rintro _ ⟨U, hU, β, ⟨D, hD, rfl⟩, rfl⟩
    exact hbox D hD U hU

end PI.VolStabW.DeterminantAdmissible

namespace PI.VolStabW

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ν1 ν2 h1 h2 h`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Conclude with `DeterminantAdmissible.detAdm_gen ν1 ν2 h1 h2 h`.
-/
theorem detAdm_holds : DetAdm := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ν1 ν2 h1 h2 h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact DeterminantAdmissible.detAdm_gen ν1 ν2 h1 h2 h

end PI.VolStabW
