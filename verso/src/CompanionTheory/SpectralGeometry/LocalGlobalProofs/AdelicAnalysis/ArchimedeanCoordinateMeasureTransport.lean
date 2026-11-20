import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphRankOneTuplesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.InfPush

/- English proof (translation)
Set `s : (ι → κ → ℝ) ≃+ (κ → ι → ℝ)` to `{ toFun := fun f k i => f i k invFun := fun g i k => g k i left_inv := fun _ => rfl right_inv := fun _ => rfl map_add' := fun _ _ => rfl }`. Establish `hs : Continuous s` using `continuous_pi fun k => continuous_pi fun i => (continuous_apply k).comp (continuous_apply i)`. Establish `hs' : Continuous s.symm` using `continuous_pi fun i => continuous_pi fun k => (continuous_apply i).comp (continuous_apply k)`. Establish `h0 : (volume : Measure (κ → ℝ)).IsAddHaarMeasure`. Rewrite using `[volume_pi]`.

Conclude with `Measure.pi.isAddHaarMeasure _`. Establish `h0' : (volume : Measure (ι → ℝ)).IsAddHaarMeasure`. Rewrite using `[volume_pi]`. Conclude with `Measure.pi.isAddHaarMeasure _`. Establish `hV : (volume : Measure (ι → κ → ℝ)).IsAddHaarMeasure`.

Rewrite using `[volume_pi]`. Conclude with `Measure.pi.isAddHaarMeasure _`. Establish `hV' : (volume : Measure (κ → ι → ℝ)).IsAddHaarMeasure`. Rewrite using `[volume_pi]`. Conclude with `Measure.pi.isAddHaarMeasure _`.

Establish `hH : ((volume : Measure (ι → κ → ℝ)).map s).IsAddHaarMeasure` using `s.isAddHaarMeasure_map _ hs hs'`. Establish `hc` using `Measure.isAddLeftInvariant_eq_smul ((volume : Measure (ι → κ → ℝ)).map s) (volume : Measure (κ → ι → ℝ))`. Use `set c := Measure.addHaarScalarFactor ((volume : Measure (ι → κ → ℝ)).map s) (volume : Measure (κ → ι → ℝ)) with hcdef`. Set `B : Set (κ → ι → ℝ)` to `Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1`. Set `B' : Set (ι → κ → ℝ)` to `Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1`.

Establish `hB : MeasurableSet B` using `MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Icc`. Establish `hpre : s ⁻¹' B = B'`. Use extensionality with `f`. Simplify using `only [B, B', Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]`. Conclude with `forall_comm`.

Establish `vB : (volume : Measure (κ → ι → ℝ)) B = 1`. Simplify using `only [B]`. Rewrite using `[volume_pi_pi]`. Use `Finset.prod_eq_one fun _ _ => ?_` and prove the remaining obligations. Rewrite using `[volume_pi_pi]`.

Use `Finset.prod_eq_one fun _ _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `vB' : (volume : Measure (ι → κ → ℝ)) B' = 1`. Simplify using `only [B']`. Rewrite using `[volume_pi_pi]`.

Use `Finset.prod_eq_one fun _ _ => ?_` and prove the remaining obligations. Rewrite using `[volume_pi_pi]`. Use `Finset.prod_eq_one fun _ _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `h1 : ((volume : Measure (ι → κ → ℝ)).map s) B = 1`.

Rewrite using `[Measure.map_apply hs.measurable hB, hpre, vB']`. Establish `hc1 : c = 1`. Rewrite `h1` using `[hc]`. Simplify using `only [Measure.smul_apply, vB] at h1`. Simplify using `using h1`.

Rewrite `hc` using `[hc1, one_smul]`. Conclude with `hc`.
-/
theorem map_swap_volume (ι κ : Type) [Fintype ι] [Fintype κ] :
    (volume : Measure (ι → κ → ℝ)).map (fun f k i => f i k) = (volume : Measure (κ → ι → ℝ)) := by
  let s : (ι → κ → ℝ) ≃+ (κ → ι → ℝ) :=
    { toFun := fun f k i => f i k
      invFun := fun g i k => g k i
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hs : Continuous s := continuous_pi fun k => continuous_pi fun i =>
    (continuous_apply k).comp (continuous_apply i)
  have hs' : Continuous s.symm := continuous_pi fun i => continuous_pi fun k =>
    (continuous_apply i).comp (continuous_apply k)
  have h0 : (volume : Measure (κ → ℝ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  have h0' : (volume : Measure (ι → ℝ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  have hV : (volume : Measure (ι → κ → ℝ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  have hV' : (volume : Measure (κ → ι → ℝ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  have hH : ((volume : Measure (ι → κ → ℝ)).map s).IsAddHaarMeasure :=
    s.isAddHaarMeasure_map _ hs hs'
  have hc := Measure.isAddLeftInvariant_eq_smul ((volume : Measure (ι → κ → ℝ)).map s)
    (volume : Measure (κ → ι → ℝ))
  set c := Measure.addHaarScalarFactor ((volume : Measure (ι → κ → ℝ)).map s)
    (volume : Measure (κ → ι → ℝ)) with hcdef
  let B : Set (κ → ι → ℝ) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1
  let B' : Set (ι → κ → ℝ) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ =>
    measurableSet_Icc
  have hpre : s ⁻¹' B = B' := by
    ext f
    simp only [B, B', Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_comm
  have vB : (volume : Measure (κ → ι → ℝ)) B = 1 := by
    simp only [B]
    rw [volume_pi_pi]
    refine Finset.prod_eq_one fun _ _ => ?_
    rw [volume_pi_pi]
    refine Finset.prod_eq_one fun _ _ => ?_
    simp
  have vB' : (volume : Measure (ι → κ → ℝ)) B' = 1 := by
    simp only [B']
    rw [volume_pi_pi]
    refine Finset.prod_eq_one fun _ _ => ?_
    rw [volume_pi_pi]
    refine Finset.prod_eq_one fun _ _ => ?_
    simp
  have h1 : ((volume : Measure (ι → κ → ℝ)).map s) B = 1 := by
    rw [Measure.map_apply hs.measurable hB, hpre, vB']
  have hc1 : c = 1 := by
    rw [hc] at h1
    simp only [Measure.smul_apply, vB] at h1
    simpa using h1
  rw [hc1, one_smul] at hc
  exact hc

/- English proof (translation)
Establish `: SigmaFinite ((c : ℝ≥0∞) • ν)`. Rewrite using `[← ENNReal.smul_def]`. Use `infer_instance`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Simplify using `only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`.
-/
theorem pi_smul_const {ι α : Type} [Fintype ι] [MeasurableSpace α] (ν : Measure α) [SigmaFinite ν]
    (c : ℝ≥0) :
    Measure.pi (fun _ : ι => (c : ℝ≥0∞) • ν) =
      ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi fun _ : ι => ν := by
  have : SigmaFinite ((c : ℝ≥0∞) • ν) := by
    rw [← ENNReal.smul_def]; infer_instance
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

/- English proof (translation)
Establish `hsf : SigmaFinite (lam.map e)`. Rewrite using `[hlam, ← ENNReal.smul_def]`. Use `infer_instance`. Establish `h1 : (Measure.pi fun _ : ι => lam).map (fun y p => e (y p)) = Measure.pi fun _ : ι => lam.map e` using `Measure.pi_map_pi (fun _ => he.aemeasurable)`. Establish `hsw : Measurable (fun (f : ι → κ → ℝ) (w : κ) (p : ι) => f p w)` using `measurable_pi_iff.2 fun w => measurable_pi_iff.2 fun p => (measurable_pi_apply w).comp (measurable_pi_apply p)`.

Establish `hc : Measurable (fun (y : ι → A) (p : ι) => e (y p))` using `measurable_pi_iff.2 fun p => he.comp (measurable_pi_apply p)`. Establish `h2 : (fun (y : ι → A) (w : κ) (p : ι) => e (y p) w) = (fun (f : ι → κ → ℝ) (w : κ) (p : ι) => f p w) ∘ (fun (y : ι → A) (p : ι) => e (y p))` using `rfl`. Rewrite using `[h2, ← Measure.map_map hsw hc, h1, hlam, pi_smul_const, Measure.map_smul]`. Use `congr 1`. Conclude with `map_swap_volume ι κ`.
-/
theorem map_coord_pi {ι κ A : Type} [Fintype ι] [Fintype κ] [MeasurableSpace A]
    (lam : Measure A) [SigmaFinite lam] (e : A → κ → ℝ) (he : Measurable e) (c : ℝ≥0)
    (hlam : lam.map e = (c : ℝ≥0∞) • (volume : Measure (κ → ℝ))) :
    (Measure.pi fun _ : ι => lam).map (fun y w p => e (y p) w) =
      ((c : ℝ≥0∞) ^ Fintype.card ι) • (volume : Measure (κ → ι → ℝ)) := by
  have hsf : SigmaFinite (lam.map e) := by
    rw [hlam, ← ENNReal.smul_def]; infer_instance
  have h1 : (Measure.pi fun _ : ι => lam).map (fun y p => e (y p)) =
      Measure.pi fun _ : ι => lam.map e :=
    Measure.pi_map_pi (fun _ => he.aemeasurable)
  have hsw : Measurable (fun (f : ι → κ → ℝ) (w : κ) (p : ι) => f p w) :=
    measurable_pi_iff.2 fun w => measurable_pi_iff.2 fun p =>
      (measurable_pi_apply w).comp (measurable_pi_apply p)
  have hc : Measurable (fun (y : ι → A) (p : ι) => e (y p)) :=
    measurable_pi_iff.2 fun p => he.comp (measurable_pi_apply p)
  have h2 : (fun (y : ι → A) (w : κ) (p : ι) => e (y p) w) =
      (fun (f : ι → κ → ℝ) (w : κ) (p : ι) => f p w) ∘ (fun (y : ι → A) (p : ι) => e (y p)) := rfl
  rw [h2, ← Measure.map_map hsw hc, h1, hlam, pi_smul_const, Measure.map_smul]
  congr 1
  exact map_swap_volume ι κ

end GlobalTheory.CompanionTheory.SW.BB.InfPush

open GlobalTheory.CompanionTheory.SW.BB.InfPush in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M d b e he laminf hH hmap`. Establish `hloc` using `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1`. Take `⟨h1, h2, h3, h4, -⟩` from `hloc`. Use `haveI := h1`. Use `haveI := h2`.

Use `haveI := h3`. Use `haveI := h4`. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Take `⟨-, hemb, hcoord⟩` from `GlobalTheory.T.coordinate_homeomorph_rank_one_tuples F E σ hσ (Ainf F) d b laminf hH M`. Establish `hem : Measurable (fun x : Ainf F => (e x : InfinitePlace F → ℝ))` using `he.continuous.measurable`.

Establish `hΦ : Measurable (fun (y : Fin M × Fin d → Ainf F) (w : InfinitePlace F) (p : Fin M × Fin d) => e (y p) w)` using `measurable_pi_iff.2 fun w => measurable_pi_iff.2 fun p => (measurable_pi_apply w).comp (hem.comp (measurable_pi_apply p))`. Establish `hcomp : (fun (X : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) => xw e b X w) = (fun (y : Fin M × Fin d → Ainf F) (w : InfinitePlace F) (p : Fin M × Fin d) => e (y p) w) ∘ (fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => cv (Ainf F) b (X 0))` using `rfl`. Establish `hr : 0 ≤ (Real.sqrt |(discr F : ℝ)|)⁻¹` using `inv_nonneg.2 (Real.sqrt_nonneg _)`. Rewrite using `[hcomp, ← Measure.map_map hΦ hemb.measurable, hcoord, map_coord_pi laminf (fun x => e x) hem _ hmap, ENNReal.ofReal_pow hr]`. Simplify using `[Fintype.card_prod, ENNReal.ofReal]`.
-/
theorem GlobalTheory.CompanionTheory.SW.BB.infPush : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → laminf.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) → (coordW (Ainf F) b laminf 1 M).map (fun X w => xw e b X w) = ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (M * d)) • (volume : Measure (InfinitePlace F → Fin M × Fin d → ℝ)) := by
  intro F E _ _ _ _ _ σ hσ M d b e he laminf hH hmap
  have hloc := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  obtain ⟨h1, h2, h3, h4, -⟩ := hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨-, hemb, hcoord⟩ := GlobalTheory.T.coordinate_homeomorph_rank_one_tuples F E σ hσ (Ainf F) d b laminf hH M
  have hem : Measurable (fun x : Ainf F => (e x : InfinitePlace F → ℝ)) := he.continuous.measurable
  have hΦ : Measurable (fun (y : Fin M × Fin d → Ainf F) (w : InfinitePlace F) (p : Fin M × Fin d) => e (y p) w) :=
    measurable_pi_iff.2 fun w => measurable_pi_iff.2 fun p =>
      (measurable_pi_apply w).comp (hem.comp (measurable_pi_apply p))
  have hcomp : (fun (X : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) => xw e b X w) =
      (fun (y : Fin M × Fin d → Ainf F) (w : InfinitePlace F) (p : Fin M × Fin d) => e (y p) w) ∘
        (fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => cv (Ainf F) b (X 0)) := rfl
  have hr : 0 ≤ (Real.sqrt |(discr F : ℝ)|)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [hcomp, ← Measure.map_map hΦ hemb.measurable, hcoord,
    map_coord_pi laminf (fun x => e x) hem _ hmap, ENNReal.ofReal_pow hr]
  simp [Fintype.card_prod, ENNReal.ofReal]
