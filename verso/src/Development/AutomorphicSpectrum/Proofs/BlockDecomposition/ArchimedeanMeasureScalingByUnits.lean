import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianMeasureScalingTransform
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoordinateMeasureScalingTensor
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Dil

/- English proof (translation)
Use `Measure.pi_eq (μ := fun i => c i • μ i) fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, Measure.pi_pi]`. Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_finset_prod, Finset.prod_mul_distrib]`.
-/
theorem pi_smul_nnreal {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  classical
  refine Measure.pi_eq (μ := fun i => c i • μ i) fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_finset_prod,
    Finset.prod_mul_distrib]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ n M d b lam hlam e he t ht`. Take `⟨j1, j2, j3, j4, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)`. Use `haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩`. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Take `⟨hK, -, -⟩` from `GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam`.

Use `haveI := hK`. Establish `hfm : ∀ a, Measurable (fun y : Ainf F ⊗[F] E => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * y)` using `fun a => (continuous_const.mul continuous_id).measurable`. Establish `hrow : ∀ a, (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).map (fun (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) = (((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (d * M)) • Measure.pi fun _ : Fin M => GlobalTheory.CompanionThe …`. Introduce `a`. Take `⟨u, hu⟩` from `ht a`.

Establish `h` using `GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar F e he lam hlam (t a) (ht a)`. Rewrite `h` using `[← hu]`. Establish `hk` using `coordK_map_unit (Ainf F) σ hσ b lam u _ h`. Rewrite `hk` using `[hu]`. Establish `hk1` using `pi_map_scale (ι := Fin M) (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) _ (hfm a) _ hk`.

Simplify using `only [Fintype.card_fin, ← pow_mul] at hk1`. Conclude with `hk1`. Establish `hrm : ∀ a, Measurable (fun (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i)` using `fun a => measurable_pi_iff.2 fun i => (hfm a).comp (measurable_pi_apply i)`. Use `haveI : ∀ a, SigmaFinite ((Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).map (fun (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i)) := fun a => by`. Rewrite using `[hrow a]`.

Use `infer_instance`. Establish `hmap` using `Measure.pi_map_pi (μ := fun _ : Fin n => Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) (f := fun a (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) (fun a => (hrm a).aemeasurable)`. Unfold `GlobalTheory.CompanionTheory.SW.coordW`. Use `hmap.trans ?_` and prove the remaining obligations. Simplify using `only [hrow]`.

Conclude with `pi_smul_nnreal _ _`.
-/
theorem coordW_map_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ), IsHomeomorph e → ∀ t : Fin n → Ainf F, (∀ a, IsUnit (t a)) → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (fun X a i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * X a i) = (∏ a, ((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  intro F E _ _ _ _ _ σ hσ n M d b lam hlam e he t ht
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  have hfm : ∀ a, Measurable (fun y : Ainf F ⊗[F] E => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * y) :=
    fun a => (continuous_const.mul continuous_id).measurable
  have hrow : ∀ a, (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).map
      (fun (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) =
      (((∏ w, ‖e (t a) w‖₊)⁻¹) ^ (d * M)) • Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam := by
    intro a
    obtain ⟨u, hu⟩ := ht a
    have h := GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar F e he lam hlam (t a) (ht a)
    rw [← hu] at h
    have hk := coordK_map_unit (Ainf F) σ hσ b lam u _ h
    rw [hu] at hk
    have hk1 := pi_map_scale (ι := Fin M) (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) _ (hfm a) _ hk
    simp only [Fintype.card_fin, ← pow_mul] at hk1
    exact hk1
  have hrm : ∀ a, Measurable (fun (x : Fin M → Ainf F ⊗[F] E) i =>
      algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) := fun a =>
    measurable_pi_iff.2 fun i => (hfm a).comp (measurable_pi_apply i)
  haveI : ∀ a, SigmaFinite ((Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).map
      (fun (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i)) := fun a => by
    rw [hrow a]; infer_instance
  have hmap := Measure.pi_map_pi (μ := fun _ : Fin n => Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam)
    (f := fun a (x : Fin M → Ainf F ⊗[F] E) i => algebraMap (Ainf F) (Ainf F ⊗[F] E) (t a) * x i) (fun a => (hrm a).aemeasurable)
  unfold GlobalTheory.CompanionTheory.SW.coordW
  refine hmap.trans ?_
  simp only [hrow]
  exact pi_smul_nnreal _ _

end GlobalTheory.CompanionTheory.SW.Dil
