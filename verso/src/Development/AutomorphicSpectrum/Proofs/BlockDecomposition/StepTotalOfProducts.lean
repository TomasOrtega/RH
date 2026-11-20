import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuous

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

/- English proof (translation)
Use `continuous_of_dominated (bound := fun y => B * ‖g y‖) (fun x => ?_) (fun x => ae_of_all _ fun y => ?_) (hg.norm.const_mul B) (ae_of_all _ fun y => ?_)` and prove the remaining obligations. Establish `h1 : Continuous (f x)` using `hf.comp (continuous_const.prodMk continuous_id)`. Conclude with `h1.aestronglyMeasurable.mul hg.1`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hB x y) (norm_nonneg _)`.

Establish `h1 : Continuous fun x => f x y` using `hf.comp (continuous_id.prodMk continuous_const)`. Conclude with `h1.mul continuous_const`.
-/
theorem continuous_integral_mul_of_bdd {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {ν : Measure Y}
    {f : X → Y → ℂ} (hf : Continuous fun w : X × Y => f w.1 w.2) {B : ℝ} (hB : ∀ x y, ‖f x y‖ ≤ B)
    {g : Y → ℂ} (hg : Integrable g ν) : Continuous fun x => ∫ y, f x y * g y ∂ν := by
  refine continuous_of_dominated (bound := fun y => B * ‖g y‖) (fun x => ?_)
    (fun x => ae_of_all _ fun y => ?_) (hg.norm.const_mul B) (ae_of_all _ fun y => ?_)
  · have h1 : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
    exact h1.aestronglyMeasurable.mul hg.1
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB x y) (norm_nonneg _)
  · have h1 : Continuous fun x => f x y := hf.comp (continuous_id.prodMk continuous_const)
    exact h1.mul continuous_const

/- English proof (translation)
Establish `hI : Integrable (fun w : X × Y => F w * (a w.1 * c w.2)) (μ.prod ν)` using `(ha.mul_prod hc).bdd_mul hF (ae_of_all _ hB)`. Rewrite using `[integral_prod _ hI]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Use `show (∫ z, F (x, z) * c z ∂ν) * a x = ∫ z, F (x, z) * (a x * c z) ∂ν`. Rewrite using `[← integral_mul_const]`.

Conclude with `integral_congr_ae (ae_of_all _ fun z => by ring)`.
-/
theorem integral_integral_mul_of_bdd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {F : X × Y → ℂ} (hF : AEStronglyMeasurable F (μ.prod ν)) {B : ℝ} (hB : ∀ w, ‖F w‖ ≤ B)
    {a : X → ℂ} {c : Y → ℂ} (ha : Integrable a μ) (hc : Integrable c ν) :
    ∫ x, (∫ z, F (x, z) * c z ∂ν) * a x ∂μ = ∫ w, F w * (a w.1 * c w.2) ∂(μ.prod ν) := by
  have hI : Integrable (fun w : X × Y => F w * (a w.1 * c w.2)) (μ.prod ν) :=
    (ha.mul_prod hc).bdd_mul hF (ae_of_all _ hB)
  rw [integral_prod _ hI]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show (∫ z, F (x, z) * c z ∂ν) * a x = ∫ z, F (x, z) * (a x * c z) ∂ν
  rw [← integral_mul_const]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

variable {D : D7} {r s p : ℕ}

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `[rowT, rowJ]`.
-/
theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  refine Matrix.ext fun i j => ?_
  simp [rowT, rowJ]

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `[rowB, rowJ]`.
-/
theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  refine Matrix.ext fun i j => ?_
  simp [rowB, rowJ]

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Proceed by induction on `i using Fin.addCases with`. Consider the case `left a => simp [rowT, rowJ]`. Consider the case `right b => simp [rowB, rowJ]`.
-/
theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  refine Matrix.ext fun i j => ?_
  induction i using Fin.addCases with
  | left a => simp [rowT, rowJ]
  | right b => simp [rowB, rowJ]

/- English proof (translation)
The claim follows from `continuous_matrix fun _ _ => continuous_id.matrix_elem _ _`.
-/
theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_matrix fun _ _ => continuous_id.matrix_elem _ _

/- English proof (translation)
The claim follows from `continuous_matrix fun _ _ => continuous_id.matrix_elem _ _`.
-/
theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_matrix fun _ _ => continuous_id.matrix_elem _ _

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Proceed by induction on `i using Fin.addCases with`. Consider the case `left a`. Simplify using `only [rowJ, Fin.addCases_left]`. Conclude with `continuous_fst.matrix_elem a j`.

Consider the case `right b`. Simplify using `only [rowJ, Fin.addCases_right]`. Conclude with `continuous_snd.matrix_elem b j`.
-/
theorem continuous_rowJ : Continuous fun w : Mx D r p × Mx D s p => rowJ w.1 w.2 := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.addCases with
  | left a =>
    simp only [rowJ, Fin.addCases_left]
    exact continuous_fst.matrix_elem a j
  | right b =>
    simp only [rowJ, Fin.addCases_right]
    exact continuous_snd.matrix_elem b j

/- English proof (translation)
The claim follows from `hΩ.cont.comp (continuous_const.prodMk continuous_id)`.
-/
theorem continuous_th_one {ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {b₀ : HermE D ρ}
    {μ : Measure (Mx D ρ p)} {Ω : G D p → Mx D ρ p → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω) : Continuous (Ω 1) :=
  hΩ.cont.comp (continuous_const.prodMk continuous_id)

/- English proof (translation)
The claim follows from `(Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf`.
-/
theorem integrable_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} (hf : Integrable f μ) :
    Integrable (fun x => conj (f x)) μ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf

/- English proof (translation)
Introduce `hP hM D r s p μr Fr μs Fs μ F hr hs h ψ hψ χr χs θ hθ br bs b hb Tr Ts u hu hbd horth`. Take `⟨B, hB⟩` from `hbd`. Establish `hμ` using `hM D r s p μr Fr μs Fs μ F hr hs h`. Substitute `hμ` using the available equality. Use `haveI : SecondCountableTopology (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.2.1`.

Use `haveI : SecondCountableTopology (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.2.1`. Use `haveI : SecondCountableTopology (Mx D (r + s) p) := (GlobalTheory.MixModel.lattice_Mx D (r + s) p).2.2.1`. Use `haveI : FirstCountableTopology (Mx D r p) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _`. Use `haveI : IsTopologicalAddGroup (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).1`. Use `haveI : IsTopologicalAddGroup (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).1`.

Use `haveI : LocallyCompactSpace (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.1`. Use `haveI : LocallyCompactSpace (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.1`. Use `haveI : BorelSpace (Mx D r p) := ⟨rfl⟩`. Use `haveI : BorelSpace (Mx D s p) := ⟨rfl⟩`. Use `haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩`.

Use `haveI := hr.1`. Use `haveI := hs.1`. Establish `hcJ` using `continuous_rowJ (D := D) (r := r) (s := s) (p := p)`. Establish `hcF : Continuous fun w : Mx D r p × Mx D s p => u (rowJ w.1 w.2)` using `hu.comp hcJ`. Establish `key : ∀ Ωr Ωs, IsTh ψ χr θ br μr Ωr → IsTh ψ χs θ bs μs Ωs → ∫ x, (∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs) * conj (Ωr 1 x) ∂μr = 0`.

Introduce `Ωr Ωs hΩr hΩs`. Establish `hT` using `hP D r s p μr Fr μs Fs hr hs ψ hψ χr χs θ hθ br bs b hb Ωr Ωs hΩr hΩs`. Establish `h0` using `horth _ hT`. Establish `hm : Continuous fun y : Mx D (r + s) p => u y * conj (Ωr 1 (rowT y) * Ωs 1 (rowB y))` using `hu.mul (Complex.continuous_conj.comp (((continuous_th_one hΩr).comp continuous_rowT).mul ((continuous_th_one hΩs).comp continuous_rowB)))`. Rewrite `h0` using `[integral_map hcJ.aemeasurable hm.aestronglyMeasurable]`.

Rewrite using `[integral_integral_mul_of_bdd (F := fun w : Mx D r p × Mx D s p => u (rowJ w.1 w.2)) hcF.aestronglyMeasurable (fun w => hB _) (integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hr (hΩr.mem 1))) (integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.i …`. Simplify `h0` using `only [rowT_rowJ, rowB_rowJ, map_mul]`. Establish `hv : ∀ Ωs, IsTh ψ χs θ bs μs Ωs → ∀ x, ∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs = 0`. Introduce `Ωs hΩs`. Establish `hi : Integrable (fun z => conj (Ωs 1 z)) μs` using `integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hs (hΩs.mem 1))`.

Use `congrFun (Tr (fun x => ∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs) ?_ ?_ ?_)` and prove the remaining obligations. Conclude with `continuous_integral_mul_of_bdd (f := fun x z => u (rowJ x z)) hcF (fun _ _ => hB _) hi`. Use `⟨B * ∫ z, ‖conj (Ωs 1 z)‖ ∂μs, fun x => ?_⟩` and prove the remaining obligations. Use `(norm_integral_le_integral_norm _).trans ?_` and prove the remaining obligations. Rewrite using `[← integral_const_mul]`.

Use `integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hi.norm.const_mul B) (ae_of_all _ fun z => ?_)` and prove the remaining obligations. Use `show ‖u (rowJ x z) * conj (Ωs 1 z)‖ ≤ B * ‖conj (Ωs 1 z)‖`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)`. Conclude with `fun Ωr hΩr => key Ωr Ωs hΩr hΩs`.

Establish `hz : ∀ x, (fun z => u (rowJ x z)) = 0` using `fun x => Ts (fun z => u (rowJ x z)) (hu.comp (hcJ.comp (continuous_const.prodMk continuous_id))) ⟨B, fun _ => hB _⟩ fun Ωs hΩs => hv Ωs hΩs x`. Use function extensionality and compare the values at `y`. Rewrite using `[← rowJ_rowT_rowB y]`. Conclude with `congrFun (hz (rowT y)) (rowB y)`.
-/
theorem stepTotal : ProdTh → ProdMeas → StepTotal := by
  intro hP hM D r s p μr Fr μs Fs μ F hr hs h ψ hψ χr χs θ hθ br bs b hb Tr Ts u hu hbd horth
  obtain ⟨B, hB⟩ := hbd
  have hμ := hM D r s p μr Fr μs Fs μ F hr hs h
  subst hμ
  haveI : SecondCountableTopology (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.2.1
  haveI : SecondCountableTopology (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.2.1
  haveI : SecondCountableTopology (Mx D (r + s) p) := (GlobalTheory.MixModel.lattice_Mx D (r + s) p).2.2.1
  haveI : FirstCountableTopology (Mx D r p) :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  haveI : IsTopologicalAddGroup (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).1
  haveI : IsTopologicalAddGroup (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).1
  haveI : LocallyCompactSpace (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.1
  haveI : LocallyCompactSpace (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.1
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI := hr.1
  haveI := hs.1
  have hcJ := continuous_rowJ (D := D) (r := r) (s := s) (p := p)
  have hcF : Continuous fun w : Mx D r p × Mx D s p => u (rowJ w.1 w.2) := hu.comp hcJ
  have key : ∀ Ωr Ωs, IsTh ψ χr θ br μr Ωr → IsTh ψ χs θ bs μs Ωs →
      ∫ x, (∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs) * conj (Ωr 1 x) ∂μr = 0 := by
    intro Ωr Ωs hΩr hΩs
    have hT := hP D r s p μr Fr μs Fs hr hs ψ hψ χr χs θ hθ br bs b hb Ωr Ωs hΩr hΩs
    have h0 := horth _ hT
    have hm : Continuous fun y : Mx D (r + s) p => u y * conj (Ωr 1 (rowT y) * Ωs 1 (rowB y)) :=
      hu.mul (Complex.continuous_conj.comp (((continuous_th_one hΩr).comp continuous_rowT).mul
        ((continuous_th_one hΩs).comp continuous_rowB)))
    rw [integral_map hcJ.aemeasurable hm.aestronglyMeasurable] at h0
    rw [integral_integral_mul_of_bdd (F := fun w : Mx D r p × Mx D s p => u (rowJ w.1 w.2))
      hcF.aestronglyMeasurable (fun w => hB _)
      (integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hr (hΩr.mem 1)))
      (integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hs (hΩs.mem 1)))]
    simpa only [rowT_rowJ, rowB_rowJ, map_mul] using h0
  have hv : ∀ Ωs, IsTh ψ χs θ bs μs Ωs → ∀ x, ∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs = 0 := by
    intro Ωs hΩs
    have hi : Integrable (fun z => conj (Ωs 1 z)) μs :=
      integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hs (hΩs.mem 1))
    refine congrFun (Tr (fun x => ∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs) ?_ ?_ ?_)
    · exact continuous_integral_mul_of_bdd (f := fun x z => u (rowJ x z)) hcF (fun _ _ => hB _) hi
    · refine ⟨B * ∫ z, ‖conj (Ωs 1 z)‖ ∂μs, fun x => ?_⟩
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hi.norm.const_mul B) (ae_of_all _ fun z => ?_)
      show ‖u (rowJ x z) * conj (Ωs 1 z)‖ ≤ B * ‖conj (Ωs 1 z)‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    · exact fun Ωr hΩr => key Ωr Ωs hΩr hΩs
  have hz : ∀ x, (fun z => u (rowJ x z)) = 0 := fun x =>
    Ts (fun z => u (rowJ x z)) (hu.comp (hcJ.comp (continuous_const.prodMk continuous_id))) ⟨B, fun _ => hB _⟩
      fun Ωs hΩs => hv Ωs hΩs x
  funext y
  rw [← rowJ_rowT_rowB y]
  exact congrFun (hz (rowT y)) (rowB y)

end GlobalTheory.CompanionTheory.ThTot

end
