import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureTensorDecompositionLocal
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.FourierPlane

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def ft2 (ψ : AddChar F Circle) (φ : (Fin 2 → F) → ℂ) (ξ : Fin 2 → F) : ℂ :=
  ∫ y, φ y * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ

/- English proof (translation)
The claim follows from `((measurePreserving_finTwoArrow (selfDualMeasure ψ)).symm.integral_comp' f).symm`.
-/
theorem integral_plane_measure_eq_prod (ψ : AddChar F Circle) (f : (Fin 2 → F) → ℂ) :
    ∫ y, f y ∂LFS.vol2 ψ =
      ∫ p : F × F, f ![p.1, p.2] ∂(selfDualMeasure ψ).prod (selfDualMeasure ψ) :=
  ((measurePreserving_finTwoArrow (selfDualMeasure ψ)).symm.integral_comp' f).symm

/- English proof (translation)
Establish `hT` using `localFourier_mem_schwartzBruhat (selfDualMeasure ψ) hψ hψ1 hf`. Establish `hI` using `integrable_mul_char_of_mem_schwartzBruhat (selfDualMeasure ψ) hψ hT (-z)`. Establish `e : (fun u => localFourier (selfDualMeasure ψ) ψ f (-u) * (ψ (u * z) : ℂ)) = fun u => (fun v => localFourier (selfDualMeasure ψ) ψ f v * (ψ (v * (-z)) : ℂ)) (-u)`. Use function extensionality and compare the values at `u`. Simplify using `only [neg_mul_neg]`.

Rewrite using `[e]`. Use `⟨hI.comp_neg, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_neg_eq_self (fun v => localFourier (selfDualMeasure ψ) ψ f v * (ψ (v * (-z)) : ℂ))]`. Establish `h` using `localFourier_localFourier_selfDual hψ hψ1 hf (-z)`. Rewrite `h` using `[neg_neg]`.

Conclude with `h`.
-/
theorem inv_one {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {f : F → ℂ}
    (hf : f ∈ schwartzBruhat F) (z : F) :
    Integrable (fun u => localFourier (selfDualMeasure ψ) ψ f (-u) * (ψ (u * z) : ℂ)) (selfDualMeasure ψ) ∧
      ∫ u, localFourier (selfDualMeasure ψ) ψ f (-u) * (ψ (u * z) : ℂ) ∂selfDualMeasure ψ = f z := by
  have hT := localFourier_mem_schwartzBruhat (selfDualMeasure ψ) hψ hψ1 hf
  have hI := integrable_mul_char_of_mem_schwartzBruhat (selfDualMeasure ψ) hψ hT (-z)
  have e : (fun u => localFourier (selfDualMeasure ψ) ψ f (-u) * (ψ (u * z) : ℂ)) =
      fun u => (fun v => localFourier (selfDualMeasure ψ) ψ f v * (ψ (v * (-z)) : ℂ)) (-u) := by
    funext u
    simp only [neg_mul_neg]
  rw [e]
  refine ⟨hI.comp_neg, ?_⟩
  rw [integral_neg_eq_self (fun v => localFourier (selfDualMeasure ψ) ψ f v * (ψ (v * (-z)) : ℂ))]
  have h := localFourier_localFourier_selfDual hψ hψ1 hf (-z)
  rw [neg_neg] at h
  exact h

/- English proof (translation)
Establish `e : ∀ p : F × F, (∑ i, f i p.1 * g i p.2) * (ψ (-(ξ 0 * p.1 + ξ 1 * p.2)) : ℂ) = ∑ i, (f i p.1 * (ψ (p.1 * -ξ 0) : ℂ)) * (g i p.2 * (ψ (p.2 * -ξ 1) : ℂ))`. Introduce `p`. Establish `hc : (ψ (-(ξ 0 * p.1 + ξ 1 * p.2)) : ℂ) = (ψ (p.1 * -ξ 0) : ℂ) * (ψ (p.2 * -ξ 1) : ℂ)`. Rewrite using `[← Circle.coe_mul, ← AddChar.map_add_eq_mul]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Unfold `ft2`. Rewrite using `[integral_plane_measure_eq_prod]`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, e]`. Rewrite using `[integral_finsetSum _ fun i _ => Integrable.mul_prod (integrable_mul_char_of_mem_schwartzBruhat _ hψ (hf i) (-ξ 0)) (integrable_mul_char_of_mem_schwartzBruhat _ hψ (hg i) (-ξ 1))]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `integral_prod_mul (fun x => f i x * (ψ (x * -ξ 0) : ℂ)) (fun x => g i x * (ψ (x * -ξ 1) : ℂ))`.
-/
theorem fourier_plane_product_sum {ψ : AddChar F Circle} (hψ : Continuous ψ) {n : ℕ} {f g : Fin n → F → ℂ}
    (hf : ∀ i, f i ∈ schwartzBruhat F) (hg : ∀ i, g i ∈ schwartzBruhat F) (ξ : Fin 2 → F) :
    ft2 ψ (fun y => ∑ i, f i (y 0) * g i (y 1)) ξ =
      ∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1) := by
  have e : ∀ p : F × F, (∑ i, f i p.1 * g i p.2) * (ψ (-(ξ 0 * p.1 + ξ 1 * p.2)) : ℂ) =
      ∑ i, (f i p.1 * (ψ (p.1 * -ξ 0) : ℂ)) * (g i p.2 * (ψ (p.2 * -ξ 1) : ℂ)) := by
    intro p
    have hc : (ψ (-(ξ 0 * p.1 + ξ 1 * p.2)) : ℂ) = (ψ (p.1 * -ξ 0) : ℂ) * (ψ (p.2 * -ξ 1) : ℂ) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [hc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold ft2
  rw [integral_plane_measure_eq_prod]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e]
  rw [integral_finsetSum _ fun i _ => Integrable.mul_prod
    (integrable_mul_char_of_mem_schwartzBruhat _ hψ (hf i) (-ξ 0))
    (integrable_mul_char_of_mem_schwartzBruhat _ hψ (hg i) (-ξ 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_prod_mul (fun x => f i x * (ψ (x * -ξ 0) : ℂ)) (fun x => g i x * (ψ (x * -ξ 1) : ℂ))

/- English proof (translation)
Establish `e : ∀ p : F × F, (∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-p.1) * localFourier (selfDualMeasure ψ) ψ (g i) (-p.2)) * (ψ (p.1 * z 0 + p.2 * z 1) : ℂ) = ∑ i, (localFourier (selfDualMeasure ψ) ψ (f i) (-p.1) * (ψ (p.1 * z 0) : ℂ)) * (localFourier (selfDualMeasure ψ) ψ (g i) ( …`. Introduce `p`. Rewrite using `[AddChar.map_add_eq_mul, Circle.coe_mul, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[integral_plane_measure_eq_prod]`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, e]`. Rewrite using `[integral_finsetSum _ fun i _ => Integrable.mul_prod (inv_one hψ hψ1 (hf i) (z 0)).1 (inv_one hψ hψ1 (hg i) (z 1)).1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[integral_prod_mul (fun u => localFourier (selfDualMeasure ψ) ψ (f i) (-u) * (ψ (u * z 0) : ℂ)) (fun u => localFourier (selfDualMeasure ψ) ψ (g i) (-u) * (ψ (u * z 1) : ℂ)), (inv_one hψ hψ1 (hf i) (z 0)).2, (inv_one hψ hψ1 (hg i) (z 1)).2]`.
-/
theorem inv_sum {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {n : ℕ} {f g : Fin n → F → ℂ}
    (hf : ∀ i, f i ∈ schwartzBruhat F) (hg : ∀ i, g i ∈ schwartzBruhat F) (z : Fin 2 → F) :
    ∫ ξ : Fin 2 → F, (∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1)) * (ψ (ξ 0 * z 0 + ξ 1 * z 1) : ℂ) ∂LFS.vol2 ψ =
      ∑ i, f i (z 0) * g i (z 1) := by
  have e : ∀ p : F × F, (∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-p.1) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-p.2)) * (ψ (p.1 * z 0 + p.2 * z 1) : ℂ) =
      ∑ i, (localFourier (selfDualMeasure ψ) ψ (f i) (-p.1) * (ψ (p.1 * z 0) : ℂ)) *
        (localFourier (selfDualMeasure ψ) ψ (g i) (-p.2) * (ψ (p.2 * z 1) : ℂ)) := by
    intro p
    rw [AddChar.map_add_eq_mul, Circle.coe_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_plane_measure_eq_prod]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e]
  rw [integral_finsetSum _ fun i _ => Integrable.mul_prod
    (inv_one hψ hψ1 (hf i) (z 0)).1 (inv_one hψ hψ1 (hg i) (z 1)).1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_prod_mul (fun u => localFourier (selfDualMeasure ψ) ψ (f i) (-u) * (ψ (u * z 0) : ℂ))
    (fun u => localFourier (selfDualMeasure ψ) ψ (g i) (-u) * (ψ (u * z 1) : ℂ)),
    (inv_one hψ hψ1 (hf i) (z 0)).2, (inv_one hψ hψ1 (hg i) (z 1)).2]

omit [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Use `GodementSectionLocal.mem_schwartzBruhat2.2 ⟨(ha.1.comp_continuous (continuous_apply 0)).mul (hb.1.comp_continuous (continuous_apply 1)), ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro ((ha.2.isCompact.prod hb.2.isCompact).image (Homeomorph.finTwoArrow (X := F)).symm.continuous) fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `hx ⟨(x 0, x 1), ⟨subset_tsupport _ fun h => hne ?_, subset_tsupport _ fun h => hne ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `[h]`.

Simplify using `[h]`. Apply the tactic sequence `ext j fin_cases j <;> simp`.
-/
theorem pure_mem {a b : F → ℂ} (ha : a ∈ schwartzBruhat F) (hb : b ∈ schwartzBruhat F) :
    (fun x : Fin 2 → F => a (x 0) * b (x 1)) ∈ GodementSectionLocal.schwartzBruhat2 F := by
  refine GodementSectionLocal.mem_schwartzBruhat2.2
    ⟨(ha.1.comp_continuous (continuous_apply 0)).mul (hb.1.comp_continuous (continuous_apply 1)), ?_⟩
  refine HasCompactSupport.intro
    ((ha.2.isCompact.prod hb.2.isCompact).image (Homeomorph.finTwoArrow (X := F)).symm.continuous) fun x hx => ?_
  by_contra hne
  refine hx ⟨(x 0, x 1), ⟨subset_tsupport _ fun h => hne ?_, subset_tsupport _ fun h => hne ?_⟩, ?_⟩
  · simp [h]
  · simp [h]
  · ext j
    fin_cases j <;> simp

omit [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨ha.1.comp_continuous continuous_neg, ha.2.comp_homeomorph (Homeomorph.neg F)⟩`.
-/
theorem reflect_mem {a : F → ℂ} (ha : a ∈ schwartzBruhat F) : (fun x => a (-x)) ∈ schwartzBruhat F :=
  ⟨ha.1.comp_continuous continuous_neg, ha.2.comp_homeomorph (Homeomorph.neg F)⟩

omit [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Establish `hl : IsLocallyConstant fun p : F × F => φ ((Homeomorph.finTwoArrow (X` using `F)).symm p) := hφ.1.comp_continuous (Homeomorph.finTwoArrow (X := F)).symm.continuous`. Establish `hc : HasCompactSupport fun p : F × F => φ ((Homeomorph.finTwoArrow (X` using `F)).symm p) := hφ.2.comp_homeomorph (Homeomorph.finTwoArrow (X := F)).symm`. Take `⟨n, f, g, hf, hg, hfg⟩` from `GlobalTheory.CompanionTheory.PureTensor.exists_pure_sum hl hc`. Use `⟨n, f, g, hf, hg, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`.

Rewrite using `[← hfg]`. Use `congr 1`. Use extensionality with `j`. Apply the tactic sequence `fin_cases j <;> rfl`.
-/
theorem exists_pure {φ : (Fin 2 → F) → ℂ} (hφ : φ ∈ GodementSectionLocal.schwartzBruhat2 F) :
    ∃ (n : ℕ) (f g : Fin n → F → ℂ), (∀ i, f i ∈ schwartzBruhat F) ∧ (∀ i, g i ∈ schwartzBruhat F) ∧
      φ = fun y => ∑ i, f i (y 0) * g i (y 1) := by
  have hl : IsLocallyConstant fun p : F × F => φ ((Homeomorph.finTwoArrow (X := F)).symm p) :=
    hφ.1.comp_continuous (Homeomorph.finTwoArrow (X := F)).symm.continuous
  have hc : HasCompactSupport fun p : F × F => φ ((Homeomorph.finTwoArrow (X := F)).symm p) :=
    hφ.2.comp_homeomorph (Homeomorph.finTwoArrow (X := F)).symm
  obtain ⟨n, f, g, hf, hg, hfg⟩ := GlobalTheory.CompanionTheory.PureTensor.exists_pure_sum hl hc
  refine ⟨n, f, g, hf, hg, ?_⟩
  funext y
  rw [← hfg]
  congr 1
  ext j
  fin_cases j <;> rfl

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ hstd φ hφ`. Establish `hψ : Continuous ψ` using `hstd.1`. Establish `hψ1 : ψ ≠ 1` using `hstd.2.1`. Take `⟨n, f, g, hf, hg, rfl⟩` from `exists_pure hφ`. Establish `e : (fun ξ : Fin 2 → F => ∫ y, (∑ i, f i (y 0) * g i (y 1)) * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ) = fun ξ => ∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) * localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1)`.

Use function extensionality and compare the values at `fun ξ => fourier_plane_product_sum hψ hf hg ξ`. Use `⟨?_, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Establish `: (fun ξ : Fin 2 → F => ∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) * localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1)) = ∑ i, fun ξ : Fin 2 → F => localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) * localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1)`. Use function extensionality and compare the values at `ξ`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => pure_mem (reflect_mem (localFourier_mem_schwartzBruhat _ hψ hψ1 (hf i))) (reflect_mem (localFourier_mem_schwartzBruhat _ hψ hψ1 (hg i)))`. Use `inv_sum hψ hψ1 hf hg z` as an intermediate fact. Simplify using `only [← congrFun e] at this`.

Conclude with `this`.
-/
theorem fourier_inversion_plane_explicit : ForS fun F _ _ _ _ _ _ ψ => ∀ φ : (Fin 2 → F) → ℂ,
    φ ∈ GodementSectionLocal.schwartzBruhat2 F →
    (fun ξ : Fin 2 → F => ∫ y, φ y * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ) ∈
        GodementSectionLocal.schwartzBruhat2 F ∧
      ∀ z : Fin 2 → F, ∫ ξ : Fin 2 → F, (∫ y, φ y * (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ) *
        (ψ (ξ 0 * z 0 + ξ 1 * z 1) : ℂ) ∂LFS.vol2 ψ = φ z := by
  intro F _ _ _ _ _ _ ψ hstd φ hφ
  have hψ : Continuous ψ := hstd.1
  have hψ1 : ψ ≠ 1 := hstd.2.1
  obtain ⟨n, f, g, hf, hg, rfl⟩ := exists_pure hφ
  have e : (fun ξ : Fin 2 → F => ∫ y, (∑ i, f i (y 0) * g i (y 1)) *
      (ψ (-(ξ 0 * y 0 + ξ 1 * y 1)) : ℂ) ∂LFS.vol2 ψ) =
      fun ξ => ∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1) :=
    funext fun ξ => fourier_plane_product_sum hψ hf hg ξ
  refine ⟨?_, fun z => ?_⟩
  · rw [e]
    have : (fun ξ : Fin 2 → F => ∑ i, localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
        localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1)) =
        ∑ i, fun ξ : Fin 2 → F => localFourier (selfDualMeasure ψ) ψ (f i) (-ξ 0) *
          localFourier (selfDualMeasure ψ) ψ (g i) (-ξ 1) := by
      funext ξ
      simp
    rw [this]
    exact Submodule.sum_mem _ fun i _ => pure_mem
      (reflect_mem (localFourier_mem_schwartzBruhat _ hψ hψ1 (hf i)))
      (reflect_mem (localFourier_mem_schwartzBruhat _ hψ hψ1 (hg i)))
  · have := inv_sum hψ hψ1 hf hg z
    simp only [← congrFun e] at this
    exact this

end GlobalTheory.CompanionTheory.FourierPlane
