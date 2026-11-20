import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CorePInvInUJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntMuCD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def rmulPR (G : Matrix (Fin n) (Fin n) ℂ) (A : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) * G

def polarPR {ε : Fin n → Bool} (kz : KG ε × (PCoord ε → ℂ)) : Fin n → Fin n → ℂ := polarM kz

/- English proof (translation)
Unfold `rmulPR`. Conclude with `(continuous_id.matrix_mul continuous_const : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A * G)`.
-/
theorem continuous_rmulPR (G : Matrix (Fin n) (Fin n) ℂ) : Continuous (rmulPR G) := by
  unfold rmulPR
  exact (continuous_id.matrix_mul continuous_const :
    Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A * G)

/- English proof (translation)
Establish `h : Continuous (polarPR (ε` using `ε)) := polarM_continuous ε`. Conclude with `h.measurable`.
-/
theorem measurable_polarPR (ε : Fin n → Bool) : Measurable (polarPR (ε := ε)) := by
  have h : Continuous (polarPR (ε := ε)) := polarM_continuous ε
  exact h.measurable

/- English proof (translation)
Establish `hE : inUJ ε (NormedSpace.exp (pmat z))` using `exp_pmat_inUJ z`. Establish `hEG : inUJ ε (NormedSpace.exp (pmat z) * G)`. Unfold `inUJ at hE hG ⊢`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Jm ε := by rw [hE, hG]`. Take `⟨⟨k', w⟩, hkw⟩` from `polarM_surj _ hEG`. Establish `hw : actR G z = w`. Use function extensionality and compare the values at `ab`.

Establish `h1 : plog (NormedSpace.exp (pmat z) * G) = pmat w`. Rewrite using `[← hkw, plog_polarM]`. Simplify using `only [actR, h1, pmat, dif_pos ab.2]`. Use `⟨k', fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[hw]`.

Simplify using `only [rmulPR, polarPR, polarM] at hkw ⊢`. Establish `hm : toMK (k * k') = toMK k * toMK k'` using `rfl`. Use `show toMK k * NormedSpace.exp (pmat z) * G = _`. Rewrite using `[Matrix.mul_assoc, ← hkw, hm, Matrix.mul_assoc]`.
-/
theorem rmulPR_polarPR {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ} (hG : inUJ ε G)
    (z : PCoord ε → ℂ) : ∃ k' : KG ε, ∀ k : KG ε,
      rmulPR G (polarPR (k, z)) = polarPR (k * k', actR G z) := by
  have hE : inUJ ε (NormedSpace.exp (pmat z)) := exp_pmat_inUJ z
  have hEG : inUJ ε (NormedSpace.exp (pmat z) * G) := by
    unfold inUJ at hE hG ⊢
    rw [Matrix.conjTranspose_mul]
    calc Gᴴ * (NormedSpace.exp (pmat z))ᴴ * Jm ε * (NormedSpace.exp (pmat z) * G)
        = Gᴴ * ((NormedSpace.exp (pmat z))ᴴ * Jm ε * NormedSpace.exp (pmat z)) * G := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hE, hG]
  obtain ⟨⟨k', w⟩, hkw⟩ := polarM_surj _ hEG
  have hw : actR G z = w := by
    funext ab
    have h1 : plog (NormedSpace.exp (pmat z) * G) = pmat w := by
      rw [← hkw, plog_polarM]
    simp only [actR, h1, pmat, dif_pos ab.2]
  refine ⟨k', fun k => ?_⟩
  rw [hw]
  simp only [rmulPR, polarPR, polarM] at hkw ⊢
  have hm : toMK (k * k') = toMK k * toMK k' := rfl
  show toMK k * NormedSpace.exp (pmat z) * G = _
  rw [Matrix.mul_assoc, ← hkw, hm, Matrix.mul_assoc]

/- English proof (translation)
Establish `hP : Measurable (polarPR (ε` using `ε)) := measurable_polarPR ε`. Establish `hR : Measurable (rmulPR G)` using `(continuous_rmulPR G).measurable`. Establish `hA : Measurable (actR (ε` using `ε) G) := (JacB.actR_continuous hG).measurable`. Establish `hc` using `coreP hG`. Establish `key : ∀ S : Set (Fin n → Fin n → ℂ), MeasurableSet S → muPolarMat ε S = ∫⁻ z, dk ε {k | polarPR (k, z) ∈ S} ∂(volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z))`.

Introduce `S hS`. Use `show (Measure.map (polarPR (ε := ε)) ((dk ε).prod (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)))) S = _`. Rewrite using `[Measure.map_apply hP hS, Measure.prod_apply_symm (hP hS)]`. Both sides reduce to the same expression. Use extensionality with `S hS`.

Rewrite using `[Measure.map_apply hR hS, key _ (hR hS), key _ hS]`. Establish `step : ∀ z : PCoord ε → ℂ, dk ε {k | polarPR (k, z) ∈ rmulPR G ⁻¹' S} = dk ε {k | polarPR (k, actR G z) ∈ S}`. Introduce `z`. Take `⟨k', hk'⟩` from `rmulPR_polarPR hG z`. Establish `hset : {k | polarPR (k, z) ∈ rmulPR G ⁻¹' S} = (fun k => k * k') ⁻¹' {k | polarPR (k, actR G z) ∈ S}`.

Use extensionality with `k`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, hk']`. Rewrite using `[hset, measure_preimage_mul_right]`. Repeatedly rewrite using `[step]`. Establish `hφ : Measurable fun w : PCoord ε → ℂ => dk ε {k | polarPR (k, w) ∈ S}` using `measurable_measure_prodMk_right (hP hS)`.

Rewrite using `[← lintegral_map hφ hA, hc]`.
-/
theorem muPolarMat_mul_right (ε : Fin n → Bool) {G : Matrix (Fin n) (Fin n) ℂ} (hG : inUJ ε G) :
    Measure.map (rmulPR G) (muPolarMat ε) = muPolarMat ε := by
  have hP : Measurable (polarPR (ε := ε)) := measurable_polarPR ε
  have hR : Measurable (rmulPR G) := (continuous_rmulPR G).measurable
  have hA : Measurable (actR (ε := ε) G) := (JacB.actR_continuous hG).measurable
  have hc := coreP hG

  have key : ∀ S : Set (Fin n → Fin n → ℂ), MeasurableSet S →
      muPolarMat ε S = ∫⁻ z, dk ε {k | polarPR (k, z) ∈ S}
        ∂(volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) := by
    intro S hS
    show (Measure.map (polarPR (ε := ε)) ((dk ε).prod
      (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)))) S = _
    rw [Measure.map_apply hP hS, Measure.prod_apply_symm (hP hS)]
    rfl
  ext S hS
  rw [Measure.map_apply hR hS, key _ (hR hS), key _ hS]
  have step : ∀ z : PCoord ε → ℂ, dk ε {k | polarPR (k, z) ∈ rmulPR G ⁻¹' S} =
      dk ε {k | polarPR (k, actR G z) ∈ S} := by
    intro z
    obtain ⟨k', hk'⟩ := rmulPR_polarPR hG z
    have hset : {k | polarPR (k, z) ∈ rmulPR G ⁻¹' S} =
        (fun k => k * k') ⁻¹' {k | polarPR (k, actR G z) ∈ S} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hk']
    rw [hset, measure_preimage_mul_right]
  simp_rw [step]
  have hφ : Measurable fun w : PCoord ε → ℂ => dk ε {k | polarPR (k, w) ∈ S} :=
    measurable_measure_prodMk_right (hP hS)
  rw [← lintegral_map hφ hA, hc]

/- English proof (translation)
Use `show Measure.map (fun x => x * g) (Measure.comap (intMuCD_eM ε) (muPolarMat ε)) = Measure.comap (intMuCD_eM ε) (muPolarMat ε)`. Distinguish the cases in `h : Function.Injective (intMuCD_eM ε) ∧ ∀ s, MeasurableSet s → NullMeasurableSet (intMuCD_eM ε '' s) (muPolarMat ε)`. Use `swap`. Simplify using `only [Measure.comap, dif_neg h, Measure.map_zero]`. Use `haveI : BorelSpace (UJ ε) := ⟨rfl⟩`.

Establish `hRm : Measurable (fun x : UJ ε => x * g)` using `(continuous_mul_right g).measurable`. Establish `hG : inUJ ε (toM g)` using `g.2`. Establish `h4` using `muPolarMat_mul_right ε hG`. Establish `hRM : Measurable (rmulPR (toM g))` using `(continuous_rmulPR (toM g)).measurable`. Use extensionality with `S hS`.

Rewrite using `[Measure.map_apply hRm hS, Measure.comap_apply₀ _ _ h.1 h.2 (hRm hS).nullMeasurableSet, Measure.comap_apply₀ _ _ h.1 h.2 hS.nullMeasurableSet]`. Establish `h1 : toM g * toM g⁻¹ = 1`. Rewrite using `[show toM g * toM g⁻¹ = toM (g * g⁻¹) from rfl, mul_inv_cancel]`. Both sides reduce to the same expression. Establish `himg : intMuCD_eM ε '' ((fun x => x * g) ⁻¹' S) = rmulPR (toM g) ⁻¹' (intMuCD_eM ε '' S)`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y * g, hy, rfl⟩`. Introduce and unpack `⟨y, hy, hxy⟩`.

Use `⟨y * g⁻¹, ?_, ?_⟩` and prove the remaining obligations. Use `show y * g⁻¹ * g ∈ S`. Rewrite using `[inv_mul_cancel_right]`. Conclude with `hy`. Establish `hx : toM y = Matrix.of x * toM g` using `hxy show toM y * toM g⁻¹ = x`.

Rewrite using `[hx, Matrix.mul_assoc, h1, Matrix.mul_one]`. Both sides reduce to the same expression. Rewrite using `[himg, ← Measure.map_apply₀ hRM.aemeasurable (by rw [h4]; exact h.2 S hS), h4]`.
-/
theorem muPolar_mul_right (ε : Fin n → Bool) (g : UJ ε) :
    Measure.map (fun x => x * g) (muPolar ε) = muPolar ε := by
  show Measure.map (fun x => x * g) (Measure.comap (intMuCD_eM ε) (muPolarMat ε)) =
    Measure.comap (intMuCD_eM ε) (muPolarMat ε)
  by_cases h : Function.Injective (intMuCD_eM ε) ∧
      ∀ s, MeasurableSet s → NullMeasurableSet (intMuCD_eM ε '' s) (muPolarMat ε)
  swap
  · simp only [Measure.comap, dif_neg h, Measure.map_zero]
  haveI : BorelSpace (UJ ε) := ⟨rfl⟩
  have hRm : Measurable (fun x : UJ ε => x * g) := (continuous_mul_right g).measurable
  have hG : inUJ ε (toM g) := g.2
  have h4 := muPolarMat_mul_right ε hG
  have hRM : Measurable (rmulPR (toM g)) := (continuous_rmulPR (toM g)).measurable
  ext S hS
  rw [Measure.map_apply hRm hS, Measure.comap_apply₀ _ _ h.1 h.2 (hRm hS).nullMeasurableSet,
    Measure.comap_apply₀ _ _ h.1 h.2 hS.nullMeasurableSet]
  have h1 : toM g * toM g⁻¹ = 1 := by
    rw [show toM g * toM g⁻¹ = toM (g * g⁻¹) from rfl, mul_inv_cancel]
    rfl
  have himg : intMuCD_eM ε '' ((fun x => x * g) ⁻¹' S) =
      rmulPR (toM g) ⁻¹' (intMuCD_eM ε '' S) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y * g, hy, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      refine ⟨y * g⁻¹, ?_, ?_⟩
      · show y * g⁻¹ * g ∈ S
        rw [inv_mul_cancel_right]
        exact hy
      · have hx : toM y = Matrix.of x * toM g := hxy
        show toM y * toM g⁻¹ = x
        rw [hx, Matrix.mul_assoc, h1, Matrix.mul_one]
        rfl
  rw [himg, ← Measure.map_apply₀ hRM.aemeasurable (by rw [h4]; exact h.2 S hS), h4]

end ReciprocityTheory.ChartRestriction.DS
