import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
open PositivityTheory.JacquetShalikaLocal

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel NNReal Pointwise

namespace GlobalTheory.CompanionTheory.JSBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Use `IsLocallyConstant.continuous ?_` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Use `⟨(fun y => y - x) ⁻¹' (𝒪[F] : Set F), (Valuation.isOpen_integer).preimage (by fun_prop), ?_, ?_⟩` and prove the remaining obligations. Simplify using `using (𝒪[F]).zero_mem`.

Introduce `y hy`. Establish `hxy : y = x + (y - x)` using `by ring`. Rewrite using `[hxy, AddChar.map_add_eq_mul, h _ hy, mul_one]`.
-/
theorem continuous_of_trivial_integer {ψ : AddChar F ℂ} (h : ∀ x ∈ 𝒪[F], ψ x = 1) : Continuous ψ := by
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' (𝒪[F] : Set F),
    (Valuation.isOpen_integer).preimage (by fun_prop), ?_, ?_⟩
  · simpa using (𝒪[F]).zero_mem
  · intro y hy
    have hxy : y = x + (y - x) := by ring
    rw [hxy, AddChar.map_add_eq_mul, h _ hy, mul_one]

/- English proof (translation)
The claim follows from `pow_ne_zero _ ((Valuation.ne_zero_iff _).mp (valuation_uniformizer_ne_zero F))`.
-/
theorem uniformizer_pow_ne_zero (M : ℕ) : (uniformizer F : F) ^ M ≠ 0 :=
  pow_ne_zero _ ((Valuation.ne_zero_iff _).mp (valuation_uniformizer_ne_zero F))

/- English proof (translation)
Use extensionality with `x`. Simplify using `[lat, Measures.mem_box]`.
-/
theorem lat_eq_preimage (m M : ℕ) : lat F m M =
    (Homeomorph.smulOfNeZero ((uniformizer F : F) ^ M) (uniformizer_pow_ne_zero M)) ⁻¹'
      Measures.box F (Fin m) := by
  ext x
  simp [lat, Measures.mem_box]

/- English proof (translation)
Rewrite using `[lat_eq_preimage]`. Conclude with `Measures.isOpen_box.preimage (Homeomorph.continuous _)`.
-/
theorem isOpen_lat (m M : ℕ) : IsOpen (lat F m M) := by
  rw [lat_eq_preimage]
  exact Measures.isOpen_box.preimage (Homeomorph.continuous _)

/- English proof (translation)
Rewrite using `[lat_eq_preimage]`. Conclude with `(Homeomorph.isCompact_preimage _).2 Measures.isCompact_box`.
-/
theorem isCompact_lat (m M : ℕ) : IsCompact (lat F m M) := by
  rw [lat_eq_preimage]
  exact (Homeomorph.isCompact_preimage _).2 Measures.isCompact_box

/- English proof (translation)
Introduce `i`. Simplify using `using (𝒪[F]).zero_mem`.
-/
theorem zero_mem_lat (m M : ℕ) : (0 : Fin m → F) ∈ lat F m M := by
  intro i
  simpa using (𝒪[F]).zero_mem

variable [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]

/- English proof (translation)
Use `haveI := Measures.sigmaCompactSpace F`. Establish `h0` using `(isOpen_lat (F := F) m M).measure_ne_zero (Measure.pi fun _ : Fin m => μ) ⟨0, zero_mem_lat m M⟩`. Establish `h1` using `(isCompact_lat (F := F) m M).measure_lt_top (μ := Measure.pi fun _ : Fin m => μ)`. Conclude with `ENNReal.toReal_pos h0 h1.ne`.
-/
theorem lat_measure_pos (m M : ℕ) :
    0 < (Measure.pi fun _ : Fin m => μ).real (lat F m M) := by
  haveI := Measures.sigmaCompactSpace F
  have h0 := (isOpen_lat (F := F) m M).measure_ne_zero (Measure.pi fun _ : Fin m => μ)
    ⟨0, zero_mem_lat m M⟩
  have h1 := (isCompact_lat (F := F) m M).measure_lt_top (μ := Measure.pi fun _ : Fin m => μ)
  exact ENNReal.toReal_pos h0 h1.ne

/- English proof (translation)
Use `haveI := Measures.sigmaCompactSpace F`. Use `haveI := Measures.metrizableSpace F`. Use `set ν : Measure (Fin m → F) := Measure.pi fun _ => μ with hν`. Use `set L := Measures.glEquiv g with hL`. Set `e : (Fin m → F) ≃ᵐ (Fin m → F)` to `(Homeomorph.smul L).toMeasurableEquiv`.

Establish `he : ∀ x, e x = (g : Matrix (Fin m) (Fin m) F) *ᵥ x` using `fun x => Measures.glEquiv_apply g x`. Establish `hc : distribHaarChar (Fin m → F) L = Measures.modulus (g : Matrix (Fin m) (Fin m) F).det`. Rewrite using `[hL, Measures.distribHaarChar_glEquiv, ← Measures.modulus_units]`. Both sides reduce to the same expression. Establish `hmap : ν.map e.symm = (Measures.modulus (g : Matrix (Fin m) (Fin m) F).det) • ν`.

Use `Measure.ext fun s _ => ?_` and prove the remaining obligations. Establish `hs : e.symm ⁻¹' s = L • s` using `(e.image_eq_preimage_symm s).symm`. Rewrite using `[e.symm.map_apply, hs, ← distribHaarChar_mul ν L s, hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Establish `himg : (fun x => (g : Matrix (Fin m) (Fin m) F) *ᵥ x) '' A = e.symm ⁻¹' A`. Rewrite using `[← e.image_eq_preimage_symm]`.

Conclude with `Set.image_congr fun x _ => (he x).symm`. Establish `key` using `setIntegral_map_equiv (μ := ν) e.symm (fun x => f (e x)) A`. Simplify using `only [MeasurableEquiv.apply_symm_apply] at key`. Rewrite using `[himg, ← key, hmap, Measure.restrict_smul, integral_smul_nnreal_measure]`. Simplify using `only [he, NNReal.smul_def, Complex.real_smul]`.
-/
theorem setIntegral_image_mulVec {m : ℕ} (g : GL (Fin m) F) (A : Set (Fin m → F))
    (f : (Fin m → F) → ℂ) :
    ∫ x in (fun x => (g : Matrix (Fin m) (Fin m) F) *ᵥ x) '' A, f x ∂(Measure.pi fun _ => μ) =
      ((Measures.modulus (g : Matrix (Fin m) (Fin m) F).det : ℝ) : ℂ) *
        ∫ x in A, f ((g : Matrix (Fin m) (Fin m) F) *ᵥ x) ∂(Measure.pi fun _ => μ) := by
  haveI := Measures.sigmaCompactSpace F
  haveI := Measures.metrizableSpace F
  set ν : Measure (Fin m → F) := Measure.pi fun _ => μ with hν
  set L := Measures.glEquiv g with hL
  let e : (Fin m → F) ≃ᵐ (Fin m → F) := (Homeomorph.smul L).toMeasurableEquiv
  have he : ∀ x, e x = (g : Matrix (Fin m) (Fin m) F) *ᵥ x := fun x => Measures.glEquiv_apply g x
  have hc : distribHaarChar (Fin m → F) L =
      Measures.modulus (g : Matrix (Fin m) (Fin m) F).det := by
    rw [hL, Measures.distribHaarChar_glEquiv, ← Measures.modulus_units]
    rfl
  have hmap : ν.map e.symm = (Measures.modulus (g : Matrix (Fin m) (Fin m) F).det) • ν := by
    refine Measure.ext fun s _ => ?_
    have hs : e.symm ⁻¹' s = L • s := (e.image_eq_preimage_symm s).symm
    rw [e.symm.map_apply, hs, ← distribHaarChar_mul ν L s, hc, Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul]
  have himg : (fun x => (g : Matrix (Fin m) (Fin m) F) *ᵥ x) '' A = e.symm ⁻¹' A := by
    rw [← e.image_eq_preimage_symm]
    exact Set.image_congr fun x _ => (he x).symm
  have key := setIntegral_map_equiv (μ := ν) e.symm (fun x => f (e x)) A
  simp only [MeasurableEquiv.apply_symm_apply] at key
  rw [himg, ← key, hmap, Measure.restrict_smul, integral_smul_nnreal_measure]
  simp only [he, NNReal.smul_def, Complex.real_smul]

/- English proof (translation)
Introduce `F _ _ _ _ _ _ μ _ ψ hψ`. Use `⟨continuous_of_trivial_integer hψ.1, fun m => ⟨fun M => ?_, fun g A f _ => ?_⟩⟩` and prove the remaining obligations. Conclude with `⟨isCompact_lat m M, isOpen_lat m M, (isOpen_lat m M).measurableSet, lat_measure_pos μ m M⟩`. Conclude with `setIntegral_image_mulVec μ g A f`.
-/
theorem l0 : L0 := by
  intro F _ _ _ _ _ _ μ _ ψ hψ
  refine ⟨continuous_of_trivial_integer hψ.1, fun m => ⟨fun M => ?_, fun g A f _ => ?_⟩⟩
  · exact ⟨isCompact_lat m M, isOpen_lat m M, (isOpen_lat m M).measurableSet, lat_measure_pos μ m M⟩
  · exact setIntegral_image_mulVec μ g A f

end GlobalTheory.CompanionTheory.JSBound

end
