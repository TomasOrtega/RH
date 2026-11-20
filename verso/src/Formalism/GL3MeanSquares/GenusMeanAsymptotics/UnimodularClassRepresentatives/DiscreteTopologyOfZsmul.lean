import Mathlib

open MeasureTheory Module ZSpan Filter Topology Pointwise Bornology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure]

/- English proof (translation)
Rewrite using `[LinearEquiv.image_eq_preimage_symm]`. Conclude with `(B.equivFunL.symm.toHomeomorph.toMeasurableEquiv.map_apply s).symm`.
-/
private theorem volume_image_equivFun_eq_map_symm {ι : Type*} [Fintype ι] (B : Basis ι ℝ E)
    (s : Set E) : volume (B.equivFun '' s) = Measure.map B.equivFunL.symm volume s := by
  rw [LinearEquiv.image_eq_preimage_symm]
  exact (B.equivFunL.symm.toHomeomorph.toMeasurableEquiv.map_apply s).symm

/- English proof (translation)
Establish `h : B.equivFun '' fundamentalDomain B = Set.univ.pi fun _ : ι ↦ Set.Ico (0 : ℝ) 1`. Use extensionality with `x`. Simplify using `only [Set.mem_image, mem_fundamentalDomain, Set.mem_univ_pi]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, rfl⟩ i`.

Simplify `hm i` using `[Basis.equivFun_apply]`. Introduce `hx`. Use `⟨B.equivFun.symm x, fun i ↦ ?_, B.equivFun.apply_symm_apply x⟩` and prove the remaining obligations. Establish `hxi` using `congrFun (B.equivFun.apply_symm_apply x) i`. Rewrite `hxi` using `[Basis.equivFun_apply]`.

Rewrite using `[hxi]`. Conclude with `hx i`. Rewrite using `[h, volume_pi_pi]`. Simplify using the standard rewrite rules.
-/
private theorem volume_image_equivFun_fundamentalDomain_eq_one {ι : Type*} [Fintype ι] (B : Basis ι ℝ E) :
    volume (B.equivFun '' fundamentalDomain B) = 1 := by
  have h : B.equivFun '' fundamentalDomain B = Set.univ.pi fun _ : ι ↦ Set.Ico (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_image, mem_fundamentalDomain, Set.mem_univ_pi]
    constructor
    · rintro ⟨m, hm, rfl⟩ i
      simpa [Basis.equivFun_apply] using hm i
    · intro hx
      refine ⟨B.equivFun.symm x, fun i ↦ ?_, B.equivFun.apply_symm_apply x⟩
      have hxi := congrFun (B.equivFun.apply_symm_apply x) i
      rw [Basis.equivFun_apply] at hxi
      rw [hxi]
      exact hx i
  rw [h, volume_pi_pi]
  simp

/- English proof (translation)
Establish `h` using `Measure.isAddLeftInvariant_eq_smul ν ν'`. Set `b` to `Module.Free.chooseBasis ℤ Λ`. Rewrite using `[ZLattice.covolume_eq_measure_fundamentalDomain Λ ν (ZLattice.isAddFundamentalDomain b ν), ZLattice.covolume_eq_measure_fundamentalDomain Λ ν' (ZLattice.isAddFundamentalDomain b ν')]`. Generalize the expression as in `Measure.addHaarScalarFactor ν ν' = c at h ⊢`. Rewrite using `[h]`.

Conclude with `measureReal_nnreal_smul_apply _`.
-/
private theorem covolume_eq_addHaarScalarFactor_mul_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ν ν' : Measure E) [ν.IsAddHaarMeasure] [ν'.IsAddHaarMeasure] :
    ZLattice.covolume Λ ν =
      (Measure.addHaarScalarFactor ν ν' : ℝ) * ZLattice.covolume Λ ν' := by
  have h := Measure.isAddLeftInvariant_eq_smul ν ν'
  let b := Module.Free.chooseBasis ℤ Λ
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ ν (ZLattice.isAddFundamentalDomain b ν),
    ZLattice.covolume_eq_measure_fundamentalDomain Λ ν' (ZLattice.isAddFundamentalDomain b ν')]
  generalize Measure.addHaarScalarFactor ν ν' = c at h ⊢
  rw [h]
  exact measureReal_nnreal_smul_apply _

/- English proof (translation)
Take `⟨ν, hν⟩ : ∃ ν : Measure E, ν = Measure.map (b.ofZLatticeBasis ℝ L).equivFunL.symm volume` from `⟨_, rfl⟩`. Establish `: ν.IsAddHaarMeasure` using `hν ▸ inferInstance`. Establish `hcov : ZLattice.covolume L ν = 1`. Rewrite using `[ZLattice.covolume_eq_measure_fundamentalDomain L ν (ZLattice.isAddFundamentalDomain b ν), measureReal_def, hν, ← volume_image_equivFun_eq_map_symm, volume_image_equivFun_fundamentalDomain_eq_one, ENNReal.toReal_one]`. Rewrite using `[volume_image_equivFun_eq_map_symm, ← hν, covolume_eq_addHaarScalarFactor_mul_covolume L μ ν, hcov, mul_one, ENNReal.ofReal_coe_nnreal]`.

Establish `hc` using `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν`. Establish `h` using `Measure.isAddLeftInvariant_eq_smul μ ν`. Generalize the expression as in `Measure.addHaarScalarFactor μ ν = c at hc h ⊢`. Establish `hc0 : (c : ENNReal) ≠ 0` using `by simpa using hc.ne'`. Rewrite using `[h, Measure.coe_nnreal_smul_apply, mul_comm, ENNReal.mul_div_cancel_right hc0 ENNReal.coe_ne_top]`.
-/
theorem volume_image_equivFun {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) (s : Set E) :
    volume ((b.ofZLatticeBasis ℝ L).equivFun '' s) =
      μ s / ENNReal.ofReal (ZLattice.covolume L μ) := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure E,
      ν = Measure.map (b.ofZLatticeBasis ℝ L).equivFunL.symm volume := ⟨_, rfl⟩
  have : ν.IsAddHaarMeasure := hν ▸ inferInstance
  have hcov : ZLattice.covolume L ν = 1 := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L ν (ZLattice.isAddFundamentalDomain b ν),
      measureReal_def, hν, ← volume_image_equivFun_eq_map_symm, volume_image_equivFun_fundamentalDomain_eq_one,
      ENNReal.toReal_one]
  rw [volume_image_equivFun_eq_map_symm, ← hν, covolume_eq_addHaarScalarFactor_mul_covolume L μ ν, hcov, mul_one,
    ENNReal.ofReal_coe_nnreal]
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν
  have h := Measure.isAddLeftInvariant_eq_smul μ ν
  generalize Measure.addHaarScalarFactor μ ν = c at hc h ⊢
  have hc0 : (c : ENNReal) ≠ 0 := by simpa using hc.ne'
  rw [h, Measure.coe_nnreal_smul_apply, mul_comm, ENNReal.mul_div_cancel_right hc0 ENNReal.coe_ne_top]

/- English proof (translation)
Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = finrank ℝ E`. Rewrite using `[← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]`. Establish `hfr : frontier (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' s) = ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' frontier s` using `(((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFunL.toHomeomorph.image_frontier s).symm`. Establish `hlim : volume.real (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' s) = μ.real s / ZLattice.covolume L μ`. Rewrite using `[measureReal_def, volume_image_equivFun L μ, ENNReal.toReal_div, ENNReal.toReal_ofReal (ZLattice.covolume_pos L μ).le, measureReal_def]`.

Establish `key` using `ZLattice.covolume.tendsto_card_div_pow'' (Module.Free.chooseBasis ℤ L) hs₁ hs₂ (by rw [hfr, volume_image_equivFun L μ, hs₃, ENNReal.zero_div])`. Rewrite `key` using `[hlim, hcard]`. Conclude with `key`.
-/
theorem tendsto_card_div_pow {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : μ (frontier s) = 0) :
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 (μ.real s / ZLattice.covolume L μ)) := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = finrank ℝ E := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  have hfr : frontier (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' s) =
      ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' frontier s :=
    (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFunL.toHomeomorph.image_frontier
      s).symm
  have hlim : volume.real (((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).equivFun '' s) =
      μ.real s / ZLattice.covolume L μ := by
    rw [measureReal_def, volume_image_equivFun L μ, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (ZLattice.covolume_pos L μ).le, measureReal_def]
  have key := ZLattice.covolume.tendsto_card_div_pow'' (Module.Free.chooseBasis ℤ L) hs₁ hs₂
    (by rw [hfr, volume_image_equivFun L μ, hs₃, ENNReal.zero_div])
  rw [hlim, hcard] at key
  exact key

set_option backward.isDefEq.respectTransparency.types false in
/- English proof (translation)
Take `⟨ν, hν⟩ : ∃ ν : Measure E, ν = Measure.map (Module.finBasis ℝ E).equivFunL.symm volume` from `⟨_, rfl⟩`. Establish `: ν.IsAddHaarMeasure` using `hν ▸ inferInstance`. Establish `he : MeasurePreserving (Module.finBasis ℝ E).equivFunL.symm volume ν`. Rewrite using `[hν]`. Conclude with `(Module.finBasis ℝ E).equivFunL.symm.continuous.measurable.measurePreserving _`.

Establish `hc` using `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν`. Rewrite using `[covolume_eq_addHaarScalarFactor_mul_covolume L₁ μ ν, covolume_eq_addHaarScalarFactor_mul_covolume L₂ μ ν, mul_div_mul_left _ _ (NNReal.coe_pos.mpr hc).ne', ← ZLattice.covolume_comap L₁ ν volume he, ← ZLattice.covolume_comap L₂ ν volume he, ZLattice.covolume_div_covolume_eq_relIn …`.
-/
theorem covolume_div_covolume (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ / ZLattice.covolume L₂ μ =
      L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure E,
      ν = Measure.map (Module.finBasis ℝ E).equivFunL.symm volume := ⟨_, rfl⟩
  have : ν.IsAddHaarMeasure := hν ▸ inferInstance
  have he : MeasurePreserving (Module.finBasis ℝ E).equivFunL.symm volume ν := by
    rw [hν]
    exact (Module.finBasis ℝ E).equivFunL.symm.continuous.measurable.measurePreserving _
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν
  rw [covolume_eq_addHaarScalarFactor_mul_covolume L₁ μ ν, covolume_eq_addHaarScalarFactor_mul_covolume L₂ μ ν,
    mul_div_mul_left _ _ (NNReal.coe_pos.mpr hc).ne', ← ZLattice.covolume_comap L₁ ν volume he,
    ← ZLattice.covolume_comap L₂ ν volume he,
    ZLattice.covolume_div_covolume_eq_relIndex _ _ (fun _ h' ↦ h h'),
    ZLattice.comap_toAddSubgroup, ZLattice.comap_toAddSubgroup, Nat.cast_inj,
    LinearEquiv.toAddMonoidHom_commutes, AddSubgroup.comap_equiv_eq_map_symm',
    AddSubgroup.comap_equiv_eq_map_symm',
    AddSubgroup.relIndex_map_map_of_injective _ _ (Module.finBasis ℝ E).equivFunL.injective]

/- English proof (translation)
Use `DiscreteTopology.of_continuous_injective (β := Λ₁) (f := fun y : Λ ↦ (⟨N • (y : E), h y y.2⟩ : Λ₁)) ?_ ?_` and prove the remaining obligations. Conclude with `((continuous_zsmul N).comp continuous_subtype_val).subtype_mk _`. Introduce `y z hyz`. Establish `h' : N • (y : E) = N • (z : E)` using `congrArg Subtype.val hyz`. Rewrite `h'` using `[← Int.cast_smul_eq_zsmul ℝ N (y : E), ← Int.cast_smul_eq_zsmul ℝ N (z : E)]`.

Conclude with `Subtype.ext (smul_right_injective E (Int.cast_ne_zero.mpr hN) h')`.
-/
theorem discreteTopology_of_zsmul {Λ₁ Λ : Submodule ℤ E} [DiscreteTopology Λ₁] {N : ℤ}
    (hN : N ≠ 0) (h : ∀ y ∈ Λ, N • y ∈ Λ₁) : DiscreteTopology Λ := by
  refine DiscreteTopology.of_continuous_injective (β := Λ₁)
    (f := fun y : Λ ↦ (⟨N • (y : E), h y y.2⟩ : Λ₁)) ?_ ?_
  · exact ((continuous_zsmul N).comp continuous_subtype_val).subtype_mk _
  · intro y z hyz
    have h' : N • (y : E) = N • (z : E) := congrArg Subtype.val hyz
    rw [← Int.cast_smul_eq_zsmul ℝ N (y : E), ← Int.cast_smul_eq_zsmul ℝ N (z : E)] at h'
    exact Subtype.ext (smul_right_injective E (Int.cast_ne_zero.mpr hN) h')

/- English proof (translation)
Establish `: DiscreteTopology Λ` using `discreteTopology_of_zsmul hN h`. Establish `: IsZLattice ℝ Λ` using `⟨by`. Rewrite using `[eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := Λ₁)]`. Conclude with `Submodule.span_mono hle⟩`. Establish `hidx` using `covolume_div_covolume μ Λ₁ Λ hle`.

Establish `h₁` using `(ZLattice.covolume_pos Λ₁ μ).ne'`. Establish `h₂` using `(ZLattice.covolume_pos Λ μ).ne'`. Establish `hne : (Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) ≠ 0`. Rewrite using `[← hidx]`. Conclude with `div_ne_zero h₁ h₂`.

Use `⟨by exact_mod_cast hne, ?_⟩` and prove the remaining obligations. Establish `key` using `tendsto_card_div_pow Λ μ hs₁ hs₂ (hs₃.addHaar_frontier μ)`. Use `key using 2` and compare the differences between its conclusion and the goal. Rewrite using `[← hidx]`. Clear the denominators using the available nonvanishing facts.
-/
theorem tendsto_card_of_le (Λ₁ Λ : Submodule ℤ E) [DiscreteTopology Λ₁] [IsZLattice ℝ Λ₁]
    (hle : Λ₁ ≤ Λ) {N : ℤ} (hN : N ≠ 0) (h : ∀ y ∈ Λ, N • y ∈ Λ₁) {s : Set E}
    (hs₁ : IsBounded s) (hs₂ : MeasurableSet s) (hs₃ : Convex ℝ s) :
    Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 ∧
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • Λ : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 (μ.real s * (Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) /
        ZLattice.covolume Λ₁ μ)) := by
  have : DiscreteTopology Λ := discreteTopology_of_zsmul hN h
  have : IsZLattice ℝ Λ := ⟨by
    rw [eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := Λ₁)]
    exact Submodule.span_mono hle⟩
  have hidx := covolume_div_covolume μ Λ₁ Λ hle
  have h₁ := (ZLattice.covolume_pos Λ₁ μ).ne'
  have h₂ := (ZLattice.covolume_pos Λ μ).ne'
  have hne : (Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) ≠ 0 := by
    rw [← hidx]
    exact div_ne_zero h₁ h₂
  refine ⟨by exact_mod_cast hne, ?_⟩
  have key := tendsto_card_div_pow Λ μ hs₁ hs₂ (hs₃.addHaar_frontier μ)
  convert key using 2
  rw [← hidx]
  field_simp

end Formalism.HermitianLattices.Ext.L3.BallA
