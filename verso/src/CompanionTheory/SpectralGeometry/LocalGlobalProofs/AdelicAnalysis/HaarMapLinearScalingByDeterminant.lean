import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.DetScale

open Matrix
open scoped Pointwise

section Ring

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R]
  [BorelSpace R] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
The claim follows from `(continuous_const.matrix_mulVec continuous_id : Continuous fun x : ι → R => A *ᵥ x).measurable`.
-/
theorem measurable_mulVec (A : Matrix ι ι R) :
    Measurable (fun x : ι → R => A *ᵥ x) :=
  (continuous_const.matrix_mulVec continuous_id : Continuous fun x : ι → R => A *ᵥ x).measurable

/- English proof (translation)
Establish `hm : Measurable fun x : R => (u : R) * x` using `(continuous_const.mul continuous_id).measurable`. Use extensionality with `S hS`. Rewrite using `[Measure.smul_apply, Measure.map_apply hm hS]`. Establish `h1` using `distribHaarChar_mul lam u ((fun x : R => (u : R) * x) ⁻¹' S)`. Establish `e : u • ((fun x : R => (u : R) * x) ⁻¹' S) = S`.

Use extensionality with `y`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Simplify using `[Units.smul_def]`. Rewrite `h1` using `[e]`. Rewrite using `[ENNReal.smul_def, smul_eq_mul]`.

Conclude with `h1`.
-/
theorem char_smul_map (lam : Measure R) [lam.IsAddHaarMeasure] (u : Rˣ) :
    distribHaarChar R u • lam.map (fun x => (u : R) * x) = lam := by
  have hm : Measurable fun x : R => (u : R) * x :=
    (continuous_const.mul continuous_id).measurable
  ext S hS
  rw [Measure.smul_apply, Measure.map_apply hm hS]
  have h1 := distribHaarChar_mul lam u ((fun x : R => (u : R) * x) ⁻¹' S)
  have e : u • ((fun x : R => (u : R) * x) ⁻¹' S) = S := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e] at h1
  rw [ENNReal.smul_def, smul_eq_mul]
  exact h1

/- English proof (translation)
Establish `ht` using `measurable_mulVec (transvection i j c)`. Use `(Measure.pi_eq fun s hs ↦ ?_).symm` and prove the remaining obligations. Establish `h2s : MeasurableSet (Set.univ.pi s)` using `.pi Set.countable_univ fun i _ ↦ hs i`. Repeatedly rewrite using `[← Measure.pi_pi, ← lintegral_indicator_one h2s]`. Rewrite using `[lintegral_map (measurable_one.indicator h2s) ht]`.

Use `lintegral_eq_of_lmarginal_eq {i} ((measurable_one.indicator h2s).comp ht) (measurable_one.indicator h2s) ?_` and prove the remaining obligations. Repeatedly rewrite using `[lmarginal_singleton]`. Use extensionality with `x`. Simplify using `[transvection, add_mulVec, single_mulVec, hij.symm, ← Function.update_add, lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x i xᵢ)]`.
-/
theorem map_transvection (lam : Measure R) [lam.IsAddHaarMeasure] (i j : ι) (c : R) (hij : i ≠ j) :
    (Measure.pi fun _ : ι => lam).map (fun x => transvection i j c *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  have ht := measurable_mulVec (transvection i j c)
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  simp [transvection, add_mulVec, single_mulVec, hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x i xᵢ)]

/- English proof (translation)
Use `(Measure.pi_eq fun s hs => ?_).symm` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, Measure.map_apply (measurable_mulVec _) (MeasurableSet.univ_pi hs)]`. Establish `h1 : (fun x : ι → R => diagonal (fun i => (d i : R)) *ᵥ x) ⁻¹' Set.pi Set.univ s = Set.pi Set.univ fun i => (fun y : R => (d i : R) * y) ⁻¹' s i`. Use extensionality with `f`. Simplify using `[mulVec_diagonal]`.

Establish `hm : ∀ i, Measurable fun x : R => (d i : R) * x` using `fun i => (continuous_const.mul continuous_id).measurable`. Rewrite using `[h1, Measure.pi_pi, map_prod, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_finset_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h2` using `congrArg (fun m : Measure R => m (s i)) (char_smul_map lam (d i))`. Simplify using `only [Measure.smul_apply, Measure.map_apply (hm i) (hs i)] at h2`.

Rewrite using `[← h2]`. Both sides reduce to the same expression.
-/
theorem map_diagonal (lam : Measure R) [lam.IsAddHaarMeasure] (d : ι → Rˣ) :
    distribHaarChar R (∏ i, d i) •
        (Measure.pi fun _ : ι => lam).map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.smul_apply, Measure.map_apply (measurable_mulVec _) (MeasurableSet.univ_pi hs)]
  have h1 : (fun x : ι → R => diagonal (fun i => (d i : R)) *ᵥ x) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun i => (fun y : R => (d i : R) * y) ⁻¹' s i := by
    ext f
    simp [mulVec_diagonal]
  have hm : ∀ i, Measurable fun x : R => (d i : R) * x := fun i =>
    (continuous_const.mul continuous_id).measurable
  rw [h1, Measure.pi_pi, map_prod, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_finset_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 := congrArg (fun m : Measure R => m (s i)) (char_smul_map lam (d i))
  simp only [Measure.smul_apply, Measure.map_apply (hm i) (hs i)] at h2
  rw [← h2]
  rfl

end Ring

/- English proof (translation)
Set `u : Fˣ →* Rˣ` to `Units.map (algebraMap F R : F →* R)`. Use `diagonal_transvection_induction_of_det_ne_zero (fun A : Matrix ι ι F => ∀ h : A.det ≠ 0, distribHaarChar R (u (Units.mk0 A.det h)) • (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) = Measure.pi fun _ : ι => lam) A h ?_ ?_ ?_ h` and prove the remaining obligations. Introduce `D hD h`. Establish `hD' : ∀ i, D i ≠ 0` using `fun i => by`. Rewrite `hD` using `[det_diagonal]`.

Conclude with `Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)`. Establish `e1 : u (Units.mk0 (diagonal D).det h) = ∏ i, u (Units.mk0 (D i) (hD' i))`. Rewrite using `[← map_prod]`. Use `congr 1`. Use `ext`.

Simplify using `[det_diagonal]`. Establish `e2 : (diagonal D).map (algebraMap F R) = diagonal fun i => ((u (Units.mk0 (D i) (hD' i)) : Rˣ) : R)`. Use extensionality with `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[u]`. Simplify using `[u, hab]`. Rewrite using `[e1, e2]`. Conclude with `map_diagonal lam _`. Introduce `t h`.

Take `⟨i, j, hij, c⟩` from `t`. Establish `e1 : u (Units.mk0 (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩).det h) = 1`. Rewrite using `[show Units.mk0 (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩).det h = 1 from Units.ext (by simpa [TransvectionStruct.toMatrix] using det_transvection_of_ne i j hij c), map_one]`. Establish `e2 : (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩ : Matrix ι ι F).map (algebraMap F R) = transvection i j (algebraMap F R c)`. Use extensionality with `a b`.

Simplify using `[TransvectionStruct.toMatrix, transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, apply_ite (algebraMap F R)]`. Rewrite using `[e1, e2, map_one, one_smul]`. Conclude with `map_transvection lam i j _ hij`. Introduce `A B hA hB IHA IHB h`. Establish `e1 : Units.mk0 (A * B).det h = Units.mk0 A.det hA * Units.mk0 B.det hB` using `Units.ext (by simp [det_mul])`.

Establish `e2 : (fun x : ι → R => (A * B).map (algebraMap F R) *ᵥ x) = (fun x => A.map (algebraMap F R) *ᵥ x) ∘ (fun x => B.map (algebraMap F R) *ᵥ x)` using `by ext1 x`. Simplify using `[Matrix.map_mul, mulVec_mulVec]`. Rewrite using `[e1, e2, map_mul, map_mul, mul_smul, ← Measure.map_map (measurable_mulVec _) (measurable_mulVec _), ← Measure.map_smul, IHB hB]`. Conclude with `IHA hA`.
-/
theorem smul_map_pi {F : Type} [Field F] {R : Type} [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
    {ι : Type} [Fintype ι] [DecidableEq ι] (lam : Measure R) [lam.IsAddHaarMeasure]
    (A : Matrix ι ι F) (h : A.det ≠ 0) :
    distribHaarChar R (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det h)) •
        (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  let u : Fˣ →* Rˣ := Units.map (algebraMap F R : F →* R)
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun A : Matrix ι ι F => ∀ h : A.det ≠ 0, distribHaarChar R (u (Units.mk0 A.det h)) •
        (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      Measure.pi fun _ : ι => lam) A h ?_ ?_ ?_ h
  · intro D hD h
    have hD' : ∀ i, D i ≠ 0 := fun i => by
      rw [det_diagonal] at hD
      exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have e1 : u (Units.mk0 (diagonal D).det h) = ∏ i, u (Units.mk0 (D i) (hD' i)) := by
      rw [← map_prod]
      congr 1
      ext
      simp [det_diagonal]
    have e2 : (diagonal D).map (algebraMap F R) =
        diagonal fun i => ((u (Units.mk0 (D i) (hD' i)) : Rˣ) : R) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [u]
      · simp [u, hab]
    rw [e1, e2]
    exact map_diagonal lam _
  · intro t h
    obtain ⟨i, j, hij, c⟩ := t
    have e1 : u (Units.mk0 (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩).det h) = 1 := by
      rw [show Units.mk0 (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩).det h = 1 from
        Units.ext (by simpa [TransvectionStruct.toMatrix] using det_transvection_of_ne i j hij c), map_one]
    have e2 : (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩ : Matrix ι ι F).map (algebraMap F R) =
        transvection i j (algebraMap F R c) := by
      ext a b
      simp [TransvectionStruct.toMatrix, transvection, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply, apply_ite (algebraMap F R)]
    rw [e1, e2, map_one, one_smul]
    exact map_transvection lam i j _ hij
  · intro A B hA hB IHA IHB h
    have e1 : Units.mk0 (A * B).det h = Units.mk0 A.det hA * Units.mk0 B.det hB :=
      Units.ext (by simp [det_mul])
    have e2 : (fun x : ι → R => (A * B).map (algebraMap F R) *ᵥ x) =
        (fun x => A.map (algebraMap F R) *ᵥ x) ∘ (fun x => B.map (algebraMap F R) *ᵥ x) := by
      ext1 x
      simp [Matrix.map_mul, mulVec_mulVec]
    rw [e1, e2, map_mul, map_mul, mul_smul,
      ← Measure.map_map (measurable_mulVec _) (measurable_mulVec _), ← Measure.map_smul, IHB hB]
    exact IHA hA

/- English proof (translation)
Introduce `F _ R _ _ _ _ _ _ _ _ _ ι _ _ A hA lam hlam c hc μ hμ`. Establish `h1` using `smul_map_pi lam A hA`. Establish `h2` using `char_smul_map lam (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det hA))`. Use `set d := distribHaarChar R (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det hA))`. Establish `h2' : d • lam.map (fun x => algebraMap F R A.det * x) = lam` using `h2`.

Rewrite `h2'` using `[hc]`. Take `⟨K, hKc, hK0⟩ : ∃ K : Set R, IsCompact K ∧ K ∈ 𝓝 (0 : R)` from `exists_compact_mem_nhds 0`. Establish `hdc : d * c = 1`. Establish `h3` using `congrArg (fun m : Measure R => m K) h2'`. Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3`.

Rewrite `h3` using `[← mul_assoc, ← ENNReal.coe_mul]`. Establish `h4 : ((d * c : ℝ≥0) : ℝ≥0∞) = 1` using `(ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds lam hK0).ne' hKc.measure_lt_top.ne).1 (h3.trans (one_mul _).symm)`. Conclude with `h4` after adjusting the coercions. Establish `h4 : (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) = c • Measure.pi fun _ : ι => lam` using `by conv_rhs => rw [← h1]`. Rewrite using `[smul_smul, mul_comm c d, hdc, one_smul]`.

Take `⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • Measure.pi fun _ : ι => lam` from `⟨_, Measure.isAddLeftInvariant_eq_smul_of_regular μ (Measure.pi fun _ : ι => lam)⟩`. Rewrite using `[hk, Measure.map_smul, h4, smul_comm]`.
-/
theorem map_mulVec_eq_smul : ∀ (F : Type) [Field F] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (ι : Type)
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∀ (lam : Measure R),
    lam.IsAddHaarMeasure → ∀ c : ℝ≥0, lam.map (fun x => algebraMap F R A.det * x) = c • lam →
    ∀ μ : Measure (ι → R), μ.IsAddHaarMeasure →
      μ.map (fun x => A.map (algebraMap F R) *ᵥ x) = c • μ := by
  intro F _ R _ _ _ _ _ _ _ _ _ ι _ _ A hA lam hlam c hc μ hμ
  have h1 := smul_map_pi lam A hA
  have h2 := char_smul_map lam (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det hA))
  set d := distribHaarChar R (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det hA))
  have h2' : d • lam.map (fun x => algebraMap F R A.det * x) = lam := h2
  rw [hc] at h2'
  obtain ⟨K, hKc, hK0⟩ : ∃ K : Set R, IsCompact K ∧ K ∈ 𝓝 (0 : R) := exists_compact_mem_nhds 0
  have hdc : d * c = 1 := by
    have h3 := congrArg (fun m : Measure R => m K) h2'
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    rw [← mul_assoc, ← ENNReal.coe_mul] at h3
    have h4 : ((d * c : ℝ≥0) : ℝ≥0∞) = 1 :=
      (ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds lam hK0).ne' hKc.measure_lt_top.ne).1
        (h3.trans (one_mul _).symm)
    exact_mod_cast h4
  have h4 : (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      c • Measure.pi fun _ : ι => lam := by
    conv_rhs => rw [← h1]
    rw [smul_smul, mul_comm c d, hdc, one_smul]
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • Measure.pi fun _ : ι => lam :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul_of_regular μ (Measure.pi fun _ : ι => lam)⟩
  rw [hk, Measure.map_smul, h4, smul_comm]

end GlobalTheory.CompanionTheory.SW.DetScale
