import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Locfin

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

/- English proof (translation)
Use `show ∑ w, (star ((c • z) w) ⬝ᵥ mat h w *ᵥ (c • z) w).re = c ^ 2 * ∑ w, (star (z w) ⬝ᵥ mat h w *ᵥ z w).re`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `e : (c • z) w = (c : ℂ) • z w`. Use extensionality with `i`.

Simplify using `[Complex.real_smul]`. Rewrite using `[e, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]`. Simplify using `[smul_eq_mul, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem qR_smul_VR {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N) (c : ℝ)
    (z : VR L N) : qR h (c • z) = c ^ 2 * qR h z := by
  show ∑ w, (star ((c • z) w) ⬝ᵥ mat h w *ᵥ (c • z) w).re =
    c ^ 2 * ∑ w, (star (z w) ⬝ᵥ mat h w *ᵥ z w).re
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (c • z) w = (c : ℂ) • z w := by
    ext i; simp [Complex.real_smul]
  rw [e, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp [smul_eq_mul, Complex.conj_ofReal]
  ring

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨w0, hw0⟩ : ∃ w, z w ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hz (funext hc)`. Use `show 0 < ∑ w, (star (z w) ⬝ᵥ mat h w *ᵥ z w).re`.

Establish `hnn : ∀ w, 0 ≤ (star (z w) ⬝ᵥ mat h w *ᵥ z w).re` using `fun w => by`. Use `(hp w).posSemidef.dotProduct_mulVec_nonneg (z w)` as an intermediate fact. Conclude with `(Complex.nonneg_iff.mp this).1`. Establish `hpos : 0 < (star (z w0) ⬝ᵥ mat h w0 *ᵥ z w0).re` using `(hp w0).re_dotProduct_pos hw0`. Conclude with `Finset.sum_pos' (fun w _ => hnn w) ⟨w0, Finset.mem_univ _, hpos⟩`.
-/
private theorem qR_pos_of_mem_Pos_of_VR_ne_zero {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) (z : VR L N) (hz : z ≠ 0) : 0 < qR h z := by
  obtain ⟨w0, hw0⟩ : ∃ w, z w ≠ 0 := by
    by_contra hc; push_neg at hc; exact hz (funext hc)
  show 0 < ∑ w, (star (z w) ⬝ᵥ mat h w *ᵥ z w).re
  have hnn : ∀ w, 0 ≤ (star (z w) ⬝ᵥ mat h w *ᵥ z w).re := fun w => by
    have := (hp w).posSemidef.dotProduct_mulVec_nonneg (z w)
    exact (Complex.nonneg_iff.mp this).1
  have hpos : 0 < (star (z w0) ⬝ᵥ mat h w0 *ᵥ z w0).re := (hp w0).re_dotProduct_pos hw0
  exact Finset.sum_pos' (fun w _ => hnn w) ⟨w0, Finset.mem_univ _, hpos⟩

/- English proof (translation)
Use `show Continuous fun x => ∑ w, (star (g x w) ⬝ᵥ mat (f x) w *ᵥ g x w).re`. Use `continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_` and prove the remaining obligations. Establish `h1 : Continuous fun x => g x w` using `(continuous_apply w).comp hg`. Establish `h2 : Continuous fun x => mat (f x) w` using `(continuous_apply w).comp (continuous_subtype_val.comp hf)`. Conclude with `h1.star.dotProduct (h2.matrix_mulVec h1)`.
-/
private theorem continuous_qR_comp {L : Type} [Field L] [NumberField L] {N : ℕ} {X : Type*}
    [TopologicalSpace X] {f : X → HS L N} {g : X → VR L N} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => qR (f x) (g x) := by
  show Continuous fun x => ∑ w, (star (g x w) ⬝ᵥ mat (f x) w *ᵥ g x w).re
  refine continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_
  have h1 : Continuous fun x => g x w := (continuous_apply w).comp hg
  have h2 : Continuous fun x => mat (f x) w :=
    (continuous_apply w).comp (continuous_subtype_val.comp hf)
  exact h1.star.dotProduct (h2.matrix_mulVec h1)

/- English proof (translation)
Simplify using `using qR_smul_VR h 0 0`.
-/
private theorem qR_zero_right {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N) :
    qR h 0 = 0 := by
  simpa using qR_smul_VR h 0 0

/- English proof (translation)
Use `⟨‖z‖, norm_pos_iff.mpr hz, ‖z‖⁻¹ • z, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]`. Rewrite using `[smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]`.
-/
private theorem exists_pos_smul_unit_sphere_eq_of_ne_zero {L : Type} [Field L] [NumberField L] {N : ℕ} (z : VR L N)
    (hz : z ≠ 0) : ∃ r : ℝ, 0 < r ∧ ∃ u ∈ Metric.sphere (0 : VR L N) 1, z = r • u := by
  refine ⟨‖z‖, norm_pos_iff.mpr hz, ‖z‖⁻¹ • z, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]

/- English proof (translation)
Introduce and unpack `rfl`. Simplify using `at hu`.
-/
private theorem ne_zero_of_mem_unit_sphere_VR {L : Type} [Field L] [NumberField L] {N : ℕ}
    (u : VR L N) (hu : u ∈ Metric.sphere (0 : VR L N) 1) : u ≠ 0 := by
  rintro rfl
  simp at hu

/- English proof (translation)
Establish `hS : IsCompact (Metric.sphere (0 : VR L N) 1)` using `isCompact_sphere 0 1`. Establish `hc : ContinuousOn (fun p : HS L N × VR L N => qR h0 p.2 / qR p.1 p.2) (K ×ˢ Metric.sphere (0 : VR L N) 1)`. Use `ContinuousOn.div ?_ (continuous_qR_comp continuous_fst continuous_snd).continuousOn ?_` and prove the remaining obligations. Conclude with `(continuous_qR_comp continuous_const continuous_snd).continuousOn`. Introduce and unpack `⟨h, z⟩ ⟨hh, hz⟩`.

Conclude with `(qR_pos_of_mem_Pos_of_VR_ne_zero h (hKP hh) z (ne_zero_of_mem_unit_sphere_VR z hz)).ne'`. Take `⟨C, hC⟩` from `(hK.prod hS).bddAbove_image hc`. Use `⟨max C 0, le_max_right _ _, fun h hh z => ?_⟩` and prove the remaining obligations. Break down `eq_or_ne z 0 with rfl | hz` into its components or cases. Simplify using `[qR_zero_right]`.

Take `⟨r, -, u, hu, rfl⟩` from `exists_pos_smul_unit_sphere_eq_of_ne_zero z hz`. Establish `hpu : 0 < qR h u` using `qR_pos_of_mem_Pos_of_VR_ne_zero h (hKP hh) u (ne_zero_of_mem_unit_sphere_VR u hu)`. Establish `hb : qR h0 u / qR h u ≤ C` using `hC ⟨(h, u), ⟨hh, hu⟩, rfl⟩`. Establish `h1 : qR h0 u ≤ max C 0 * qR h u`. Rewrite `hb` using `[div_le_iff₀ hpu]`.

Conclude with `hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpu.le)`. Rewrite using `[qR_smul_VR, qR_smul_VR]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem exists_qR_le_mul_qR_on_compact_subset_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (K : Set (HS L N))
    (hK : IsCompact K) (hKP : K ⊆ Pos L N) (h0 : HS L N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ K, ∀ z, qR h0 z ≤ C * qR h z := by
  have hS : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have hc : ContinuousOn (fun p : HS L N × VR L N => qR h0 p.2 / qR p.1 p.2)
      (K ×ˢ Metric.sphere (0 : VR L N) 1) := by
    refine ContinuousOn.div ?_ (continuous_qR_comp continuous_fst continuous_snd).continuousOn ?_
    · exact (continuous_qR_comp continuous_const continuous_snd).continuousOn
    · rintro ⟨h, z⟩ ⟨hh, hz⟩
      exact (qR_pos_of_mem_Pos_of_VR_ne_zero h (hKP hh) z (ne_zero_of_mem_unit_sphere_VR z hz)).ne'
  obtain ⟨C, hC⟩ := (hK.prod hS).bddAbove_image hc
  refine ⟨max C 0, le_max_right _ _, fun h hh z => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp [qR_zero_right]
  obtain ⟨r, -, u, hu, rfl⟩ := exists_pos_smul_unit_sphere_eq_of_ne_zero z hz
  have hpu : 0 < qR h u := qR_pos_of_mem_Pos_of_VR_ne_zero h (hKP hh) u (ne_zero_of_mem_unit_sphere_VR u hu)
  have hb : qR h0 u / qR h u ≤ C := hC ⟨(h, u), ⟨hh, hu⟩, rfl⟩
  have h1 : qR h0 u ≤ max C 0 * qR h u := by
    rw [div_le_iff₀ hpu] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpu.le)
  rw [qR_smul_VR, qR_smul_VR]
  calc r ^ 2 * qR h0 u ≤ r ^ 2 * (max C 0 * qR h u) := mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
    _ = max C 0 * (r ^ 2 * qR h u) := by ring

/- English proof (translation)
The claim follows from `|qR k u - qR h u| - 1 / 2 * qR h u < 0 := by have hS : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1 have c1 : Continuous fun p : HS L N × VR L N => qR p.1 p.2 := continuous_qR_comp continuous_fst continuous_snd have c2 : Continuous fun p : HS L N × VR L N => q …`.
-/
private theorem eventually_nhds_unit_sphere_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) :
    ∀ᶠ k in nhds h, ∀ u ∈ Metric.sphere (0 : VR L N) 1,
      |qR k u - qR h u| - 1 / 2 * qR h u < 0 := by
  have hS : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have c1 : Continuous fun p : HS L N × VR L N => qR p.1 p.2 :=
    continuous_qR_comp continuous_fst continuous_snd
  have c2 : Continuous fun p : HS L N × VR L N => qR h p.2 :=
    continuous_qR_comp continuous_const continuous_snd
  refine hS.eventually_forall_of_forall_eventually fun u hu => ?_
  have hpu : 0 < qR h u := qR_pos_of_mem_Pos_of_VR_ne_zero h hp u (ne_zero_of_mem_unit_sphere_VR u hu)
  set f : HS L N × VR L N → ℝ := fun p => |qR p.1 p.2 - qR h p.2| - 1 / 2 * qR h p.2 with hf
  have hcont : Continuous f :=
    ((c1.sub c2).abs).sub (continuous_const.mul c2)
  have hv : f (h, u) < 0 := by
    show |qR h u - qR h u| - 1 / 2 * qR h u < 0
    rw [sub_self, abs_zero, zero_sub, neg_lt_zero]
    linarith
  have h2 : ∀ᶠ p in nhds (h, u), f p < 0 := hcont.continuousAt.eventually (Iio_mem_nhds hv)
  filter_upwards [h2] with p hp'
  exact hp'

/- English proof (translation)
Use `filter_upwards [eventually_nhds_unit_sphere_of_mem_Pos h hp] with k hk z`. Break down `eq_or_ne z 0 with rfl | hz` into its components or cases. Rewrite using `[qR_zero_right, qR_zero_right]`. Evaluate the numerical expressions. Take `⟨r, -, u, hu, rfl⟩` from `exists_pos_smul_unit_sphere_eq_of_ne_zero z hz`.

Rewrite using `[qR_smul_VR, qR_smul_VR, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg r)]`. Establish `h1 : |qR k u - qR h u| ≤ 1 / 2 * qR h u` using `by linarith [hk u hu]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem eventually_nhds_abs_qR_sub_le_half_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) :
    ∀ᶠ k in nhds h, ∀ z : VR L N, |qR k z - qR h z| ≤ 1 / 2 * qR h z := by
  filter_upwards [eventually_nhds_unit_sphere_of_mem_Pos h hp] with k hk z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [qR_zero_right, qR_zero_right]
    norm_num
  obtain ⟨r, -, u, hu, rfl⟩ := exists_pos_smul_unit_sphere_eq_of_ne_zero z hz
  rw [qR_smul_VR, qR_smul_VR, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg r)]
  have h1 : |qR k u - qR h u| ≤ 1 / 2 * qR h u := by linarith [hk u hu]
  calc r ^ 2 * |qR k u - qR h u| ≤ r ^ 2 * (1 / 2 * qR h u) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
    _ = 1 / 2 * (r ^ 2 * qR h u) := by ring

/- English proof (translation)
Introduce `hB L _ _ N`. Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hu : Pos L 0 = Set.univ`. Use extensionality with `h`.

Simplify using `only [Set.mem_univ, iff_true]`. Introduce `w`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => absurd (Subsingleton.elim x 0) hx` and prove the remaining obligations. Conclude with `h.2 w`. Rewrite using `[hu]`.

Conclude with `isOpen_univ`. Introduce `K _ _`. Apply `Set.Subsingleton.finite` to reduce the goal to its premises. Introduce `a _ b _`. Conclude with `Units.ext (Subsingleton.elim _ _)`.

Take `⟨hPos, hEq, -, hCl, -, -⟩` from `hB L N hN`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `isOpen_iff_mem_nhds.mpr fun h hh => ?_ filter_upwards [eventually_nhds_abs_qR_sub_le_half_of_mem_Pos h hh] with k hk` and prove the remaining obligations. Conclude with `(hCl (1 / 2) (by norm_num) le_rfl h hh k hk).1`. Introduce `K hK hKP`.

Break down `K.eq_empty_or_nonempty with rfl | ⟨h0, hh0⟩` into its components or cases. Simplify using the standard rewrite rules. Take `⟨C, hC0, hC⟩` from `exists_qR_le_mul_qR_on_compact_subset_Pos K hK hKP h0`. Establish `hbd : ∀ i : Fin N, ∃ B : ℝ, ∀ h ∈ K, q h (Pi.single i 1 : UpperTheory.V.KT.Lat L N) ≤ B`. Introduce `i`.

Establish `hc : Continuous fun h : HS L N => qR h (toR (Pi.single i 1 : UpperTheory.V.KT.Lat L N))` using `continuous_qR_comp continuous_id continuous_const`. Take `⟨B, hB'⟩` from `hK.bddAbove_image hc.continuousOn`. Conclude with `⟨B, fun h hh => hB' ⟨h, hh, rfl⟩⟩`. Use `choose B hBd using hbd`. Establish `hF : (⋃ i, {v : UpperTheory.V.KT.Lat L N | q h0 v ≤ C * B i}).Finite` using `Set.finite_iUnion fun i => (hPos h0 (hKP hh0)).2.2.2.2 _`.

Establish `hmaps : ∀ γ ∈ {γ : Gm L N | ∃ h ∈ K, ac γ h ∈ K}, (fun i : Fin N => γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) ∈ Set.pi Set.univ (fun _ => ⋃ i, {v : UpperTheory.V.KT.Lat L N | q h0 v ≤ C * B i})`. Introduce and unpack `γ ⟨h, hh, hγ⟩ i -`. Use `Set.mem_iUnion.mpr ⟨i, ?_⟩` and prove the remaining obligations. Use `show q h0 (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) ≤ C * B i`. Combine the equalities or inequalities in the displayed calculation.

Establish `hinj : Set.InjOn (fun γ : Gm L N => fun i : Fin N => γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) {γ : Gm L N | ∃ h ∈ K, ac γ h ∈ K}`. Introduce `a _ b _ hab`. Establish `hinv : (a⁻¹ : Gm L N) = b⁻¹`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `j i`.

Establish `e` using `congrFun (congrFun hab i) j`. Express the relevant statement in the definitionally equal form `((↑(a⁻¹ : GL (Fin N) (𝓞 L)) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ Pi.single i 1) j = ((↑(b⁻¹ : GL (Fin N) (𝓞 L)) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ Pi.single i 1) j at e`. Simplify `e` using `[Matrix.mulVec_single_one]`. Conclude with `inv_injective hinv`. Conclude with `Set.Finite.of_finite_image ((Set.Finite.pi fun _ => hF).subset (Set.image_subset_iff.mpr hmaps)) hinj`.
-/
theorem pf_GProper : GProper := by
  intro hB L _ _ N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨?_, ?_⟩
    · have hu : Pos L 0 = Set.univ := by
        ext h
        simp only [Set.mem_univ, iff_true]
        intro w
        refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => absurd (Subsingleton.elim x 0) hx
        exact h.2 w
      rw [hu]
      exact isOpen_univ
    · intro K _ _
      apply Set.Subsingleton.finite
      intro a _ b _
      exact Units.ext (Subsingleton.elim _ _)
  obtain ⟨hPos, hEq, -, hCl, -, -⟩ := hB L N hN
  refine ⟨?_, ?_⟩
  · refine isOpen_iff_mem_nhds.mpr fun h hh => ?_
    filter_upwards [eventually_nhds_abs_qR_sub_le_half_of_mem_Pos h hh] with k hk
    exact (hCl (1 / 2) (by norm_num) le_rfl h hh k hk).1
  intro K hK hKP
  rcases K.eq_empty_or_nonempty with rfl | ⟨h0, hh0⟩
  · simp
  obtain ⟨C, hC0, hC⟩ := exists_qR_le_mul_qR_on_compact_subset_Pos K hK hKP h0
  have hbd : ∀ i : Fin N, ∃ B : ℝ, ∀ h ∈ K, q h (Pi.single i 1 : UpperTheory.V.KT.Lat L N) ≤ B := by
    intro i
    have hc : Continuous fun h : HS L N => qR h (toR (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) :=
      continuous_qR_comp continuous_id continuous_const
    obtain ⟨B, hB'⟩ := hK.bddAbove_image hc.continuousOn
    exact ⟨B, fun h hh => hB' ⟨h, hh, rfl⟩⟩
  choose B hBd using hbd
  have hF : (⋃ i, {v : UpperTheory.V.KT.Lat L N | q h0 v ≤ C * B i}).Finite :=
    Set.finite_iUnion fun i => (hPos h0 (hKP hh0)).2.2.2.2 _
  have hmaps : ∀ γ ∈ {γ : Gm L N | ∃ h ∈ K, ac γ h ∈ K},
      (fun i : Fin N => γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) ∈
        Set.pi Set.univ (fun _ => ⋃ i, {v : UpperTheory.V.KT.Lat L N | q h0 v ≤ C * B i}) := by
    rintro γ ⟨h, hh, hγ⟩ i -
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    show q h0 (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) ≤ C * B i
    calc q h0 (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N))
        ≤ C * q h (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) := hC h hh _
      _ = C * q (ac γ h) (Pi.single i 1 : UpperTheory.V.KT.Lat L N) := by rw [hEq]
      _ ≤ C * B i := mul_le_mul_of_nonneg_left (hBd i _ hγ) hC0
  have hinj : Set.InjOn (fun γ : Gm L N => fun i : Fin N => γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N))
      {γ : Gm L N | ∃ h ∈ K, ac γ h ∈ K} := by
    intro a _ b _ hab
    have hinv : (a⁻¹ : Gm L N) = b⁻¹ := by
      apply Units.ext
      ext j i
      have e := congrFun (congrFun hab i) j
      change ((↑(a⁻¹ : GL (Fin N) (𝓞 L)) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ Pi.single i 1) j =
        ((↑(b⁻¹ : GL (Fin N) (𝓞 L)) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ Pi.single i 1) j at e
      simpa [Matrix.mulVec_single_one] using e
    exact inv_injective hinv
  exact Set.Finite.of_finite_image ((Set.Finite.pi fun _ => hF).subset (Set.image_subset_iff.mpr hmaps)) hinj

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
