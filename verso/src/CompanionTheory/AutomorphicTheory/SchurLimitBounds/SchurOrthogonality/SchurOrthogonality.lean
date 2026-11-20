import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.URepSchur

noncomputable section

set_option linter.unusedSectionVars false

namespace CompanionTheory.LimBd.URep

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate

section Families

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/- English proof (translation)
Set `T₀ : H →ₗ[ℂ] Lp ℂ 2 μ` to `{ toFun := fun v => (hΦ v).toLp _ map_add' := fun v w => by`. Rewrite using `[← MemLp.toLp_add]`. Conclude with `MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by simp)`. Use the proof step `map_smul' := fun c v => by`. Rewrite using `[RingHom.id_apply, ← MemLp.toLp_const_smul]`.

Conclude with `MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by simp) }`. Establish `hT₀ : ∀ v, (T₀ v : X → ℂ) =ᵐ[μ] fun x => Φ x v` using `fun v => MemLp.coeFn_toLp (hΦ v)`. Establish `hc : Continuous T₀`. Use `T₀.continuous_of_seq_closed_graph fun u x y hu hy => ?_` and prove the remaining obligations. Take `⟨ns, hns, hae⟩` from `(tendstoInMeasure_of_tendsto_Lp hy).exists_seq_tendsto_ae`.

Establish `hall : ∀ᵐ a ∂μ, ∀ n, (T₀ (u n) : X → ℂ) a = Φ a (u n)` using `ae_all_iff.2 fun n => hT₀ (u n)`. Use `Lp.ext ?_` and prove the remaining obligations. Use `filter_upwards [hae, hall, hT₀ x] with a h1 h2 h3`. Rewrite using `[h3]`. Establish `h4 : Tendsto (fun i => Φ a (u (ns i))) atTop (𝓝 (Φ a x))` using `((Φ a).continuous.tendsto x).comp (hu.comp hns.tendsto_atTop)`.

Use `tendsto_nhds_unique ?_ h4` and prove the remaining obligations. Simplify `h1` using `only [Function.comp_apply, h2]`. Conclude with `⟨⟨T₀, hc⟩, hT₀⟩`.
-/
theorem exists_to_L2 (Φ : X → (H →L[ℂ] ℂ)) (hΦ : ∀ v, MemLp (fun x => Φ x v) 2 μ) :
    ∃ T : H →L[ℂ] Lp ℂ 2 μ, ∀ v, (T v : X → ℂ) =ᵐ[μ] fun x => Φ x v := by
  let T₀ : H →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun v => (hΦ v).toLp _
      map_add' := fun v w => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by simp)
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by simp) }
  have hT₀ : ∀ v, (T₀ v : X → ℂ) =ᵐ[μ] fun x => Φ x v := fun v => MemLp.coeFn_toLp (hΦ v)
  have hc : Continuous T₀ := by
    refine T₀.continuous_of_seq_closed_graph fun u x y hu hy => ?_
    obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hy).exists_seq_tendsto_ae
    have hall : ∀ᵐ a ∂μ, ∀ n, (T₀ (u n) : X → ℂ) a = Φ a (u n) := ae_all_iff.2 fun n => hT₀ (u n)
    refine Lp.ext ?_
    filter_upwards [hae, hall, hT₀ x] with a h1 h2 h3
    rw [h3]
    have h4 : Tendsto (fun i => Φ a (u (ns i))) atTop (𝓝 (Φ a x)) :=
      ((Φ a).continuous.tendsto x).comp (hu.comp hns.tendsto_atTop)
    refine tendsto_nhds_unique ?_ h4
    simpa only [Function.comp_apply, h2] using h1
  exact ⟨⟨T₀, hc⟩, hT₀⟩

/- English proof (translation)
Take `⟨T, hT⟩` from `exists_to_L2 Φ hΦ`. Take `⟨S, hS⟩` from `exists_to_L2 Ψ hΨ`. Use `⟨(ContinuousLinearMap.adjoint S).comp T, fun v v' => ?_⟩` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hT v, hS v'] with x h1 h2`. Rewrite using `[h1, h2]`. Simplify using the standard rewrite rules.
-/
theorem exists_pairing_op (Φ : X → (H →L[ℂ] ℂ)) (hΦ : ∀ v, MemLp (fun x => Φ x v) 2 μ)
    (Ψ : X → (K →L[ℂ] ℂ)) (hΨ : ∀ v, MemLp (fun x => Ψ x v) 2 μ) :
    ∃ A : H →L[ℂ] K, ∀ v v', ∫ x, Φ x v * star (Ψ x v') ∂μ = ⟪v', A v⟫_ℂ := by
  obtain ⟨T, hT⟩ := exists_to_L2 Φ hΦ
  obtain ⟨S, hS⟩ := exists_to_L2 Ψ hΨ
  refine ⟨(ContinuousLinearMap.adjoint S).comp T, fun v v' => ?_⟩
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hT v, hS v'] with x h1 h2
  rw [h1, h2]
  simp

end Families

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def SqInt (μ : Measure G) (π : UnitaryRep G H) : Prop := ∀ v w : H, MemLp (fun g => ⟪w, π g v⟫_ℂ) 2 μ

def pairing (μ : Measure G) (π : UnitaryRep G H) (σ : UnitaryRep G K) (v w : H) (v' w' : K) : ℂ :=
  ∫ g, ⟪w, π g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ

/- English proof (translation)
The claim follows from `(hπ v w).integrable_mul (hσ v' w').star`.
-/
theorem integrable_pairing {π : UnitaryRep G H} {σ : UnitaryRep G K} (hπ : SqInt μ π) (hσ : SqInt μ σ)
    (v w : H) (v' w' : K) : Integrable (fun g => ⟪w, π g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ :=
  (hπ v w).integrable_mul (hσ v' w').star

/- English proof (translation)
Establish `e : Measure.map (· * h) μ = Measure.modularCharacterFun h • μ`. Rewrite using `[Measure.modularCharacterFun_eq_haarScalarFactor μ h]`. Conclude with `Measure.isMulLeftInvariant_eq_smul _ μ`. Use `(measurableEmbedding_mulRight h).integral_map (μ := μ) f` as an intermediate fact. Rewrite using `[← this, e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]`.
-/
theorem integral_mul_right (f : G → ℂ) (h : G) :
    ∫ g, f (g * h) ∂μ = (Measure.modularCharacterFun h : ℝ) * ∫ g, f g ∂μ := by
  have e : Measure.map (· * h) μ = Measure.modularCharacterFun h • μ := by
    rw [Measure.modularCharacterFun_eq_haarScalarFactor μ h]
    exact Measure.isMulLeftInvariant_eq_smul _ μ
  have := (measurableEmbedding_mulRight h).integral_map (μ := μ) f
  rw [← this, e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_mul_right]`. Simplify using `only [UnitaryRep.map_mul_apply]`.
-/
theorem pairing_right (π : UnitaryRep G H) (σ : UnitaryRep G K) (v w : H) (v' w' : K) (h : G) :
    pairing μ π σ (π h v) w (σ h v') w' = (Measure.modularCharacterFun h : ℝ) * pairing μ π σ v w v' w' := by
  unfold pairing
  rw [← integral_mul_right]
  simp only [UnitaryRep.map_mul_apply]

/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_mul_left_eq_self (μ := μ) (fun g => ⟪w, π g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) h⁻¹]`. Simplify using `only [UnitaryRep.map_mul_apply, UnitaryRep.inner_map_left]`.
-/
theorem pairing_left (π : UnitaryRep G H) (σ : UnitaryRep G K) (v w : H) (v' w' : K) (h : G) :
    pairing μ π σ v (π h w) v' (σ h w') = pairing μ π σ v w v' w' := by
  unfold pairing
  rw [← integral_mul_left_eq_self (μ := μ) (fun g => ⟪w, π g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) h⁻¹]
  simp only [UnitaryRep.map_mul_apply, UnitaryRep.inner_map_left]

/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_complex_ofReal]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[Complex.star_def, Complex.mul_conj']`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem pairing_self (π : UnitaryRep G H) (v w : H) :
    pairing μ π π v w v w = ((∫ g, ‖⟪w, π g v⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  unfold pairing
  rw [← integral_complex_ofReal]
  congr 1
  funext g
  rw [Complex.star_def, Complex.mul_conj']
  push_cast
  rfl

/- English proof (translation)
Establish `hc : Continuous fun g => ‖⟪v, π g v⟫_ℂ‖ ^ 2` using `((continuous_const.inner (π.continuous_orbit v)).norm).pow 2`. Establish `hi : Integrable (fun g => ‖⟪v, π g v⟫_ℂ‖ ^ 2) μ` using `(hπ v v).norm.integrable_sq`. Rewrite using `[integral_pos_iff_support_of_nonneg (fun g => by positivity) hi]`. Use `hc.isOpen_support.measure_pos μ ⟨1, ?_⟩` and prove the remaining obligations. Simplify using `[hv]`.
-/
theorem integral_sq_pos {π : UnitaryRep G H} (hπ : SqInt μ π) {v : H} (hv : v ≠ 0) :
    0 < ∫ g, ‖⟪v, π g v⟫_ℂ‖ ^ 2 ∂μ := by
  have hc : Continuous fun g => ‖⟪v, π g v⟫_ℂ‖ ^ 2 :=
    ((continuous_const.inner (π.continuous_orbit v)).norm).pow 2
  have hi : Integrable (fun g => ‖⟪v, π g v⟫_ℂ‖ ^ 2) μ := (hπ v v).norm.integrable_sq
  rw [integral_pos_iff_support_of_nonneg (fun g => by positivity) hi]
  refine hc.isOpen_support.measure_pos μ ⟨1, ?_⟩
  simp [hv]

/- English proof (translation)
The claim follows from `exists_pairing_op (fun g => (innerSL ℂ w).comp (π g)) (fun v => hπ v w) (fun g => (innerSL ℂ w').comp (σ g)) (fun v => hσ v w')`.
-/
theorem exists_op_right {π : UnitaryRep G H} {σ : UnitaryRep G K} (hπ : SqInt μ π) (hσ : SqInt μ σ)
    (w : H) (w' : K) : ∃ A : H →L[ℂ] K, ∀ v v', pairing μ π σ v w v' w' = ⟪v', A v⟫_ℂ :=
  exists_pairing_op (fun g => (innerSL ℂ w).comp (π g)) (fun v => hπ v w)
    (fun g => (innerSL ℂ w').comp (σ g)) (fun v => hσ v w')

/- English proof (translation)
Take `⟨A, hA⟩` from `exists_pairing_op (μ := μ) (fun g => innerSL ℂ (π g v)) (fun w => by simpa [Pi.star_def] using (hπ v w).star) (fun g => innerSL ℂ (σ g v')) (fun w => by simpa [Pi.star_def] using (hσ v' w).star)`. Establish `key : ∀ w w', pairing μ π σ v w v' w' = ⟪A w, w'⟫_ℂ`. Introduce `w w'`. Rewrite using `[← inner_conj_symm, ← hA, ← integral_conj]`. Unfold `pairing`.

Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules. Use `⟨A, fun h w => ?_, key⟩` and prove the remaining obligations. Use `ext_inner_right ℂ fun w' => ?_` and prove the remaining obligations.

Rewrite using `[UnitaryRep.inner_map_left, ← key, ← key, ← pairing_left π σ v w v' _ h]`. Simplify using the standard rewrite rules.
-/
theorem exists_op_left {π : UnitaryRep G H} {σ : UnitaryRep G K} (hπ : SqInt μ π) (hσ : SqInt μ σ)
    (v : H) (v' : K) : ∃ A ∈ π.intertwiners σ, ∀ w w', pairing μ π σ v w v' w' = ⟪A w, w'⟫_ℂ := by
  obtain ⟨A, hA⟩ := exists_pairing_op (μ := μ) (fun g => innerSL ℂ (π g v))
    (fun w => by simpa [Pi.star_def] using (hπ v w).star) (fun g => innerSL ℂ (σ g v'))
    (fun w => by simpa [Pi.star_def] using (hσ v' w).star)
  have key : ∀ w w', pairing μ π σ v w v' w' = ⟪A w, w'⟫_ℂ := by
    intro w w'
    rw [← inner_conj_symm, ← hA, ← integral_conj]
    unfold pairing
    congr 1
    funext g
    simp
  refine ⟨A, fun h w => ?_, key⟩
  refine ext_inner_right ℂ fun w' => ?_
  rw [UnitaryRep.inner_map_left, ← key, ← key, ← pairing_left π σ v w v' _ h]
  simp

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_ne (0 : H)`. Take `⟨A, hA⟩` from `exists_op_right hπ hπ v v`. Use `set s := ∫ g, ‖⟪v, π g v⟫_ℂ‖ ^ 2 ∂μ`. Establish `hs : 0 < s` using `integral_sq_pos hπ hv`. Establish `hb : ∀ g : G, (Measure.modularCharacterFun g : ℝ) ≤ ‖A‖ * ‖v‖ ^ 2 / s`.

Introduce `g`. Establish `e` using `pairing_right (μ := μ) π π v v v v g`. Rewrite `e` using `[hA, pairing_self]`. Establish `e2` using `congrArg norm e`. Rewrite `e2` using `[norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _), Real.norm_of_nonneg hs.le]`.

Rewrite using `[le_div_iff₀ hs, ← e2]`. Combine the equalities or inequalities in the displayed calculation. Establish `hle : ∀ g : G, (Measure.modularCharacterFun g : ℝ) ≤ 1`. Introduce `g`. Assume the negation of the conclusion as `hlt`.

Use `push Not at hlt`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (‖A‖ * ‖v‖ ^ 2 / s) hlt`. Use `hb (g ^ n)` as an intermediate fact. Establish `e : Measure.modularCharacterFun (g ^ n) = Measure.modularCharacterFun g ^ n` using `map_pow (Measure.modularCharacter (G := G)) g n`. Rewrite `this` using `[e]`.

Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm : (Measure.modularCharacterFun h : ℝ) * Measure.modularCharacterFun h⁻¹ = 1`. Rewrite using `[← NNReal.coe_mul, ← Measure.modularCharacterFun_map_mul, mul_inv_cancel, Measure.modularCharacterFun_map_one, NNReal.coe_one]`. Establish `h1` using `hle h`.

Establish `h2` using `hle h⁻¹`. Establish `h3 : (0 : ℝ) ≤ Measure.modularCharacterFun h` using `NNReal.coe_nonneg _`. Establish `: (Measure.modularCharacterFun h : ℝ) = 1` using `by nlinarith`. Conclude with `this` after adjusting the coercions.
-/
theorem modular_eq_one {π : UnitaryRep G H} [Nontrivial H] (hπ : SqInt μ π) (h : G) :
    Measure.modularCharacterFun h = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  obtain ⟨A, hA⟩ := exists_op_right hπ hπ v v
  set s := ∫ g, ‖⟪v, π g v⟫_ℂ‖ ^ 2 ∂μ
  have hs : 0 < s := integral_sq_pos hπ hv
  have hb : ∀ g : G, (Measure.modularCharacterFun g : ℝ) ≤ ‖A‖ * ‖v‖ ^ 2 / s := by
    intro g
    have e := pairing_right (μ := μ) π π v v v v g
    rw [hA, pairing_self] at e
    have e2 := congrArg norm e
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _),
      Real.norm_of_nonneg hs.le] at e2
    rw [le_div_iff₀ hs, ← e2]
    calc ‖⟪π g v, A (π g v)⟫_ℂ‖ ≤ ‖π g v‖ * ‖A (π g v)‖ := norm_inner_le_norm _ _
      _ ≤ ‖π g v‖ * (‖A‖ * ‖π g v‖) := by gcongr; exact A.le_opNorm _
      _ = ‖A‖ * ‖v‖ ^ 2 := by simp; ring
  have hle : ∀ g : G, (Measure.modularCharacterFun g : ℝ) ≤ 1 := by
    intro g
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖A‖ * ‖v‖ ^ 2 / s) hlt
    have := hb (g ^ n)
    have e : Measure.modularCharacterFun (g ^ n) = Measure.modularCharacterFun g ^ n :=
      map_pow (Measure.modularCharacter (G := G)) g n
    rw [e] at this
    push_cast at this
    linarith
  have hm : (Measure.modularCharacterFun h : ℝ) * Measure.modularCharacterFun h⁻¹ = 1 := by
    rw [← NNReal.coe_mul, ← Measure.modularCharacterFun_map_mul, mul_inv_cancel,
      Measure.modularCharacterFun_map_one, NNReal.coe_one]
  have h1 := hle h
  have h2 := hle h⁻¹
  have h3 : (0 : ℝ) ≤ Measure.modularCharacterFun h := NNReal.coe_nonneg _
  have : (Measure.modularCharacterFun h : ℝ) = 1 := by nlinarith
  exact_mod_cast this

/- English proof (translation)
Take `⟨A, hA⟩` from `exists_op_right hπ hσ w w'`. Use `⟨A, fun h v => ?_, hA⟩` and prove the remaining obligations. Use `ext_inner_left ℂ fun v' => ?_` and prove the remaining obligations. Establish `e` using `pairing_right (μ := μ) π σ v w (σ h⁻¹ v') w' h`. Rewrite `e` using `[modular_eq_one hπ h]`.

Rewrite using `[UnitaryRep.inner_map_right, ← hA, ← hA]`. Simplify using `using e`.
-/
theorem exists_op_right' {π : UnitaryRep G H} {σ : UnitaryRep G K} [Nontrivial H] (hπ : SqInt μ π)
    (hσ : SqInt μ σ) (w : H) (w' : K) :
    ∃ A ∈ π.intertwiners σ, ∀ v v', pairing μ π σ v w v' w' = ⟪v', A v⟫_ℂ := by
  obtain ⟨A, hA⟩ := exists_op_right hπ hσ w w'
  refine ⟨A, fun h v => ?_, hA⟩
  refine ext_inner_left ℂ fun v' => ?_
  have e := pairing_right (μ := μ) π σ v w (σ h⁻¹ v') w' h
  rw [modular_eq_one hπ h] at e
  rw [UnitaryRep.inner_map_right, ← hA, ← hA]
  simpa using e

/- English proof (translation)
Use `hirr.1` as an intermediate fact. Take `⟨u₀, hu₀⟩` from `exists_ne (0 : H)`. Set `u : H` to `((‖u₀‖⁻¹ : ℝ) : ℂ) • u₀`. Establish `hn : ‖u‖ = 1`. Simplify using `[u, norm_smul, hu₀]`.

Establish `hu : u ≠ 0` using `fun h => by simp [h] at hn`. Establish `huu : ⟪u, u⟫_ℂ = 1` using `by rw [inner_self_eq_norm_sq_to_K, hn]; simp`. Use `set s := ∫ g, ‖⟪u, π g u⟫_ℂ‖ ^ 2 ∂μ`. Establish `hs : 0 < s` using `integral_sq_pos hπ hu`. Establish `hL : ∀ v v', ∃ c : ℂ, ∀ w w', pairing μ π π v w v' w' = c * ⟪w, w'⟫_ℂ`.

Introduce `v v'`. Take `⟨A, hA, h⟩` from `exists_op_left hπ hπ v v'`. Take `⟨c, rfl⟩` from `hirr.exists_eq_smul_one hA`. Conclude with `⟨conj c, fun w w' => by rw [h]; simp [mul_comm]⟩`. Take `⟨A, hA, h⟩` from `exists_op_right' hπ hπ u u`.

Take `⟨e, rfl⟩` from `hirr.exists_eq_smul_one hA`. Establish `he : ∀ v v', pairing μ π π v u v' u = e * ⟪v', v⟫_ℂ` using `fun v v' => by`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Establish `hes : e = (s : ℂ)`.

Use `he u u` as an intermediate fact. Rewrite `this` using `[huu, mul_one, pairing_self]`. Conclude with `this.symm`. Use `⟨s⁻¹, inv_pos.2 hs, fun v w v' w' => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hL v v'`.

Establish `hce : c = e * ⟪v', v⟫_ℂ` using `by rw [← he, hc, huu, mul_one]`. Rewrite using `[hc, hce, hes]`. Use `push_cast`. Rewrite using `[div_inv_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem schur_orthogonality {π : UnitaryRep G H} (hirr : π.IsIrreducible) (hπ : SqInt μ π) :
    ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H, pairing μ π π v w v' w' = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
  have := hirr.1
  obtain ⟨u₀, hu₀⟩ := exists_ne (0 : H)
  let u : H := ((‖u₀‖⁻¹ : ℝ) : ℂ) • u₀
  have hn : ‖u‖ = 1 := by
    simp [u, norm_smul, hu₀]
  have hu : u ≠ 0 := fun h => by simp [h] at hn
  have huu : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hn]; simp
  set s := ∫ g, ‖⟪u, π g u⟫_ℂ‖ ^ 2 ∂μ
  have hs : 0 < s := integral_sq_pos hπ hu
  have hL : ∀ v v', ∃ c : ℂ, ∀ w w', pairing μ π π v w v' w' = c * ⟪w, w'⟫_ℂ := by
    intro v v'
    obtain ⟨A, hA, h⟩ := exists_op_left hπ hπ v v'
    obtain ⟨c, rfl⟩ := hirr.exists_eq_smul_one hA
    exact ⟨conj c, fun w w' => by rw [h]; simp [mul_comm]⟩
  obtain ⟨A, hA, h⟩ := exists_op_right' hπ hπ u u
  obtain ⟨e, rfl⟩ := hirr.exists_eq_smul_one hA
  have he : ∀ v v', pairing μ π π v u v' u = e * ⟪v', v⟫_ℂ := fun v v' => by
    rw [h]; simp
  have hes : e = (s : ℂ) := by
    have := he u u
    rw [huu, mul_one, pairing_self] at this
    exact this.symm
  refine ⟨s⁻¹, inv_pos.2 hs, fun v w v' w' => ?_⟩
  obtain ⟨c, hc⟩ := hL v v'
  have hce : c = e * ⟪v', v⟫_ℂ := by rw [← he, hc, huu, mul_one]
  rw [hc, hce, hes]
  push_cast
  rw [div_inv_eq_mul]
  ring

/- English proof (translation)
Take `⟨A, hA, h⟩` from `exists_op_left hπ hσ v v'`. Rewrite using `[h, hπi.eq_zero_of_not_isEquivalent hσi hne hA]`. Simplify using the standard rewrite rules.
-/
theorem pairing_eq_zero {π : UnitaryRep G H} {σ : UnitaryRep G K} (hπi : π.IsIrreducible)
    (hσi : σ.IsIrreducible) (hπ : SqInt μ π) (hσ : SqInt μ σ) (hne : ¬ π.IsEquivalent σ)
    (v w : H) (v' w' : K) : pairing μ π σ v w v' w' = 0 := by
  obtain ⟨A, hA, h⟩ := exists_op_left hπ hσ v v'
  rw [h, hπi.eq_zero_of_not_isEquivalent hσi hne hA]
  simp

end Group

end CompanionTheory.LimBd.URep
