import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft

open MeasureTheory Matrix Topology Filter
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.NilUnimod

section Abstract

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

/- English proof (translation)
Establish `h` using `Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ`. Rewrite `h` using `[← Measure.modularCharacterFun_eq_haarScalarFactor μ g]`. Conclude with `h`.
-/
theorem map_mul_right (μ : Measure H) [μ.IsHaarMeasure] (g : H) :
    Measure.map (· * g) μ = Measure.modularCharacter g • μ := by
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ
  rw [← Measure.modularCharacterFun_eq_haarScalarFactor μ g] at h
  exact h

/- English proof (translation)
Set `ν : Measure H` to `Measure.haar`. Establish `hm : Measurable φ` using `h1.measurable`. Use `haveI : (Measure.map φ ν).IsHaarMeasure := MulEquiv.isHaarMeasure_map ν φ h1 h2`. Establish `e : Measure.map (· * φ g) (Measure.map φ ν) = Measure.modularCharacter g • Measure.map φ ν`. Rewrite using `[Measure.map_map (measurable_mul_const _) hm]`.

Establish `: (fun x => x * φ g) ∘ φ = φ ∘ (fun x => x * g)`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Rewrite using `[this, ← Measure.map_map hm (measurable_mul_const _), map_mul_right ν g, Measure.map_smul]`. Use `show Measure.modularCharacterFun (φ g) = Measure.modularCharacter g`.

Establish `hs : ∀ (m : Measure H) [IsFiniteMeasureOnCompacts m] [m.IsMulLeftInvariant], m = Measure.modularCharacter g • Measure.map φ ν → Measure.haarScalarFactor m (Measure.map φ ν) = Measure.modularCharacter g`. Introduce `m _ _ h`. Substitute `h` using the available equality. Rewrite using `[Measure.haarScalarFactor_smul, Measure.haarScalarFactor_self]`. Simplify using the standard rewrite rules.

Rewrite using `[Measure.modularCharacterFun_eq_haarScalarFactor (Measure.map φ ν) (φ g)]`. Conclude with `hs _ e`.
-/
theorem modular_comp (φ : H ≃* H) (h1 : Continuous φ) (h2 : Continuous φ.symm) (g : H) :
    Measure.modularCharacter (φ g) = Measure.modularCharacter g := by
  let ν : Measure H := Measure.haar
  have hm : Measurable φ := h1.measurable
  haveI : (Measure.map φ ν).IsHaarMeasure := MulEquiv.isHaarMeasure_map ν φ h1 h2
  have e : Measure.map (· * φ g) (Measure.map φ ν) =
      Measure.modularCharacter g • Measure.map φ ν := by
    rw [Measure.map_map (measurable_mul_const _) hm]
    have : (fun x => x * φ g) ∘ φ = φ ∘ (fun x => x * g) := by
      funext x
      simp
    rw [this, ← Measure.map_map hm (measurable_mul_const _), map_mul_right ν g,
      Measure.map_smul]
  show Measure.modularCharacterFun (φ g) = Measure.modularCharacter g
  have hs : ∀ (m : Measure H) [IsFiniteMeasureOnCompacts m] [m.IsMulLeftInvariant],
      m = Measure.modularCharacter g • Measure.map φ ν →
        Measure.haarScalarFactor m (Measure.map φ ν) = Measure.modularCharacter g := by
    intro m _ _ h
    subst h
    rw [Measure.haarScalarFactor_smul, Measure.haarScalarFactor_self]
    simp
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.map φ ν) (φ g)]
  exact hs _ e

/- English proof (translation)
Set `ν : Measure H` to `Measure.haar`. Take `⟨K, hK, h1⟩` from `exists_compact_mem_nhds (1 : H)`. Establish `hA : IsCompact (K * K)` using `hK.mul hK`. Establish `hA1 : K * K ∈ 𝓝 (1 : H)` using `mem_of_superset h1 (fun x hx => ⟨x, hx, 1, mem_of_mem_nhds h1, by simp⟩)`. Establish `hKp : 0 < ν K` using `Measure.measure_pos_of_mem_nhds ν h1`.

Establish `hAp : 0 < ν (K * K)` using `Measure.measure_pos_of_mem_nhds ν hA1`. Establish `hKf : ν K ≠ ∞` using `hK.measure_lt_top.ne`. Establish `hAf : ν (K * K) ≠ ∞` using `hA.measure_lt_top.ne`. Use `⟨(ν K / ν (K * K)).toNNReal, ?_, K, h1, fun g hg => ?_⟩` and prove the remaining obligations. Conclude with `ENNReal.toNNReal_pos (ENNReal.div_pos hKp.ne' hAf).ne' (ENNReal.div_ne_top hKf hAp.ne')`.

Establish `h2 : ν K ≤ Measure.modularCharacter g * ν (K * K)`. Establish `h3` using `congrArg (fun m : Measure H => m (K * K)) (map_mul_right ν g)`. Simplify using `only [Measure.coe_nnreal_smul_apply] at h3`. Rewrite `h3` using `[Measure.map_apply (measurable_mul_const _) hA.isClosed.measurableSet]`. Rewrite using `[← h3]`.

Conclude with `measure_mono fun x hx => ⟨x, hx, g, hg, rfl⟩`. Establish `h4 : ν K / ν (K * K) ≤ Measure.modularCharacter g` using `ENNReal.div_le_of_le_mul h2`. Establish `h5` using `ENNReal.toNNReal_mono ENNReal.coe_ne_top h4`. Simplify using `using h5`.
-/
theorem modular_lower : ∃ c : ℝ≥0, 0 < c ∧ ∃ K ∈ 𝓝 (1 : H), ∀ g ∈ K,
    c ≤ Measure.modularCharacter g := by
  let ν : Measure H := Measure.haar
  obtain ⟨K, hK, h1⟩ := exists_compact_mem_nhds (1 : H)
  have hA : IsCompact (K * K) := hK.mul hK
  have hA1 : K * K ∈ 𝓝 (1 : H) := mem_of_superset h1 (fun x hx => ⟨x, hx, 1, mem_of_mem_nhds h1, by simp⟩)
  have hKp : 0 < ν K := Measure.measure_pos_of_mem_nhds ν h1
  have hAp : 0 < ν (K * K) := Measure.measure_pos_of_mem_nhds ν hA1
  have hKf : ν K ≠ ∞ := hK.measure_lt_top.ne
  have hAf : ν (K * K) ≠ ∞ := hA.measure_lt_top.ne
  refine ⟨(ν K / ν (K * K)).toNNReal, ?_, K, h1, fun g hg => ?_⟩
  · exact ENNReal.toNNReal_pos (ENNReal.div_pos hKp.ne' hAf).ne' (ENNReal.div_ne_top hKf hAp.ne')
  · have h2 : ν K ≤ Measure.modularCharacter g * ν (K * K) := by
      have h3 := congrArg (fun m : Measure H => m (K * K)) (map_mul_right ν g)
      simp only [Measure.coe_nnreal_smul_apply] at h3
      rw [Measure.map_apply (measurable_mul_const _) hA.isClosed.measurableSet] at h3
      rw [← h3]
      exact measure_mono fun x hx => ⟨x, hx, g, hg, rfl⟩
    have h4 : ν K / ν (K * K) ≤ Measure.modularCharacter g :=
      ENNReal.div_le_of_le_mul h2
    have h5 := ENNReal.toNNReal_mono ENNReal.coe_ne_top h4
    simpa using h5

/- English proof (translation)
Take `⟨c, c0, K, hK, hl⟩` from `modular_lower (H := H)`. Establish `key : ∀ v : H, 1 ≤ Measure.modularCharacter v` using `fun v => by`. Assume the negation of the conclusion as `hlt`. Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one c0 (not_le.1 hlt)`. Take `⟨φ, h1, h2, h3⟩` from `hc (v ^ k) K hK`.

Establish `h4` using `hl _ h3`. Rewrite `h4` using `[modular_comp φ h1 h2, map_pow]`. Conclude with `absurd hk (not_lt.2 h4)`. Establish `h1 : Measure.modularCharacter g * Measure.modularCharacter g⁻¹ = 1`. Rewrite using `[← map_mul]`.

Simplify using the standard rewrite rules. Conclude with `le_antisymm (by`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem modular_eq_one
    (hc : ∀ (u : H), ∀ C ∈ 𝓝 (1 : H), ∃ φ : H ≃* H, Continuous φ ∧ Continuous φ.symm ∧ φ u ∈ C)
    (g : H) : Measure.modularCharacter g = 1 := by
  obtain ⟨c, c0, K, hK, hl⟩ := modular_lower (H := H)
  have key : ∀ v : H, 1 ≤ Measure.modularCharacter v := fun v => by
    by_contra hlt
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one c0 (not_le.1 hlt)
    obtain ⟨φ, h1, h2, h3⟩ := hc (v ^ k) K hK
    have h4 := hl _ h3
    rw [modular_comp φ h1 h2, map_pow] at h4
    exact absurd hk (not_lt.2 h4)
  have h1 : Measure.modularCharacter g * Measure.modularCharacter g⁻¹ = 1 := by
    rw [← map_mul]
    simp
  exact le_antisymm (by
    calc Measure.modularCharacter g ≤ Measure.modularCharacter g * Measure.modularCharacter g⁻¹ :=
          le_mul_of_one_le_right zero_le (key _)
      _ = 1 := h1) (key g)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun g => by rw [map_mul_right ν g, modular_eq_one hc g, one_smul]⟩`.
-/
theorem rightInvariant
    (hc : ∀ (u : H), ∀ C ∈ 𝓝 (1 : H), ∃ φ : H ≃* H, Continuous φ ∧ Continuous φ.symm ∧ φ u ∈ C)
    (ν : Measure H) [ν.IsHaarMeasure] : ν.IsMulRightInvariant :=
  ⟨fun g => by rw [map_mul_right ν g, modular_eq_one hc g, one_smul]⟩

end Abstract

section Frame

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC (nilSet)

variable {n : ℕ}

/- English proof (translation)
Take `⟨C, hC⟩` from `Submodule.exists_isCompl W`. Set `f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)` to `W.subtype ∘ₗ Submodule.linearProjOfIsCompl W C hC`. Use `⟨LinearMap.toMatrix' f, fun v => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Simplify using `[f]`.

Rewrite using `[LinearMap.toMatrix'_mulVec]`. Conclude with `congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hC ⟨v, hv⟩)`.
-/
theorem exists_proj (W : Submodule ℂ (Fin n → ℂ)) :
    ∃ P : Mat n, (∀ v, P *ᵥ v ∈ W) ∧ ∀ v ∈ W, P *ᵥ v = v := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  let f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := W.subtype ∘ₗ Submodule.linearProjOfIsCompl W C hC
  refine ⟨LinearMap.toMatrix' f, fun v => ?_, fun v hv => ?_⟩
  · rw [LinearMap.toMatrix'_mulVec]
    simp [f]
  · rw [LinearMap.toMatrix'_mulVec]
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hC ⟨v, hv⟩)

/- English proof (translation)
The claim follows from `Matrix.toLin'.injective (LinearMap.ext h)`.
-/
theorem mat_ext {A B : Mat n} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext h)

structure Tri (P Q R : Mat n) : Prop where
  sum : P + Q + R = 1
  pp : P * P = P
  qq : Q * Q = Q
  rr : R * R = R
  pq : P * Q = 0
  pr : P * R = 0
  qp : Q * P = 0
  qr : Q * R = 0
  rp : R * P = 0
  rq : R * Q = 0

/- English proof (translation)
Take `⟨E, hE1, hE2⟩` from `exists_proj W₁`. Take `⟨F, hF1, hF2⟩` from `exists_proj W₂`. Establish `hFF : F * F = F` using `mat_ext fun v => by`. Rewrite using `[← Matrix.mulVec_mulVec, hF2 _ (hF1 v)]`. Establish `hP1 : ∀ v, (E * F) *ᵥ v ∈ W₁` using `fun v => by`.

Rewrite using `[← Matrix.mulVec_mulVec]`. Conclude with `hE1 _`. Establish `hP2 : ∀ v ∈ W₁, (E * F) *ᵥ v = v` using `fun v hv => by`. Rewrite using `[← Matrix.mulVec_mulVec, hF2 v (h12 hv), hE2 v hv]`. Establish `hPF : (E * F) * F = E * F` using `by rw [mul_assoc, hFF]`.

Establish `hFP : F * (E * F) = E * F` using `mat_ext fun v => by`. Rewrite using `[← Matrix.mulVec_mulVec, hF2 _ (h12 (hP1 v))]`. Establish `hPP : (E * F) * (E * F) = E * F` using `mat_ext fun v => by`. Rewrite using `[← Matrix.mulVec_mulVec, hP2 _ (hP1 v)]`. Generalize the expression as in `E * F = P at hP1 hP2 hPF hFP hPP`.

Use `⟨P, F - P, 1 - F, ⟨by abel, hPP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun v => ?_, fun v => ?_⟩` and prove the remaining obligations. Simplify using `[sub_mul, mul_sub, hFF, hPF, hFP, hPP]`. Simplify using `[sub_mul, mul_sub, hFF]`. Simplify using `[sub_mul, mul_sub, hPF, hPP]`. Simplify using `[sub_mul, mul_sub, hPF]`.

Simplify using `[sub_mul, mul_sub, hFP, hPP]`. Simplify using `[sub_mul, mul_sub, hFF, hFP, hPF]`. Simplify using `[sub_mul, mul_sub, hFP]`. Simplify using `[sub_mul, mul_sub, hFF, hPF, hFP]`. Simplify using `only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]`.

Prove the components needed by the constructor for the conclusion. Introduce `hv`. Rewrite using `[hP2 v hv, hF2 v (h12 hv)]`. Conclude with `⟨rfl, rfl⟩`. Introduce and unpack `⟨h1, h2⟩`.

Rewrite `h1` using `[← h2]`. Establish `: P *ᵥ v = v` using `by rw [← h1, h2]`. Rewrite using `[← this]`. Conclude with `hP1 v`. Simplify using `only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]`.

Prove the components needed by the constructor for the conclusion. Introduce `hv`. Conclude with `(hF2 v hv).symm`. Introduce `h`. Rewrite using `[h]`.

Conclude with `hF1 v`.
-/
theorem exists_tri {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (h12 : W₁ ≤ W₂) :
    ∃ P Q R : Mat n, Tri P Q R ∧ (∀ v, v ∈ W₁ ↔ Q *ᵥ v = 0 ∧ R *ᵥ v = 0) ∧
      ∀ v, v ∈ W₂ ↔ R *ᵥ v = 0 := by
  obtain ⟨E, hE1, hE2⟩ := exists_proj W₁
  obtain ⟨F, hF1, hF2⟩ := exists_proj W₂
  have hFF : F * F = F := mat_ext fun v => by
    rw [← Matrix.mulVec_mulVec, hF2 _ (hF1 v)]
  have hP1 : ∀ v, (E * F) *ᵥ v ∈ W₁ := fun v => by
    rw [← Matrix.mulVec_mulVec]
    exact hE1 _
  have hP2 : ∀ v ∈ W₁, (E * F) *ᵥ v = v := fun v hv => by
    rw [← Matrix.mulVec_mulVec, hF2 v (h12 hv), hE2 v hv]
  have hPF : (E * F) * F = E * F := by rw [mul_assoc, hFF]
  have hFP : F * (E * F) = E * F := mat_ext fun v => by
    rw [← Matrix.mulVec_mulVec, hF2 _ (h12 (hP1 v))]
  have hPP : (E * F) * (E * F) = E * F := mat_ext fun v => by
    rw [← Matrix.mulVec_mulVec, hP2 _ (hP1 v)]
  generalize E * F = P at hP1 hP2 hPF hFP hPP
  refine ⟨P, F - P, 1 - F, ⟨by abel, hPP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun v => ?_, fun v => ?_⟩
  · simp [sub_mul, mul_sub, hFF, hPF, hFP, hPP]
  · simp [sub_mul, mul_sub, hFF]
  · simp [sub_mul, mul_sub, hPF, hPP]
  · simp [sub_mul, mul_sub, hPF]
  · simp [sub_mul, mul_sub, hFP, hPP]
  · simp [sub_mul, mul_sub, hFF, hFP, hPF]
  · simp [sub_mul, mul_sub, hFP]
  · simp [sub_mul, mul_sub, hFF, hPF, hFP]
  · simp only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    constructor
    · intro hv
      rw [hP2 v hv, hF2 v (h12 hv)]
      exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      rw [← h2] at h1
      have : P *ᵥ v = v := by rw [← h1, h2]
      rw [← this]
      exact hP1 v
  · simp only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    constructor
    · intro hv
      exact (hF2 v hv).symm
    · intro h
      rw [h]
      exact hF1 v

def aM (P Q R : Mat n) (t s : ℂ) : Mat n := t • P + Q + s • R

/- English proof (translation)
Simplify using `only [aM, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h.pp, h.qq, h.rr, h.pq, h.pr, h.qp, h.qr, h.rp, h.rq, smul_zero, add_zero, zero_add, smul_smul]`. Rewrite using `[mul_comm t' t, mul_comm s' s]`.
-/
theorem aM_mul {P Q R : Mat n} (h : Tri P Q R) (t s t' s' : ℂ) :
    aM P Q R t s * aM P Q R t' s' = aM P Q R (t * t') (s * s') := by
  simp only [aM, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h.pp, h.qq, h.rr, h.pq, h.pr,
    h.qp, h.qr, h.rp, h.rq, smul_zero, add_zero, zero_add, smul_smul]
  rw [mul_comm t' t, mul_comm s' s]

/- English proof (translation)
Simplify using `[aM, h.sum]`.
-/
theorem aM_one {P Q R : Mat n} (h : Tri P Q R) : aM P Q R 1 1 = 1 := by
  simp [aM, h.sum]

def gA {P Q R : Mat n} (h : Tri P Q R) (t : ℂˣ) : G n where
  val := aM P Q R t (t⁻¹ : ℂˣ)
  inv := aM P Q R (t⁻¹ : ℂˣ) t
  val_inv := by rw [aM_mul h]; simp [aM_one h]
  inv_val := by rw [aM_mul h]; simp [aM_one h]

/- English proof (translation)
Take `⟨ha, hb, hc⟩` from `hu`. Establish `e : ∀ v, ((g * u * g⁻¹).val - 1) *ᵥ v = g.val *ᵥ ((u.val - 1) *ᵥ ((g⁻¹).val *ᵥ v))` using `fun v => by`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Use `congr 1`. Establish `: g.val * (g⁻¹).val = 1` using `by rw [← Units.val_mul]; simp`.

Simplify using `only [Units.val_mul, mul_sub, sub_mul, mul_one, this, mul_assoc]`. Use `⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `h2 _ (ha _)`. Rewrite using `[e]`.

Conclude with `h1 _ (hb _ (h2' _ hv))`. Rewrite using `[e, hc _ (h1' _ hv)]`. Simplify using the standard rewrite rules.
-/
theorem conj_mem_nilSet {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (g : G n)
    (h1 : ∀ v ∈ W₁, g.val *ᵥ v ∈ W₁) (h2 : ∀ v ∈ W₂, g.val *ᵥ v ∈ W₂)
    (h1' : ∀ v ∈ W₁, (g⁻¹).val *ᵥ v ∈ W₁) (h2' : ∀ v ∈ W₂, (g⁻¹).val *ᵥ v ∈ W₂)
    {u : G n} (hu : u ∈ nilSet W₁ W₂) : g * u * g⁻¹ ∈ nilSet W₁ W₂ := by
  obtain ⟨ha, hb, hc⟩ := hu
  have e : ∀ v, ((g * u * g⁻¹).val - 1) *ᵥ v = g.val *ᵥ ((u.val - 1) *ᵥ ((g⁻¹).val *ᵥ v)) := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    have : g.val * (g⁻¹).val = 1 := by rw [← Units.val_mul]; simp
    simp only [Units.val_mul, mul_sub, sub_mul, mul_one, this, mul_assoc]
  refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [e]
    exact h2 _ (ha _)
  · rw [e]
    exact h1 _ (hb _ (h2' _ hv))
  · rw [e, hc _ (h1' _ hv)]
    simp

/- English proof (translation)
Establish `hc : ∀ v : Fin n → ℂ, Continuous fun u : G n => (u.val - 1) *ᵥ v` using `fun v => Continuous.matrix_mulVec (Units.continuous_val.sub continuous_const) continuous_const`. Establish `c₁ : IsClosed (W₁ : Set (Fin n → ℂ))` using `W₁.closed_of_finiteDimensional`. Establish `c₂ : IsClosed (W₂ : Set (Fin n → ℂ))` using `W₂.closed_of_finiteDimensional`. Simplify using `only [nilSet, Set.setOf_and, Set.setOf_forall]`. Conclude with `(isClosed_iInter fun v => c₂.preimage (hc v)).inter ((isClosed_iInter fun v => isClosed_iInter fun _ => c₁.preimage (hc v)).inter (isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_eq (hc v) continuous_const))`.
-/
theorem isClosed_nilSet (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) : IsClosed (nilSet W₁ W₂) := by
  have hc : ∀ v : Fin n → ℂ, Continuous fun u : G n => (u.val - 1) *ᵥ v := fun v =>
    Continuous.matrix_mulVec (Units.continuous_val.sub continuous_const) continuous_const
  have c₁ : IsClosed (W₁ : Set (Fin n → ℂ)) := W₁.closed_of_finiteDimensional
  have c₂ : IsClosed (W₂ : Set (Fin n → ℂ)) := W₂.closed_of_finiteDimensional
  simp only [nilSet, Set.setOf_and, Set.setOf_forall]
  exact (isClosed_iInter fun v => c₂.preimage (hc v)).inter
    ((isClosed_iInter fun v => isClosed_iInter fun _ => c₁.preimage (hc v)).inter
      (isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_eq (hc v) continuous_const))

end Frame

section Main

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC (nilSet)

variable {n : ℕ}

/- English proof (translation)
Take `⟨ha, hb, hc⟩` from `hu`. Use `set X : Mat n := u.val - 1 with hX`. Establish `hRv : ∀ A : Mat n, R * A = 0 ↔ ∀ v, A *ᵥ v ∈ W₂` using `fun A => by`. Prove the components needed by the constructor for the conclusion. Introduce `e v`.

Rewrite using `[h2, Matrix.mulVec_mulVec, e]`. Simplify using the standard rewrite rules. Introduce `e`. Conclude with `mat_ext fun v => by`. Rewrite using `[← Matrix.mulVec_mulVec, (h2 _).1 (e v)]`.

Simplify using the standard rewrite rules. Establish `hRX : R * X = 0` using `(hRv X).2 ha`. Establish `hPm : ∀ v, P *ᵥ v ∈ W₁` using `fun v => (h1 _).2 ⟨by rw [Matrix.mulVec_mulVec, h.qp]; simp, by rw [Matrix.mulVec_mulVec, h.rp]; simp⟩`. Establish `hQm : ∀ v, Q *ᵥ v ∈ W₂` using `fun v => (h2 _).2 (by rw [Matrix.mulVec_mulVec, h.rq]; simp)`. Establish `hXP : X * P = 0` using `mat_ext fun v => by`.

Rewrite using `[← Matrix.mulVec_mulVec, hc _ (hPm v)]`. Simplify using the standard rewrite rules. Establish `hQXQ : Q * X * Q = 0` using `mat_ext fun v => by`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ((h1 _).1 (hb _ (hQm v))).1]`. Simplify using the standard rewrite rules.

Establish `hu' : u.val = 1 + X` using `by simp [hX]`. Establish `hone : aM P Q R t (t⁻¹ : ℂˣ) * aM P Q R (t⁻¹ : ℂˣ) t = 1`. Rewrite using `[aM_mul h]`. Simplify using `[aM_one h]`. Establish `hiv : ((gA h t)⁻¹).val = aM P Q R (t⁻¹ : ℂˣ) t` using `rfl`.

Establish `hv : (gA h t).val = aM P Q R t (t⁻¹ : ℂˣ)` using `rfl`. Establish `e1 : aM P Q R t (t⁻¹ : ℂˣ) * X * aM P Q R (t⁻¹ : ℂˣ) t = (t : ℂ) • (P * X * Q + Q * X * R) + (t : ℂ) ^ 2 • (P * X * R)`. Establish `hPXP : P * X * P = 0` using `by rw [mul_assoc, hXP, mul_zero]`. Establish `hQXP : Q * X * P = 0` using `by rw [mul_assoc, hXP, mul_zero]`. Simplify using `only [aM, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hRX, hXP, hPXP, hQXP, hQXQ, zero_mul, smul_zero, add_zero, zero_add]`.

Use `module`. Rewrite using `[Units.val_mul, Units.val_mul, hiv, hv, hu', mul_add, add_mul, mul_one, hone, e1]`. Simplify using `only [add_sub_cancel_left, add_assoc]`.
-/
theorem conj_val {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {P Q R : Mat n} (h : Tri P Q R)
    (h1 : ∀ v, v ∈ W₁ ↔ Q *ᵥ v = 0 ∧ R *ᵥ v = 0) (h2 : ∀ v, v ∈ W₂ ↔ R *ᵥ v = 0)
    {u : G n} (hu : u ∈ nilSet W₁ W₂) (t : ℂˣ) :
    (gA h t * u * (gA h t)⁻¹).val =
      1 + (t : ℂ) • (P * (u.val - 1) * Q + Q * (u.val - 1) * R) +
        (t : ℂ) ^ 2 • (P * (u.val - 1) * R) := by
  obtain ⟨ha, hb, hc⟩ := hu
  set X : Mat n := u.val - 1 with hX
  have hRv : ∀ A : Mat n, R * A = 0 ↔ ∀ v, A *ᵥ v ∈ W₂ := fun A => by
    constructor
    · intro e v
      rw [h2, Matrix.mulVec_mulVec, e]
      simp
    · intro e
      exact mat_ext fun v => by
        rw [← Matrix.mulVec_mulVec, (h2 _).1 (e v)]
        simp
  have hRX : R * X = 0 := (hRv X).2 ha
  have hPm : ∀ v, P *ᵥ v ∈ W₁ := fun v => (h1 _).2 ⟨by rw [Matrix.mulVec_mulVec, h.qp]; simp,
    by rw [Matrix.mulVec_mulVec, h.rp]; simp⟩
  have hQm : ∀ v, Q *ᵥ v ∈ W₂ := fun v => (h2 _).2 (by rw [Matrix.mulVec_mulVec, h.rq]; simp)
  have hXP : X * P = 0 := mat_ext fun v => by
    rw [← Matrix.mulVec_mulVec, hc _ (hPm v)]
    simp
  have hQXQ : Q * X * Q = 0 := mat_ext fun v => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ((h1 _).1 (hb _ (hQm v))).1]
    simp
  have hu' : u.val = 1 + X := by simp [hX]
  have hone : aM P Q R t (t⁻¹ : ℂˣ) * aM P Q R (t⁻¹ : ℂˣ) t = 1 := by
    rw [aM_mul h]
    simp [aM_one h]
  have hiv : ((gA h t)⁻¹).val = aM P Q R (t⁻¹ : ℂˣ) t := rfl
  have hv : (gA h t).val = aM P Q R t (t⁻¹ : ℂˣ) := rfl
  have e1 : aM P Q R t (t⁻¹ : ℂˣ) * X * aM P Q R (t⁻¹ : ℂˣ) t =
      (t : ℂ) • (P * X * Q + Q * X * R) + (t : ℂ) ^ 2 • (P * X * R) := by
    have hPXP : P * X * P = 0 := by rw [mul_assoc, hXP, mul_zero]
    have hQXP : Q * X * P = 0 := by rw [mul_assoc, hXP, mul_zero]
    simp only [aM, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hRX, hXP, hPXP, hQXP, hQXQ,
      zero_mul, smul_zero, add_zero, zero_add]
    module
  rw [Units.val_mul, Units.val_mul, hiv, hv, hu', mul_add, add_mul, mul_one, hone, e1]
  simp only [add_sub_cancel_left, add_assoc]

def conjN (N : Subgroup (G n)) (g : G n) (hg : ∀ u ∈ N, g * u * g⁻¹ ∈ N)
    (hg' : ∀ u ∈ N, g⁻¹ * u * g ∈ N) : N ≃* N where
  toFun u := ⟨g * u.1 * g⁻¹, hg _ u.2⟩
  invFun u := ⟨g⁻¹ * u.1 * g, hg' _ u.2⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' u v := Subtype.ext (by simp [mul_assoc])

/- English proof (translation)
Introduce `v hv` and use `by have hR : R * aM P Q R t s = s • R := by simp [aM, mul_add, h.rp, h.rq, h.rr] have hQ : Q * aM P Q R t s = Q := by simp [aM, mul_add, h.qp, h.qq, h.qr] obtain ⟨a, b⟩ := (h1 v).1 hv refine (h1 _).2 ⟨?_, ?_⟩ · rw [Matrix.mulVec_mulVec, hQ, a] · rw [Matrix.mulVec_mulVec, hR, Matr …`.
-/
theorem aM_pres1 {W₁ : Submodule ℂ (Fin n → ℂ)} {P Q R : Mat n} (h : Tri P Q R)
    (h1 : ∀ v, v ∈ W₁ ↔ Q *ᵥ v = 0 ∧ R *ᵥ v = 0) (t s : ℂ) :
    ∀ v ∈ W₁, aM P Q R t s *ᵥ v ∈ W₁ := fun v hv => by
  have hR : R * aM P Q R t s = s • R := by simp [aM, mul_add, h.rp, h.rq, h.rr]
  have hQ : Q * aM P Q R t s = Q := by simp [aM, mul_add, h.qp, h.qq, h.qr]
  obtain ⟨a, b⟩ := (h1 v).1 hv
  refine (h1 _).2 ⟨?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, hQ, a]
  · rw [Matrix.mulVec_mulVec, hR, Matrix.smul_mulVec, b, smul_zero]

/- English proof (translation)
Introduce `v hv` and use `by have hR : R * aM P Q R t s = s • R := by simp [aM, mul_add, h.rp, h.rq, h.rr] refine (h2 _).2 ?_ rw [Matrix.mulVec_mulVec, hR, Matrix.smul_mulVec, (h2 v).1 hv, smul_zero]`.
-/
theorem aM_pres2 {W₂ : Submodule ℂ (Fin n → ℂ)} {P Q R : Mat n} (h : Tri P Q R)
    (h2 : ∀ v, v ∈ W₂ ↔ R *ᵥ v = 0) (t s : ℂ) :
    ∀ v ∈ W₂, aM P Q R t s *ᵥ v ∈ W₂ := fun v hv => by
  have hR : R * aM P Q R t s = s • R := by simp [aM, mul_add, h.rp, h.rq, h.rr]
  refine (h2 _).2 ?_
  rw [Matrix.mulVec_mulVec, hR, Matrix.smul_mulVec, (h2 v).1 hv, smul_zero]

def sq (k : ℕ) : ℂˣ := (Units.mk0 (1 / 2 : ℂ) (by norm_num)) ^ k

/- English proof (translation)
Establish `: Tendsto (fun k : ℕ => (1 / 2 : ℂ) ^ k) atTop (𝓝 0)` using `tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)`. Simplify `this` using `[sq]`.
-/
theorem tendsto_sq : Tendsto (fun k => (sq k : ℂ)) atTop (𝓝 0) := by
  have : Tendsto (fun k : ℕ => (1 / 2 : ℂ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  simpa [sq] using this

/- English proof (translation)
Establish `hcont : Continuous fun t : ℂ => (1 : Mat n) + t • B + t ^ 2 • C` using `by fun_prop`. Use `(hcont.tendsto 0).comp tendsto_sq` as an intermediate fact. Simplify `this` using `[Function.comp_def]`.
-/
theorem tendsto_poly (B C : Mat n) :
    Tendsto (fun k => (1 : Mat n) + (sq k : ℂ) • B + (sq k : ℂ) ^ 2 • C) atTop (𝓝 1) := by
  have hcont : Continuous fun t : ℂ => (1 : Mat n) + t • B + t ^ 2 • C := by fun_prop
  have := (hcont.tendsto 0).comp tendsto_sq
  simpa [Function.comp_def] using this

/- English proof (translation)
Rewrite using `[Units.isEmbedding_embedProduct.tendsto_nhds_iff]`. Use `a.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp b)` as an intermediate fact. Conclude with `this`.
-/
theorem tendsto_units {f : ℕ → G n} (a : Tendsto (fun k => (f k).val) atTop (𝓝 1))
    (b : Tendsto (fun k => ((f k)⁻¹).val) atTop (𝓝 1)) : Tendsto f atTop (𝓝 1) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  have := a.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp b)
  exact this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gA_val {P Q R : Mat n} (h : Tri P Q R) (t : ℂˣ) :
    (gA h t).val = aM P Q R t (t⁻¹ : ℂˣ) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gA_inv_val {P Q R : Mat n} (h : Tri P Q R) (t : ℂˣ) :
    ((gA h t)⁻¹).val = aM P Q R (t⁻¹ : ℂˣ) t := rfl

/- English proof (translation)
Take `⟨P, Q, R, h, h1, h2⟩` from `exists_tri h12`. Establish `hmem : ∀ x : G n, x ∈ N ↔ x ∈ nilSet W₁ W₂` using `fun x => by rw [← hN]; rfl`. Establish `p1 : ∀ (t : ℂˣ), ∀ v ∈ W₁, (gA h t).val *ᵥ v ∈ W₁` using `fun t v hv => by`. Rewrite using `[gA_val]`. Conclude with `aM_pres1 h h1 _ _ v hv`.

Establish `p2 : ∀ (t : ℂˣ), ∀ v ∈ W₂, (gA h t).val *ᵥ v ∈ W₂` using `fun t v hv => by`. Rewrite using `[gA_val]`. Conclude with `aM_pres2 h h2 _ _ v hv`. Establish `q1 : ∀ (t : ℂˣ), ∀ v ∈ W₁, ((gA h t)⁻¹).val *ᵥ v ∈ W₁` using `fun t v hv => by`. Rewrite using `[gA_inv_val]`.

Conclude with `aM_pres1 h h1 _ _ v hv`. Establish `q2 : ∀ (t : ℂˣ), ∀ v ∈ W₂, ((gA h t)⁻¹).val *ᵥ v ∈ W₂` using `fun t v hv => by`. Rewrite using `[gA_inv_val]`. Conclude with `aM_pres2 h h2 _ _ v hv`. Establish `hA : ∀ (t : ℂˣ) (x : G n), x ∈ N → gA h t * x * (gA h t)⁻¹ ∈ N` using `fun t x hx => (hmem _).2 (conj_mem_nilSet (gA h t) (p1 t) (p2 t) (q1 t) (q2 t) ((hmem _).1 hx))`.

Establish `hA' : ∀ (t : ℂˣ) (x : G n), x ∈ N → (gA h t)⁻¹ * x * gA h t ∈ N` using `fun t x hx => by`. Use `conj_mem_nilSet (W₁ := W₁) (W₂ := W₂) (gA h t)⁻¹ (q1 t) (q2 t) (by rw [inv_inv]; exact p1 t) (by rw [inv_inv]; exact p2 t) ((hmem _).1 hx)` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Conclude with `(hmem _).2 this`. Establish `hcφ : ∀ t, Continuous (conjN N (gA h t) (hA t) (hA' t))` using `fun t => Continuous.subtype_mk (((continuous_const.mul continuous_subtype_val).mul continuous_const)) _`.

Establish `hcφ' : ∀ t, Continuous (conjN N (gA h t) (hA t) (hA' t)).symm` using `fun t => Continuous.subtype_mk (((continuous_const.mul continuous_subtype_val).mul continuous_const)) _`. Establish `hlim : ∀ x ∈ nilSet W₁ W₂, Tendsto (fun k => (gA h (sq k) * x * (gA h (sq k))⁻¹).val) atTop (𝓝 1)` using `fun x hx => by`. Simplify using `only [conj_val h h1 h2 hx]`. Conclude with `tendsto_poly _ _`. Establish `hT : Tendsto (fun k => conjN N (gA h (sq k)) (hA _) (hA' _) u) atTop (𝓝 1)`.

Rewrite using `[tendsto_subtype_rng]`. Use `tendsto_units (hlim u.1 ((hmem _).1 u.2)) ?_` and prove the remaining obligations. Establish `hu2` using `hlim (u.1)⁻¹ ((hmem _).1 (N.inv_mem u.2))`. Use `hu2.congr fun k => ?_` and prove the remaining obligations. Use `show (gA h (sq k) * (u.1)⁻¹ * (gA h (sq k))⁻¹).val = ((gA h (sq k) * u.1 * (gA h (sq k))⁻¹)⁻¹).val`.

Use `congr 1`. Use `group`. Take `⟨k, hk⟩` from `(hT.eventually hC).exists`. Conclude with `⟨_, hcφ _, hcφ' _, hk⟩`.
-/
theorem contract {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (h12 : W₁ ≤ W₂) (N : Subgroup (G n))
    (hN : (N : Set (G n)) = nilSet W₁ W₂) (u : N) (C : Set N) (hC : C ∈ 𝓝 (1 : N)) :
    ∃ φ : N ≃* N, Continuous φ ∧ Continuous φ.symm ∧ φ u ∈ C := by
  obtain ⟨P, Q, R, h, h1, h2⟩ := exists_tri h12
  have hmem : ∀ x : G n, x ∈ N ↔ x ∈ nilSet W₁ W₂ := fun x => by rw [← hN]; rfl
  have p1 : ∀ (t : ℂˣ), ∀ v ∈ W₁, (gA h t).val *ᵥ v ∈ W₁ := fun t v hv => by
    rw [gA_val]
    exact aM_pres1 h h1 _ _ v hv
  have p2 : ∀ (t : ℂˣ), ∀ v ∈ W₂, (gA h t).val *ᵥ v ∈ W₂ := fun t v hv => by
    rw [gA_val]
    exact aM_pres2 h h2 _ _ v hv
  have q1 : ∀ (t : ℂˣ), ∀ v ∈ W₁, ((gA h t)⁻¹).val *ᵥ v ∈ W₁ := fun t v hv => by
    rw [gA_inv_val]
    exact aM_pres1 h h1 _ _ v hv
  have q2 : ∀ (t : ℂˣ), ∀ v ∈ W₂, ((gA h t)⁻¹).val *ᵥ v ∈ W₂ := fun t v hv => by
    rw [gA_inv_val]
    exact aM_pres2 h h2 _ _ v hv
  have hA : ∀ (t : ℂˣ) (x : G n), x ∈ N → gA h t * x * (gA h t)⁻¹ ∈ N := fun t x hx =>
    (hmem _).2 (conj_mem_nilSet (gA h t) (p1 t) (p2 t) (q1 t) (q2 t) ((hmem _).1 hx))
  have hA' : ∀ (t : ℂˣ) (x : G n), x ∈ N → (gA h t)⁻¹ * x * gA h t ∈ N := fun t x hx => by
    have := conj_mem_nilSet (W₁ := W₁) (W₂ := W₂) (gA h t)⁻¹ (q1 t) (q2 t)
      (by rw [inv_inv]; exact p1 t) (by rw [inv_inv]; exact p2 t) ((hmem _).1 hx)
    rw [inv_inv] at this
    exact (hmem _).2 this
  have hcφ : ∀ t, Continuous (conjN N (gA h t) (hA t) (hA' t)) := fun t =>
    Continuous.subtype_mk (((continuous_const.mul continuous_subtype_val).mul continuous_const)) _
  have hcφ' : ∀ t, Continuous (conjN N (gA h t) (hA t) (hA' t)).symm := fun t =>
    Continuous.subtype_mk (((continuous_const.mul continuous_subtype_val).mul continuous_const)) _
  have hlim : ∀ x ∈ nilSet W₁ W₂, Tendsto (fun k => (gA h (sq k) * x * (gA h (sq k))⁻¹).val) atTop
      (𝓝 1) := fun x hx => by
    simp only [conj_val h h1 h2 hx]
    exact tendsto_poly _ _
  have hT : Tendsto (fun k => conjN N (gA h (sq k)) (hA _) (hA' _) u) atTop (𝓝 1) := by
    rw [tendsto_subtype_rng]
    refine tendsto_units (hlim u.1 ((hmem _).1 u.2)) ?_
    have hu2 := hlim (u.1)⁻¹ ((hmem _).1 (N.inv_mem u.2))
    refine hu2.congr fun k => ?_
    show (gA h (sq k) * (u.1)⁻¹ * (gA h (sq k))⁻¹).val = ((gA h (sq k) * u.1 * (gA h (sq k))⁻¹)⁻¹).val
    congr 1
    group
  obtain ⟨k, hk⟩ := (hT.eventually hC).exists
  exact ⟨_, hcφ _, hcφ' _, hk⟩

/- English proof (translation)
Introduce `n _ _ W₁ W₂ h12 N hN`. Establish `hcl : IsClosed (N : Set (G n))` using `hN ▸ isClosed_nilSet W₁ W₂`. Use `⟨hcl, fun ν _ => ?_⟩` and prove the remaining obligations. Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))`. Use `haveI : LocallyCompactSpace (GL (Fin n) ℂ) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace`.

Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Use `haveI : SecondCountableTopology (GL (Fin n) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology`. Use `haveI : LocallyCompactSpace N := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology`.

Use `haveI : ν.IsMulRightInvariant := rightInvariant (fun u C hC => contract h12 N hN u C hC) ν`. Conclude with `GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant ν`.
-/
theorem nilUni : PositivityTheory.RgBcC.NilUni := by
  intro n _ _ W₁ W₂ h12 N hN
  have hcl : IsClosed (N : Set (G n)) := hN ▸ isClosed_nilSet W₁ W₂
  refine ⟨hcl, fun ν _ => ?_⟩
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (GL (Fin n) ℂ) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace N := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : ν.IsMulRightInvariant := rightInvariant (fun u C hC => contract h12 N hN u C hC) ν
  exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant ν

end Main

end GlobalTheory.CompanionTheory.NilUnimod
