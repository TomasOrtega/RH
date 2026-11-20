import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnit
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

/- English proof (translation)
Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Use `haveI : SecondCountableTopology F := secondCountable_of_proper`. Use `haveI := hV.1`. Use `haveI := hν.1`. Set `E₁ : V ≃L[F] (Fin r → F)` to `{ e₁ with continuous_toFun := IsModuleTopology.continuous_of_linearMap e₁.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap e₁.symm.toLinearMap }`.

Set `E₂ : V ≃L[F] (Fin r → F)` to `{ e₂ with continuous_toFun := IsModuleTopology.continuous_of_linearMap e₂.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap e₂.symm.toLinearMap }`. Use `haveI : (Measure.map E₁ μV).IsAddHaarMeasure := E₁.isAddHaarMeasure_map μV`. Use `haveI : (Measure.map E₂ μV).IsAddHaarMeasure := E₂.isAddHaarMeasure_map μV`. Establish `hm₁` using `Measure.isAddLeftInvariant_eq_smul (Measure.map E₁ μV) ν`. Establish `hm₂` using `Measure.isAddLeftInvariant_eq_smul (Measure.map E₂ μV) ν`.

Use `set c₁ := (Measure.map E₁ μV).addHaarScalarFactor ν`. Use `set c₂ := (Measure.map E₂ μV).addHaarScalarFactor ν`. Set `M₁` to `E₁.toHomeomorph.toMeasurableEquiv`. Set `M₂` to `E₂.toHomeomorph.toMeasurableEquiv`. Establish `hM₁ : ∀ x, M₁ x = e₁ x` using `fun _ => rfl`.

Establish `hM₂ : ∀ x, M₂ x = e₂ x` using `fun _ => rfl`. Establish `hmap : ∀ (M : V ≃ᵐ (Fin r → F)) (c : ENNReal), Measure.map M μV = c • ν → ∀ φ : (Fin r → F) → ℂ, ∫ x, φ (M x) ∂μV = (c.toReal : ℂ) * ∫ y, φ y ∂ν`. Introduce `M c hc φ`. Rewrite using `[← integral_map_equiv M φ, hc, integral_smul_measure, Complex.real_smul]`. Use `set FF := fourB ν (fun x y => ψ (x ⬝ᵥ y))`.

Use `set FV := fourB μV (fun x y => ψ (B x y))`. Use `set f : V → ℂ := h₀ ∘ E₁`. Establish `hf : IsTest f` using `⟨ht₀.1.comp_continuous E₁.continuous, ht₀.2.comp_homeomorph E₁.toHomeomorph⟩`. Establish `ha : ∀ c, FV f c = (c₁ : ℂ) * FF h₀ (e₂ c)`. Introduce `c`.

Use `hmap M₁ c₁ hm₁ (fun y => h₀ y * ψ (y ⬝ᵥ e₂ c))` as an intermediate fact. Simplify using `only [hM₁, ENNReal.coe_toReal] at this`. Simplify using `only [FV, FF, fourB, f, Function.comp_apply]`. Rewrite using `[← this]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Simplify using `only [← hB]`. Both sides reduce to the same expression. Establish `hb : ∀ b, FV (FV f) b = (c₁ : ℂ) * (c₂ : ℂ) * FF (FF h₀) (e₁ b)`. Introduce `b`. Use `hmap M₂ c₂ hm₂ (fun y => FF h₀ y * ψ (y ⬝ᵥ e₁ b))` as an intermediate fact.

Simplify using `only [hM₂, ENNReal.coe_toReal] at this`. Use `show ∫ c, FV f c * ψ (B c b) ∂μV = _`. Simplify using `only [ha]`. Establish `e : ∀ c, (c₁ : ℂ) * FF h₀ (e₂ c) * ψ (B c b) = (c₁ : ℂ) * (FF h₀ (e₂ c) * ψ (e₂ c ⬝ᵥ e₁ b))`. Introduce `c`.

Rewrite using `[hBs, ← hB, dotProduct_comm, mul_assoc]`. Simplify using `only [e]`. Rewrite using `[integral_const_mul, this, mul_assoc]`. Both sides reduce to the same expression. Use `⟨c₁, c₂, fun φ => ?_, fun φ => ?_, ?_⟩` and prove the remaining obligations.

Use `hmap M₁ c₁ hm₁ φ` as an intermediate fact. Simplify `this` using `only [hM₁, ENNReal.coe_toReal]`. Use `hmap M₂ c₂ hm₂ φ` as an intermediate fact. Simplify `this` using `only [hM₂, ENNReal.coe_toReal]`. Establish `h1` using `hb 0`.

Establish `h3 : FV (FV f) 0 = f (-0)` using `hV.2 f hf 0`. Establish `h4 : FF (FF h₀) 0 = h₀ (-0)` using `hν.2 h₀ ht₀ 0`. Rewrite `h1` using `[h3, map_zero, h4]`. Simplify using `only [neg_zero, f, Function.comp_apply, map_zero, h₀0, mul_one] at h1`. Rewrite using `[← h1]`.
-/
theorem map_pair_selfDual {F : Type} [NontriviallyNormedField F] [LocallyCompactSpace F] [MeasurableSpace F]
    [BorelSpace F] {r : ℕ} {V : Type} [AddCommGroup V] [Module F V] [TopologicalSpace V] [IsModuleTopology F V]
    [IsTopologicalAddGroup V] [ContinuousSMul F V] [MeasurableSpace V] [BorelSpace V]
    (ψ : AddChar F ℂ) (B : V → V → F) (hBs : ∀ x y, B x y = B y x)
    (e₁ e₂ : V ≃ₗ[F] (Fin r → F)) (hB : ∀ x y, e₁ x ⬝ᵥ e₂ y = B x y)
    (μV : Measure V) (hV : SelfDual μV (fun x y => ψ (B x y)))
    (ν : Measure (Fin r → F)) (hν : SelfDual ν (fun x y => ψ (x ⬝ᵥ y)))
    (h₀ : (Fin r → F) → ℂ) (ht₀ : IsTest h₀) (h₀0 : h₀ 0 = 1) :
    ∃ c₁ c₂ : ℂ, (∀ φ : (Fin r → F) → ℂ, ∫ x, φ (e₁ x) ∂μV = c₁ * ∫ y, φ y ∂ν) ∧
      (∀ φ : (Fin r → F) → ℂ, ∫ x, φ (e₂ x) ∂μV = c₂ * ∫ y, φ y ∂ν) ∧ c₁ * c₂ = 1 := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology F := secondCountable_of_proper
  haveI := hV.1
  haveI := hν.1
  let E₁ : V ≃L[F] (Fin r → F) :=
    { e₁ with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₁.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₁.symm.toLinearMap }
  let E₂ : V ≃L[F] (Fin r → F) :=
    { e₂ with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₂.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₂.symm.toLinearMap }
  haveI : (Measure.map E₁ μV).IsAddHaarMeasure := E₁.isAddHaarMeasure_map μV
  haveI : (Measure.map E₂ μV).IsAddHaarMeasure := E₂.isAddHaarMeasure_map μV
  have hm₁ := Measure.isAddLeftInvariant_eq_smul (Measure.map E₁ μV) ν
  have hm₂ := Measure.isAddLeftInvariant_eq_smul (Measure.map E₂ μV) ν
  set c₁ := (Measure.map E₁ μV).addHaarScalarFactor ν
  set c₂ := (Measure.map E₂ μV).addHaarScalarFactor ν
  let M₁ := E₁.toHomeomorph.toMeasurableEquiv
  let M₂ := E₂.toHomeomorph.toMeasurableEquiv
  have hM₁ : ∀ x, M₁ x = e₁ x := fun _ => rfl
  have hM₂ : ∀ x, M₂ x = e₂ x := fun _ => rfl
  have hmap : ∀ (M : V ≃ᵐ (Fin r → F)) (c : ENNReal), Measure.map M μV = c • ν →
      ∀ φ : (Fin r → F) → ℂ, ∫ x, φ (M x) ∂μV = (c.toReal : ℂ) * ∫ y, φ y ∂ν := by
    intro M c hc φ
    rw [← integral_map_equiv M φ, hc, integral_smul_measure, Complex.real_smul]
  set FF := fourB ν (fun x y => ψ (x ⬝ᵥ y))
  set FV := fourB μV (fun x y => ψ (B x y))
  set f : V → ℂ := h₀ ∘ E₁
  have hf : IsTest f := ⟨ht₀.1.comp_continuous E₁.continuous, ht₀.2.comp_homeomorph E₁.toHomeomorph⟩
  have ha : ∀ c, FV f c = (c₁ : ℂ) * FF h₀ (e₂ c) := by
    intro c
    have := hmap M₁ c₁ hm₁ (fun y => h₀ y * ψ (y ⬝ᵥ e₂ c))
    simp only [hM₁, ENNReal.coe_toReal] at this
    simp only [FV, FF, fourB, f, Function.comp_apply]
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [← hB]; rfl
  have hb : ∀ b, FV (FV f) b = (c₁ : ℂ) * (c₂ : ℂ) * FF (FF h₀) (e₁ b) := by
    intro b
    have := hmap M₂ c₂ hm₂ (fun y => FF h₀ y * ψ (y ⬝ᵥ e₁ b))
    simp only [hM₂, ENNReal.coe_toReal] at this
    show ∫ c, FV f c * ψ (B c b) ∂μV = _
    simp only [ha]
    have e : ∀ c, (c₁ : ℂ) * FF h₀ (e₂ c) * ψ (B c b) = (c₁ : ℂ) * (FF h₀ (e₂ c) * ψ (e₂ c ⬝ᵥ e₁ b)) := by
      intro c; rw [hBs, ← hB, dotProduct_comm, mul_assoc]
    simp only [e]
    rw [integral_const_mul, this, mul_assoc]
    rfl
  refine ⟨c₁, c₂, fun φ => ?_, fun φ => ?_, ?_⟩
  · have := hmap M₁ c₁ hm₁ φ; simpa only [hM₁, ENNReal.coe_toReal] using this
  · have := hmap M₂ c₂ hm₂ φ; simpa only [hM₂, ENNReal.coe_toReal] using this
  have h1 := hb 0
  have h3 : FV (FV f) 0 = f (-0) := hV.2 f hf 0
  have h4 : FF (FF h₀) 0 = h₀ (-0) := hν.2 h₀ ht₀ 0
  rw [h3, map_zero, h4] at h1
  simp only [neg_zero, f, Function.comp_apply, map_zero, h₀0, mul_one] at h1
  rw [← h1]

/- English proof (translation)
Use `haveI := hU.ultraF`. Use `haveI := hU.lcF`. Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Use `haveI : SecondCountableTopology F := secondCountable_of_proper`. Use `set S : Set (Fin r → F) := Set.univ.pi fun _ => Metric.closedBall 0 1 with hSdef`.

Establish `hmem : ∀ y : Fin r → F, y ∈ S ↔ ∀ i, ‖y i‖ ≤ 1`. Introduce `y`. Simplify using `[S, Set.mem_pi, Metric.mem_closedBall, dist_zero_right]`. Establish `hSo : IsOpen S` using `isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall 0 one_ne_zero`. Establish `hSc : IsCompact S` using `isCompact_univ_pi fun _ => isCompact_closedBall 0 1`.

Establish `hScl : IsClosed S` using `isClosed_set_pi fun _ _ => Metric.isClosed_closedBall`. Set `Mg : AddSubgroup (Fin r → F)` to `{ carrier := S zero_mem' := by rw [hmem]; simp add_mem' := by`. Introduce `a b ha hb`. Rewrite `ha`, `hb`, the goal using `[hmem]`. Introduce `i`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))`. Use the proof step `neg_mem' := by`. Introduce `a ha`. Rewrite `ha`, the goal using `[hmem]`. Introduce `i`.

Simplify using `using ha i }`. Establish `hMg : (Mg : Set (Fin r → F)) = S` using `rfl`. Set `β : LinearMap.BilinForm F (Fin r → F)` to `Matrix.toBilin' 1`. Establish `hβ : ∀ x y, β x y = x ⬝ᵥ y` using `by intro x y; simp [β, Matrix.toBilin'_apply']`. Establish `hβs : β.IsSymm` using `by first`.

Consider the case `exact ⟨fun x y => by simp [hβ, dotProduct_comm]⟩`. Consider the case `exact fun x y => by simp [hβ, dotProduct_comm]`. Establish `hβn : β.Nondegenerate` using `Matrix.Nondegenerate.toBilin' (Matrix.nondegenerate_of_det_ne_zero (by simp))`. Establish `key` using `(GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → F) β hβs hβn (Measure.pi fun _ => μF) inferInstance).1 Mg (by rw [hMg]; exact hSo) (by rw [hMg]; exact hSc)`. Establish `hdual : {y | ∀ x ∈ Mg, ψ (β x y) = 1} = S`.

Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, hβ]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[hmem]`.

Introduce `i`. Assume the negation of the conclusion as `hi`. Use `push_neg at hi`. Take `⟨x0, hx0, hx0'⟩` from `hψ.2`. Establish `hyi : y i ≠ 0` using `by intro h0; rw [h0, norm_zero] at hi; linarith`.

Establish `hsmall : ‖(y i)⁻¹‖ < 1` using `by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hi`. Establish `hx : Pi.single i (x0 * (y i)⁻¹) ∈ Mg` using `by show _ ∈ S`. Rewrite using `[hmem]`. Introduce `j`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Simplify using `only [Pi.single_eq_same]`. Conclude with `hx0' _ hsmall`. Simplify using `[Pi.single_eq_of_ne hj]`. Establish `h2` using `h _ hx`.

Establish `e : Pi.single i (x0 * (y i)⁻¹) ⬝ᵥ y = x0`. Simplify using `only [dotProduct, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[mul_assoc, inv_mul_cancel₀ hyi, mul_one]`. Rewrite `h2` using `[e]`. Conclude with `hx0 h2`.

Introduce `hy x hx`. Establish `hx' : x ∈ S` using `hx`. Rewrite `hy`, `hx'` using `[hmem]`. Apply `hψ.1` to reduce the goal to its premises. Simplify using `only [dotProduct]`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hx' i) (norm_nonneg _) (hy i)`. Establish `hvolS : (Measure.pi fun _ : Fin r => μF) S = 1`. Rewrite using `[hSdef, Measure.pi_pi]`.

Simplify using `[hvol]`. Establish `hsd : SelfDual (Measure.pi fun _ : Fin r => μF) (fun x y => ψ (β x y))` using `key.1.2 (by rw [hdual, hMg, hvolS, one_mul])`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : (fun x y : Fin r → F => ψ (x ⬝ᵥ y)) = (fun x y => ψ (β x y))` using `by funext x y; rw [hβ]`. Rewrite using `[e]`.

Conclude with `hsd`. Conclude with `⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hScl, hSo⟩).isLocallyConstant, HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _⟩`.
-/
theorem pi_selfDual (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] [MeasurableSpace F] [BorelSpace F] (μF : Measure F) [μF.IsAddHaarMeasure]
    (hvol : μF (Metric.closedBall 0 1) = 1) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (r : ℕ) :
    SelfDual (Measure.pi fun _ : Fin r => μF) (fun x y => ψ (x ⬝ᵥ y)) ∧
      IsTest ((Set.univ.pi fun _ : Fin r => Metric.closedBall (0 : F) 1).indicator 1) := by
  haveI := hU.ultraF
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology F := secondCountable_of_proper
  set S : Set (Fin r → F) := Set.univ.pi fun _ => Metric.closedBall 0 1 with hSdef
  have hmem : ∀ y : Fin r → F, y ∈ S ↔ ∀ i, ‖y i‖ ≤ 1 := by
    intro y; simp [S, Set.mem_pi, Metric.mem_closedBall, dist_zero_right]
  have hSo : IsOpen S :=
    isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall 0 one_ne_zero
  have hSc : IsCompact S := isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hScl : IsClosed S := isClosed_set_pi fun _ _ => Metric.isClosed_closedBall
  let Mg : AddSubgroup (Fin r → F) :=
    { carrier := S
      zero_mem' := by rw [hmem]; simp
      add_mem' := by
        intro a b ha hb
        rw [hmem] at ha hb ⊢
        intro i; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
      neg_mem' := by
        intro a ha
        rw [hmem] at ha ⊢
        intro i; simpa using ha i }
  have hMg : (Mg : Set (Fin r → F)) = S := rfl
  let β : LinearMap.BilinForm F (Fin r → F) := Matrix.toBilin' 1
  have hβ : ∀ x y, β x y = x ⬝ᵥ y := by intro x y; simp [β, Matrix.toBilin'_apply']
  have hβs : β.IsSymm := by
    first
    | exact ⟨fun x y => by simp [hβ, dotProduct_comm]⟩
    | exact fun x y => by simp [hβ, dotProduct_comm]
  have hβn : β.Nondegenerate := Matrix.Nondegenerate.toBilin' (Matrix.nondegenerate_of_det_ne_zero (by simp))
  have key := (GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → F) β hβs hβn (Measure.pi fun _ => μF) inferInstance).1 Mg
    (by rw [hMg]; exact hSo) (by rw [hMg]; exact hSc)
  have hdual : {y | ∀ x ∈ Mg, ψ (β x y) = 1} = S := by
    ext y
    simp only [Set.mem_setOf_eq, hβ]
    constructor
    · intro h
      rw [hmem]
      intro i
      by_contra hi
      push_neg at hi
      obtain ⟨x0, hx0, hx0'⟩ := hψ.2
      have hyi : y i ≠ 0 := by intro h0; rw [h0, norm_zero] at hi; linarith
      have hsmall : ‖(y i)⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hi
      have hx : Pi.single i (x0 * (y i)⁻¹) ∈ Mg := by
        show _ ∈ S
        rw [hmem]
        intro j
        by_cases hj : j = i
        · subst hj; simp only [Pi.single_eq_same]; exact hx0' _ hsmall
        · simp [Pi.single_eq_of_ne hj]
      have h2 := h _ hx
      have e : Pi.single i (x0 * (y i)⁻¹) ⬝ᵥ y = x0 := by
        simp only [dotProduct, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [mul_assoc, inv_mul_cancel₀ hyi, mul_one]
      rw [e] at h2
      exact hx0 h2
    · intro hy x hx
      have hx' : x ∈ S := hx
      rw [hmem] at hy hx'
      apply hψ.1
      simp only [dotProduct]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
      rw [norm_mul]; exact mul_le_one₀ (hx' i) (norm_nonneg _) (hy i)
  have hvolS : (Measure.pi fun _ : Fin r => μF) S = 1 := by
    rw [hSdef, Measure.pi_pi]; simp [hvol]
  have hsd : SelfDual (Measure.pi fun _ : Fin r => μF) (fun x y => ψ (β x y)) :=
    key.1.2 (by rw [hdual, hMg, hvolS, one_mul])
  refine ⟨?_, ?_⟩
  · have e : (fun x y : Fin r → F => ψ (x ⬝ᵥ y)) = (fun x y => ψ (β x y)) := by funext x y; rw [hβ]
    rw [e]; exact hsd
  · exact ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hScl, hSo⟩).isLocallyConstant,
      HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _⟩

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

/- English proof (translation)
Introduce `F E _ _ _ _ hU A r τ p hG lam M ψ hψ μK hK f' _ g b c`. Use `letI := M.mF`. Use `haveI := M.bF`. Use `haveI := M.haarF`. Use `haveI := hU.lcF`.

Take `⟨hsd, ht0⟩` from `pi_selfDual F E M.μF M.volF ψ hψ r`. Use `set ν : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hν`. Set `gm : Matrix (Fin r) (Fin r) F` to `(g : Matrix (Fin r) (Fin r) F)`. Set `gi : Matrix (Fin r) (Fin r) F` to `((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)`. Establish `hgig : gi * gm = 1` using `by simp [gi, gm]`.

Establish `hggi : gm * gi = 1` using `by simp [gi, gm]`. Set `gL : (Fin r → F) ≃ₗ[F] (Fin r → F)` to `{ toFun := fun v => gm *ᵥ v invFun := fun v => gi *ᵥ v map_add' := fun v w => mulVec_add _ _ _ map_smul' := fun a v => by simp [mulVec_smul] left_inv := fun v => by simp [mulVec_mulVec, hgig] right_inv := fun v => by simp [mulVec_mulVec, hggi] }`. Set `hL : (Fin r → F) ≃ₗ[F] (Fin r → F)` to `{ toFun := fun v => v ᵥ* gi invFun := fun v => v ᵥ* gm map_add' := fun v w => add_vecMul _ _ _ map_smul' := fun a v => by simp [smul_vecMul] left_inv := fun v => by simp [vecMul_vecMul, hgig] right_inv := fun v => by simp [vecMul_vecMul, hggi] }`. Set `ρL : A.K →ₗ[F] (Fin r → F)` to `{ toFun := fun c i => Algebra.trace F A.K (τ ^ (i : ℕ) * c) map_add' := by intro x y; funext i; simp [mul_add] map_smul' := by intro a x; funext i; simp [mul_smul_comm] }`. Establish `hρ : Function.Bijective ρL` using `(GlobalTheory.JR.EtInv.invK_regular_iff_isUnit F E A r τ p lam hG).1`.

Set `e₁ : A.K ≃ₗ[F] (Fin r → F)` to `(bas A hG).equivFun.trans gL`. Set `e₂ : A.K ≃ₗ[F] (Fin r → F)` to `(LinearEquiv.ofBijective ρL hρ).trans hL`. Establish `he₁ : ∀ x, e₁ x = gm *ᵥ (bas A hG).equivFun x` using `fun _ => rfl`. Establish `he₂ : ∀ x, e₂ x = (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * x)) ᵥ* gi` using `fun _ => rfl`. Establish `hB : ∀ x y, e₁ x ⬝ᵥ e₂ y = Algebra.trace F A.K (x * y)`.

Introduce `x y`. Rewrite using `[he₁, he₂, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec, hgig, one_mulVec]`. Use `conv_rhs => rw [← (bas A hG).sum_equivFun x]`. Rewrite using `[Finset.sum_mul, map_sum]`. Simplify using `only [dotProduct]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[bas_apply, smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]`. Take `⟨c₁, c₂, h₁, h₂, hc⟩` from `map_pair_selfDual ψ (fun x y => Algebra.trace F A.K (x * y)) (fun x y => by rw [mul_comm]) e₁ e₂ hB μK hK ν hsd _ ht0 (by simp)`. Set `X : Matrix (Fin r) (Fin r) F` to `gm * companion p * gi`. Set `G : (Fin r → F) → (Fin r → F) → ℂ` to `fun x y => f' (X, x, y, lam) * ψ (y ⬝ᵥ e₁ b + e₂ c ⬝ᵥ x)`.

Establish `lhs : fourG M ψ f' (act g (pt A hG lam b c)) = ∫ x, (∫ y, G x y ∂ν) ∂ν` using `rfl`. Establish `rhs : A.fourK μK ψ (fun x => f' (act g (pt A hG lam x.1 x.2))) (b, c) = ∫ x, (∫ y, G (e₁ x) (e₂ y) ∂μK) ∂μK`. Unfold `Et.fourK`. Use `integral_congr_ae (Eventually.of_forall fun x => integral_congr_ae (Eventually.of_forall fun y => ?_))` and prove the remaining obligations. Use `show f' (act g (pt A hG lam x y)) * A.psiK ψ (b * y + x * c) = G (e₁ x) (e₂ y)`.

Simplify using `only [G]`. Use `congr 1`. Rewrite using `[Et.psiK, map_add, ← hB, ← hB, dotProduct_comm (e₁ b), dotProduct_comm (e₁ x)]`. Rewrite using `[lhs, rhs]`. Establish `inner : ∀ x, ∫ y, G (e₁ x) (e₂ y) ∂μK = c₂ * ∫ y, G (e₁ x) y ∂ν` using `fun x => h₂ (fun y => G (e₁ x) y)`.

Rewrite using `[integral_congr_ae (Eventually.of_forall inner), integral_const_mul, h₁ (fun x => ∫ y, G x y ∂ν)]`. Rewrite using `[← mul_assoc, mul_comm c₂, hc, one_mul]`.
-/
theorem fourG_act_pt_eq_fourK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ μK : Measure A.K, SelfDual μK (A.kerK ψ) → ∀ f' : Gl r F → ℂ, IsTest f' → ∀ (g : GL (Fin r) F) (b c : A.K), fourG M ψ f' (act g (LinDesc.pt A hG lam b c)) = A.fourK μK ψ (fun x => f' (act g (LinDesc.pt A hG lam x.1 x.2))) (b, c) := by
  intro F E _ _ _ _ hU A r τ p hG lam M ψ hψ μK hK f' _ g b c
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI := hU.lcF
  obtain ⟨hsd, ht0⟩ := pi_selfDual F E M.μF M.volF ψ hψ r
  set ν : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hν
  let gm : Matrix (Fin r) (Fin r) F := (g : Matrix (Fin r) (Fin r) F)
  let gi : Matrix (Fin r) (Fin r) F := ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
  have hgig : gi * gm = 1 := by simp [gi, gm]
  have hggi : gm * gi = 1 := by simp [gi, gm]
  let gL : (Fin r → F) ≃ₗ[F] (Fin r → F) :=
    { toFun := fun v => gm *ᵥ v
      invFun := fun v => gi *ᵥ v
      map_add' := fun v w => mulVec_add _ _ _
      map_smul' := fun a v => by simp [mulVec_smul]
      left_inv := fun v => by simp [mulVec_mulVec, hgig]
      right_inv := fun v => by simp [mulVec_mulVec, hggi] }
  let hL : (Fin r → F) ≃ₗ[F] (Fin r → F) :=
    { toFun := fun v => v ᵥ* gi
      invFun := fun v => v ᵥ* gm
      map_add' := fun v w => add_vecMul _ _ _
      map_smul' := fun a v => by simp [smul_vecMul]
      left_inv := fun v => by simp [vecMul_vecMul, hgig]
      right_inv := fun v => by simp [vecMul_vecMul, hggi] }
  let ρL : A.K →ₗ[F] (Fin r → F) :=
    { toFun := fun c i => Algebra.trace F A.K (τ ^ (i : ℕ) * c)
      map_add' := by intro x y; funext i; simp [mul_add]
      map_smul' := by intro a x; funext i; simp [mul_smul_comm] }
  have hρ : Function.Bijective ρL := (GlobalTheory.JR.EtInv.invK_regular_iff_isUnit F E A r τ p lam hG).1
  let e₁ : A.K ≃ₗ[F] (Fin r → F) := (bas A hG).equivFun.trans gL
  let e₂ : A.K ≃ₗ[F] (Fin r → F) := (LinearEquiv.ofBijective ρL hρ).trans hL
  have he₁ : ∀ x, e₁ x = gm *ᵥ (bas A hG).equivFun x := fun _ => rfl
  have he₂ : ∀ x, e₂ x = (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * x)) ᵥ* gi := fun _ => rfl
  have hB : ∀ x y, e₁ x ⬝ᵥ e₂ y = Algebra.trace F A.K (x * y) := by
    intro x y
    rw [he₁, he₂, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec, hgig, one_mulVec]
    conv_rhs => rw [← (bas A hG).sum_equivFun x]
    rw [Finset.sum_mul, map_sum]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bas_apply, smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
  obtain ⟨c₁, c₂, h₁, h₂, hc⟩ := map_pair_selfDual ψ (fun x y => Algebra.trace F A.K (x * y))
    (fun x y => by rw [mul_comm]) e₁ e₂ hB μK hK ν hsd _ ht0 (by simp)
  let X : Matrix (Fin r) (Fin r) F := gm * companion p * gi
  let G : (Fin r → F) → (Fin r → F) → ℂ := fun x y => f' (X, x, y, lam) * ψ (y ⬝ᵥ e₁ b + e₂ c ⬝ᵥ x)
  have lhs : fourG M ψ f' (act g (pt A hG lam b c)) = ∫ x, (∫ y, G x y ∂ν) ∂ν := rfl
  have rhs : A.fourK μK ψ (fun x => f' (act g (pt A hG lam x.1 x.2))) (b, c) =
      ∫ x, (∫ y, G (e₁ x) (e₂ y) ∂μK) ∂μK := by
    unfold Et.fourK
    refine integral_congr_ae (Eventually.of_forall fun x => integral_congr_ae (Eventually.of_forall fun y => ?_))
    show f' (act g (pt A hG lam x y)) * A.psiK ψ (b * y + x * c) = G (e₁ x) (e₂ y)
    simp only [G]
    congr 1
    rw [Et.psiK, map_add, ← hB, ← hB, dotProduct_comm (e₁ b), dotProduct_comm (e₁ x)]
  rw [lhs, rhs]
  have inner : ∀ x, ∫ y, G (e₁ x) (e₂ y) ∂μK = c₂ * ∫ y, G (e₁ x) y ∂ν := fun x => h₂ (fun y => G (e₁ x) y)
  rw [integral_congr_ae (Eventually.of_forall inner), integral_const_mul, h₁ (fun x => ∫ y, G x y ∂ν)]
  rw [← mul_assoc, mul_comm c₂, hc, one_mul]

end GlobalTheory.JR.LinDesc
