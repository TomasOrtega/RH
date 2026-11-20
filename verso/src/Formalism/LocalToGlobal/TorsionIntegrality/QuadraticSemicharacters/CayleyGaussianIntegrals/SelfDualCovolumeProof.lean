import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.DiagIntegrable

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Formalism.L2.Th1.H

namespace UC

section Neg

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [imgLat, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, LinearEquiv.neg_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `Λ.neg_mem hy`.

Introduce `hx`. Conclude with `⟨-x, Λ.neg_mem hx, neg_neg x⟩`.
-/
theorem img_neg (Λ : AddSubgroup V) : imgLat ((LinearEquiv.neg ℂ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) Λ = Λ := by
  ext x
  simp only [imgLat, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    LinearEquiv.neg_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Λ.neg_mem hy
  · intro hx
    exact ⟨-x, Λ.neg_mem hx, neg_neg x⟩

/- English proof (translation)
The claim follows from `AddSubgroup.relIndex_self Λ`.
-/
theorem relIdx_self (Λ : AddSubgroup V) : relIdx Λ Λ = 1 := AddSubgroup.relIndex_self Λ

/- English proof (translation)
The claim follows from `hH pos := hP selfDual := hsd semi := hα isom := by intro x y simp semi' := by rw [img_neg]; exact hα inv := fun x hx => (semiCharBasic V H hH Λ α hα).2.1 x hx idx₁ := by rw [img_neg, relIdx_self]; exact one_ne_zero idx₂ := by rw [img_neg, relIdx_self]; exact one_ne_zero cay := by …`.
-/
theorem data_neg {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ} (hH : IsHerm H) (hP : IsPosDef H)
    (hsd : IsSelfDual H Λ) (hα : IsSemiChar H Λ α) :
    UnitaryData H Λ α (LinearEquiv.neg ℂ) (LinearEquiv.smulOfNeZero ℂ V 2 two_ne_zero) where
  herm := hH
  pos := hP
  selfDual := hsd
  semi := hα
  isom := by
    intro x y
    simp
  semi' := by rw [img_neg]; exact hα
  inv := fun x hx => (semiCharBasic V H hH Λ α hα).2.1 x hx
  idx₁ := by rw [img_neg, relIdx_self]; exact one_ne_zero
  idx₂ := by rw [img_neg, relIdx_self]; exact one_ne_zero
  cay := by
    intro x
    simp [two_smul]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `hS : IsReps Λ Λ ({0} : Finset V)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[Finset.mem_singleton.mp hx]`.

Conclude with `Λ.zero_mem`. Introduce `x hx y hy _`. Rewrite using `[Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy]`. Introduce `y hy`. Conclude with `⟨0, Finset.mem_singleton_self 0, by simpa using hy⟩`.

Rewrite using `[interReps V H hH Λ Λ α hα F hF {0} hS z, relIdx_self, sumU, Finset.sum_singleton, hF 0 Λ.zero_mem z]`. Simplify using the standard rewrite rules.
-/
theorem inter_self {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ} (hH : IsHerm H) (hα : IsSemiChar H Λ α)
    {F : V → ℂ} (hF : F ∈ fixedBy H α Λ) : inter H α Λ Λ F = F := by
  funext z
  have hS : IsReps Λ Λ ({0} : Finset V) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_singleton.mp hx]
      exact Λ.zero_mem
    · intro x hx y hy _
      rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy]
    · intro y hy
      exact ⟨0, Finset.mem_singleton_self 0, by simpa using hy⟩
  rw [interReps V H hH Λ Λ α hα F hF {0} hS z, relIdx_self, sumU, Finset.sum_singleton,
    hF 0 Λ.zero_mem z]
  simp

end Neg

end UC

/- English proof (translation)
Introduce `V _ _ _ _ _ μ _ H Λ α hH hP hL hsd hα hLine D hD hb`. Establish `hU` using `UC.data_neg hH hP hsd hα`. Take `⟨S, hS⟩` from `(repsExist V _ _ (UC.latA_idx_ne hL hU)).1`. Establish `hD' : IsAddFundamentalDomain (Λ ⊓ imgLat ((LinearEquiv.neg ℂ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) Λ : AddSubgroup V) D μ`. Rewrite using `[UC.img_neg, inf_idem]`.

Conclude with `hD`. Take `⟨c, hc, hval⟩` from `UC.const_value μ hL hU hLine hD' hb hS`. Establish `hcard` using `UC.sqrt_card hL hU hS`. Establish `hphi` using `UC.norm_sum_phi hU hS`. Rewrite `hval`, `hcard` using `[UC.img_neg, UC.relIdx_self]`.

Rewrite `hc` using `[UC.img_neg]`. Take `⟨w, z, hwz⟩` from `UC.kerPNonzero V H Λ α hH hP hL hsd hα`. Establish `hm` using `(UC.kerPTh V H Λ α hH hP hL hα w).2`. Establish `hc'` using `hc _ hm`. Rewrite `hc'` using `[UC.inter_self hH hα hm.2]`.

Establish `h1 : kerP H α Λ (-z) w = c * kerP H α Λ z w`. Use `congrFun hc' z` as an intermediate fact. Simplify `this` using `[pullInv]`. Establish `h2 : kerP H α Λ z w = c * kerP H α Λ (-z) w`. Use `congrFun hc' (-z)` as an intermediate fact.

Simplify `this` using `[pullInv]`. Establish `hc2 : c * c = 1`. Rewrite `h2` using `[h1, ← mul_assoc]`. Conclude with `(mul_right_cancel₀ hwz (by rw [one_mul]; exact h2)).symm`. Establish `hcn : ‖c‖ = 1`.

Establish `h` using `congrArg norm hc2`. Rewrite `h` using `[norm_mul, norm_one]`. Use polynomial arithmetic with `[norm_nonneg c]`. Establish `hγ : 0 < ∫ z, wt H z ∂μ` using `(UC.gaussIntegrable V μ H hH hP Real.pi Real.pi_pos).2`. Establish `hdt0 : LinearMap.det ((LinearEquiv.smulOfNeZero ℂ V 2 two_ne_zero : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) ≠ 0` using `(LinearEquiv.isUnit_det' _).ne_zero`.

Establish `hn` using `congrArg norm hval`. Rewrite `hn` using `[norm_mul, norm_mul, norm_mul, norm_div, hcn, hphi, hcard, Complex.norm_real, Complex.norm_real, norm_inv, Complex.norm_real]`. Simplify using `only [Nat.cast_one, Real.sqrt_one, norm_one, inv_one, one_mul] at hn`. Rewrite `hn` using `[Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_of_nonneg (le_of_lt hγ)]`. Rewrite using `[hn]`.

Establish `: ‖LinearMap.det ((LinearEquiv.smulOfNeZero ℂ V 2 two_ne_zero : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)‖ ≠ 0` using `norm_ne_zero_iff.mpr hdt0`. Clear the denominators using the available nonvanishing facts.
-/
theorem SelfDualCovolume_proof : SelfDualCovolume := by
  intro V _ _ _ _ _ μ _ H Λ α hH hP hL hsd hα hLine D hD hb
  have hU := UC.data_neg hH hP hsd hα
  obtain ⟨S, hS⟩ := (repsExist V _ _ (UC.latA_idx_ne hL hU)).1
  have hD' : IsAddFundamentalDomain
      (Λ ⊓ imgLat ((LinearEquiv.neg ℂ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) Λ : AddSubgroup V) D μ := by
    rw [UC.img_neg, inf_idem]
    exact hD
  obtain ⟨c, hc, hval⟩ := UC.const_value μ hL hU hLine hD' hb hS
  have hcard := UC.sqrt_card hL hU hS
  have hphi := UC.norm_sum_phi hU hS
  rw [UC.img_neg, UC.relIdx_self] at hval hcard
  rw [UC.img_neg] at hc

  obtain ⟨w, z, hwz⟩ := UC.kerPNonzero V H Λ α hH hP hL hsd hα
  have hm := (UC.kerPTh V H Λ α hH hP hL hα w).2
  have hc' := hc _ hm
  rw [UC.inter_self hH hα hm.2] at hc'
  have h1 : kerP H α Λ (-z) w = c * kerP H α Λ z w := by
    have := congrFun hc' z
    simpa [pullInv] using this
  have h2 : kerP H α Λ z w = c * kerP H α Λ (-z) w := by
    have := congrFun hc' (-z)
    simpa [pullInv] using this
  have hc2 : c * c = 1 := by
    rw [h1, ← mul_assoc] at h2
    exact (mul_right_cancel₀ hwz (by rw [one_mul]; exact h2)).symm
  have hcn : ‖c‖ = 1 := by
    have h := congrArg norm hc2
    rw [norm_mul, norm_one] at h
    nlinarith [norm_nonneg c]
  have hγ : 0 < ∫ z, wt H z ∂μ := (UC.gaussIntegrable V μ H hH hP Real.pi Real.pi_pos).2
  have hdt0 : LinearMap.det ((LinearEquiv.smulOfNeZero ℂ V 2 two_ne_zero : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) ≠ 0 :=
    (LinearEquiv.isUnit_det' _).ne_zero
  have hn := congrArg norm hval
  rw [norm_mul, norm_mul, norm_mul, norm_div, hcn, hphi, hcard, Complex.norm_real, Complex.norm_real,
    norm_inv, Complex.norm_real] at hn
  simp only [Nat.cast_one, Real.sqrt_one, norm_one, inv_one, one_mul] at hn
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_of_nonneg (le_of_lt hγ)] at hn
  rw [hn]
  have : ‖LinearMap.det ((LinearEquiv.smulOfNeZero ℂ V 2 two_ne_zero : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hdt0
  field_simp

/- English proof (translation)
Introduce `V _ _ _ H Λ α δ Ae hL hU hLine S hS θ hθ`. Set `_ : MeasurableSpace V` to `borel V`. Establish `: BorelSpace V` using `⟨rfl⟩`. Set `μ : Measure V` to `Measure.addHaar`. Take `⟨D, hDf, hDb, hDpos, hsub⟩` from `fundamentalDomainExists V μ Λ hL`.

Establish `hidx : relIdx (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ) Λ = relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ` using `AddSubgroup.inf_relIndex_left _ _`. Take `⟨D', hD'f, hD'b, hD'm⟩` from `hsub (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ) inf_le_left (by rw [hidx]; exact hU.idx₁)`. Take `⟨c, hc, hval⟩` from `UC.const_value μ hL hU hLine hD'f hD'b hS`. Establish `hcov` using `SelfDualCovolume_proof V μ H Λ α hU.herm hU.pos hL hU.selfDual hU.semi hLine D hDf hDb`. Establish `hcard` using `UC.sqrt_card hL hU hS`.

Establish `hie` using `indexEq V H hU.herm Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) hU.selfDual (Cay.selfDual_img H Λ δ hU.isom hU.selfDual) hU.idx₂ hU.idx₁`. Rewrite using `[hc θ hθ]`. Use `congr 1`. Rewrite using `[gaussC, hcard]`. Rewrite `hval` using `[hD'm, hidx, hie, hcov]`.

Rewrite `hval` using `[← hcov]`. Take `⟨n, hn⟩ : ∃ n : ℝ, n = (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ : ℝ)` from `⟨_, rfl⟩`. Rewrite `hval`, the goal using `[← hn]`. Establish `hnpos : 0 < n`. Rewrite using `[hn]`.

Conclude with `Nat.pos_of_ne_zero hU.idx₁` after adjusting the coercions. Take `⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt n` from `⟨_, rfl⟩`. Establish `hspos : 0 < s` using `by rw [hs]; exact Real.sqrt_pos.mpr hnpos`. Establish `hss : n = s * s` using `by rw [hs]; exact (Real.mul_self_sqrt hnpos.le).symm`. Rewrite `hval`, the goal using `[← hs]`.

Rewrite `hval` using `[hss]`. Establish `hdt0 : LinearMap.det (Ae : V →ₗ[ℂ] V) ≠ 0` using `(LinearEquiv.isUnit_det' Ae).ne_zero`. Establish `hdn : ((‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ : ℝ) : ℂ) ≠ 0`. Conclude with `norm_ne_zero_iff.mpr hdt0` after adjusting the coercions. Establish `hsc : (s : ℂ) ≠ 0` using `by exact_mod_cast hspos.ne'`.

Establish `hDc : (((μ D).toReal : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hDpos.ne'`. Move the coercions through the operations in `at hval ⊢`. Clear denominators, using `at hval ⊢` for the nonvanishing conditions. Take the linear combination `hval`.
-/
theorem UnitaryConstant_proof : UnitaryConstant := by
  intro V _ _ _ H Λ α δ Ae hL hU hLine S hS θ hθ
  let _ : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  let μ : Measure V := Measure.addHaar
  obtain ⟨D, hDf, hDb, hDpos, hsub⟩ := fundamentalDomainExists V μ Λ hL
  have hidx : relIdx (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ) Λ = relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ :=
    AddSubgroup.inf_relIndex_left _ _
  obtain ⟨D', hD'f, hD'b, hD'm⟩ := hsub (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ) inf_le_left
    (by rw [hidx]; exact hU.idx₁)
  obtain ⟨c, hc, hval⟩ := UC.const_value μ hL hU hLine hD'f hD'b hS
  have hcov := SelfDualCovolume_proof V μ H Λ α hU.herm hU.pos hL hU.selfDual hU.semi hLine D hDf hDb
  have hcard := UC.sqrt_card hL hU hS
  have hie := indexEq V H hU.herm Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) hU.selfDual
    (Cay.selfDual_img H Λ δ hU.isom hU.selfDual) hU.idx₂ hU.idx₁
  rw [hc θ hθ]
  congr 1
  rw [gaussC, hcard]
  rw [hD'm, hidx, hie, hcov] at hval
  rw [← hcov] at hval
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ : ℝ) := ⟨_, rfl⟩
  rw [← hn] at hval ⊢
  have hnpos : 0 < n := by
    rw [hn]
    exact_mod_cast Nat.pos_of_ne_zero hU.idx₁
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt n := ⟨_, rfl⟩
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hnpos
  have hss : n = s * s := by rw [hs]; exact (Real.mul_self_sqrt hnpos.le).symm
  rw [← hs] at hval ⊢
  rw [hss] at hval
  have hdt0 : LinearMap.det (Ae : V →ₗ[ℂ] V) ≠ 0 := (LinearEquiv.isUnit_det' Ae).ne_zero
  have hdn : ((‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hdt0
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  have hDc : (((μ D).toReal : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
  push_cast at hval ⊢
  field_simp at hval ⊢
  linear_combination hval

/- English proof (translation)
The claim follows from `UnitaryEighth_of UnitaryConstant_proof (UnitaryGauss_of gaussSumEighthPower) unitary_index`.
-/
theorem UnitaryEighth_proof : UnitaryEighth :=
  UnitaryEighth_of UnitaryConstant_proof (UnitaryGauss_of gaussSumEighthPower) unitary_index

end Formalism.L2.Th1.H
