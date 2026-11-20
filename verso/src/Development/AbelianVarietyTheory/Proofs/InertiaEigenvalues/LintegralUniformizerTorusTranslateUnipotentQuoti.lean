import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralQuotientComparisonFundamentalDomainsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureInverseInvariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureUniformizerTranslateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainRationalUpperUnitriangulaStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

namespace ChangeVar

/- English proof (translation)
The claim follows from `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Ad E)) haveI : LocallyCompactS …`.
-/
theorem locallyCompact_GA_chv : LocallyCompactSpace (GA E n) :=
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Ad E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

/- English proof (translation)
The claim follows from `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E)) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Ad E)) haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ := MulOpposite.opH …`.
-/
theorem secondCountable_GA_chv : SecondCountableTopology (GA E n) :=
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E`. Establish `hv : Continuous fun g : GA E n => (g : Matrix (Fin n) (Fin n) (Ad E))` using `Units.continuous_val`. Establish `: ((NA E n : Subgroup (GA E n)) : Set (GA E n)) = (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : j < i), {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i j = 0}) ∩ ⋂ i : Fin n, {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i i = 1}`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]`.

Conclude with `GlobalTheory.SmGL.mem_unipB (Ad E)`. Rewrite using `[this]`. Use `IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_) (isClosed_iInter fun i => ?_)` and prove the remaining obligations. Conclude with `isClosed_eq (hv.matrix_elem i j) continuous_const`. Conclude with `isClosed_eq (hv.matrix_elem i i) continuous_const`.
-/
theorem isClosed_NA : IsClosed ((NA E n : Subgroup (GA E n)) : Set (GA E n)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  have hv : Continuous fun g : GA E n => (g : Matrix (Fin n) (Fin n) (Ad E)) := Units.continuous_val
  have : ((NA E n : Subgroup (GA E n)) : Set (GA E n)) =
      (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : j < i), {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i j = 0}) ∩
      ⋂ i : Fin n, {g : GA E n | (g : Matrix (Fin n) (Fin n) (Ad E)) i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact GlobalTheory.SmGL.mem_unipB (Ad E)
  rw [this]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_)
    (isClosed_iInter fun i => ?_)
  · exact isClosed_eq (hv.matrix_elem i j) continuous_const
  · exact isClosed_eq (hv.matrix_elem i i) continuous_const

/- English proof (translation)
Introduce and unpack `_ ⟨u, hu, rfl⟩`. Take `⟨h1, h2⟩` from `(GlobalTheory.SmGL.mem_unipB E).1 hu`. Use `(GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap E (Ad E) ((u : Matrix (Fin n) (Fin n) E) i j) = 0`. Rewrite using `[h1 i j hij, map_zero]`.

Express the relevant statement in the definitionally equal form `algebraMap E (Ad E) ((u : Matrix (Fin n) (Fin n) E) i i) = 1`. Rewrite using `[h2 i, map_one]`.
-/
theorem NE_le_NA : NE E n ≤ NA E n := by
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB E).1 hu
  refine (GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · change algebraMap E (Ad E) ((u : Matrix (Fin n) (Fin n) E) i j) = 0
    rw [h1 i j hij, map_zero]
  · change algebraMap E (Ad E) ((u : Matrix (Fin n) (Fin n) E) i i) = 1
    rw [h2 i, map_one]

/- English proof (translation)
Use `haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable`. Use `haveI : Countable (GL (Fin n) E) := Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j) fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)`. Conclude with `((Set.countable_range (ratGL E n)).mono (by rintro _ ⟨u, -, rfl⟩; exact ⟨u, rfl⟩)).to_subtype`.
-/
theorem countable_NE : Countable (NE E n) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j)
      fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  exact ((Set.countable_range (ratGL E n)).mono (by rintro _ ⟨u, -, rfl⟩; exact ⟨u, rfl⟩)).to_subtype

/- English proof (translation)
Establish `h` using `diagT_conj_mem (n := n) (R := Ad E) (fun i => finId E (adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l)))⁻¹ hu`. Rewrite `h` using `[map_inv, inv_inv, ← tl_eq_diagT]`. Conclude with `h`.
-/
theorem tl_inv_conj_mem (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {u : GA E n} (hu : u ∈ NA E n) :
    (tl n ϖ l)⁻¹ * u * tl n ϖ l ∈ NA E n := by
  have h := diagT_conj_mem (n := n) (R := Ad E)
    (fun i => finId E (adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l)))⁻¹ hu
  rw [map_inv, inv_inv, ← tl_eq_diagT] at h
  exact h

end ChangeVar

open ChangeVar

/- English proof (translation)
Introduce `E _ _ n _ _ μ _ ϖ hϖ l 𝓕 h𝓕 F hF hinv`. Use `haveI : LocallyCompactSpace (GA E n) := locallyCompact_GA_chv`. Use `haveI : SecondCountableTopology (GA E n) := secondCountable_GA_chv`. Use `haveI : SigmaCompactSpace (GA E n) := sigmaCompactSpace_of_locallyCompact_secondCountable`. Use `haveI : SFinite μ := inferInstance`.

Use `haveI : MeasurableMul₂ (GA E n) := inferInstance`. Use `haveI : MeasurableInv (GA E n) := inferInstance`. Use `haveI : LocallyCompactSpace (NA E n) := isClosed_NA.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology (NA E n) := isClosed_NA.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology`. Use `haveI : SigmaCompactSpace (NA E n) := sigmaCompactSpace_of_locallyCompact_secondCountable`.

Use `haveI := countable_NE (E := E) (n := n)`. Use `set ν : Measure (NA E n) := Measure.haar with hν`. Use `haveI : ν.IsInvInvariant := GlobalTheory.T.haar_measure_inverse_invariant E n ν`. Use `haveI : SFinite ν := inferInstance`. Take `⟨D, hD, hD0, hDtop⟩` from `GlobalTheory.T.exists_fundamentalDomain_rational_upperUnitriangular E n ν`.

Use `set t := tl n ϖ l with ht`. Set `cM : NA E n ≃* NA E n` to `{ toFun := fun u => ⟨t * u * t⁻¹, tl_conj_mem ϖ l u.2⟩ invFun := fun u => ⟨t⁻¹ * u * t, tl_inv_conj_mem ϖ l u.2⟩ left_inv := fun u => Subtype.ext (by simp only; group) right_inv := fun u => Subtype.ext (by simp only; group) map_mul' := fun u v => Subtype.ext (by simp only [Subgro …`. Establish `hcM : ∀ u : NA E n, ((cM u : NA E n) : GA E n) = t * u * t⁻¹` using `fun _ => rfl`. Set `c : NA E n ≃ᵐ NA E n` to `{ toEquiv := cM.toEquiv measurable_toFun := ((measurable_mul_const _).comp ((measurable_const_mul _).comp measurable_subtype_coe)).subtype_mk measurable_invFun := ((measurable_mul_const _).comp ((measurable_const_mul _).comp measurable_subtype_coe)).subtype_mk }`. Establish `hmod : ∀ A, MeasurableSet A → ν (c ⁻¹' A) = ENNReal.ofReal (dinv n l) * ν A`.

Introduce `A hA`. Rewrite using `[← GlobalTheory.T.haar_measure_uniformizer_translate E n ν ϖ hϖ l A hA]`. Use `congr 1`. Use extensionality with `u`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨_, h, rfl⟩`. Introduce and unpack `⟨a, ha, hau⟩`. Use `ha` and compare the differences between its conclusion and the goal.

Conclude with `Subtype.ext hau.symm`. Establish `hmap : Measure.map c ν = ENNReal.ofReal (dinv n l) • ν`. Use extensionality with `A hA`. Rewrite using `[Measure.map_apply c.measurable hA, hmod A hA, Measure.smul_apply, smul_eq_mul]`. Establish `hmod' : ∀ A, ν (c ⁻¹' A) = ENNReal.ofReal (dinv n l) * ν A` using `fun A => by`.

Rewrite using `[← c.map_apply, hmap, Measure.smul_apply, smul_eq_mul]`. Use `set Γ : Subgroup (NA E n) := (NE E n).subgroupOf (NA E n) with hΓ`. Use `set Γ' : Subgroup (NA E n) := Γ.comap cM.toMonoidHom with hΓ'`. Establish `hΓmap : Γ.map (NA E n).subtype = NE E n`. Rewrite using `[hΓ, Subgroup.subgroupOf_map_subtype, inf_of_le_left NE_le_NA]`.

Establish `hmemΓ' : ∀ x : GA E n, x ∈ Γ'.map (NA E n).subtype ↔ t * x * t⁻¹ ∈ NE E n`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hy)`.

Introduce `hx`. Establish `hxN : x ∈ NA E n`. Use `tl_inv_conj_mem ϖ l (NE_le_NA hx)` as an intermediate fact. Rewrite `this` using `[show t⁻¹ * (t * x * t⁻¹) * t = x by group]`. Then use the resulting hypothesis. Conclude with `⟨⟨x, hxN⟩, Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 hx), rfl⟩`.

Use `haveI : Countable Γ := Function.Injective.countable (f := fun g : Γ => (⟨(g : NA E n), g.2⟩ : NE E n)) fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : NE E n => (z : GA E n)) h))`. Use `haveI : Countable Γ' := Function.Injective.countable (f := fun g : Γ' => (⟨cM g, g.2⟩ : Γ)) fun a b h => Subtype.ext (cM.injective (congrArg (fun z : Γ => (z : NA E n)) h))`. Establish `hD' : IsFundamentalDomain Γ' (c ⁻¹' D) ν`. Establish `hsymm : ∀ u : NA E n, ((cM.symm u : NA E n) : GA E n) = t⁻¹ * u * t` using `fun _ => rfl`. Establish `hc : ∀ u : NA E n, c u = cM u` using `fun _ => rfl`.

Use `hD.preimage_of_equiv (f := c) ⟨c.measurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩ (e := fun g : Γ => (⟨cM.symm g, Subgroup.mem_comap.2 (by` and prove the remaining obligations. Rewrite using `[MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]`. Conclude with `g.2)⟩ : Γ'))`. Use the proof step `⟨fun a b h => Subtype.ext (cM.symm.injective (congrArg (fun z : Γ' => (z : NA E n)) h)), fun g => ⟨⟨cM g, g.2⟩, Subtype.ext (by simp only [MulEquiv.symm_apply_apply])⟩⟩ ?_`. Introduce `g x`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.smul_def, smul_eq_mul, hc, hcM, hsymm, Subgroup.coe_mul]`. Use `group`. Establish `h𝓕Γ : IsFundamentalDomain (Γ.map (NA E n).subtype) 𝓕 μ` using `by rw [hΓmap]; exact h𝓕`. Establish `h𝓕' : IsFundamentalDomain (Γ'.map (NA E n).subtype) ((fun g => t * g) ⁻¹' 𝓕) μ`.

Use `h𝓕.preimage_of_equiv (f := fun g => t * g) (measurePreserving_mul_left μ t).quasiMeasurePreserving (e := fun g : NE E n => (⟨t⁻¹ * g * t, (hmemΓ' _).2 (by convert g.2 using 1; group)⟩ : Γ'.map (NA E n).subtype)) ⟨fun a b h => Subtype.ext (by` and prove the remaining obligations. Establish `h'` using `congrArg (fun z : Γ'.map (NA E n).subtype => t * (z : GA E n) * t⁻¹) h`. Simplify `h'),` using `[mul_assoc]`. Use `fun y => ⟨⟨t * y * t⁻¹, (hmemΓ' y).1 y.2⟩, Subtype.ext (by simp only; group)⟩⟩ ?_`. Introduce `g x`.

Express the relevant statement in the definitionally equal form `t * ((t⁻¹ * g * t) * x) = (g : GA E n) * (t * x)`. Use `group`. Establish `key` using `GlobalTheory.T.lintegral_quotient_comparison_fundamentalDomains μ (NA E n) ν Γ Γ' D (c ⁻¹' D) hD hD' 𝓕 ((fun g => t * g) ⁻¹' 𝓕) h𝓕Γ h𝓕' F hF (fun h g => hinv h h.2 g)`. Rewrite `key` using `[hmod']`. Establish `hchg : ∫⁻ g in 𝓕, F (t⁻¹ * g) ∂μ = ∫⁻ g in (fun g => t * g) ⁻¹' 𝓕, F g ∂μ`.

Rewrite using `[← (measurePreserving_mul_left μ t).setLIntegral_comp_preimage_emb (MeasurableEquiv.mulLeft t).measurableEmbedding (fun b => F (t⁻¹ * b)) 𝓕]`. Simplify using `only [inv_mul_cancel_left]`. Rewrite using `[hchg]`. Use `((ENNReal.mul_right_inj hD0.ne' hDtop.ne).1 ?_)` and prove the remaining obligations. Rewrite using `[← key]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lintegral_tl_inv_mul : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (μ : Measure (GA E n)) [μ.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (𝓕 : Set (GA E n)),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E n) 𝓕 μ → ∀ F : GA E n → ℝ≥0∞, Measurable F →
    (∀ u ∈ GlobalTheory.CellDec.NA E n, ∀ g, F (u * g) = F g) →
    ∫⁻ g in 𝓕, F ((GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g) ∂μ = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ∫⁻ g in 𝓕, F g ∂μ := by
  intro E _ _ n _ _ μ _ ϖ hϖ l 𝓕 h𝓕 F hF hinv
  haveI : LocallyCompactSpace (GA E n) := locallyCompact_GA_chv
  haveI : SecondCountableTopology (GA E n) := secondCountable_GA_chv
  haveI : SigmaCompactSpace (GA E n) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite μ := inferInstance
  haveI : MeasurableMul₂ (GA E n) := inferInstance
  haveI : MeasurableInv (GA E n) := inferInstance
  haveI : LocallyCompactSpace (NA E n) := isClosed_NA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (NA E n) :=
    isClosed_NA.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : SigmaCompactSpace (NA E n) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI := countable_NE (E := E) (n := n)
  set ν : Measure (NA E n) := Measure.haar with hν
  haveI : ν.IsInvInvariant := GlobalTheory.T.haar_measure_inverse_invariant E n ν
  haveI : SFinite ν := inferInstance
  obtain ⟨D, hD, hD0, hDtop⟩ := GlobalTheory.T.exists_fundamentalDomain_rational_upperUnitriangular E n ν
  set t := tl n ϖ l with ht

  let cM : NA E n ≃* NA E n :=
    { toFun := fun u => ⟨t * u * t⁻¹, tl_conj_mem ϖ l u.2⟩
      invFun := fun u => ⟨t⁻¹ * u * t, tl_inv_conj_mem ϖ l u.2⟩
      left_inv := fun u => Subtype.ext (by simp only; group)
      right_inv := fun u => Subtype.ext (by simp only; group)
      map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcM : ∀ u : NA E n, ((cM u : NA E n) : GA E n) = t * u * t⁻¹ := fun _ => rfl
  let c : NA E n ≃ᵐ NA E n :=
    { toEquiv := cM.toEquiv
      measurable_toFun := ((measurable_mul_const _).comp ((measurable_const_mul _).comp measurable_subtype_coe)).subtype_mk
      measurable_invFun := ((measurable_mul_const _).comp ((measurable_const_mul _).comp measurable_subtype_coe)).subtype_mk }
  have hmod : ∀ A, MeasurableSet A → ν (c ⁻¹' A) = ENNReal.ofReal (dinv n l) * ν A := by
    intro A hA
    rw [← GlobalTheory.T.haar_measure_uniformizer_translate E n ν ϖ hϖ l A hA]
    congr 1
    ext u
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨a, ha, hau⟩
      convert ha
      exact Subtype.ext hau.symm
  have hmap : Measure.map c ν = ENNReal.ofReal (dinv n l) • ν := by
    ext A hA
    rw [Measure.map_apply c.measurable hA, hmod A hA, Measure.smul_apply, smul_eq_mul]
  have hmod' : ∀ A, ν (c ⁻¹' A) = ENNReal.ofReal (dinv n l) * ν A := fun A => by
    rw [← c.map_apply, hmap, Measure.smul_apply, smul_eq_mul]

  set Γ : Subgroup (NA E n) := (NE E n).subgroupOf (NA E n) with hΓ
  set Γ' : Subgroup (NA E n) := Γ.comap cM.toMonoidHom with hΓ'
  have hΓmap : Γ.map (NA E n).subtype = NE E n := by
    rw [hΓ, Subgroup.subgroupOf_map_subtype, inf_of_le_left NE_le_NA]
  have hmemΓ' : ∀ x : GA E n, x ∈ Γ'.map (NA E n).subtype ↔ t * x * t⁻¹ ∈ NE E n := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hy)
    · intro hx
      have hxN : x ∈ NA E n := by
        have := tl_inv_conj_mem ϖ l (NE_le_NA hx)
        rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at this
      exact ⟨⟨x, hxN⟩, Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  haveI : Countable Γ := Function.Injective.countable (f := fun g : Γ => (⟨(g : NA E n), g.2⟩ : NE E n))
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : NE E n => (z : GA E n)) h))
  haveI : Countable Γ' := Function.Injective.countable (f := fun g : Γ' => (⟨cM g, g.2⟩ : Γ))
    fun a b h => Subtype.ext (cM.injective (congrArg (fun z : Γ => (z : NA E n)) h))

  have hD' : IsFundamentalDomain Γ' (c ⁻¹' D) ν := by
    have hsymm : ∀ u : NA E n, ((cM.symm u : NA E n) : GA E n) = t⁻¹ * u * t := fun _ => rfl
    have hc : ∀ u : NA E n, c u = cM u := fun _ => rfl
    refine hD.preimage_of_equiv (f := c) ⟨c.measurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
      (e := fun g : Γ => (⟨cM.symm g, Subgroup.mem_comap.2 (by
          rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]; exact g.2)⟩ : Γ'))
      ⟨fun a b h => Subtype.ext (cM.symm.injective (congrArg (fun z : Γ' => (z : NA E n)) h)),
        fun g => ⟨⟨cM g, g.2⟩, Subtype.ext (by simp only [MulEquiv.symm_apply_apply])⟩⟩ ?_
    intro g x
    apply Subtype.ext
    simp only [Subgroup.smul_def, smul_eq_mul, hc, hcM, hsymm, Subgroup.coe_mul]
    group
  have h𝓕Γ : IsFundamentalDomain (Γ.map (NA E n).subtype) 𝓕 μ := by rw [hΓmap]; exact h𝓕
  have h𝓕' : IsFundamentalDomain (Γ'.map (NA E n).subtype) ((fun g => t * g) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv (f := fun g => t * g) (measurePreserving_mul_left μ t).quasiMeasurePreserving
      (e := fun g : NE E n => (⟨t⁻¹ * g * t, (hmemΓ' _).2 (by convert g.2 using 1; group)⟩ : Γ'.map (NA E n).subtype))
      ⟨fun a b h => Subtype.ext (by
          have h' := congrArg (fun z : Γ'.map (NA E n).subtype => t * (z : GA E n) * t⁻¹) h
          simpa [mul_assoc] using h'),
        fun y => ⟨⟨t * y * t⁻¹, (hmemΓ' y).1 y.2⟩, Subtype.ext (by simp only; group)⟩⟩ ?_
    intro g x
    change t * ((t⁻¹ * g * t) * x) = (g : GA E n) * (t * x)
    group
  have key := GlobalTheory.T.lintegral_quotient_comparison_fundamentalDomains μ (NA E n) ν Γ Γ' D (c ⁻¹' D) hD hD' 𝓕 ((fun g => t * g) ⁻¹' 𝓕) h𝓕Γ h𝓕' F hF
    (fun h g => hinv h h.2 g)
  rw [hmod'] at key
  have hchg : ∫⁻ g in 𝓕, F (t⁻¹ * g) ∂μ = ∫⁻ g in (fun g => t * g) ⁻¹' 𝓕, F g ∂μ := by
    rw [← (measurePreserving_mul_left μ t).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.mulLeft t).measurableEmbedding (fun b => F (t⁻¹ * b)) 𝓕]
    simp only [inv_mul_cancel_left]
  rw [hchg]
  refine ((ENNReal.mul_right_inj hD0.ne' hDtop.ne).1 ?_)
  rw [← key]
  ring

end GlobalTheory.CellDec
