import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletionStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AbOverSubfield

/- English proof (translation)
Establish `hint : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A` using `fun x => by`. Establish `h : IsIntegral A (algebraMap K Ω (x : K))` using `(x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom).tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h`. Rewrite using `[← hy]`. Conclude with `y.2`.

Set `f : 𝓞 K →+* A` to `((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hint`. Set `P : Ideal (𝓞 K)` to `(IsLocalRing.maximalIdeal A).comap f`. Establish `hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P` using `fun x => (A.valuation_lt_one_iff (f x)).symm`. Establish `hu : v.asIdeal = P.comap (algebraMap (𝓞 F) (𝓞 K))`. Use extensionality with `x`.

Rewrite using `[← hA x, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply F K Ω]`. Both sides reduce to the same expression. Establish `hne : P ≠ ⊥`. Introduce `h`. Apply `v.ne_bot` to reduce the goal to its premises.

Rewrite using `[hu, h]`. Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)`. Conclude with `⟨⟨P, inferInstance, hne⟩, hP⟩`.
-/
theorem exists_place_between {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F K] [Algebra K Ω] [Algebra F Ω] [IsScalarTower F K Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 K), IsPlaceOver A w := by
  have hint : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap K Ω (x : K)) :=
      (x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hint
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
    ext x
    rw [← hA x, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply F K Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP⟩

/- English proof (translation)
Establish `: ∀ u ∈ T, ∃ a : 𝓞 F, a ∈ u.asIdeal ∧ a ∉ v.asIdeal`. Introduce `u hu`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hle : u.asIdeal ≤ v.asIdeal` using `hc`.

Use `u.isMaximal.eq_of_le v.isPrime.ne_top hle` as an intermediate fact. Conclude with `hvT (HeightOneSpectrum.ext this ▸ hu)`. Use `choose! a ha using this`. Use `⟨∏ u ∈ T, a u, ?_, fun u hu => ?_⟩` and prove the remaining obligations. Introduce `hmem`.

Take `⟨u, hu, hau⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hmem`. Conclude with `(ha u hu).2 hau`. Rewrite using `[← Finset.mul_prod_erase T a hu]`. Conclude with `Ideal.mul_mem_right _ _ (ha u hu).1`.
-/
theorem exists_avoid {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hvT : v ∉ T) :
    ∃ c : 𝓞 F, c ∉ v.asIdeal ∧ ∀ u ∈ T, c ∈ u.asIdeal := by
  classical
  have : ∀ u ∈ T, ∃ a : 𝓞 F, a ∈ u.asIdeal ∧ a ∉ v.asIdeal := by
    intro u hu
    by_contra hc
    push_neg at hc
    have hle : u.asIdeal ≤ v.asIdeal := hc
    have := u.isMaximal.eq_of_le v.isPrime.ne_top hle
    exact hvT (HeightOneSpectrum.ext this ▸ hu)
  choose! a ha using this
  refine ⟨∏ u ∈ T, a u, ?_, fun u hu => ?_⟩
  · intro hmem
    obtain ⟨u, hu, hau⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hmem
    exact (ha u hu).2 hau
  · rw [← Finset.mul_prod_erase T a hu]
    exact Ideal.mul_mem_right _ _ (ha u hu).1

end GlobalTheory.AbOverSubfield

namespace GlobalTheory.AbOverSubfield

/- English proof (translation)
Introduce `Ω _ F _ _ _ _ A v h T hvT F₁ hF₁ hre V hV hcomm`. Use `haveI : NumberField F₁ := NumberField.of_module_finite F F₁`. Use `haveI : Algebra.IsAlgebraic F₁ Ω := Algebra.IsAlgebraic.tower_top (K := F) F₁`. Use `haveI : IsAlgClosure F₁ Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩`. Use `haveI : IsTotallyReal F₁ := ⟨fun w => NumberField.InfinitePlace.isReal_iff.2 (hre _)⟩`.

Set `ρ : (Ω ≃ₐ[F₁] Ω) →* (Ω ≃ₐ[F] Ω)` to `AlgEquiv.restrictScalarsHom F`. Establish `hρdec : ∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F₁] Ω), ρ g ∈ Dec (F` using `F) B ↔ g ∈ Dec (F := F₁) B := fun _ _ => Iff.rfl`. Establish `hρfix : ∀ g, ρ g ∈ F₁.fixingSubgroup` using `fun g => by`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`.

Conclude with `g.commutes ⟨x, hx⟩`. Establish `hlift : ∀ g ∈ F₁.fixingSubgroup, ∃ g' : Ω ≃ₐ[F₁] Ω, ρ g' = g` using `fun g hg => ⟨IntermediateField.fixingSubgroupEquiv F₁ ⟨g, hg⟩, by ext x; rfl⟩`. Take `⟨v₁, hv₁⟩` from `exists_place_between (K := F₁) h`. Take `⟨c, hcv, hcT⟩` from `exists_avoid v T hvT`. Use `set c₁ : 𝓞 F₁ := algebraMap (𝓞 F) (𝓞 F₁) c with hc₁`.

Establish `hc₁val : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F₁)), IsPlaceOver B w → (c₁ ∈ w.asIdeal ↔ B.valuation (algebraMap F Ω (c : F)) < 1)`. Introduce `B w hw`. Rewrite using `[← hw, IsScalarTower.algebraMap_apply F F₁ Ω]`. Both sides reduce to the same expression. Establish `hc0 : c₁ ≠ 0`.

Introduce `h0`. Apply `hcv` to reduce the goal to its premises. Establish `: c = 0` using `(FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 F₁)) (by rw [← hc₁, h0, map_zero])`. Rewrite using `[this]`. Conclude with `v.asIdeal.zero_mem`.

Establish `hfin : {w : HeightOneSpectrum (𝓞 F₁) | c₁ ∈ w.asIdeal}.Finite` using `(Ideal.finite_factors (I := Ideal.span {c₁}) (by simpa using hc0)).subset fun w hw => Ideal.dvd_span_singleton.mpr hw`. Use `set T₁ := hfin.toFinset`. Establish `hv₁T : v₁ ∉ T₁`. Rewrite using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, hc₁val A v₁ hv₁, h]`. Conclude with `hcv`.

Set `V₁ : Subgroup (Dec (F` to `F₁) A) := (V.comap ρ).comap (Dec (F := F₁) A).subtype`. Establish `hV₁ : IsOpen (V₁ : Set (Dec (F` using `F₁) A)) := by`. Take `⟨E, hE, hEV⟩` from `(krullTopology_mem_nhds_one_iff F Ω (V : Set (G F Ω))).1 (hV.mem_nhds V.one_mem)`. Use `haveI : FiniteDimensional F (E ⊔ F₁ : IntermediateField F Ω) := IntermediateField.finiteDimensional_sup _ _`. Set `E₁ : IntermediateField F₁ Ω` to `IntermediateField.extendScalars (le_sup_right : F₁ ≤ E ⊔ F₁)`.

Use `haveI : FiniteDimensional F E₁ := (inferInstance : FiniteDimensional F (E ⊔ F₁ : IntermediateField F Ω))`. Use `haveI : FiniteDimensional F₁ E₁ := FiniteDimensional.right F F₁ _`. Use `Subgroup.isOpen_mono (H₁ := (E₁.fixingSubgroup).comap (Dec (F := F₁) A).subtype) ?_ ((E₁.fixingSubgroup_isOpen).preimage continuous_subtype_val)` and prove the remaining obligations. Introduce `g hg`. Simplify using `only [V₁, Subgroup.mem_comap]`.

Apply `hEV` to reduce the goal to its premises. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Rewrite `hg` using `[Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]`. Conclude with `hg x ((IntermediateField.mem_extendScalars _).2 (le_sup_left (a := E) hx))`.

Establish `hcomm₁ : commutator (Dec (F` using `F₁) A) ≤ V₁ := by`. Rewrite using `[commutator_def, Subgroup.commutator_le]`. Introduce `g₁ _ g₂ _`. Simplify using `only [V₁, Subgroup.mem_comap, map_commutatorElement]`. Apply `hcomm` to reduce the goal to its premises.

Conclude with `Subgroup.commutator_mem_commutator ⟨(hρdec A _).2 g₁.2, hρfix _⟩ ⟨(hρdec A _).2 g₂.2, hρfix _⟩`. Take `⟨F₂', hfin₂, hab, hreal₂, hiff, hsplit⟩` from `GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion Ω F₁ A v₁ hv₁ V₁ hV₁ hcomm₁ T₁ hv₁T`. Establish `hcomm₂ : commutator (Ω ≃ₐ[F₁] Ω) ≤ F₂'.fixingSubgroup`. Rewrite using `[← F₂'.restrictNormalHom_ker, commutator_def, Subgroup.commutator_le]`. Introduce `x _ y _`.

Rewrite using `[MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]`. Conclude with `IsMulCommutative.is_comm.comm _ _`. Establish `hfix₂ : ∀ g : Ω ≃ₐ[F₁] Ω, ρ g ∈ (F₂'.restrictScalars F).fixingSubgroup ↔ g ∈ F₂'.fixingSubgroup` using `fun _ => Iff.rfl`. Establish `hle : F₁ ≤ F₂'.restrictScalars F`. Introduce `x hx`.

Use `show x ∈ F₂'`. Simplify using `using F₂'.algebraMap_mem ⟨x, hx⟩`. Use `⟨F₂'.restrictScalars F, hle, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `FiniteDimensional.trans F F₁ F₂'`. Rewrite using `[Subgroup.commutator_le]`.

Introduce `g₁ h₁ g₂ h₂`. Take `⟨g₁', rfl⟩` from `hlift g₁ h₁`. Take `⟨g₂', rfl⟩` from `hlift g₂ h₂`. Rewrite using `[← map_commutatorElement, hfix₂]`. Conclude with `hcomm₂ (by rw [commutator_def]; exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))`.

Introduce `φ`. Conclude with `hreal₂ φ`. Introduce and unpack `g ⟨hgA, hg₂⟩`. Establish `hg₁ : g ∈ F₁.fixingSubgroup`. Establish `hg₂' : g ∈ (F₂'.restrictScalars F).fixingSubgroup` using `hg₂`.

Rewrite `hg₂'`, the goal using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Conclude with `hg₂' x (hle hx)`. Take `⟨g', rfl⟩` from `hlift g hg₁`. Use `(hiff ⟨g', (hρdec A g').1 hgA⟩).1 ((hfix₂ g').1 hg₂)` as an intermediate fact.

Conclude with `this`. Introduce `u hu A' hA' g ⟨hgA, hg₁⟩`. Take `⟨g', rfl⟩` from `hlift g hg₁`. Take `⟨w', hw'⟩` from `exists_place_between (K := F₁) hA'`. Establish `hw'T : w' ∈ T₁`.

Rewrite using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, hc₁val A' w' hw', hA']`. Conclude with `hcT u hu`. Conclude with `(hfix₂ g').2 (hsplit w' hw'T A' hw' ((hρdec A' g').1 hgA))`.
-/
theorem exists_abelian_over_subfield : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v) (T : Finset (HeightOneSpectrum (𝓞 F))), v ∉ T → ∀ F₁ : IntermediateField F Ω, FiniteDimensional F F₁ → (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) → ∀ V : Subgroup (G F Ω), IsOpen (V : Set (G F Ω)) → ⁅Dec (F := F) A ⊓ F₁.fixingSubgroup, Dec (F := F) A ⊓ F₁.fixingSubgroup⁆ ≤ V → ∃ F₂ : IntermediateField F Ω, F₁ ≤ F₂ ∧ FiniteDimensional F F₂ ∧ ⁅F₁.fixingSubgroup, F₁.fixingSubgroup⁆ ≤ F₂.fixingSubgroup ∧ (∀ φ : F₂ →+* ℂ, ComplexEmbedding.IsReal φ) ∧ Dec (F := F) A ⊓ F₂.fixingSubgroup ≤ V ∧ ∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Dec (F := F) A' ⊓ F₁.fixingSubgroup ≤ F₂.fixingSubgroup := by
  intro Ω _ F _ _ _ _ A v h T hvT F₁ hF₁ hre V hV hcomm
  haveI : NumberField F₁ := NumberField.of_module_finite F F₁
  haveI : Algebra.IsAlgebraic F₁ Ω := Algebra.IsAlgebraic.tower_top (K := F) F₁
  haveI : IsAlgClosure F₁ Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
  haveI : IsTotallyReal F₁ := ⟨fun w => NumberField.InfinitePlace.isReal_iff.2 (hre _)⟩
  let ρ : (Ω ≃ₐ[F₁] Ω) →* (Ω ≃ₐ[F] Ω) := AlgEquiv.restrictScalarsHom F
  have hρdec : ∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F₁] Ω), ρ g ∈ Dec (F := F) B ↔ g ∈ Dec (F := F₁) B :=
    fun _ _ => Iff.rfl
  have hρfix : ∀ g, ρ g ∈ F₁.fixingSubgroup := fun g => by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact g.commutes ⟨x, hx⟩

  have hlift : ∀ g ∈ F₁.fixingSubgroup, ∃ g' : Ω ≃ₐ[F₁] Ω, ρ g' = g := fun g hg =>
    ⟨IntermediateField.fixingSubgroupEquiv F₁ ⟨g, hg⟩, by ext x; rfl⟩
  obtain ⟨v₁, hv₁⟩ := exists_place_between (K := F₁) h
  obtain ⟨c, hcv, hcT⟩ := exists_avoid v T hvT
  set c₁ : 𝓞 F₁ := algebraMap (𝓞 F) (𝓞 F₁) c with hc₁
  have hc₁val : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F₁)), IsPlaceOver B w →
      (c₁ ∈ w.asIdeal ↔ B.valuation (algebraMap F Ω (c : F)) < 1) := by
    intro B w hw
    rw [← hw, IsScalarTower.algebraMap_apply F F₁ Ω]
    rfl
  have hc0 : c₁ ≠ 0 := by
    intro h0
    apply hcv
    have : c = 0 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 F₁)) (by rw [← hc₁, h0, map_zero])
    rw [this]; exact v.asIdeal.zero_mem
  have hfin : {w : HeightOneSpectrum (𝓞 F₁) | c₁ ∈ w.asIdeal}.Finite :=
    (Ideal.finite_factors (I := Ideal.span {c₁}) (by simpa using hc0)).subset
      fun w hw => Ideal.dvd_span_singleton.mpr hw
  set T₁ := hfin.toFinset
  have hv₁T : v₁ ∉ T₁ := by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hc₁val A v₁ hv₁, h]
    exact hcv
  let V₁ : Subgroup (Dec (F := F₁) A) := (V.comap ρ).comap (Dec (F := F₁) A).subtype
  have hV₁ : IsOpen (V₁ : Set (Dec (F := F₁) A)) := by
    obtain ⟨E, hE, hEV⟩ := (krullTopology_mem_nhds_one_iff F Ω (V : Set (G F Ω))).1 (hV.mem_nhds V.one_mem)
    haveI : FiniteDimensional F (E ⊔ F₁ : IntermediateField F Ω) := IntermediateField.finiteDimensional_sup _ _
    let E₁ : IntermediateField F₁ Ω := IntermediateField.extendScalars (le_sup_right : F₁ ≤ E ⊔ F₁)
    haveI : FiniteDimensional F E₁ := (inferInstance : FiniteDimensional F (E ⊔ F₁ : IntermediateField F Ω))
    haveI : FiniteDimensional F₁ E₁ := FiniteDimensional.right F F₁ _
    refine Subgroup.isOpen_mono (H₁ := (E₁.fixingSubgroup).comap (Dec (F := F₁) A).subtype) ?_
      ((E₁.fixingSubgroup_isOpen).preimage continuous_subtype_val)
    intro g hg
    simp only [V₁, Subgroup.mem_comap]
    apply hEV
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg x ((IntermediateField.mem_extendScalars _).2 (le_sup_left (a := E) hx))
  have hcomm₁ : commutator (Dec (F := F₁) A) ≤ V₁ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    simp only [V₁, Subgroup.mem_comap, map_commutatorElement]
    apply hcomm
    exact Subgroup.commutator_mem_commutator ⟨(hρdec A _).2 g₁.2, hρfix _⟩ ⟨(hρdec A _).2 g₂.2, hρfix _⟩
  obtain ⟨F₂', hfin₂, hab, hreal₂, hiff, hsplit⟩ := GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion Ω F₁ A v₁ hv₁ V₁ hV₁ hcomm₁ T₁ hv₁T
  have hcomm₂ : commutator (Ω ≃ₐ[F₁] Ω) ≤ F₂'.fixingSubgroup := by
    rw [← F₂'.restrictNormalHom_ker, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact IsMulCommutative.is_comm.comm _ _
  have hfix₂ : ∀ g : Ω ≃ₐ[F₁] Ω, ρ g ∈ (F₂'.restrictScalars F).fixingSubgroup ↔ g ∈ F₂'.fixingSubgroup :=
    fun _ => Iff.rfl
  have hle : F₁ ≤ F₂'.restrictScalars F := by
    intro x hx
    show x ∈ F₂'
    simpa using F₂'.algebraMap_mem ⟨x, hx⟩
  refine ⟨F₂'.restrictScalars F, hle, ?_, ?_, ?_, ?_, ?_⟩
  · exact FiniteDimensional.trans F F₁ F₂'
  · rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    obtain ⟨g₁', rfl⟩ := hlift g₁ h₁
    obtain ⟨g₂', rfl⟩ := hlift g₂ h₂
    rw [← map_commutatorElement, hfix₂]
    exact hcomm₂ (by rw [commutator_def]; exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  · intro φ
    exact hreal₂ φ
  · rintro g ⟨hgA, hg₂⟩
    have hg₁ : g ∈ F₁.fixingSubgroup := by
      have hg₂' : g ∈ (F₂'.restrictScalars F).fixingSubgroup := hg₂
      rw [IntermediateField.mem_fixingSubgroup_iff] at hg₂' ⊢
      intro x hx
      exact hg₂' x (hle hx)
    obtain ⟨g', rfl⟩ := hlift g hg₁
    have := (hiff ⟨g', (hρdec A g').1 hgA⟩).1 ((hfix₂ g').1 hg₂)
    exact this
  · intro u hu A' hA' g ⟨hgA, hg₁⟩
    obtain ⟨g', rfl⟩ := hlift g hg₁
    obtain ⟨w', hw'⟩ := exists_place_between (K := F₁) hA'
    have hw'T : w' ∈ T₁ := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hc₁val A' w' hw', hA']
      exact hcT u hu
    exact (hfix₂ g').2 (hsplit w' hw'T A' hw' ((hρdec A' g').1 hgA))

end GlobalTheory.AbOverSubfield
