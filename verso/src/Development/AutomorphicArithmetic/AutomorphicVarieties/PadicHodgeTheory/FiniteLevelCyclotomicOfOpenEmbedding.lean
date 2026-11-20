import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import ReciprocityTheory.GroupCohomology.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContCohomologyTransportMulEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Set `K0 : FinExt v` to `⟨IntermediateField.adjoin ℚ_[v] (Set.range fun x : ℚ => j (algebraMap ℚ Ω x)), GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap ℚ Ω))⟩`. Take `⟨e, he, he', hec⟩` from `GlobalTheory.PlaceBridge.exists_mulEquiv (E := ℚ) hA K0 rfl`. Establish `h0 : ∀ τ, τ ∈ GK K0` using `fun τ => (GlobalTheory.PlaceBridge.mem_GK_iff K0 rfl τ).2 fun x => by simp`. Set `r : GQ v →* (Ω ≃ₐ[ℚ] Ω)` to `(Subgroup.subtype _).comp (e.symm.toMonoidHom.comp ((MonoidHom.id _).codRestrict _ h0))`. Establish `hr : ∀ τ x, τ (j x) = j (r τ x)` using `fun τ x => by`.

Use `hec (e.symm ⟨τ, h0 τ⟩) x` as an intermediate fact. Rewrite `this` using `[MulEquiv.apply_symm_apply]`. Conclude with `this`. Establish `hrc : Continuous r` using `continuous_subtype_val.comp (he'.comp (continuous_id.subtype_mk _))`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed ℚ`.

Establish `: IsGalois ℚ Ω` using `IsAlgClosure.isGalois ℚ Ω`. Establish `hK` using `K.2`. Establish `hle : K.1 ≤ IntermediateField.adjoin ℚ_[v] (j '' {a | j a ∈ K.1})`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ_[v] _), IntermediateField.le_iff_le]`. Introduce `τ hτ`.

Set `H : ClosedSubgroup (Ω ≃ₐ[ℚ] Ω)` to `⟨(GK K).map r, ((IntermediateField.fixingSubgroup_isClosed K.1).isCompact.image hrc).isClosed⟩`. Establish `h1 : r τ ∈ H.1`. Rewrite using `[← InfiniteGalois.fixingSubgroup_fixedField H, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `a ha`. Apply `j.injective` to reduce the goal to its premises.

Rewrite using `[← hr]`. Use `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ _ (IntermediateField.subset_adjoin _ _ ⟨a, ?_, rfl⟩)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `j a ∈ K.1`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]`. Introduce `σ hσ`.

Rewrite using `[hr, (IntermediateField.mem_fixedField_iff _ _).1 ha _ ⟨σ, hσ, rfl⟩]`. Take `⟨σ, hσ, hst⟩` from `h1`. Establish `: σ = τ` using `GlobalTheory.PlaceBridge.algEquiv_ext (GlobalTheory.PlaceBridge.denseRange_embedding j) fun x => by rw [hr, hr, hst]`. Conclude with `this ▸ hσ`. Take `⟨x, hx⟩` from `Field.exists_primitive_element ℚ_[v] K.1`.

Establish `hx' : IntermediateField.adjoin ℚ_[v] {(x : PadicAlgCl v)} = K.1`. Rewrite using `[← IntermediateField.lift_adjoin_simple, hx, IntermediateField.lift_top]`. Take `⟨T, hT, hxT⟩` from `IntermediateField.exists_finset_of_mem_adjoin (hle x.2)`. Establish `hfin : Finite (j ⁻¹' (T : Set (PadicAlgCl v)))` using `(T.finite_toSet.preimage j.injective.injOn).to_subtype`. Use `⟨IntermediateField.adjoin ℚ (j ⁻¹' (T : Set (PadicAlgCl v))), IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z, le_antisymm ?_ ?_⟩` and prove the remaining obligations.

Rewrite using `[← hx', IntermediateField.adjoin_simple_le_iff]`. Use `IntermediateField.adjoin.mono _ _ _ (fun t ht => ?_) hxT` and prove the remaining obligations. Take `⟨a, -, rfl⟩` from `hT ht`. Conclude with `⟨⟨a, IntermediateField.subset_adjoin _ _ ht⟩, rfl⟩`. Rewrite using `[IntermediateField.adjoin_le_iff]`.

Introduce and unpack `_ ⟨⟨y, hy⟩, rfl⟩`. Express the relevant statement in the definitionally equal form `j y ∈ K.1`. Proceed by induction on `hy using IntermediateField.adjoin_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, h⟩` from `hT hy`.

Conclude with `h ▸ ha`. Consider the case `algebraMap y => rw [eq_ratCast, map_ratCast]`. Conclude with `SubfieldClass.ratCast_mem _ _`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`.

Consider the case `inv a _ ha => rw [map_inv₀]`. Conclude with `inv_mem ha`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_mem ha hb`.
-/
private theorem numField {v : ℕ} [Fact v.Prime] (K : FinExt v) {Ω : Type} [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl v) (A : ValuationSubring Ω) (hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ F : IntermediateField ℚ Ω, FiniteDimensional ℚ F ∧
      K.1 = IntermediateField.adjoin ℚ_[v] (Set.range fun x : F => j (algebraMap F Ω x)) := by
  let K0 : FinExt v := ⟨IntermediateField.adjoin ℚ_[v] (Set.range fun x : ℚ => j (algebraMap ℚ Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap ℚ Ω))⟩
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := ℚ) hA K0 rfl
  have h0 : ∀ τ, τ ∈ GK K0 := fun τ => (GlobalTheory.PlaceBridge.mem_GK_iff K0 rfl τ).2 fun x => by simp
  let r : GQ v →* (Ω ≃ₐ[ℚ] Ω) := (Subgroup.subtype _).comp
    (e.symm.toMonoidHom.comp ((MonoidHom.id _).codRestrict _ h0))
  have hr : ∀ τ x, τ (j x) = j (r τ x) := fun τ x => by
    have := hec (e.symm ⟨τ, h0 τ⟩) x
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hrc : Continuous r := continuous_subtype_val.comp (he'.comp (continuous_id.subtype_mk _))
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hK := K.2
  have hle : K.1 ≤ IntermediateField.adjoin ℚ_[v] (j '' {a | j a ∈ K.1}) := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ_[v] _),
      IntermediateField.le_iff_le]
    intro τ hτ
    let H : ClosedSubgroup (Ω ≃ₐ[ℚ] Ω) := ⟨(GK K).map r,
      ((IntermediateField.fixingSubgroup_isClosed K.1).isCompact.image hrc).isClosed⟩
    have h1 : r τ ∈ H.1 := by
      rw [← InfiniteGalois.fixingSubgroup_fixedField H, IntermediateField.mem_fixingSubgroup_iff]
      intro a ha
      apply j.injective
      rw [← hr]
      refine (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ _
        (IntermediateField.subset_adjoin _ _ ⟨a, ?_, rfl⟩)
      change j a ∈ K.1
      rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
      intro σ hσ
      rw [hr, (IntermediateField.mem_fixedField_iff _ _).1 ha _ ⟨σ, hσ, rfl⟩]
    obtain ⟨σ, hσ, hst⟩ := h1
    have : σ = τ := GlobalTheory.PlaceBridge.algEquiv_ext (GlobalTheory.PlaceBridge.denseRange_embedding j)
      fun x => by rw [hr, hr, hst]
    exact this ▸ hσ
  obtain ⟨x, hx⟩ := Field.exists_primitive_element ℚ_[v] K.1
  have hx' : IntermediateField.adjoin ℚ_[v] {(x : PadicAlgCl v)} = K.1 := by
    rw [← IntermediateField.lift_adjoin_simple, hx, IntermediateField.lift_top]
  obtain ⟨T, hT, hxT⟩ := IntermediateField.exists_finset_of_mem_adjoin (hle x.2)
  have hfin : Finite (j ⁻¹' (T : Set (PadicAlgCl v))) :=
    (T.finite_toSet.preimage j.injective.injOn).to_subtype
  refine ⟨IntermediateField.adjoin ℚ (j ⁻¹' (T : Set (PadicAlgCl v))),
    IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z,
    le_antisymm ?_ ?_⟩
  · rw [← hx', IntermediateField.adjoin_simple_le_iff]
    refine IntermediateField.adjoin.mono _ _ _ (fun t ht => ?_) hxT
    obtain ⟨a, -, rfl⟩ := hT ht
    exact ⟨⟨a, IntermediateField.subset_adjoin _ _ ht⟩, rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    change j y ∈ K.1
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy =>
      obtain ⟨a, ha, h⟩ := hT hy
      exact h ▸ ha
    | algebraMap y => rw [eq_ratCast, map_ratCast]; exact SubfieldClass.ratCast_mem _ _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

open NumberField IsDedekindDomain in
/- English proof (translation)
Establish `hm : ∀ x : 𝓞 F, algebraMap F Ω x ∈ A` using `fun x => by`. Establish `h : IsIntegral ℤ (algebraMap F Ω x)` using `x.isIntegral_coe.map (algebraMap F Ω).toIntAlgHom`. Use `(Valuation.integer.integers A.valuation).mem_of_integral (x := algebraMap F Ω x) h.tower_top` as an intermediate fact. Conclude with `(A.valuation_le_one_iff _).1 this`. Set `f : 𝓞 F →+* A` to `((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict A hm`.

Establish `hf : ∀ x, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔ A.valuation (algebraMap F Ω x) < 1` using `fun x => A.valuation_lt_one_iff (f x)`. Establish `hn : ∀ n : ℕ, (n : 𝓞 F) ∈ (IsLocalRing.maximalIdeal A).comap f ↔ v ∣ n` using `fun n => by`. Rewrite using `[hf, ← Int.natCast_dvd_natCast, ← GlobalTheory.PlaceBridge.val_int_lt_one_iff A hv hA]`. Simplify using the standard rewrite rules. Use `⟨⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun h => ?_⟩, fun x => (hf x).symm, fun l hl hvl h => hvl ((Nat.prime_dvd_prime_iff_eq hv hl).1 ((hn l).1 h))⟩` and prove the remaining obligations.

Use `(hn v).2 dvd_rfl` as an intermediate fact. Rewrite `this` using `[h, Ideal.mem_bot]`. Conclude with `hv.ne_zero (Nat.cast_eq_zero.1 this)`.
-/
private theorem placeBelow {v : ℕ} (hv : v.Prime) (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (A : ValuationSubring Ω) (hA : A.valuation (v : Ω) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 F), Formalism.ConjugateSelfDual.IsPlaceOver A w ∧
      ∀ l : ℕ, l.Prime → v ≠ l → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal := by
  have hm : ∀ x : 𝓞 F, algebraMap F Ω x ∈ A := fun x => by
    have h : IsIntegral ℤ (algebraMap F Ω x) := x.isIntegral_coe.map (algebraMap F Ω).toIntAlgHom
    have := (Valuation.integer.integers A.valuation).mem_of_integral (x := algebraMap F Ω x) h.tower_top
    exact (A.valuation_le_one_iff _).1 this
  let f : 𝓞 F →+* A := ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict A hm
  have hf : ∀ x, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔ A.valuation (algebraMap F Ω x) < 1 :=
    fun x => A.valuation_lt_one_iff (f x)
  have hn : ∀ n : ℕ, (n : 𝓞 F) ∈ (IsLocalRing.maximalIdeal A).comap f ↔ v ∣ n := fun n => by
    rw [hf, ← Int.natCast_dvd_natCast, ← GlobalTheory.PlaceBridge.val_int_lt_one_iff A hv hA]
    simp
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun h => ?_⟩, fun x => (hf x).symm,
    fun l hl hvl h => hvl ((Nat.prime_dvd_prime_iff_eq hv hl).1 ((hn l).1 h))⟩
  have := (hn v).2 dvd_rfl
  rw [h, Ideal.mem_bot] at this
  exact hv.ne_zero (Nat.cast_eq_zero.1 this)

/- English proof (translation)
Establish `h' : ∀ g m, ρ g m = ρ' (e.symm g) m` using `fun g m => by rw [h, e.apply_symm_apply]`. Rewrite `hs`, the goal using `[GlobalTheory.Published.subsingleton_Hn_succ_iff]`. Introduce `f hf hd`. Take `⟨c, hc, hcf⟩` from `hs (fun x => f (fun i => e.symm (x i))) (hf.comp (continuous_pi fun i => he'.comp (continuous_apply i))) (by`. Use function extensionality and compare the values at `g`.

Use `GlobalTheory.dn_comp_monoidHom e.symm.toMonoidHom ρ' ρ h' (n + 1) f g` as an intermediate fact. Rewrite `this` using `[hd]`. Conclude with `this)`. Use `⟨fun x => c (fun i => e (x i)), hc.comp (continuous_pi fun i => he.comp (continuous_apply i)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`.

Use `GlobalTheory.dn_comp_monoidHom e.toMonoidHom ρ ρ' h n c g` as an intermediate fact. Rewrite `this` using `[hcf]`. Use `this.trans ?_` and prove the remaining obligations. Conclude with `congrArg f (funext fun i => e.symm_apply_apply _)`.
-/
private theorem hn_transport {R Γ Γ' M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [Group Γ']
    [TopologicalSpace Γ'] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (e : Γ' ≃* Γ) (he : Continuous e) (he' : Continuous e.symm) (ρ : Representation R Γ M)
    (ρ' : Representation R Γ' M) (h : ∀ g m, ρ' g m = ρ (e g) m) (n : ℕ)
    (hs : Subsingleton (Hn ρ (n + 1))) : Subsingleton (Hn ρ' (n + 1)) := by
  have h' : ∀ g m, ρ g m = ρ' (e.symm g) m := fun g m => by rw [h, e.apply_symm_apply]
  rw [GlobalTheory.Published.subsingleton_Hn_succ_iff] at hs ⊢
  intro f hf hd
  obtain ⟨c, hc, hcf⟩ := hs (fun x => f (fun i => e.symm (x i)))
    (hf.comp (continuous_pi fun i => he'.comp (continuous_apply i))) (by
      funext g
      have := GlobalTheory.dn_comp_monoidHom e.symm.toMonoidHom ρ' ρ h' (n + 1) f g
      rw [hd] at this
      exact this)
  refine ⟨fun x => c (fun i => e (x i)),
    hc.comp (continuous_pi fun i => he.comp (continuous_apply i)), ?_⟩
  funext g
  have := GlobalTheory.dn_comp_monoidHom e.toMonoidHom ρ ρ' h n c g
  rw [hcf] at this
  refine this.trans ?_
  exact congrArg f (funext fun i => e.symm_apply_apply _)

/- English proof (translation)
Take `⟨⟨e1⟩, ⟨e2⟩, -⟩` from `GlobalTheory.contCohomology_transport_mulEquiv _ _ _ M e he he' σ ρ h`. Take `⟨j⟩` from `hj`. Establish `h0 : H0 ρ = H0 σ`. Use extensionality with `m`. Rewrite using `[mem_riemannRochSpace_iff_regularAt_everywhere, mem_riemannRochSpace_iff_regularAt_everywhere]`.

Use `⟨fun hm g => ?_, fun hm g => (h g m).trans (hm _)⟩` and prove the remaining obligations. Take `⟨g, rfl⟩` from `e.surjective g`. Conclude with `(h g m).symm.trans (hm g)`. Use `⟨Finite.of_equiv _ e1, Finite.of_equiv _ e2, fun m hm => ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`.

Conclude with `hn_transport e he he' σ ρ h k (f3 _ hm)`. Rewrite using `[← Nat.card_congr e1, ← Nat.card_congr e2, h0, hE]`. Establish `hfin : Finite (TDual (ZMod n) M)` using `DFunLike.finite _`. Set `E : H2 σ ≃ Module.Dual (ZMod n) (H0 ((twDual χ σ).comp (MonoidHom.id _)))` to `(Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight j).toEquiv`. Rewrite using `[← Nat.card_congr e2, Nat.card_congr E, GlobalTheory.ZModDual.card_dual_eq]`.

Use `Nat.card_congr (Equiv.subtypeEquivRight fun f : TDual (ZMod n) M => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(∀ g, twDual χ σ g f = f) ↔ ∀ g x, f (ρ g x) = ((χG g : (ZMod n)ˣ) : ZMod n) * f x`. Prove the components needed by the constructor for the conclusion. Introduce `hf g x`. Use `congrArg (fun ψ : TDual (ZMod n) M => ψ (σ (e g) x)) (hf (e g))` as an intermediate fact.

Simplify using `only [twDual_apply] at this`. Rewrite `this` using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, hχ]`. Rewrite using `[h, this]`. Introduce `hf g`. Take `⟨g, rfl⟩` from `e.surjective g`.

Use `TDual.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[twDual_apply, hχ, ← hf, h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.
-/
private theorem core {n : ℕ} [NeZero n] {G D M : Type} [Group G] [TopologicalSpace G] [Group D]
    [TopologicalSpace D] [AddCommGroup M] [Module (ZMod n) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (e : G ≃* D) (he : Continuous e) (he' : Continuous e.symm)
    (χG : G →* (ZMod n)ˣ) (χ : D →* (ZMod n)ˣ) (hχ : ∀ g, χ (e g) = χG g)
    (ρ : Representation (ZMod n) G M) (σ : Representation (ZMod n) D M) (h : ∀ g m, ρ g m = σ (e g) m)
    (c : ℕ) (f1 : Finite (H1 σ)) (f2 : Finite (H2 σ)) (f3 : ∀ m, 3 ≤ m → Subsingleton (Hn σ m))
    (hj : Nonempty (H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod n] ZMod n))
    (hb : Function.Bijective (cup20 χ σ (MonoidHom.id _)))
    (hE : Nat.card (H1 σ) = Nat.card (H0 σ) * Nat.card (H2 σ) * c) :
    Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ (∀ m, 3 ≤ m → Subsingleton (Hn ρ m)) ∧
      Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * c ∧
      Nat.card (H2 ρ) = Nat.card (H0dual χG ρ) := by
  obtain ⟨⟨e1⟩, ⟨e2⟩, -⟩ := GlobalTheory.contCohomology_transport_mulEquiv _ _ _ M e he he' σ ρ h
  obtain ⟨j⟩ := hj
  have h0 : H0 ρ = H0 σ := by
    ext m
    rw [mem_riemannRochSpace_iff_regularAt_everywhere, mem_riemannRochSpace_iff_regularAt_everywhere]
    refine ⟨fun hm g => ?_, fun hm g => (h g m).trans (hm _)⟩
    obtain ⟨g, rfl⟩ := e.surjective g
    exact (h g m).symm.trans (hm g)
  refine ⟨Finite.of_equiv _ e1, Finite.of_equiv _ e2, fun m hm => ?_, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact hn_transport e he he' σ ρ h k (f3 _ hm)
  · rw [← Nat.card_congr e1, ← Nat.card_congr e2, h0, hE]
  · have hfin : Finite (TDual (ZMod n) M) := DFunLike.finite _
    let E : H2 σ ≃ Module.Dual (ZMod n) (H0 ((twDual χ σ).comp (MonoidHom.id _))) :=
      (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight j).toEquiv
    rw [← Nat.card_congr e2, Nat.card_congr E, GlobalTheory.ZModDual.card_dual_eq]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun f : TDual (ZMod n) M => ?_)
    change (∀ g, twDual χ σ g f = f) ↔ ∀ g x, f (ρ g x) = ((χG g : (ZMod n)ˣ) : ZMod n) * f x
    constructor
    · intro hf g x
      have := congrArg (fun ψ : TDual (ZMod n) M => ψ (σ (e g) x)) (hf (e g))
      simp only [twDual_apply] at this
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, hχ] at this
      rw [h, this]
    · intro hf g
      obtain ⟨g, rfl⟩ := e.surjective g
      refine TDual.ext fun x => ?_
      rw [twDual_apply, hχ, ← hf, h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]

/- English proof (translation)
Introduce `P v l _ _ G _ _ _ φ hφ r hr M _ _ _ _ _ ρ hρ`. Establish `hl : l.Prime` using `Fact.out`. Establish `hv : v.Prime` using `Fact.out`. Establish `: NeZero (l ^ r)` using `⟨pow_ne_zero _ hl.ne_zero⟩`. Take `⟨K, e, he, he', hc, -, hi, -⟩` from `openField φ hφ`.

Establish `hc' : ∀ g, ((e g : ↥(GK K)) : GQ v) = φ g` using `fun g => DFunLike.congr_fun hc g`. Establish `hK` using `K.2`. Distinguish the cases in `hvl : v = l`. Substitute `hvl` using the available equality. Rewrite using `[if_pos rfl, hi]`.

Take `⟨hf, hf'⟩` from `GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[v] (PadicAlgCl v) K.1`. Set `ε : G ≃* Formalism.GaloisCohomology.GK v K.1` to `e.trans (IntermediateField.fixingSubgroupEquiv K.1)`. Establish `hε : Continuous ε` using `hf.comp he`. Establish `hε' : Continuous ε.symm` using `he'.comp hf'`. Set `σ : Representation (ZMod (v ^ r)) (Formalism.GaloisCohomology.GK v K.1) M` to `ρ.comp ε.symm.toMonoidHom`.

Establish `hσ : ReciprocityTheory.Gal.ContAction σ` using `hρ.comp' hε'`. Take `⟨-, f1, f2, f3⟩` from `P.lfK v K.1 hK r M σ hr hσ`. Take `⟨hj, -, -, -, hb⟩` from `P.ltK v K.1 hK r M σ hr hσ`. Use `core ε hε hε' _ _ (fun g => ?_) ρ σ (fun g m => by simp [σ]) _ f1 f2 f3 hj hb (P.leK v K.1 hK r M σ hr hσ)` and prove the remaining obligations. Simplify using `only [MonoidHom.comp_apply, ← hc']`.

Both sides reduce to the same expression. Rewrite using `[if_neg hvl, pow_zero]`. Set `Ω` to `AlgebraicClosure ℚ`. Establish `: IsAlgClosure ℚ Ω` using `AlgebraicClosure.instIsAlgClosure ℚ`. Set `j : Ω →+* PadicAlgCl v` to `(IsAlgClosed.lift (R := ℚ) (S := Ω) (M := PadicAlgCl v)).toRingHom`.

Set `A : ValuationSubring Ω` to `(Valued.v (R := PadicAlgCl v)).valuationSubring.comap j`. Establish `hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1` using `fun x => by`. Express the relevant statement in the definitionally equal form `Valued.v (j x) ≤ 1 ↔ _`. Rewrite using `[PadicAlgCl.valuation_def]`. Conclude with `Iff.rfl`.

Establish `hAv : A.valuation (v : Ω) < 1`. Establish `h0 : 0 < ‖(v : PadicAlgCl v)‖` using `norm_pos_iff.2 (by exact_mod_cast hv.ne_zero)`. Establish `h1 : ((v : Ω))⁻¹ ∉ A`. Rewrite using `[hA, map_inv₀, map_natCast, norm_inv, not_le]`. Conclude with `(one_lt_inv₀ h0).2 GlobalTheory.PlaceBridge.norm_l_lt_one`.

Rewrite `h1` using `[← A.valuation_le_one_iff, not_le, map_inv₀]`. Conclude with `(one_lt_inv₀ (zero_lt_iff.2 (by simpa using hv.ne_zero))).1 h1`. Take `⟨F, hF, hKF⟩` from `numField K j A hA`. Establish `: NumberField F` using `⟨⟩`. Establish `: IsAlgClosure F Ω` using `⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩`.

Take `⟨w, hw, hwl⟩` from `placeBelow hv F A hAv`. Take `⟨d, hd, hd', hdc⟩` from `GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hA K hKF`. Set `ε` to `e.trans d.symm`. Establish `hε : Continuous ε` using `hd'.comp he`. Establish `hε' : Continuous ε.symm` using `he'.comp hd`.

Set `σ : Representation (ZMod (l ^ r)) _ M` to `ρ.comp ε.symm.toMonoidHom`. Establish `hσ : ReciprocityTheory.Gal.ContAction σ` using `hρ.comp' hε'`. Take `⟨-, f1, f2, f3⟩` from `P.lf F Ω l r M A σ w hr hw hσ`. Take `⟨hj, -, -, -, hb⟩` from `P.lt F Ω l r M A σ w hr hw hσ`. Use `core ε hε hε' _ ((cycMod F Ω l r).comp (Subgroup.subtype _)) (fun g => Units.ext ?_) ρ σ (fun g m => by simp [σ]) _ f1 f2 f3 hj hb (((P.le F Ω l r M A σ w hr hw hσ).2 (hwl l hl hvl)).trans (mul_one _).symm)` and prove the remaining obligations.

Establish `: NeZero ((l : ℕ) : Ω)` using `⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩`. Establish `: NeZero ((l : ℕ) : PadicAlgCl v)` using `⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)`. Establish `hζ'` using `hζ.map_of_injective j.injective`. Establish `ha : (ε g : Ω ≃ₐ[F] Ω) ζ = ζ ^ ((cycMod F Ω l r (ε g : Ω ≃ₐ[F] Ω) : ZMod (l ^ r))).val` using `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω (ε g : Ω ≃ₐ[F] Ω)) ζ hζ.pow_eq_one`.

Establish `hb : φ g (j ζ) = j ζ ^ (PadicInt.toZModPow r ((cyc v l (φ g) : ℤ_[l]ˣ) : ℤ_[l])).val` using `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ v) (PadicAlgCl v) (φ g)) _ hζ'.pow_eq_one`. Establish `h3 : φ g (j ζ) = j ((ε g : Ω ≃ₐ[F] Ω) ζ)`. Rewrite using `[← hdc, ← hc']`. Simplify using `[ε]`. Rewrite `hb` using `[h3, ha, map_pow]`.

Conclude with `ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)`.
-/
theorem UpperTheory.finiteLevel_cyclotomic_of_openEmbedding :
    LocalPublishedTheorems → ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v), IsOpenEmbedding φ → FinLevelMod l G ((cyc v l).comp φ) (if v = l then φ.range.index else 0) := by
  intro P v l _ _ G _ _ _ φ hφ r hr M _ _ _ _ _ ρ hρ
  have hl : l.Prime := Fact.out
  have hv : v.Prime := Fact.out
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨K, e, he, he', hc, -, hi, -⟩ := openField φ hφ
  have hc' : ∀ g, ((e g : ↥(GK K)) : GQ v) = φ g := fun g => DFunLike.congr_fun hc g
  have hK := K.2
  by_cases hvl : v = l
  · subst hvl
    rw [if_pos rfl, hi]
    obtain ⟨hf, hf'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[v] (PadicAlgCl v) K.1
    let ε : G ≃* Formalism.GaloisCohomology.GK v K.1 := e.trans (IntermediateField.fixingSubgroupEquiv K.1)
    have hε : Continuous ε := hf.comp he
    have hε' : Continuous ε.symm := he'.comp hf'
    let σ : Representation (ZMod (v ^ r)) (Formalism.GaloisCohomology.GK v K.1) M := ρ.comp ε.symm.toMonoidHom
    have hσ : ReciprocityTheory.Gal.ContAction σ := hρ.comp' hε'
    obtain ⟨-, f1, f2, f3⟩ := P.lfK v K.1 hK r M σ hr hσ
    obtain ⟨hj, -, -, -, hb⟩ := P.ltK v K.1 hK r M σ hr hσ
    refine core ε hε hε' _ _ (fun g => ?_) ρ σ (fun g m => by simp [σ]) _ f1 f2 f3 hj hb
      (P.leK v K.1 hK r M σ hr hσ)
    simp only [MonoidHom.comp_apply, ← hc']
    rfl
  · rw [if_neg hvl, pow_zero]
    let Ω := AlgebraicClosure ℚ
    have : IsAlgClosure ℚ Ω := AlgebraicClosure.instIsAlgClosure ℚ
    let j : Ω →+* PadicAlgCl v := (IsAlgClosed.lift (R := ℚ) (S := Ω) (M := PadicAlgCl v)).toRingHom
    let A : ValuationSubring Ω := (Valued.v (R := PadicAlgCl v)).valuationSubring.comap j
    have hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1 := fun x => by
      change Valued.v (j x) ≤ 1 ↔ _
      rw [PadicAlgCl.valuation_def]
      exact Iff.rfl
    have hAv : A.valuation (v : Ω) < 1 := by
      have h0 : 0 < ‖(v : PadicAlgCl v)‖ := norm_pos_iff.2 (by exact_mod_cast hv.ne_zero)
      have h1 : ((v : Ω))⁻¹ ∉ A := by
        rw [hA, map_inv₀, map_natCast, norm_inv, not_le]
        exact (one_lt_inv₀ h0).2 GlobalTheory.PlaceBridge.norm_l_lt_one
      rw [← A.valuation_le_one_iff, not_le, map_inv₀] at h1
      exact (one_lt_inv₀ (zero_lt_iff.2 (by simpa using hv.ne_zero))).1 h1
    obtain ⟨F, hF, hKF⟩ := numField K j A hA
    have : NumberField F := ⟨⟩
    have : IsAlgClosure F Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩
    obtain ⟨w, hw, hwl⟩ := placeBelow hv F A hAv
    obtain ⟨d, hd, hd', hdc⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hA K hKF
    let ε := e.trans d.symm
    have hε : Continuous ε := hd'.comp he
    have hε' : Continuous ε.symm := he'.comp hd
    let σ : Representation (ZMod (l ^ r)) _ M := ρ.comp ε.symm.toMonoidHom
    have hσ : ReciprocityTheory.Gal.ContAction σ := hρ.comp' hε'
    obtain ⟨-, f1, f2, f3⟩ := P.lf F Ω l r M A σ w hr hw hσ
    obtain ⟨hj, -, -, -, hb⟩ := P.lt F Ω l r M A σ w hr hw hσ
    refine core ε hε hε' _ ((cycMod F Ω l r).comp (Subgroup.subtype _)) (fun g => Units.ext ?_) ρ σ
      (fun g m => by simp [σ]) _ f1 f2 f3 hj hb
      (((P.le F Ω l r M A σ w hr hw hσ).2 (hwl l hl hvl)).trans (mul_one _).symm)
    have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
    have : NeZero ((l : ℕ) : PadicAlgCl v) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
    have hζ' := hζ.map_of_injective j.injective
    have ha : (ε g : Ω ≃ₐ[F] Ω) ζ = ζ ^ ((cycMod F Ω l r (ε g : Ω ≃ₐ[F] Ω) : ZMod (l ^ r))).val :=
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω (ε g : Ω ≃ₐ[F] Ω)) ζ
        hζ.pow_eq_one
    have hb : φ g (j ζ) = j ζ ^ (PadicInt.toZModPow r ((cyc v l (φ g) : ℤ_[l]ˣ) : ℤ_[l])).val :=
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ v) (PadicAlgCl v) (φ g)) _
        hζ'.pow_eq_one
    have h3 : φ g (j ζ) = j ((ε g : Ω ≃ₐ[F] Ω) ζ) := by
      rw [← hdc, ← hc']
      simp [ε]
    rw [h3, ha, map_pow] at hb
    exact ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)
