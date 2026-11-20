import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual

/- English proof (translation)
Set `K0 : FinExt v` to `⟨IntermediateField.adjoin ℚ_[v] (Set.range fun x : ℚ => j (algebraMap ℚ Ω x)), GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap ℚ Ω))⟩`. Take `⟨e, he, he', hec⟩` from `GlobalTheory.PlaceBridge.exists_mulEquiv (E := ℚ) hA K0 rfl`. Establish `hall : ∀ τ : GQ v, τ ∈ GK K0` using `fun τ => (GlobalTheory.PlaceBridge.mem_GK_iff (j := j) K0 rfl τ).2 fun x => by simp`. Set `ψ : ↥(Dec (F` to `ℚ) A) →* GQ v := (GK K0).subtype.comp e.toMonoidHom`. Establish `hψ : Continuous ψ` using `continuous_subtype_val.comp he`.

Take `⟨W, hW, hWe⟩` from `isOpen_induced_iff.1 (hU.preimage hψ)`. Establish `hW1 : (1 : Ω ≃ₐ[ℚ] Ω) ∈ W`. Establish `: (1 : ↥(Dec (F` using `ℚ) A)) ∈ ψ ⁻¹' (U : Set (GQ v)) := by show ψ 1 ∈ U`. Rewrite using `[map_one]`. Conclude with `U.one_mem`.

Rewrite `this` using `[← hWe]`. Conclude with `this`. Use `haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω`. Take `⟨N, hN⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW hW1`. Set `H : Subgroup (Ω ≃ₐ[ℚ] Ω)` to `(U.comap ψ).map (Dec (F := ℚ) A).subtype ⊔ N.toSubgroup`.

Establish `hHo : IsOpen (H : Set (Ω ≃ₐ[ℚ] Ω))` using `Subgroup.isOpen_mono le_sup_right N.isOpen`. Establish `hHc : IsClosed (H : Set (Ω ≃ₐ[ℚ] Ω))` using `H.isClosed_of_isOpen hHo`. Establish `hfix : (IntermediateField.fixedField H).fixingSubgroup = H` using `InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHc⟩`. Establish `hmem : ∀ g : ↥(Dec (F` using `ℚ) A), (g : Ω ≃ₐ[ℚ] Ω) ∈ H ↔ ψ g ∈ U := fun g => by`. Use `⟨fun hg => ?_, fun hg => Subgroup.mem_sup_left ⟨g, hg, rfl⟩⟩` and prove the remaining obligations.

Establish `hg' : (g : Ω ≃ₐ[ℚ] Ω) ∈ (H : Set (Ω ≃ₐ[ℚ] Ω))` using `hg`. Rewrite `hg'` using `[Subgroup.mul_normal]`. Take `⟨_, ⟨u, hu, rfl⟩, n, hn, hun⟩` from `hg'`. Establish `h1 : u⁻¹ * g ∈ ψ ⁻¹' (U : Set (GQ v))`. Rewrite using `[← hWe]`.

Apply `hN` to reduce the goal to its premises. Establish `: ((u⁻¹ * g : ↥(Dec (F` using `ℚ) A)) : Ω ≃ₐ[ℚ] Ω) = n := by`. Rewrite using `[Subgroup.coe_mul, ← hun]`. Simplify using the standard rewrite rules. Use `show ((u⁻¹ * g : ↥(Dec (F := ℚ) A)) : Ω ≃ₐ[ℚ] Ω) ∈ N`.

Rewrite using `[this]`. Conclude with `hn`. Establish `h2` using `U.mul_mem (show ψ u ∈ U from hu) (show ψ (u⁻¹ * g) ∈ U from h1)`. Rewrite `h2` using `[← map_mul, mul_inv_cancel_left]`. Then use the resulting hypothesis. Use `⟨IntermediateField.fixedField H, ?_, fun τ => ?_⟩` and prove the remaining obligations.

Rewrite using `[← InfiniteGalois.isOpen_iff_finite, hfix]`. Conclude with `hHo`. Take `⟨g, hg⟩` from `e.surjective ⟨τ, hall τ⟩`. Establish `hτ : ψ g = τ` using `congrArg Subtype.val hg`. Establish `hc : ∀ x, τ (j x) = j ((g : Ω ≃ₐ[ℚ] Ω) x)` using `fun x => by rw [← hτ]; exact hec g x`.

Rewrite using `[← hτ, ← hmem, hτ]`. Use `conv_lhs => rw [← hfix]`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Simplify using `only [hc, j.injective.eq_iff]`. Conclude with `⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩`.
-/
private theorem exists_field {v : ℕ} [Fact v.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {A : ValuationSubring Ω} {j : Ω →+* PadicAlgCl v} (hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
    (U : Subgroup (GQ v)) (hU : IsOpen (U : Set (GQ v))) :
    ∃ F : IntermediateField ℚ Ω, FiniteDimensional ℚ F ∧
      ∀ τ : GQ v, τ ∈ U ↔ ∀ x : F, τ (j (algebraMap F Ω x)) = j (algebraMap F Ω x) := by
  let K0 : FinExt v := ⟨IntermediateField.adjoin ℚ_[v] (Set.range fun x : ℚ => j (algebraMap ℚ Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap ℚ Ω))⟩
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := ℚ) hA K0 rfl
  have hall : ∀ τ : GQ v, τ ∈ GK K0 := fun τ =>
    (GlobalTheory.PlaceBridge.mem_GK_iff (j := j) K0 rfl τ).2 fun x => by simp
  let ψ : ↥(Dec (F := ℚ) A) →* GQ v := (GK K0).subtype.comp e.toMonoidHom
  have hψ : Continuous ψ := continuous_subtype_val.comp he
  obtain ⟨W, hW, hWe⟩ := isOpen_induced_iff.1 (hU.preimage hψ)
  have hW1 : (1 : Ω ≃ₐ[ℚ] Ω) ∈ W := by
    have : (1 : ↥(Dec (F := ℚ) A)) ∈ ψ ⁻¹' (U : Set (GQ v)) := by
      show ψ 1 ∈ U
      rw [map_one]; exact U.one_mem
    rw [← hWe] at this
    exact this
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW hW1
  let H : Subgroup (Ω ≃ₐ[ℚ] Ω) := (U.comap ψ).map (Dec (F := ℚ) A).subtype ⊔ N.toSubgroup
  have hHo : IsOpen (H : Set (Ω ≃ₐ[ℚ] Ω)) := Subgroup.isOpen_mono le_sup_right N.isOpen
  have hHc : IsClosed (H : Set (Ω ≃ₐ[ℚ] Ω)) := H.isClosed_of_isOpen hHo
  have hfix : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHc⟩
  have hmem : ∀ g : ↥(Dec (F := ℚ) A), (g : Ω ≃ₐ[ℚ] Ω) ∈ H ↔ ψ g ∈ U := fun g => by
    refine ⟨fun hg => ?_, fun hg => Subgroup.mem_sup_left ⟨g, hg, rfl⟩⟩
    have hg' : (g : Ω ≃ₐ[ℚ] Ω) ∈ (H : Set (Ω ≃ₐ[ℚ] Ω)) := hg
    rw [Subgroup.mul_normal] at hg'
    obtain ⟨_, ⟨u, hu, rfl⟩, n, hn, hun⟩ := hg'
    have h1 : u⁻¹ * g ∈ ψ ⁻¹' (U : Set (GQ v)) := by
      rw [← hWe]
      apply hN
      have : ((u⁻¹ * g : ↥(Dec (F := ℚ) A)) : Ω ≃ₐ[ℚ] Ω) = n := by
        rw [Subgroup.coe_mul, ← hun]; simp
      show ((u⁻¹ * g : ↥(Dec (F := ℚ) A)) : Ω ≃ₐ[ℚ] Ω) ∈ N
      rw [this]; exact hn
    have h2 := U.mul_mem (show ψ u ∈ U from hu) (show ψ (u⁻¹ * g) ∈ U from h1)
    rwa [← map_mul, mul_inv_cancel_left] at h2
  refine ⟨IntermediateField.fixedField H, ?_, fun τ => ?_⟩
  · rw [← InfiniteGalois.isOpen_iff_finite, hfix]; exact hHo
  · obtain ⟨g, hg⟩ := e.surjective ⟨τ, hall τ⟩
    have hτ : ψ g = τ := congrArg Subtype.val hg
    have hc : ∀ x, τ (j x) = j ((g : Ω ≃ₐ[ℚ] Ω) x) := fun x => by rw [← hτ]; exact hec g x
    rw [← hτ, ← hmem, hτ]
    conv_lhs => rw [← hfix]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    simp only [hc, j.injective.eq_iff]
    exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩

/- English proof (translation)
Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Set `j0 : Ω →ₐ[ℚ] PadicAlgCl v` to `IsAlgClosed.lift`. Set `j : Ω →+* PadicAlgCl v` to `j0.toRingHom`.

Set `A : ValuationSubring Ω` to `(Valued.v (R := PadicAlgCl v)).valuationSubring.comap j`. Establish `hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1` using `fun x => by`. Express the relevant statement in the definitionally equal form `Valued.v (j x) ≤ 1 ↔ _`. Rewrite using `[PadicAlgCl.valuation_def]`. Conclude with `Iff.rfl`.

Take `⟨F, hF, hFU⟩` from `exists_field hA φ.range (by simpa using hφ.isOpen_range)`. Apply the tactic sequence `haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := by convert hF <;> exact Subsingleton.elim _ _ }`. Use `haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩`. Set `K : FinExt v` to `⟨IntermediateField.adjoin ℚ_[v] (Set.range fun x : F => j (algebraMap F Ω x)), GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩`. Take `⟨e, he, he', hec⟩` from `GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hA K rfl`.

Establish `hK : GK K = φ.range` using `Subgroup.ext fun τ => (GlobalTheory.PlaceBridge.mem_GK_iff (j := j) K rfl τ).trans (hFU τ).symm`. Take `⟨w, hw, hAw⟩` from `GlobalTheory.DecLocal.exists_place_below (p := v) (F := F) A ((GlobalTheory.DecLocal.norm_lt_one_iff A j hA _).1 (by simpa using GlobalTheory.PlaceBridge.norm_l_lt_one (l := v)))`. Set `e' : ↥(Dec (F` to `F) A) ≃* G := (e.trans (MulEquiv.subgroupCongr hK)).trans (MonoidHom.ofInjective hφ.injective).symm`. Establish `he1 : ∀ g, φ (e' g) = (e g : GQ v)` using `fun g => MonoidHom.apply_ofInjective_symm hφ.injective _`. Use `⟨F, inferInstance, A, w, e', hAw, hw, ?_, ?_, ?_, fun l _ r g => ?_⟩` and prove the remaining obligations.

Rewrite using `[hφ.isInducing.continuous_iff]`. Establish `: φ ∘ e' = fun g => (e g : GQ v)` using `funext he1`. Rewrite using `[this]`. Conclude with `continuous_subtype_val.comp he`. Establish `: (e'.symm : G → _) = fun g => e.symm ⟨φ g, hK ▸ ⟨g, rfl⟩⟩` using `rfl`.

Rewrite using `[this]`. Conclude with `he'.comp (hφ.continuous.subtype_mk _)`. Rewrite using `[← GlobalTheory.DecLocal.finrank_closure_eq_locDeg v F Ω A j hA w hAw, ← hK]`. Conclude with `IntermediateField.finrank_eq_fixingSubgroup_index _ _`. Establish `hl : l.Prime` using `Fact.out`.

Establish `: NeZero ((l : ℕ) : Ω)` using `⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩`. Establish `: NeZero ((l : ℕ) : Om v)` using `⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩`. Establish `: NeZero (l ^ r)` using `⟨pow_ne_zero _ hl.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)`. Establish `hζ'` using `hζ.map_of_injective j.injective`.

Establish `ha : (g : Ω ≃ₐ[F] Ω) ζ = ζ ^ ((cycMod F Ω l r (g : Ω ≃ₐ[F] Ω) : ZMod (l ^ r))).val` using `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω (g : Ω ≃ₐ[F] Ω)) ζ hζ.pow_eq_one`. Establish `hb : (φ (e' g)) (j ζ) = j ζ ^ (PadicInt.toZModPow r ((cyc v l (φ (e' g)) : ℤ_[l]ˣ) : ℤ_[l])).val` using `cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ v) (Om v) (φ (e' g))) _ hζ'.pow_eq_one`. Establish `hc : (φ (e' g)) (j ζ) = j ((g : Ω ≃ₐ[F] Ω) ζ)` using `by rw [he1]; exact hec g ζ`. Rewrite `hb` using `[hc, ha, map_pow]`. Conclude with `(ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)).symm`.
-/
theorem UpperTheory.V.Loc.exists_dec {v : ℕ} [Fact v.Prime] {G : Type} [Group G] [TopologicalSpace G]
    (φ : G →* GQ v) (hφ : IsOpenEmbedding φ) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] :
    ∃ (F : IntermediateField ℚ Ω) (_ : NumberField F) (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F))
      (e : ↥(Dec (F := F) A) ≃* G), IsPlaceOver A w ∧ ((v : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ Continuous e ∧
      Continuous e.symm ∧ locDeg w = φ.range.index ∧ ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (g : ↥(Dec (F := F) A)),
        PadicInt.toZModPow r ((cyc v l (φ (e g)) : ℤ_[l]ˣ) : ℤ_[l]) =
          (cycMod F Ω l r (g : Ω ≃ₐ[F] Ω) : ZMod (l ^ r)) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let j0 : Ω →ₐ[ℚ] PadicAlgCl v := IsAlgClosed.lift
  let j : Ω →+* PadicAlgCl v := j0.toRingHom
  let A : ValuationSubring Ω := (Valued.v (R := PadicAlgCl v)).valuationSubring.comap j
  have hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1 := fun x => by
    change Valued.v (j x) ≤ 1 ↔ _
    rw [PadicAlgCl.valuation_def]
    exact Iff.rfl
  obtain ⟨F, hF, hFU⟩ := exists_field hA φ.range (by simpa using hφ.isOpen_range)
  haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := by convert hF <;> exact Subsingleton.elim _ _ }
  haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩
  let K : FinExt v := ⟨IntermediateField.adjoin ℚ_[v] (Set.range fun x : F => j (algebraMap F Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hA K rfl
  have hK : GK K = φ.range := Subgroup.ext fun τ =>
    (GlobalTheory.PlaceBridge.mem_GK_iff (j := j) K rfl τ).trans (hFU τ).symm
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := F) A
    ((GlobalTheory.DecLocal.norm_lt_one_iff A j hA _).1 (by simpa using GlobalTheory.PlaceBridge.norm_l_lt_one (l := v)))
  let e' : ↥(Dec (F := F) A) ≃* G :=
    (e.trans (MulEquiv.subgroupCongr hK)).trans (MonoidHom.ofInjective hφ.injective).symm
  have he1 : ∀ g, φ (e' g) = (e g : GQ v) := fun g => MonoidHom.apply_ofInjective_symm hφ.injective _
  refine ⟨F, inferInstance, A, w, e', hAw, hw, ?_, ?_, ?_, fun l _ r g => ?_⟩
  · rw [hφ.isInducing.continuous_iff]
    have : φ ∘ e' = fun g => (e g : GQ v) := funext he1
    rw [this]
    exact continuous_subtype_val.comp he
  · have : (e'.symm : G → _) = fun g => e.symm ⟨φ g, hK ▸ ⟨g, rfl⟩⟩ := rfl
    rw [this]
    exact he'.comp (hφ.continuous.subtype_mk _)
  · rw [← GlobalTheory.DecLocal.finrank_closure_eq_locDeg v F Ω A j hA w hAw, ← hK]
    exact IntermediateField.finrank_eq_fixingSubgroup_index _ _
  · have hl : l.Prime := Fact.out
    have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
    have : NeZero ((l : ℕ) : Om v) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
    have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
    have hζ' := hζ.map_of_injective j.injective
    have ha : (g : Ω ≃ₐ[F] Ω) ζ = ζ ^ ((cycMod F Ω l r (g : Ω ≃ₐ[F] Ω) : ZMod (l ^ r))).val :=
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω (g : Ω ≃ₐ[F] Ω)) ζ
        hζ.pow_eq_one
    have hb : (φ (e' g)) (j ζ) = j ζ ^ (PadicInt.toZModPow r ((cyc v l (φ (e' g)) : ℤ_[l]ˣ) : ℤ_[l])).val :=
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ v) (Om v) (φ (e' g))) _
        hζ'.pow_eq_one
    have hc : (φ (e' g)) (j ζ) = j ((g : Ω ≃ₐ[F] Ω) ζ) := by rw [he1]; exact hec g ζ
    rw [hc, ha, map_pow] at hb
    exact (ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)).symm

section Transport

variable {R R' Γ Γ' M : Type} [CommRing R] [CommRing R'] [Group Γ] [TopologicalSpace Γ] [Group Γ']
  [TopologicalSpace Γ'] [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R Γ M) (ρ' : Representation R' Γ' M) (e : Γ' ≃* Γ) (he : Continuous e)
  (he' : Continuous e.symm) (h : ∀ g m, ρ' g m = ρ (e g) m)

include h in
/- English proof (translation)
Assemble the required witnesses or components as `⟨Equiv.subtypeEquivRight fun m => by rw [mem_riemannRochSpace_iff_regularAt_everywhere, mem_riemannRochSpace_iff_regularAt_everywhere] refine ⟨fun hm g => by rw [h, hm], fun hm g => ?_⟩ rw [← e.apply_symm_apply g, ← h, hm]⟩`.
-/
private theorem invariants_equiv : Nonempty (H0 ρ ≃ H0 ρ') :=
  ⟨Equiv.subtypeEquivRight fun m => by
    rw [mem_riemannRochSpace_iff_regularAt_everywhere, mem_riemannRochSpace_iff_regularAt_everywhere]
    refine ⟨fun hm g => by rw [h, hm], fun hm g => ?_⟩
    rw [← e.apply_symm_apply g, ← h, hm]⟩

include he he' h in
/- English proof (translation)
Set `E : Z1 ρ ≃ Z1 ρ'` to `{ toFun := fun c => ⟨fun g => c.1 (e g), c.2.1.comp he, fun g g' => by beta_reduce`. Rewrite using `[h, map_mul, c.2.2]⟩`. Use `invFun := fun c => ⟨fun g => c.1 (e.symm g), c.2.1.comp he', fun g g' => by beta_reduce`. Rewrite using `[map_mul, c.2.2, h, e.apply_symm_apply]⟩`. Use `left_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (e.apply_symm_apply g))`.

Use `right_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (e.symm_apply_apply g)) }`. Use `⟨Quotient.congr E fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap, mem_coboundaries1, mem_coboundaries1]`. Use `exists_congr fun m => ⟨fun hm g => ?_, fun hm g => ?_⟩` and prove the remaining obligations. Rewrite using `[h]`.

Conclude with `hm (e g)`. Use `hm (e.symm g)` as an intermediate fact. Rewrite `this` using `[h, e.apply_symm_apply]`. Rewrite using `[← this]`. Use `show a.1 g - b.1 g = a.1 (e (e.symm g)) - b.1 (e (e.symm g))`.

Rewrite using `[e.apply_symm_apply]`.
-/
private theorem first_cohomology_equiv : Nonempty (H1 ρ ≃ H1 ρ') := by
  let E : Z1 ρ ≃ Z1 ρ' :=
    { toFun := fun c => ⟨fun g => c.1 (e g), c.2.1.comp he, fun g g' => by
        beta_reduce
        rw [h, map_mul, c.2.2]⟩
      invFun := fun c => ⟨fun g => c.1 (e.symm g), c.2.1.comp he', fun g g' => by
        beta_reduce
        rw [map_mul, c.2.2, h, e.apply_symm_apply]⟩
      left_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (e.apply_symm_apply g))
      right_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (e.symm_apply_apply g)) }
  refine ⟨Quotient.congr E fun a b => ?_⟩
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap,
    mem_coboundaries1, mem_coboundaries1]
  refine exists_congr fun m => ⟨fun hm g => ?_, fun hm g => ?_⟩
  · rw [h]; exact hm (e g)
  · have := hm (e.symm g)
    rw [h, e.apply_symm_apply] at this
    rw [← this]
    show a.1 g - b.1 g = a.1 (e (e.symm g)) - b.1 (e (e.symm g))
    rw [e.apply_symm_apply]

include he he' h in
/- English proof (translation)
Set `E : Z2 ρ ≃ Z2 ρ'` to `{ toFun := fun c => ⟨fun p => c.1 (e p.1, e p.2), c.2.1.comp (he.prodMap he), fun g g' g'' => by`. Simplify using `only [h, map_mul]`. Conclude with `c.2.2 _ _ _⟩`. Use `invFun := fun c => ⟨fun p => c.1 (e.symm p.1, e.symm p.2), c.2.1.comp (he'.prodMap he'), fun g g' g'' => by`. Use `c.2.2 (e.symm g) (e.symm g') (e.symm g'')` as an intermediate fact.

Rewrite `this` using `[h, e.apply_symm_apply]`. Simplify using `only [map_mul]`. Conclude with `this⟩`. Use `left_inv := fun c => Subtype.ext (funext fun p => by simp)`. Use `right_inv := fun c => Subtype.ext (funext fun p => by simp) }`.

Use `⟨Quotient.congr E fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap, separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, hd⟩`. Use `⟨fun g => c (e g), hc.comp he, funext fun ⟨g, g'⟩ => ?_⟩` and prove the remaining obligations.

Use `congrFun hd (e g, e g')` as an intermediate fact. Rewrite `this`, the goal using `[d1_apply]`. Rewrite using `[h, map_mul]`. Conclude with `this`. Introduce and unpack `⟨c, hc, hd⟩`.

Use `⟨fun g => c (e.symm g), hc.comp he', funext fun ⟨g, g'⟩ => ?_⟩` and prove the remaining obligations. Use `congrFun hd (e.symm g, e.symm g')` as an intermediate fact. Rewrite `this` using `[d1_apply, h, e.apply_symm_apply]`. Rewrite using `[d1_apply, map_mul, this]`. Use `show a.1 (e (e.symm g), e (e.symm g')) - b.1 (e (e.symm g), e (e.symm g')) = a.1 (g, g') - b.1 (g, g')`.

Rewrite using `[e.apply_symm_apply, e.apply_symm_apply]`.
-/
private theorem second_cohomology_equiv : Nonempty (H2 ρ ≃ H2 ρ') := by
  let E : Z2 ρ ≃ Z2 ρ' :=
    { toFun := fun c => ⟨fun p => c.1 (e p.1, e p.2), c.2.1.comp (he.prodMap he), fun g g' g'' => by
        simp only [h, map_mul]
        exact c.2.2 _ _ _⟩
      invFun := fun c => ⟨fun p => c.1 (e.symm p.1, e.symm p.2), c.2.1.comp (he'.prodMap he'), fun g g' g'' => by
        have := c.2.2 (e.symm g) (e.symm g') (e.symm g'')
        rw [h, e.apply_symm_apply] at this
        simp only [map_mul]
        exact this⟩
      left_inv := fun c => Subtype.ext (funext fun p => by simp)
      right_inv := fun c => Subtype.ext (funext fun p => by simp) }
  refine ⟨Quotient.congr E fun a b => ?_⟩
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap,
    separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]
  constructor
  · rintro ⟨c, hc, hd⟩
    refine ⟨fun g => c (e g), hc.comp he, funext fun ⟨g, g'⟩ => ?_⟩
    have := congrFun hd (e g, e g')
    rw [d1_apply] at this ⊢
    rw [h, map_mul]
    exact this
  · rintro ⟨c, hc, hd⟩
    refine ⟨fun g => c (e.symm g), hc.comp he', funext fun ⟨g, g'⟩ => ?_⟩
    have := congrFun hd (e.symm g, e.symm g')
    rw [d1_apply, h, e.apply_symm_apply] at this
    rw [d1_apply, map_mul, this]
    show a.1 (e (e.symm g), e (e.symm g')) - b.1 (e (e.symm g), e (e.symm g')) = a.1 (g, g') - b.1 (g, g')
    rw [e.apply_symm_apply, e.apply_symm_apply]

end Transport

/- English proof (translation)
Use `haveI : Finite R := Finite.of_injective _ (algebraMap R k).injective`. Set `T : Module.Dual k M →+ Module.Dual R M` to `{ toFun := fun f => (Algebra.trace R k).comp (f.restrictScalars R) map_zero' := by ext; simp map_add' := fun f f' => by ext; simp }`. Establish `hT : ∀ f m, T f m = Algebra.trace R k (f m)` using `fun _ _ => rfl`. Establish `hinj : Function.Injective T`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `f hf`. Use extensionality with `m`. Use `(traceForm_nondegenerate R k).1 (f m) fun a => ?_` and prove the remaining obligations. Use `hT f (a • m)` as an intermediate fact. Rewrite `this` using `[hf, f.map_smul, smul_eq_mul, mul_comm]`.

Conclude with `this.symm`. Use `haveI : Finite (Module.Dual R M) := DFunLike.finite _`. Establish `hbij : Function.Bijective T` using `hinj.bijective_of_nat_card_le (by`. Rewrite using `[Module.natCard_eq_pow_finrank (K := R) (V := Dual R M), Module.natCard_eq_pow_finrank (K := k) (V := Dual k M), Subspace.dual_finrank_eq, Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank])`. Use `Nat.card_congr ((Equiv.ofBijective _ hbij).subtypeEquiv fun f => ?_)` and prove the remaining obligations.

Rewrite using `[Equiv.ofBijective_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `hf g x`. Rewrite using `[hT, hT, h, hf, hχ, ← Algebra.smul_def, map_smul, smul_eq_mul]`. Introduce `hf g x`.

Take `⟨g, rfl⟩` from `e.surjective g`. Establish `: f.comp (ρ (e g)) = (χ (e g) : k) • f` using `hinj (LinearMap.ext fun y => by`. Use `hf g y` as an intermediate fact. Rewrite `this` using `[hT, hT, h]`. Rewrite using `[hT, hT, LinearMap.comp_apply, this, LinearMap.smul_apply, smul_eq_mul, hχ, ← Algebra.smul_def, map_smul, smul_eq_mul])`.

Conclude with `LinearMap.congr_fun this x`.
-/
private theorem card_H0dual {R k Γ Γ' M : Type} [Field R] [Field k] [Finite k] [Algebra R k] [Group Γ] [Group Γ']
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower R k M] [Finite M]
    (ρ : Representation k Γ M) (ρ' : Representation R Γ' M) (e : Γ' ≃* Γ) (h : ∀ g m, ρ' g m = ρ (e g) m)
    (χ : Γ →* kˣ) (χ' : Γ' →* Rˣ) (hχ : ∀ g, (χ (e g) : k) = algebraMap R k (χ' g)) :
    Nat.card (H0dual χ ρ) = Nat.card (H0dual χ' ρ') := by
  haveI : Finite R := Finite.of_injective _ (algebraMap R k).injective
  let T : Module.Dual k M →+ Module.Dual R M :=
    { toFun := fun f => (Algebra.trace R k).comp (f.restrictScalars R)
      map_zero' := by ext; simp
      map_add' := fun f f' => by ext; simp }
  have hT : ∀ f m, T f m = Algebra.trace R k (f m) := fun _ _ => rfl
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    ext m
    refine (traceForm_nondegenerate R k).1 (f m) fun a => ?_
    have := hT f (a • m)
    rw [hf, f.map_smul, smul_eq_mul, mul_comm] at this
    exact this.symm
  haveI : Finite (Module.Dual R M) := DFunLike.finite _
  have hbij : Function.Bijective T := hinj.bijective_of_nat_card_le (by
    rw [Module.natCard_eq_pow_finrank (K := R) (V := Dual R M), Module.natCard_eq_pow_finrank (K := k) (V := Dual k M),
      Subspace.dual_finrank_eq, Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank,
      ← Module.natCard_eq_pow_finrank])
  refine Nat.card_congr ((Equiv.ofBijective _ hbij).subtypeEquiv fun f => ?_)
  rw [Equiv.ofBijective_apply]
  constructor
  · intro hf g x
    rw [hT, hT, h, hf, hχ, ← Algebra.smul_def, map_smul, smul_eq_mul]
  · intro hf g x
    obtain ⟨g, rfl⟩ := e.surjective g
    have : f.comp (ρ (e g)) = (χ (e g) : k) • f := hinj (LinearMap.ext fun y => by
      have := hf g y
      rw [hT, hT, h] at this
      rw [hT, hT, LinearMap.comp_apply, this, LinearMap.smul_apply, smul_eq_mul, hχ, ← Algebra.smul_def,
        map_smul, smul_eq_mul])
    exact LinearMap.congr_fun this x

/- English proof (translation)
Use `Nat.card_congr (Equiv.subtypeEquivRight (α := TDual R M) fun y => ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `hy g m`. Establish `e` using `congrArg (fun φ : TDual R M => φ (ρ g m)) (hy g)`. Simplify using `only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply] at e`.

Rewrite `e` using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Conclude with `e.symm`. Introduce `hy g`. Use `TDual.ext fun m => ?_` and prove the remaining obligations. Simplify using `only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply]`.

Use `hy g (ρ g⁻¹ m)` as an intermediate fact. Rewrite `this` using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Conclude with `this.symm`.
-/
private theorem card_twDual {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (χ : Γ →* Rˣ) (ρ : Representation R Γ M) :
    Nat.card (H0 ((twDual χ ρ).comp (MonoidHom.id Γ))) = Nat.card (H0dual χ ρ) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (α := TDual R M) fun y => ?_)
  constructor
  · intro hy g m
    have e := congrArg (fun φ : TDual R M => φ (ρ g m)) (hy g)
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply] at e
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at e
    exact e.symm
  · intro hy g
    refine TDual.ext fun m => ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply]
    have := hy g (ρ g⁻¹ m)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    exact this.symm

/- English proof (translation)
Establish `h1 : x - (PadicInt.appr x 1 : ℕ) ∈ Ideal.span {(l : ℤ_[l]) ^ 1}` using `PadicInt.appr_spec 1 x`. Establish `h2 : PadicInt.toZModPow 1 x = (PadicInt.appr x 1 : ℕ)`. Rewrite using `[← sub_eq_zero, ← map_natCast (PadicInt.toZModPow (p := l) 1), ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow]`. Conclude with `h1`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 h1`.

Rewrite using `[h2, map_natCast, ← map_natCast (algebraMap ℤ_[l] k), ← sub_eq_zero, ← map_sub, ← hy]`. Simplify using `[h0]`.
-/
private theorem algebraMap_eq {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [Algebra ℤ_[l] k]
    [Algebra (ZMod (l ^ 1)) k] (h0 : (l : k) = 0) (x : ℤ_[l]) :
    algebraMap ℤ_[l] k x = algebraMap (ZMod (l ^ 1)) k (PadicInt.toZModPow 1 x) := by
  have h1 : x - (PadicInt.appr x 1 : ℕ) ∈ Ideal.span {(l : ℤ_[l]) ^ 1} := PadicInt.appr_spec 1 x
  have h2 : PadicInt.toZModPow 1 x = (PadicInt.appr x 1 : ℕ) := by
    rw [← sub_eq_zero, ← map_natCast (PadicInt.toZModPow (p := l) 1), ← map_sub, ← RingHom.mem_ker,
      PadicInt.ker_toZModPow]
    exact h1
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h1
  rw [h2, map_natCast, ← map_natCast (algebraMap ℤ_[l] k), ← sub_eq_zero, ← map_sub, ← hy]
  simp [h0]

/- English proof (translation)
Assemble the required witnesses or components as `⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance⟩`.
-/
private theorem exists_closure (K : Type) [Field K] :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra K Ω), IsAlgClosure K Ω :=
  ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance⟩

/- English proof (translation)
Introduce `hP v l _ _ G _ _ _ φ hφ k _ _ _ _ M _ _ _ _ _ ρ hρ`. Take `⟨Ω, _, _, _⟩` from `exists_closure ℚ`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Take `⟨F, _, A, w, e, hAw, hw, he, he', hdeg, hcyc⟩` from `exists_dec φ hφ Ω`.

Establish `hl : l.Prime` using `Fact.out`. Establish `h0 : (l : k) = 0` using `CharP.cast_eq_zero k l`. Use `haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩`. Use `haveI : Fact (l ^ 1).Prime := ⟨by rwa [pow_one]⟩`. Use `haveI : CharP k (l ^ 1) := by rwa [pow_one]`.

Use `letI : Algebra (ZMod (l ^ 1)) k := ZMod.algebra k (l ^ 1)`. Use `letI : Module (ZMod (l ^ 1)) M := Module.compHom M (algebraMap (ZMod (l ^ 1)) k)`. Use `haveI : IsScalarTower (ZMod (l ^ 1)) k M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Use `haveI : Finite M := Module.finite_of_finite k`. Set `ρ' : Representation (ZMod (l ^ 1)) ↥(Dec (F` to `F) A) M := resCoef (ZMod (l ^ 1)) (ρ.comp e.toMonoidHom)`.

Establish `h : ∀ g m, ρ' g m = ρ (e g) m` using `fun _ _ => rfl`. Establish `hρ' : ContAction ρ'` using `hρ.comp (he.prodMap continuous_id)`. Take `⟨e0⟩` from `invariants_equiv ρ ρ' e h`. Take `⟨e1⟩` from `first_cohomology_equiv ρ ρ' e he he' h`. Take `⟨e2⟩` from `second_cohomology_equiv ρ ρ' e he he' h`.

Take `⟨-, f1, f2, -⟩` from `hP.lf F Ω l 1 M A ρ' w one_pos hAw hρ'`. Take `⟨⟨inv⟩, -, -, -, hb⟩` from `hP.lt F Ω l 1 M A ρ' w one_pos hAw hρ'`. Establish `hE` using `hP.le F Ω l 1 M A ρ' w one_pos hAw hρ'`. Use `haveI : Finite (H1 ρ) := Finite.of_equiv _ e1.symm`. Use `haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm`.

Establish `hk : 1 < Nat.card k` using `Finite.one_lt_card`. Use `⟨Module.Finite.of_finite, Module.Finite.of_finite, ?_, ?_⟩` and prove the remaining obligations. Apply `Nat.pow_right_injective hk beta_reduce` to reduce the goal to its premises. Rewrite using `[pow_add, pow_add, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, Nat.card_congr e0, Nat.card_congr e1, Nat.card_congr e2]`. Use `split_ifs with hvl`.

Substitute `hvl` using the available equality. Rewrite using `[mul_comm φ.range.index, pow_mul, ← Module.natCard_eq_pow_finrank, ← hdeg]`. Conclude with `hE.1 hw`. Rewrite using `[pow_zero, mul_one]`. Use `hE.2 fun hlw => w.isPrime.ne_top ?_` and prove the remaining obligations.

Take `⟨a, b, hab⟩` from `(Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes Fact.out hl).2 hvl)).map (Int.castRingHom (𝓞 F))`. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`. Conclude with `w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by simpa using hw)) (w.asIdeal.mul_mem_left _ (by simpa using hlw))`. Apply `Nat.pow_right_injective hk beta_reduce` to reduce the goal to its premises. Set `χ` to `(cycMod F Ω l 1).comp (Dec (F := F) A).subtype`.

Use `haveI : Finite (Module.Dual k M) := DFunLike.finite _`. Use `haveI : Finite (TDual (ZMod (l ^ 1)) M) := (DFunLike.finite _ : Finite (M →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))`. Set `B : Type` to `H0 ((twDual χ ρ').comp (MonoidHom.id _))`. Set `E : H2 ρ' ≃ Module.Dual (ZMod (l ^ 1)) B` to `(Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight inv).toEquiv`. Use `haveI : Finite B := Subtype.finite`.

Rewrite using `[← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, Nat.card_congr e2, card_H0dual ρ ρ' e h _ χ fun g => (algebraMap_eq (l := l) (k := k) h0 _).trans (congrArg _ (hcyc l 1 g)), ← card_twDual, Nat.card_congr E, Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)), Subs …`.
-/
theorem UpperTheory.V.Loc.tateFin :
    LocalPublishedTheorems → ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v) (hφ : IsOpenEmbedding φ) (k : Type) [Field k] [Finite k] [CharP k l] [Algebra ℤ_[l] k] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k G M), ContAction ρ → Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ finrank k (H1 ρ) = finrank k ↥(H0 ρ) + finrank k (H2 ρ) + (if v = l then φ.range.index * finrank k M else 0) ∧ finrank k (H2 ρ) = finrank k ↥(H0dual ((cycA v l k).comp φ) ρ) := by
  intro hP v l _ _ G _ _ _ φ hφ k _ _ _ _ M _ _ _ _ _ ρ hρ
  obtain ⟨Ω, _, _, _⟩ := exists_closure ℚ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  obtain ⟨F, _, A, w, e, hAw, hw, he, he', hdeg, hcyc⟩ := exists_dec φ hφ Ω
  have hl : l.Prime := Fact.out
  have h0 : (l : k) = 0 := CharP.cast_eq_zero k l
  haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩
  haveI : Fact (l ^ 1).Prime := ⟨by rwa [pow_one]⟩
  haveI : CharP k (l ^ 1) := by rwa [pow_one]
  letI : Algebra (ZMod (l ^ 1)) k := ZMod.algebra k (l ^ 1)
  letI : Module (ZMod (l ^ 1)) M := Module.compHom M (algebraMap (ZMod (l ^ 1)) k)
  haveI : IsScalarTower (ZMod (l ^ 1)) k M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Finite M := Module.finite_of_finite k
  let ρ' : Representation (ZMod (l ^ 1)) ↥(Dec (F := F) A) M := resCoef (ZMod (l ^ 1)) (ρ.comp e.toMonoidHom)
  have h : ∀ g m, ρ' g m = ρ (e g) m := fun _ _ => rfl
  have hρ' : ContAction ρ' := hρ.comp (he.prodMap continuous_id)
  obtain ⟨e0⟩ := invariants_equiv ρ ρ' e h
  obtain ⟨e1⟩ := first_cohomology_equiv ρ ρ' e he he' h
  obtain ⟨e2⟩ := second_cohomology_equiv ρ ρ' e he he' h
  obtain ⟨-, f1, f2, -⟩ := hP.lf F Ω l 1 M A ρ' w one_pos hAw hρ'
  obtain ⟨⟨inv⟩, -, -, -, hb⟩ := hP.lt F Ω l 1 M A ρ' w one_pos hAw hρ'
  have hE := hP.le F Ω l 1 M A ρ' w one_pos hAw hρ'
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1.symm
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm
  have hk : 1 < Nat.card k := Finite.one_lt_card
  refine ⟨Module.Finite.of_finite, Module.Finite.of_finite, ?_, ?_⟩
  · apply Nat.pow_right_injective hk
    beta_reduce
    rw [pow_add, pow_add, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank,
      ← Module.natCard_eq_pow_finrank, Nat.card_congr e0, Nat.card_congr e1, Nat.card_congr e2]
    split_ifs with hvl
    · subst hvl
      rw [mul_comm φ.range.index, pow_mul, ← Module.natCard_eq_pow_finrank, ← hdeg]
      exact hE.1 hw
    · rw [pow_zero, mul_one]
      refine hE.2 fun hlw => w.isPrime.ne_top ?_
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes Fact.out hl).2 hvl)).map
        (Int.castRingHom (𝓞 F))
      rw [Ideal.eq_top_iff_one, ← hab]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by simpa using hw))
        (w.asIdeal.mul_mem_left _ (by simpa using hlw))
  · apply Nat.pow_right_injective hk
    beta_reduce
    let χ := (cycMod F Ω l 1).comp (Dec (F := F) A).subtype
    haveI : Finite (Module.Dual k M) := DFunLike.finite _
    haveI : Finite (TDual (ZMod (l ^ 1)) M) := (DFunLike.finite _ : Finite (M →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))
    let B : Type := H0 ((twDual χ ρ').comp (MonoidHom.id _))
    let E : H2 ρ' ≃ Module.Dual (ZMod (l ^ 1)) B :=
      (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight inv).toEquiv
    haveI : Finite B := Subtype.finite
    rw [← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, Nat.card_congr e2,
      card_H0dual ρ ρ' e h _ χ fun g => (algebraMap_eq (l := l) (k := k) h0 _).trans (congrArg _ (hcyc l 1 g)),
      ← card_twDual, Nat.card_congr E, Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)),
      Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank]
