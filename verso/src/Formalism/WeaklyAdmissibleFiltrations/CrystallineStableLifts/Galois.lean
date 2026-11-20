import Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module TensorProduct

section CobGalois

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cob_apply_galois (x : V) (g : G) : cob ρ x g = ρ g x - x := rfl

variable [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul LL V]

/- English proof (translation)
Use `⟨⟨?_, fun g h => ?_⟩, x ⊗ₜ[Qp] (1 : B), fun g => ?_⟩` and prove the remaining obligations. Conclude with `(hcont x).sub continuous_const`. Simplify using `only [cob_apply_galois, map_mul, Module.End.mul_apply, map_sub]`. Normalize the expressions using the abelian group laws. Simplify using `[cob_apply_galois, actVB, sub_tmul]`.
-/
theorem coboundaryMap_mem_finiteCocycles (hcont : ∀ x, Continuous fun g => ρ g x) (x : V) :
    cob ρ x ∈ finiteCocycles PD ρ := by
  refine ⟨⟨?_, fun g h => ?_⟩, x ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · exact (hcont x).sub continuous_const
  · simp only [cob_apply_galois, map_mul, Module.End.mul_apply, map_sub]
    abel
  · simp [cob_apply_galois, actVB, sub_tmul]

/- English proof (translation)
Introduce and unpack `c ⟨x, rfl⟩`. Conclude with `coboundaryMap_mem_finiteCocycles hcont x`.
-/
theorem coboundaries_le_finiteCocycles (hcont : ∀ x, Continuous fun g => ρ g x) : B1 ρ ≤ finiteCocycles PD ρ := by
  rintro c ⟨x, rfl⟩
  exact coboundaryMap_mem_finiteCocycles hcont x

end CobGalois

/- English proof (translation)
Unfold `CobF`. Use `intros`. Conclude with `⟨coboundaries_le_finiteCocycles ‹_›, fun c hc => hc.1⟩`.
-/
theorem cobF : CobF := by
  unfold CobF
  intros
  exact ⟨coboundaries_le_finiteCocycles ‹_›, fun c hc => hc.1⟩

/- English proof (translation)
Introduce `G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ O _ _ V _ _ _ _ _ _ ρ _ _ _ _ L c a hc ha h`. Use `⟨hc, ?_⟩` and prove the remaining obligations. Establish `h2 : (algebraMap O LL a) • c ∈ finiteCocycles PD ρ`. Rewrite using `[algebraMap_smul]`. Conclude with `h.2`.

Establish `h3` using `(finiteCocycles PD ρ).smul_mem (algebraMap O LL a)⁻¹ h2`. Rewrite `h3` using `[inv_smul_smul₀ ha]`. Conclude with `h3`.
-/
theorem torsFreeT : TorsFreeT := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ O _ _ V _ _ _ _ _ _ ρ
    _ _ _ _ L c a hc ha h
  refine ⟨hc, ?_⟩
  have h2 : (algebraMap O LL a) • c ∈ finiteCocycles PD ρ := by
    rw [algebraMap_smul]
    exact h.2
  have h3 := (finiteCocycles PD ρ).smul_mem (algebraMap O LL a)⁻¹ h2
  rw [inv_smul_smul₀ ha] at h3
  exact h3

/- English proof (translation)
Introduce `G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V V' _ _ _ _ _ _ _ _ ρ ρ' _ _ _ _ _ _ _ f hf hequiv c`. Establish `hZ : c ∈ continuousCocycles ρ → ⇑f ∘ c ∈ continuousCocycles ρ'`. Introduce and unpack `⟨hc1, hc2⟩`. Use `⟨hf.comp hc1, fun g h => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f (c (g * h)) = f (c g) + ρ' g (f (c h))`.

Rewrite using `[hc2, map_add, hequiv]`. Use `⟨hZ, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨hc, x, hx⟩`. Set `m` to `AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)`. Establish `hm : ∀ g y, m (actVB PD ρ g y) = actVB PD ρ' g (m y)`.

Introduce `g y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [m, actVB, hequiv]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.

Use `⟨hZ hc, m x, fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f (c g) ⊗ₜ[Qp] (1 : B) = _`. Use `congrArg m (hx g)` as an intermediate fact. Simplify using `only [m, AlgebraTensorModule.map_tmul, LinearMap.id_apply, map_sub] at this`. Rewrite using `[this, ← hm]`.
-/
theorem cocyclesFunctorial_holds : CocyclesFunctorial := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V V' _ _ _ _ _ _ _ _ ρ ρ'
    _ _ _ _ _ _ _ f hf hequiv c
  have hZ : c ∈ continuousCocycles ρ → ⇑f ∘ c ∈ continuousCocycles ρ' := by
    rintro ⟨hc1, hc2⟩
    refine ⟨hf.comp hc1, fun g h => ?_⟩
    change f (c (g * h)) = f (c g) + ρ' g (f (c h))
    rw [hc2, map_add, hequiv]
  refine ⟨hZ, ?_⟩
  rintro ⟨hc, x, hx⟩
  let m := AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)
  have hm : ∀ g y, m (actVB PD ρ g y) = actVB PD ρ' g (m y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [m, actVB, hequiv]
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨hZ hc, m x, fun g => ?_⟩
  change f (c g) ⊗ₜ[Qp] (1 : B) = _
  have := congrArg m (hx g)
  simp only [m, AlgebraTensorModule.map_tmul, LinearMap.id_apply, map_sub] at this
  rw [this, ← hm]

section ImGalois

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace G]

/- English proof (translation)
Unfold `LatHom.col LatHom.LiftF`. Rewrite using `[Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]`. Simplify using `only [pow_zero, one_smul]`. Conclude with `⟨fun h c hc => h hc, fun h c hc => h c hc⟩`.
-/
theorem colZero_iff_galois [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L') :
    F.col PD = 0 ↔ F.LiftF PD 0 := by
  unfold LatHom.col LatHom.LiftF
  rw [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
    Submodule.comap_subtype_eq_top]
  simp only [pow_zero, one_smul]
  exact ⟨fun h c hc => h hc, fun h c hc => h c hc⟩

/- English proof (translation)
Use `sup_le (Submodule.map_le_iff_le_comap.mpr fun c hc => F.post_Z1fT PD c hc) ?_` and prove the remaining obligations. Introduce and unpack `c ⟨x, hx, rfl⟩`. Establish `hf : cob ρ' x ∈ finiteCocycles PD ρ'` using `coboundaryMap_mem_finiteCocycles hcont x`. Use `⟨⟨hf.1, ?_⟩, hf⟩` and prove the remaining obligations. Introduce `g _`.

Conclude with `L'.T.sub_mem (L'.stable g x hx) hx`.
-/
theorem imF_le_galois [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L')
    (hcont : ∀ x, Continuous fun g => ρ' g x) : F.ImF PD ≤ latticeFiniteCocycles PD L' := by
  refine sup_le (Submodule.map_le_iff_le_comap.mpr fun c hc => F.post_Z1fT PD c hc) ?_
  rintro c ⟨x, hx, rfl⟩
  have hf : cob ρ' x ∈ finiteCocycles PD ρ' := coboundaryMap_mem_finiteCocycles hcont x
  refine ⟨⟨hf.1, ?_⟩, hf⟩
  intro g _
  exact L'.T.sub_mem (L'.stable g x hx) hx

end ImGalois

/- English proof (translation)
Unfold `ImFLe`. Use `intros`. Conclude with `⟨imF_le_galois _ ‹_›, colZero_iff_galois _⟩`.
-/
theorem imFLe : ImFLe := by
  unfold ImFLe
  intros
  exact ⟨imF_le_galois _ ‹_›, colZero_iff_galois _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨cobF, torsFreeT, cocyclesFunctorial_holds, imFLe⟩`.
-/
theorem finiteCocycles_properties : CobF ∧ TorsFreeT ∧ CocyclesFunctorial ∧ ImFLe :=
  ⟨cobF, torsFreeT, cocyclesFunctorial_holds, imFLe⟩

end Formalism.WeaklyAdmissibleFiltrations
