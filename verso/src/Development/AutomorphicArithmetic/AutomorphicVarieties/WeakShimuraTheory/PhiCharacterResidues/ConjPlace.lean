import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

open scoped Pointwise in
/- English proof (translation)
Rewrite using `[valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_inv_pointwise_smul_iff, ValuationSubring.mem_inv_pointwise_smul_iff]`. Simplify using `only [AlgEquiv.smul_def, map_inv₀, map_eq_zero]`.
-/
private theorem val_lt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) (t : G F Ω) (y : Ω) :
    (t⁻¹ • A).valuation y < 1 ↔ A.valuation (t y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_inv_pointwise_smul_iff,
    ValuationSubring.mem_inv_pointwise_smul_iff]
  simp only [AlgEquiv.smul_def, map_inv₀, map_eq_zero]

open scoped Pointwise in
/- English proof (translation)
Use `⟨fun x => ?_, fun σ hσ => ?_⟩` and prove the remaining obligations. Rewrite using `[val_lt, AlgEquiv.commutes]`. Conclude with `h x`. Take `⟨hd, hi⟩` from `hσ`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite `hd`, the goal using `[ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]`. Rewrite using `[mul_smul, mul_smul, smul_inv_smul, hd]`. Rewrite `hx` using `[ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_inv_pointwise_smul_iff, AlgEquiv.smul_def]`. Rewrite using `[val_lt, map_sub]`. Use `hi (t x) ((ValuationSubring.valuation_le_one_iff A _).2 hx)` as an intermediate fact.

Simplify `this` using `[AlgEquiv.mul_apply, mul_inv_apply]`.
-/
private theorem conj_place {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (t : G F Ω) :
    IsPlaceOver (t⁻¹ • A) v ∧ ∀ σ ∈ Ine (F := F) A, t⁻¹ * σ * t ∈ Ine (F := F) (t⁻¹ • A) := by
  refine ⟨fun x => ?_, fun σ hσ => ?_⟩
  · rw [val_lt, AlgEquiv.commutes]
    exact h x
  · obtain ⟨hd, hi⟩ := hσ
    refine ⟨?_, fun x hx => ?_⟩
    · rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hd ⊢
      rw [mul_smul, mul_smul, smul_inv_smul, hd]
    · rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_inv_pointwise_smul_iff,
        AlgEquiv.smul_def] at hx
      rw [val_lt, map_sub]
      have := hi (t x) ((ValuationSubring.valuation_le_one_iff A _).2 hx)
      simpa [AlgEquiv.mul_apply, mul_inv_apply] using this

/- English proof (translation)
Introduce `l _ L Ω _ _ _ _ _ _ s V`. Establish `hres : ∀ (g : G L Ω) (x : Ω), W.resP L Ω g x = g x` using `fun _ _ => rfl`. Establish `hinj : Function.Injective (W.resP L Ω)` using `fun a b h => AlgEquiv.ext fun x => by rw [← hres a x, ← hres b x, h]`. Establish `hsurj : Function.Surjective V.pr`. Introduce and unpack `⟨y, hy⟩`.

Take `⟨g', rfl⟩` from `QuotientGroup.mk'_surjective (NS Ω V.S') y`. Take `⟨g, rfl⟩` from `(V.hη g').1 hy`. Conclude with `⟨g, rfl⟩`. Establish `hcont : Continuous V.pr` using `V.pr_cont W.continuous_resP`. Use `haveI : IsClosed ((NS Ω V.S' : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) := isClosed_NS Ω V.S'`.

Use `haveI : T2Space (GS Ω V.S') := by`. Unfold `GS`. Use `infer_instance`. Use `⟨hsurj, (hcont.isClosedMap).isQuotientMap hcont hsurj, fun U hU hI g hg => ?_⟩` and prove the remaining obligations. Use `open scoped Pointwise in`.

Establish `hsm : ∀ (g : G L Ω) (B : ValuationSubring Ω), W.resP L Ω g • B = g • B`. Introduce `g B`. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, AlgEquiv.smul_def, AlgEquiv.smul_def, hres]`. Establish `hM : IsClosed ((U.map (W.resP L Ω) : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω))`.

Rewrite using `[Subgroup.coe_map]`. Conclude with `((hU.isCompact).image W.continuous_resP).isClosed`. Establish `hle : NS Ω V.S' ≤ U.map (W.resP L Ω)`. Unfold `NS`. Use `Subgroup.topologicalClosure_minimal _ ?_ hM` and prove the remaining obligations.

Rewrite using `[Subgroup.normalClosure, Subgroup.closure_le]`. Introduce `c hc`. Rewrite `hc` using `[Group.mem_conjugatesOfSet_iff]`. Take `⟨a, ha, hac⟩` from `hc`. Take `⟨d, rfl⟩` from `isConj_iff.1 hac`.

Simplify using `only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq, exists_prop] at ha`. Take `⟨v, hv, A, hA, haA⟩` from `ha`. Establish `key` using `conj_place hA d⁻¹`. Simplify using `only [inv_inv] at key`. Take `⟨hA', hconj⟩` from `key`.

Establish `hb` using `hconj a haA`. Take `⟨g0, hg0⟩` from `s.unr _ v hA' hb`. Use `⟨g0, hI _ v hA' hv ?_, hg0⟩` and prove the remaining obligations. Rewrite `hb` using `[← hg0]`. Take `⟨hd, hi⟩` from `hb`.

Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Use `open scoped Pointwise in`. Rewrite `hd`, the goal using `[ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]`. Use `open scoped Pointwise in`. Rewrite using `[← hsm]` and apply the resulting hypothesis.

Use `hi x hx` as an intermediate fact. Rewrite `this` using `[hres]`. Then use the resulting hypothesis. Establish `hgN : W.resP L Ω g ∈ NS Ω V.S'`. Rewrite `hg` using `[MonoidHom.mem_ker, Subtype.ext_iff]`. Conclude with `(QuotientGroup.eq_one_iff _).1 hg`.

Take `⟨u, hu, hug⟩` from `hle hgN`. Rewrite using `[← hinj hug]`. Conclude with `hu`.
-/
theorem UpperTheory.V.Ws.phiKer :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev), Function.Surjective V.pr ∧ Topology.IsQuotientMap V.pr ∧ ∀ U : Subgroup (G L Ω), IsClosed (U : Set (G L Ω)) → (∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)), IsPlaceOver A v → v ∉ V.S' → Ine (F := L) A ≤ U) → V.pr.ker ≤ U := by
  intro l _ L Ω _ _ _ _ _ _ s V
  have hres : ∀ (g : G L Ω) (x : Ω), W.resP L Ω g x = g x := fun _ _ => rfl
  have hinj : Function.Injective (W.resP L Ω) := fun a b h =>
    AlgEquiv.ext fun x => by rw [← hres a x, ← hres b x, h]
  have hsurj : Function.Surjective V.pr := by
    rintro ⟨y, hy⟩
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (NS Ω V.S') y
    obtain ⟨g, rfl⟩ := (V.hη g').1 hy
    exact ⟨g, rfl⟩
  have hcont : Continuous V.pr := V.pr_cont W.continuous_resP
  haveI : IsClosed ((NS Ω V.S' : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) := isClosed_NS Ω V.S'
  haveI : T2Space (GS Ω V.S') := by
    unfold GS
    infer_instance
  refine ⟨hsurj, (hcont.isClosedMap).isQuotientMap hcont hsurj, fun U hU hI g hg => ?_⟩
  open scoped Pointwise in
  have hsm : ∀ (g : G L Ω) (B : ValuationSubring Ω), W.resP L Ω g • B = g • B := by
    intro g B
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, AlgEquiv.smul_def,
      AlgEquiv.smul_def, hres]
  have hM : IsClosed ((U.map (W.resP L Ω) : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) := by
    rw [Subgroup.coe_map]
    exact ((hU.isCompact).image W.continuous_resP).isClosed
  have hle : NS Ω V.S' ≤ U.map (W.resP L Ω) := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ hM
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro c hc
    rw [Group.mem_conjugatesOfSet_iff] at hc
    obtain ⟨a, ha, hac⟩ := hc
    obtain ⟨d, rfl⟩ := isConj_iff.1 hac
    simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq, exists_prop] at ha
    obtain ⟨v, hv, A, hA, haA⟩ := ha
    have key := conj_place hA d⁻¹
    simp only [inv_inv] at key
    obtain ⟨hA', hconj⟩ := key
    have hb := hconj a haA
    obtain ⟨g0, hg0⟩ := s.unr _ v hA' hb
    refine ⟨g0, hI _ v hA' hv ?_, hg0⟩
    rw [← hg0] at hb
    obtain ⟨hd, hi⟩ := hb
    refine ⟨?_, fun x hx => ?_⟩
    · open scoped Pointwise in
      rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hd ⊢
      open scoped Pointwise in
      rwa [← hsm]
    · have := hi x hx
      rwa [hres] at this
  have hgN : W.resP L Ω g ∈ NS Ω V.S' := by
    rw [MonoidHom.mem_ker, Subtype.ext_iff] at hg
    exact (QuotientGroup.eq_one_iff _).1 hg
  obtain ⟨u, hu, hug⟩ := hle hgN
  rw [← hinj hug]
  exact hu
