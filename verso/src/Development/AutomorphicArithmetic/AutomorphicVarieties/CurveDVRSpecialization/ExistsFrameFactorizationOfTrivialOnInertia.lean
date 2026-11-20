import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open scoped Matrix
set_option linter.overlappingInstances false

/- English proof (translation)
Establish `h : IsLift (RingEquiv.refl ℚ) ((g.symm : Ω ≃ₐ[ℚ] Ω) : Ω ≃+* Ω)` using `fun q => g.symm.commutes q`. Set `σ : Ω ≃+* Ω` to `((g.symm : Ω ≃ₐ[ℚ] Ω) : Ω ≃+* Ω)`. Establish `hA : ∀ y : Ω, σ y ∈ A ↔ y ∈ A.comap (σ : Ω →+* Ω)` using `fun y => by`. Rewrite using `[ValuationSubring.mem_comap]`. Both sides reduce to the same expression.

Use `⟨A.comap (σ : Ω →+* Ω), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← val_lt_one hA (l : Ω), map_natCast]`. Conclude with `hl`. Establish `hc` using `conjGal_mem_Ine h hA hx`. Use `hc using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `z`. Both sides reduce to the same expression.
-/
private theorem fac_conj {Ω : Type} [Field Ω] [CharZero Ω] (l : ℕ) (A : ValuationSubring Ω) (g x : G ℚ Ω)
    (hl : ¬ A.valuation (l : Ω) < 1) (hx : x ∈ Ine (F := ℚ) A) :
    ∃ A' : ValuationSubring Ω, ¬ A'.valuation (l : Ω) < 1 ∧ g * x * g⁻¹ ∈ Ine (F := ℚ) A' := by
  have h : IsLift (RingEquiv.refl ℚ) ((g.symm : Ω ≃ₐ[ℚ] Ω) : Ω ≃+* Ω) := fun q => g.symm.commutes q
  let σ : Ω ≃+* Ω := ((g.symm : Ω ≃ₐ[ℚ] Ω) : Ω ≃+* Ω)
  have hA : ∀ y : Ω, σ y ∈ A ↔ y ∈ A.comap (σ : Ω →+* Ω) := fun y => by
    rw [ValuationSubring.mem_comap]
    rfl
  refine ⟨A.comap (σ : Ω →+* Ω), ?_, ?_⟩
  · rw [← val_lt_one hA (l : Ω), map_natCast]
    exact hl
  · have hc := conjGal_mem_Ine h hA hx
    convert hc using 1
    ext z
    rfl

/- English proof (translation)
Introduce `Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ Φ k n r hr hine`. Establish `hgal : ∀ s : G L Ω, galEmb ℚ L Ω s ∈ upl Ω L ⊓ η.ker` using `fun s => by`. Establish `h` using `galEmb_mem ℚ L Ω s`. Rewrite `h` using `[k.gal]`. Then use the resulting hypothesis. Establish `hmem : ∀ s : G L Ω, galEmb ℚ L Ω s ∈ upl Ω L` using `fun s => (hgal s).1`.

Establish `hq : ∀ s, (k.p0 s : Φ.Γ) = k.p ⟨galEmb ℚ L Ω s, hmem s⟩` using `fun s => rfl`. Set `q : G L Ω →* Φ.G0` to `{ toFun := k.p0 map_one' := by`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hq]`. Rewrite using `[show (⟨galEmb ℚ L Ω 1, hmem 1⟩ : upl Ω L) = 1 from Subtype.ext (map_one _), map_one]`.

Both sides reduce to the same expression. Use the proof step `map_mul' := fun s t => by`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Subgroup.coe_mul, hq, hq, hq, ← map_mul]`. Conclude with `congrArg k.p (Subtype.ext (map_mul _ _ _)) }`.

Establish `hqv : ∀ s, ((q s : Φ.G0) : Φ.Γ) = k.p ⟨galEmb ℚ L Ω s, hmem s⟩` using `fun s => rfl`. Establish `hqs : Function.Surjective q`. Introduce `x`. Take `⟨u, hu⟩` from `k.p_surj x.val`. Establish `hu1 : (u : G ℚ Ω) ∈ galOf ℚ L Ω`.

Rewrite using `[k.gal]`. Use `⟨u.2, MonoidHom.mem_ker.mpr ?_⟩` and prove the remaining obligations. Rewrite using `[← k.del u, hu]`. Conclude with `MonoidHom.mem_ker.mp x.2`. Rewrite `hu1` using `[← range_galEmb ℚ L Ω]`.

Take `⟨s, hs⟩` from `hu1`. Use `⟨s, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hqv, ← hu]`. Conclude with `congrArg k.p (Subtype.ext hs)`. Establish `hgc : Continuous (galEmb ℚ L Ω)` using `(galEmbTop ℚ L Ω).1.continuous`.

Establish `hqc : Continuous q`. Use `continuous_induced_rng.2 ?_` and prove the remaining obligations. Conclude with `k.p_cont.comp (hgc.subtype_mk hmem)`. Establish `hinj : Function.Injective (galEmb ℚ L Ω)` using `(galEmbTop ℚ L Ω).1.injective`. Establish `hker : ∀ s, q s = 1 → r s = 1`.

Introduce `s hs`. Establish `h1 : (⟨galEmb ℚ L Ω s, hmem s⟩ : upl Ω L) ∈ k.p.ker`. Rewrite using `[MonoidHom.mem_ker, ← hqv, hs]`. Both sides reduce to the same expression. Rewrite `h1` using `[k.p_ker]`.

Set `H' : Subgroup (upl Ω L)` to `(r.ker.map (galEmb ℚ L Ω)).comap (upl Ω L).subtype`. Establish `hcl : IsClosed (H' : Set (upl Ω L))`. Establish `hk : IsClosed (r.ker : Set (G L Ω))` using `by haveI : T2Space (Qbar l) := inferInstance haveI : T2Space (Matrix (Fin n) (Fin n) (Qbar l)) := (inferInstance : T2Space (Fin n → Fin n → Qbar l)) haveI h2 : T2Space (GL (Fin n) (Qbar l)) := inferInstance haveI : T1Space (GL (Fin n) (Qbar l)) := @T2Space.t1Space _ _ h2`. Conclude with `isClosed_singleton.preimage hr`. Establish `hi : IsClosed ((galEmb ℚ L Ω) '' (r.ker : Set (G L Ω)))` using `(hk.isCompact.image hgc).isClosed`.

Conclude with `hi.preimage continuous_subtype_val`. Establish `hX : Subgroup.normalClosure {s : upl Ω L | ∃ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 ∧ (s : G ℚ Ω) ∈ Ine B' ∧ η s = 1 ∧ barChar O Ψ s = 1} ≤ H'`. Unfold `Subgroup.normalClosure`. Use `(Subgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce `c hc`.

Rewrite `hc` using `[Group.mem_conjugatesOfSet_iff]`. Take `⟨x, ⟨B', hB'l, hxI, hxη, hxbar⟩, hconj⟩` from `hc`. Take `⟨u, hu⟩` from `isConj_iff.mp hconj`. Establish `hcv : (c : G ℚ Ω) = u * x * (u : G ℚ Ω)⁻¹`. Rewrite using `[← hu, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]`.

Take `⟨A', hA'l, hcI⟩` from `fac_conj l B' u x hB'l hxI`. Rewrite `hcI` using `[← hcv]`. Establish `hcη : η c = 1`. Rewrite using `[hcv, map_mul, map_mul, hxη, mul_one, ← map_mul, mul_inv_cancel, map_one]`. Establish `hcbar : barChar O Ψ c = 1`.

Rewrite using `[hcv, map_mul, map_mul, hxbar, mul_one, ← map_mul, mul_inv_cancel, map_one]`. Establish `hcgal : (c : G ℚ Ω) ∈ galOf ℚ L Ω`. Rewrite using `[k.gal]`. Conclude with `⟨c.2, hcη⟩`. Rewrite `hcgal` using `[← range_galEmb ℚ L Ω]`.

Take `⟨t, ht⟩` from `hcgal`. Establish `hΨ : Ψ c = 1` using `k.teich A' hA'l c ⟨hcI, c.2⟩ hcbar`. Use `show (c : G ℚ Ω) ∈ r.ker.map (galEmb ℚ L Ω)`. Use `⟨t, ?_, ht⟩` and prove the remaining obligations. Use `show r t = 1`.

Use `hine A' hA'l t ?_ ?_` and prove the remaining obligations. Use `show galEmb ℚ L Ω t ∈ Ine (F := ℚ) A'`. Rewrite using `[ht]`. Conclude with `hcI`. Rewrite using `[ht]`.

Conclude with `hΨ`. Establish `h2` using `(Subgroup.topologicalClosure_minimal _ hX hcl) h1`. Take `⟨t, ht, hts⟩` from `h2`. Rewrite `ht` using `[hinj hts]`. Conclude with `ht`.

Establish `hle : q.ker ≤ r.ker` using `fun s hs => hker s hs`. Set `e` to `QuotientGroup.quotientKerEquivOfSurjective q hqs`. Set `r' : Φ.G0 →* GL (Fin n) (Qbar l)` to `(QuotientGroup.lift q.ker r hle).comp e.symm.toMonoidHom`. Establish `hr'q : ∀ s, r' (q s) = r s`. Introduce `s`.

Establish `he : e.symm (q s) = (s : G L Ω ⧸ q.ker)`. Rewrite using `[MulEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Use `show QuotientGroup.lift q.ker r hle (e.symm (q s)) = r s`. Rewrite using `[he]`.

Both sides reduce to the same expression. Establish `hqq : Topology.IsQuotientMap q` using `Topology.IsQuotientMap.of_surjective_continuous hqs hqc`. Establish `hr'c : Continuous r'`. Rewrite using `[hqq.continuous_iff]`. Use `hr using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `s`. Conclude with `hr'q s`. Use `⟨r', hr'c, fun s => hr'q s, ?_⟩` and prove the remaining obligations. Introduce `P hP g`. Take `⟨s, rfl⟩` from `hqs g`.

Take `⟨hσ, hσc⟩` from `k.c`. Establish `hs'gal : σ * galEmb ℚ L Ω s * σ⁻¹ ∈ galOf ℚ L Ω`. Rewrite using `[k.gal]`. Use `⟨(upl Ω L).mul_mem ((upl Ω L).mul_mem hσ (hmem s)) ((upl Ω L).inv_mem hσ), MonoidHom.mem_ker.mpr ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, MonoidHom.mem_ker.mp (hgal s).2, mul_one, ← map_mul, mul_inv_cancel, map_one]`.

Rewrite `hs'gal` using `[← range_galEmb ℚ L Ω]`. Take `⟨s', hs'⟩` from `hs'gal`. Establish `hconj : Φ.conj (q s) = q s'`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[show ((Φ.conj (q s) : Φ.G0) : Φ.Γ) = Φ.c * (q s : Φ.Γ) * Φ.c⁻¹ from MulAut.conjNormal_apply _ _]`.

Rewrite using `[hqv, hqv, ← hσc, ← map_inv, ← map_mul, ← map_mul]`. Apply `congrArg k.p` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Conclude with `hs'.symm`.

Rewrite using `[hconj, hr'q, hr'q]`. Establish `h` using `hP s s' hs'`. Rewrite `h` using `[MonoidHom.one_apply, Units.val_one, one_smul]`. Conclude with `h`.
-/
theorem UpperTheory.exists_frame_factorization_of_trivial_on_inertia :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ} {L : Type} [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) {n : ℕ} (r : G L Ω →* GL (Fin n) (Qbar l)), Continuous r → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A, Ψ (galEmb ℚ L Ω s) = 1 → r s = 1) → ∃ r' : Φ.G0 →* GL (Fin n) (Qbar l), Continuous r' ∧ (∀ s, r' (k.p0 s) = r s) ∧ ∀ P : GL (Fin n) (Qbar l), Sd.IsPair σ r 1 P → ∀ g, (r' g).valᵀ * P.val * (r' (Φ.conj g)).val = P.val := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ Φ k n r hr hine
  have hgal : ∀ s : G L Ω, galEmb ℚ L Ω s ∈ upl Ω L ⊓ η.ker := fun s => by
    have h := galEmb_mem ℚ L Ω s
    rwa [k.gal] at h
  have hmem : ∀ s : G L Ω, galEmb ℚ L Ω s ∈ upl Ω L := fun s => (hgal s).1
  have hq : ∀ s, (k.p0 s : Φ.Γ) = k.p ⟨galEmb ℚ L Ω s, hmem s⟩ := fun s => rfl
  let q : G L Ω →* Φ.G0 :=
    { toFun := k.p0
      map_one' := by
        apply Subtype.ext
        rw [hq]
        rw [show (⟨galEmb ℚ L Ω 1, hmem 1⟩ : upl Ω L) = 1 from Subtype.ext (map_one _), map_one]
        rfl
      map_mul' := fun s t => by
        apply Subtype.ext
        rw [Subgroup.coe_mul, hq, hq, hq, ← map_mul]
        exact congrArg k.p (Subtype.ext (map_mul _ _ _)) }
  have hqv : ∀ s, ((q s : Φ.G0) : Φ.Γ) = k.p ⟨galEmb ℚ L Ω s, hmem s⟩ := fun s => rfl
  have hqs : Function.Surjective q := by
    intro x
    obtain ⟨u, hu⟩ := k.p_surj x.val
    have hu1 : (u : G ℚ Ω) ∈ galOf ℚ L Ω := by
      rw [k.gal]
      refine ⟨u.2, MonoidHom.mem_ker.mpr ?_⟩
      rw [← k.del u, hu]
      exact MonoidHom.mem_ker.mp x.2
    rw [← range_galEmb ℚ L Ω] at hu1
    obtain ⟨s, hs⟩ := hu1
    refine ⟨s, Subtype.ext ?_⟩
    rw [hqv, ← hu]
    exact congrArg k.p (Subtype.ext hs)
  have hgc : Continuous (galEmb ℚ L Ω) := (galEmbTop ℚ L Ω).1.continuous
  have hqc : Continuous q := by
    refine continuous_induced_rng.2 ?_
    exact k.p_cont.comp (hgc.subtype_mk hmem)
  have hinj : Function.Injective (galEmb ℚ L Ω) := (galEmbTop ℚ L Ω).1.injective
  have hker : ∀ s, q s = 1 → r s = 1 := by
    intro s hs
    have h1 : (⟨galEmb ℚ L Ω s, hmem s⟩ : upl Ω L) ∈ k.p.ker := by
      rw [MonoidHom.mem_ker, ← hqv, hs]
      rfl
    rw [k.p_ker] at h1
    let H' : Subgroup (upl Ω L) := (r.ker.map (galEmb ℚ L Ω)).comap (upl Ω L).subtype
    have hcl : IsClosed (H' : Set (upl Ω L)) := by
      have hk : IsClosed (r.ker : Set (G L Ω)) := by
        haveI : T2Space (Qbar l) := inferInstance
        haveI : T2Space (Matrix (Fin n) (Fin n) (Qbar l)) :=
          (inferInstance : T2Space (Fin n → Fin n → Qbar l))
        haveI h2 : T2Space (GL (Fin n) (Qbar l)) := inferInstance
        haveI : T1Space (GL (Fin n) (Qbar l)) := @T2Space.t1Space _ _ h2
        exact isClosed_singleton.preimage hr
      have hi : IsClosed ((galEmb ℚ L Ω) '' (r.ker : Set (G L Ω))) :=
        (hk.isCompact.image hgc).isClosed
      exact hi.preimage continuous_subtype_val
    have hX : Subgroup.normalClosure
        {s : upl Ω L | ∃ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 ∧ (s : G ℚ Ω) ∈ Ine B' ∧
          η s = 1 ∧ barChar O Ψ s = 1} ≤ H' := by
      unfold Subgroup.normalClosure
      refine (Subgroup.closure_le _).2 ?_
      intro c hc
      rw [Group.mem_conjugatesOfSet_iff] at hc
      obtain ⟨x, ⟨B', hB'l, hxI, hxη, hxbar⟩, hconj⟩ := hc
      obtain ⟨u, hu⟩ := isConj_iff.mp hconj
      have hcv : (c : G ℚ Ω) = u * x * (u : G ℚ Ω)⁻¹ := by
        rw [← hu, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      obtain ⟨A', hA'l, hcI⟩ := fac_conj l B' u x hB'l hxI
      rw [← hcv] at hcI
      have hcη : η c = 1 := by
        rw [hcv, map_mul, map_mul, hxη, mul_one, ← map_mul, mul_inv_cancel, map_one]
      have hcbar : barChar O Ψ c = 1 := by
        rw [hcv, map_mul, map_mul, hxbar, mul_one, ← map_mul, mul_inv_cancel, map_one]
      have hcgal : (c : G ℚ Ω) ∈ galOf ℚ L Ω := by
        rw [k.gal]
        exact ⟨c.2, hcη⟩
      rw [← range_galEmb ℚ L Ω] at hcgal
      obtain ⟨t, ht⟩ := hcgal
      have hΨ : Ψ c = 1 := k.teich A' hA'l c ⟨hcI, c.2⟩ hcbar
      show (c : G ℚ Ω) ∈ r.ker.map (galEmb ℚ L Ω)
      refine ⟨t, ?_, ht⟩
      show r t = 1
      refine hine A' hA'l t ?_ ?_
      · show galEmb ℚ L Ω t ∈ Ine (F := ℚ) A'
        rw [ht]
        exact hcI
      · rw [ht]
        exact hΨ
    have h2 := (Subgroup.topologicalClosure_minimal _ hX hcl) h1
    obtain ⟨t, ht, hts⟩ := h2
    rw [hinj hts] at ht
    exact ht
  have hle : q.ker ≤ r.ker := fun s hs => hker s hs
  let e := QuotientGroup.quotientKerEquivOfSurjective q hqs
  let r' : Φ.G0 →* GL (Fin n) (Qbar l) := (QuotientGroup.lift q.ker r hle).comp e.symm.toMonoidHom
  have hr'q : ∀ s, r' (q s) = r s := by
    intro s
    have he : e.symm (q s) = (s : G L Ω ⧸ q.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift q.ker r hle (e.symm (q s)) = r s
    rw [he]
    rfl
  have hqq : Topology.IsQuotientMap q := Topology.IsQuotientMap.of_surjective_continuous hqs hqc
  have hr'c : Continuous r' := by
    rw [hqq.continuous_iff]
    convert hr using 1
    funext s
    exact hr'q s
  refine ⟨r', hr'c, fun s => hr'q s, ?_⟩
  intro P hP g
  obtain ⟨s, rfl⟩ := hqs g
  obtain ⟨hσ, hσc⟩ := k.c
  have hs'gal : σ * galEmb ℚ L Ω s * σ⁻¹ ∈ galOf ℚ L Ω := by
    rw [k.gal]
    refine ⟨(upl Ω L).mul_mem ((upl Ω L).mul_mem hσ (hmem s)) ((upl Ω L).inv_mem hσ),
      MonoidHom.mem_ker.mpr ?_⟩
    rw [map_mul, map_mul, MonoidHom.mem_ker.mp (hgal s).2, mul_one, ← map_mul, mul_inv_cancel, map_one]
  rw [← range_galEmb ℚ L Ω] at hs'gal
  obtain ⟨s', hs'⟩ := hs'gal
  have hconj : Φ.conj (q s) = q s' := by
    apply Subtype.ext
    rw [show ((Φ.conj (q s) : Φ.G0) : Φ.Γ) = Φ.c * (q s : Φ.Γ) * Φ.c⁻¹ from
      MulAut.conjNormal_apply _ _]
    rw [hqv, hqv, ← hσc, ← map_inv, ← map_mul, ← map_mul]
    apply congrArg k.p
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hs'.symm
  rw [hconj, hr'q, hr'q]
  have h := hP s s' hs'
  rw [MonoidHom.one_apply, Units.val_one, one_smul] at h
  exact h
