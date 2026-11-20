import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LengthEqAddEigen
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

/- English proof (translation)
Establish `hN : (NS Ω S).Normal` using `Subgroup.is_normal_topologicalClosure _`. Establish `hclosed : IsClosed ((NS Ω S).comap φ : Set (G F' Ω'))` using `(isClosed_NS Ω S).preimage h1`. Use `haveI : ((NS Ω S).comap φ).Normal := hN.comap φ`. Apply `Subgroup.topologicalClosure_minimal _ _ hclosed` to reduce the goal to its premises. Apply `Subgroup.normalClosure_le_normal` to reduce the goal to its premises.

Introduce `g hg`. Simplify using `only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq] at hg`. Take `⟨v', hv', A', hA', hgA⟩` from `hg`. Take `⟨v, A, hA, habove, -, -, hine⟩` from `placeTransport F Ω F' Ω' f σ hσ φ h2 v' A' hA'`. Establish `hgi : φ g ∈ Ine A` using `(hine g).2 hgA`.

Use `show φ g ∈ NS Ω S`. Apply `Subgroup.le_topologicalClosure` to reduce the goal to its premises. Apply `Subgroup.subset_normalClosure` to reduce the goal to its premises. Simplify using `only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq]`. Use `⟨v, ?_, A, hA, hgi⟩` and prove the remaining obligations.

Rewrite using `[hS]`. Rewrite `hv'` using `[hS']`. Conclude with `fun h => hv' ((habove l).1 h)`.
-/
private theorem UpperTheory.V.LDataCardLeFinrank.transport_mem_NS
    {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {F' Ω' : Type} [Field F']
    [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] {l : ℕ} [Fact l.Prime] (f : F →+* F')
    (σ : Ω ≃+* Ω') (hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) (φ : G F' Ω' →* G F Ω)
    (h1 : Continuous φ) (h2 : ∀ g x, σ (φ g x) = g (σ x))
    {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S = Above F l) {S' : Set (HeightOneSpectrum (𝓞 F'))}
    (hS' : S' = Above F' l) : NS Ω' S' ≤ (NS Ω S).comap φ := by
  have hN : (NS Ω S).Normal := Subgroup.is_normal_topologicalClosure _
  have hclosed : IsClosed ((NS Ω S).comap φ : Set (G F' Ω')) := (isClosed_NS Ω S).preimage h1
  haveI : ((NS Ω S).comap φ).Normal := hN.comap φ
  apply Subgroup.topologicalClosure_minimal _ _ hclosed
  apply Subgroup.normalClosure_le_normal
  intro g hg
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq] at hg
  obtain ⟨v', hv', A', hA', hgA⟩ := hg
  obtain ⟨v, A, hA, habove, -, -, hine⟩ := placeTransport F Ω F' Ω' f σ hσ φ h2 v' A' hA'
  have hgi : φ g ∈ Ine A := (hine g).2 hgA
  show φ g ∈ NS Ω S
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq]
  refine ⟨v, ?_, A, hA, hgi⟩
  rw [hS]
  rw [hS'] at hv'
  exact fun h => hv' ((habove l).1 h)

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ l _ D D' f σ hσ`. Take `⟨φ, hφc, hφact, hφcyc, -, -⟩` from `galTransport F Ω F' Ω' (f : F →+* F') σ hσ`. Establish `hσ' : ∀ x : F', σ.symm (algebraMap F' Ω' x) = algebraMap F Ω ((f.symm : F' →+* F) x)`. Introduce `x`. Apply `σ.injective` to reduce the goal to its premises.

Rewrite using `[RingEquiv.apply_symm_apply, hσ]`. Simplify using the standard rewrite rules. Take `⟨φ', hφ'c, hφ'act, -, -, -⟩` from `galTransport F' Ω' F Ω (f.symm : F' →+* F) σ.symm hσ'`. Establish `hleft : ∀ g, φ' (φ g) = g`. Introduce `g`.

Use `AlgEquiv.ext fun y => ?_` and prove the remaining obligations. Apply `σ.symm.injective` to reduce the goal to its premises. Rewrite using `[hφ'act]`. Apply `σ.injective` to reduce the goal to its premises. Rewrite using `[hφact, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`.

Establish `hright : ∀ g, φ (φ' g) = g`. Introduce `g`. Use `AlgEquiv.ext fun x => ?_` and prove the remaining obligations. Apply `σ.injective` to reduce the goal to its premises. Rewrite using `[hφact]`.

Apply `σ.symm.injective` to reduce the goal to its premises. Rewrite using `[hφ'act, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]`. Set `Φ : G F' Ω' ≃* G F Ω` to `{ toFun := φ, invFun := φ', left_inv := hleft, right_inv := hright, map_mul' := φ.map_mul }`. Use `haveI : (NS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F')))).Normal := Subgroup.is_normal_topologicalClosure _`. Use `haveI : (NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))).Normal := Subgroup.is_normal_topologicalClosure _`.

Establish `hmap : (NS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F')))).map (Φ : G F' Ω' →* G F Ω) = NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Subgroup.map_le_iff_le_comap]`. Conclude with `UpperTheory.V.LDataCardLeFinrank.transport_mem_NS (f : F →+* F') σ hσ φ hφc hφact D.hS D'.hS`. Introduce `h hh`.

Use `⟨φ' h, ?_, hright h⟩` and prove the remaining obligations. Conclude with `UpperTheory.V.LDataCardLeFinrank.transport_mem_NS (f.symm : F' →+* F) σ.symm hσ' φ' hφ'c hφ'act D'.hS D.hS hh`. Set `Ψ : GS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F'))) ≃* GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))` to `QuotientGroup.congr _ _ Φ hmap`. Establish `hΨmk : ∀ g : G F' Ω', Ψ (QuotientGroup.mk g) = QuotientGroup.mk (φ g)` using `fun g => QuotientGroup.congr_mk _ _ Φ hmap g`. Establish `hΨsmk : ∀ g : G F Ω, Ψ.symm (QuotientGroup.mk g) = QuotientGroup.mk (φ' g)`.

Introduce `g`. Apply `Ψ.injective` to reduce the goal to its premises. Rewrite using `[MulEquiv.apply_symm_apply, hΨmk, hright]`. Establish `hΨc : Continuous Ψ`. Rewrite using `[(QuotientGroup.isQuotientMap_mk _).continuous_iff]`.

Establish `: (Ψ ∘ QuotientGroup.mk) = (QuotientGroup.mk ∘ φ)` using `funext hΨmk`. Rewrite using `[this]`. Conclude with `QuotientGroup.continuous_mk.comp hφc`. Establish `hΨsc : Continuous Ψ.symm`. Rewrite using `[(QuotientGroup.isQuotientMap_mk _).continuous_iff]`.

Establish `: (Ψ.symm ∘ QuotientGroup.mk) = (QuotientGroup.mk ∘ φ')` using `funext hΨsmk`. Rewrite using `[this]`. Conclude with `QuotientGroup.continuous_mk.comp hφ'c`. Use `⟨Φ, Ψ, hφc, hφ'c, hΨc, hΨsc, hφact, fun g => hΨmk g, ?_⟩` and prove the remaining obligations. Introduce `g`.

Take `⟨h, rfl⟩` from `QuotientGroup.mk_surjective g`. Rewrite using `[hΨmk]`. Use `show D.chi (toGS Ω _ (φ h)) = D'.chi (toGS Ω' _ h)`. Establish `e1 : D.chi (toGS Ω _ (φ h)) = cycZ F Ω l (φ h)`. Rewrite using `[← D.hchi]`.

Both sides reduce to the same expression. Establish `e2 : D'.chi (toGS Ω' _ h) = cycZ F' Ω' l h`. Rewrite using `[← D'.hchi]`. Both sides reduce to the same expression. Conclude with `e1.trans ((hφcyc l h).trans e2.symm)`.
-/
theorem UpperTheory.V.LDataCardLeFinrank.gsTransport :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (D' : LData F' Ω' l) (f : F ≃+* F') (σ : Ω ≃+* Ω'), (∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) →
      ∃ (φ : G F' Ω' ≃* G F Ω) (ψ : GS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F'))) ≃* GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))),
        Continuous φ ∧ Continuous φ.symm ∧ Continuous ψ ∧ Continuous ψ.symm ∧ (∀ g x, σ (φ g x) = g (σ x)) ∧
        (∀ g, ψ (toGS Ω' _ g) = toGS Ω _ (φ g)) ∧ ∀ g, D.chi (ψ g) = D'.chi g := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ l _ D D' f σ hσ
  obtain ⟨φ, hφc, hφact, hφcyc, -, -⟩ := galTransport F Ω F' Ω' (f : F →+* F') σ hσ
  have hσ' : ∀ x : F', σ.symm (algebraMap F' Ω' x) = algebraMap F Ω ((f.symm : F' →+* F) x) := by
    intro x
    apply σ.injective
    rw [RingEquiv.apply_symm_apply, hσ]
    simp
  obtain ⟨φ', hφ'c, hφ'act, -, -, -⟩ := galTransport F' Ω' F Ω (f.symm : F' →+* F) σ.symm hσ'
  have hleft : ∀ g, φ' (φ g) = g := by
    intro g
    refine AlgEquiv.ext fun y => ?_
    apply σ.symm.injective
    rw [hφ'act]
    apply σ.injective
    rw [hφact, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hright : ∀ g, φ (φ' g) = g := by
    intro g
    refine AlgEquiv.ext fun x => ?_
    apply σ.injective
    rw [hφact]
    apply σ.symm.injective
    rw [hφ'act, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  let Φ : G F' Ω' ≃* G F Ω :=
    { toFun := φ, invFun := φ', left_inv := hleft, right_inv := hright, map_mul' := φ.map_mul }
  haveI : (NS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F')))).Normal :=
    Subgroup.is_normal_topologicalClosure _
  haveI : (NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))).Normal :=
    Subgroup.is_normal_topologicalClosure _
  have hmap : (NS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F')))).map (Φ : G F' Ω' →* G F Ω) =
      NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact UpperTheory.V.LDataCardLeFinrank.transport_mem_NS (f : F →+* F') σ hσ φ hφc hφact D.hS D'.hS
    · intro h hh
      refine ⟨φ' h, ?_, hright h⟩
      exact UpperTheory.V.LDataCardLeFinrank.transport_mem_NS (f.symm : F' →+* F) σ.symm hσ' φ' hφ'c hφ'act D'.hS D.hS hh
  let Ψ : GS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F'))) ≃* GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) :=
    QuotientGroup.congr _ _ Φ hmap
  have hΨmk : ∀ g : G F' Ω', Ψ (QuotientGroup.mk g) = QuotientGroup.mk (φ g) :=
    fun g => QuotientGroup.congr_mk _ _ Φ hmap g
  have hΨsmk : ∀ g : G F Ω, Ψ.symm (QuotientGroup.mk g) = QuotientGroup.mk (φ' g) := by
    intro g
    apply Ψ.injective
    rw [MulEquiv.apply_symm_apply, hΨmk, hright]
  have hΨc : Continuous Ψ := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have : (Ψ ∘ QuotientGroup.mk) = (QuotientGroup.mk ∘ φ) := funext hΨmk
    rw [this]
    exact QuotientGroup.continuous_mk.comp hφc
  have hΨsc : Continuous Ψ.symm := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have : (Ψ.symm ∘ QuotientGroup.mk) = (QuotientGroup.mk ∘ φ') := funext hΨsmk
    rw [this]
    exact QuotientGroup.continuous_mk.comp hφ'c
  refine ⟨Φ, Ψ, hφc, hφ'c, hΨc, hΨsc, hφact, fun g => hΨmk g, ?_⟩
  intro g
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
  rw [hΨmk]
  show D.chi (toGS Ω _ (φ h)) = D'.chi (toGS Ω' _ h)
  have e1 : D.chi (toGS Ω _ (φ h)) = cycZ F Ω l (φ h) := by
    rw [← D.hchi]
    rfl
  have e2 : D'.chi (toGS Ω' _ h) = cycZ F' Ω' l h := by
    rw [← D'.hchi]
    rfl
  exact e1.trans ((hφcyc l h).trans e2.symm)
