import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

open ReciprocityTheory.Neutral.Bridge.HCFR

/- English proof (translation)
Establish `hcont : Continuous (Complex.ofRealHom.comp (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw))` using `Complex.continuous_ofReal.comp (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous`. Set `i0 : {i : w.Completion →+* ℂ // Continuous i}` to `⟨_, hcont⟩`. Establish `huniq : ∀ i : {i : w.Completion →+* ℂ // Continuous i}, i = i0`. Introduce `i`. Apply `Subtype.ext` to reduce the goal to its premises.

Use extensionality with `x`. Set `E` to `NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw`. Set `g : ℝ →+* ℂ` to `(i : w.Completion →+* ℂ).comp (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom`. Establish `hg : Continuous g` using `i.2.comp E.symm.continuous`. Establish `hg'` using `Complex.ringHom_eq_ofReal_of_continuous hg`.

Establish `hx : (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x) = x` using `(NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm_apply_apply x`. Use `congrArg (fun f : ℝ →+* ℂ => f (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x)) hg'` as an intermediate fact. Simplify using `only [g, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hx] at this`. Simplify `this` using `[i0]`. Unfold `infPow`.

Rewrite using `[Finset.prod_eq_single w]`. Rewrite using `[finprod_eq_single _ i0 (fun j hj => absurd (huniq j) hj)]`. Rewrite using `[ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self, ha]`. Simplify using the standard rewrite rules. Introduce `w' _ hne`.

Simplify using `[ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_ne F w w' hne]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ w) h`.
-/
private theorem UpperTheory.infPow_infIdele_neg_one_of_const_of_isReal {F : Type} [Field F] [NumberField F] (a : (F →+* ℂ) → ℤ)
    (a0 : ℤ) (ha : ∀ φ, a φ = a0) (w : InfinitePlace F) (hw : w.IsReal) :
    infPow a (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F w (-1)) = (-1) ^ a0 := by
  have hcont : Continuous (Complex.ofRealHom.comp
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw)) :=
    Complex.continuous_ofReal.comp
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous
  let i0 : {i : w.Completion →+* ℂ // Continuous i} := ⟨_, hcont⟩
  have huniq : ∀ i : {i : w.Completion →+* ℂ // Continuous i}, i = i0 := by
    intro i
    apply Subtype.ext
    ext x
    let E := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    let g : ℝ →+* ℂ := (i : w.Completion →+* ℂ).comp
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
    have hg : Continuous g := i.2.comp E.symm.continuous
    have hg' := Complex.ringHom_eq_ofReal_of_continuous hg
    have hx : (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
        (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x) = x :=
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm_apply_apply x
    have := congrArg (fun f : ℝ →+* ℂ => f
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x)) hg'
    simp only [g, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hx] at this
    simpa [i0] using this
  unfold infPow
  rw [Finset.prod_eq_single w]
  · rw [finprod_eq_single _ i0 (fun j hj => absurd (huniq j) hj)]
    rw [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self, ha]
    simp
  · intro w' _ hne
    simp [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_ne F w w' hne]
  · intro h
    exact absurd (Finset.mem_univ w) h

/- English proof (translation)
Introduce `hP F Ω _ _ _ _ _ _ l _ ι χ μ hμ hs v v'`. Take `⟨-, art, a, hart, halg, hlad⟩` from `hμ`. Establish `hpar` using `hP F χ a halg`. Establish `key : ∀ w : InfinitePlace F, ∃ c : G F Ω, IsConjEl c ∧ ((χ.locInf w (-1) : ℂˣ) : ℂ) = ι (μ c) * (-1) ^ (a v.embedding)`. Introduce `w`.

Take `⟨j, c, hc, hw⟩` from `GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) w (NumberField.IsTotallyReal.isReal w)`. Use `⟨c, ⟨j, hc⟩, ?_⟩` and prove the remaining obligations. Establish `hart'` using `GlobalTheory.HilbertFromArtin.art_sign_eq hart j c hc`. Rewrite `hart'` using `[hw]`. Establish `h` using `hlad _ c hart'`.

Establish `hl : lPow ι a (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F w (-1)) = 1`. Simplify using `[GlobalTheory.HeckeGal.lPow, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_snd, GlobalTheory.HeckeGal.locPow_one]`. Rewrite `h` using `[hl, mul_one, UpperTheory.infPow_infIdele_neg_one_of_const_of_isReal a (a v.embedding) (fun φ => hpar φ v.embedding) w (NumberField.IsTotallyReal.isReal w)]`. Establish `h2` using `congrArg ι h`. Rewrite `h2` using `[RingEquiv.apply_symm_apply]`.

Rewrite using `[h2]`. Establish `hne : ((-1 : ℂ) ^ (a v.embedding)) ≠ 0` using `zpow_ne_zero _ (by norm_num)`. Rewrite using `[mul_assoc, inv_mul_cancel₀ hne, mul_one]`. Both sides reduce to the same expression. Take `⟨c, hc, hcv⟩` from `key v`.

Take `⟨c', hc', hcv'⟩` from `key v'`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hcv, hcv', hs c c' hc hc']`.
-/
theorem UpperTheory.sign_at_infinity_of_parallel_weight :
    UpperTheory.V.Af.Sol.Parallel → UpperTheory.V.Af.Sol.SignOf := by
  intro hP F Ω _ _ _ _ _ _ l _ ι χ μ hμ hs v v'
  obtain ⟨-, art, a, hart, halg, hlad⟩ := hμ
  have hpar := hP F χ a halg
  have key : ∀ w : InfinitePlace F, ∃ c : G F Ω, IsConjEl c ∧
      ((χ.locInf w (-1) : ℂˣ) : ℂ) = ι (μ c) * (-1) ^ (a v.embedding) := by
    intro w
    obtain ⟨j, c, hc, hw⟩ := GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) w
      (NumberField.IsTotallyReal.isReal w)
    refine ⟨c, ⟨j, hc⟩, ?_⟩
    have hart' := GlobalTheory.HilbertFromArtin.art_sign_eq hart j c hc
    rw [hw] at hart'
    have h := hlad _ c hart'
    have hl : lPow ι a (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F w (-1)) = 1 := by
      simp [GlobalTheory.HeckeGal.lPow, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_snd, GlobalTheory.HeckeGal.locPow_one]
    rw [hl, mul_one, UpperTheory.infPow_infIdele_neg_one_of_const_of_isReal a (a v.embedding) (fun φ => hpar φ v.embedding) w
      (NumberField.IsTotallyReal.isReal w)] at h
    have h2 := congrArg ι h
    rw [RingEquiv.apply_symm_apply] at h2
    rw [h2]
    have hne : ((-1 : ℂ) ^ (a v.embedding)) ≠ 0 := zpow_ne_zero _ (by norm_num)
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
    rfl
  obtain ⟨c, hc, hcv⟩ := key v
  obtain ⟨c', hc', hcv'⟩ := key v'
  apply Units.ext
  rw [hcv, hcv', hs c c' hc hc']
