import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnMixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelNontrivialOfCharacterSupport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqMult
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSatakeParameterOfIsSubquotientOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSegmentRepLengthOneUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.Gal.LocD

/- English proof (translation)
Introduce `E _ _ _ _ n V _ _ π hi ω hω h`. Establish `hs : IsSmooth π` using `h.isSmooth (isSmooth_parInd _ _)`. Establish `hsupp` using `GlobalTheory.CompanionTheory.SphSupp.hasSupport_prinSeries n ω hω ⟨V, π, hs, hi⟩ h`. Take `⟨hf, -, hm⟩` from `UpperTheory.V.AlgebraTools.jqMult UpperTheory.Lit.Mix.geometricLemma GlobalTheory.bernsteinZelevinskyFiniteness_holds E n V π ω hs hω h`. Use `⟨hs, UpperTheory.jacquet_borel_nontrivial_of_character_support UpperTheory.Lit.Mix.geometricLemma UpperTheory.Lit.Mix.polynomialRing E n V π _ hsupp fun y hy => ?_, hf, fun μ hμ => ?_⟩` and prove the remaining obligations.

Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hy`. Both sides reduce to the same expression. Establish `h1` using `lt_of_lt_of_le (Nat.pos_of_ne_zero fun e => hμ (Submodule.finrank_eq_zero.1 e)) (hm μ)`. Take `⟨w⟩` from `(Nat.card_pos_iff.1 h1).1`. Conclude with `⟨w.1, w.2⟩`.
-/
theorem jFacts : JFacts := by
  intro E _ _ _ _ n V _ _ π hi ω hω h
  have hs : IsSmooth π := h.isSmooth (isSmooth_parInd _ _)
  have hsupp := GlobalTheory.CompanionTheory.SphSupp.hasSupport_prinSeries n ω hω ⟨V, π, hs, hi⟩ h
  obtain ⟨hf, -, hm⟩ := UpperTheory.V.AlgebraTools.jqMult UpperTheory.Lit.Mix.geometricLemma GlobalTheory.bernsteinZelevinskyFiniteness_holds
    E n V π ω hs hω h
  refine ⟨hs, UpperTheory.jacquet_borel_nontrivial_of_character_support UpperTheory.Lit.Mix.geometricLemma UpperTheory.Lit.Mix.polynomialRing E n V π _ hsupp fun y hy => ?_,
    hf, fun μ hμ => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · have h1 := lt_of_lt_of_le (Nat.pos_of_ne_zero fun e => hμ (Submodule.finrank_eq_zero.1 e)) (hm μ)
    obtain ⟨w⟩ := (Nat.card_pos_iff.1 h1).1
    exact ⟨w.1, w.2⟩

/- English proof (translation)
Introduce `k _ _ _ _ n V _ _ π μ hμ`. Use `⟨fun hs => ⟨hs.isIrreducible, ?_⟩, fun h => GlobalTheory.CompanionTheory.SphSupp.hasSupport_prinSeries n μ hμ ⟨V, π, h.2.isSmooth (isSmooth_parInd _ _), h.1⟩ h.2⟩` and prove the remaining obligations. Establish `hd : ∑ i, (IrrGL.ofChar (μ i) (hμ i)).1 = n` using `by simp [IrrGL.ofChar]`. Use `IsSubquotient.trans ?_ (GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries _ hd μ hμ fun _ => rfl)` and prove the remaining obligations. Take `⟨Z, Ψ, -, hΨ, -⟩` from `UpperTheory.Lit.Mix.polynomialRing k`.

Establish `h1` using `SupportRing.pos_pc_sub hΨ hs hs.isSmooth hs.isIrreducible`. Take `⟨hp, ep⟩` from `SupportRing.prodIrr_cls hΨ _ hd`. Use `SupportRing.isSubquotient_of_clsGL_ne hp hs.isSmooth hs.isIrreducible ?_` and prove the remaining obligations. Establish `h2` using `h1 (IrrGL.of π hs.isSmooth hs.isIrreducible)`. Rewrite `h2` using `[SupportRing.pc_map, ← ep]`.

Establish `e1 : ∀ (A : GrothGL k) (y : IrrGL k), Ψ.symm (Ψ A - SupportRing.bas Ψ y) y = A y - 1`. Introduce `A y`. Rewrite using `[SupportRing.bas, ← map_sub, Ψ.symm_apply_apply, Finsupp.sub_apply, Finsupp.single_eq_same]`. Rewrite `h2` using `[e1]`. Introduce `h3`.

Rewrite `h2` using `[h3]`. Conclude with `absurd h2 (by norm_num)`.
-/
theorem ofSupport : OfSupport := by
  intro k _ _ _ _ n V _ _ π μ hμ
  refine ⟨fun hs => ⟨hs.isIrreducible, ?_⟩, fun h =>
    GlobalTheory.CompanionTheory.SphSupp.hasSupport_prinSeries n μ hμ ⟨V, π, h.2.isSmooth (isSmooth_parInd _ _), h.1⟩ h.2⟩
  have hd : ∑ i, (IrrGL.ofChar (μ i) (hμ i)).1 = n := by simp [IrrGL.ofChar]
  refine IsSubquotient.trans ?_ (GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries _ hd μ hμ fun _ => rfl)
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := UpperTheory.Lit.Mix.polynomialRing k
  have h1 := SupportRing.pos_pc_sub hΨ hs hs.isSmooth hs.isIrreducible
  obtain ⟨hp, ep⟩ := SupportRing.prodIrr_cls hΨ _ hd
  refine SupportRing.isSubquotient_of_clsGL_ne hp hs.isSmooth hs.isIrreducible ?_
  have h2 := h1 (IrrGL.of π hs.isSmooth hs.isIrreducible)
  rw [SupportRing.pc_map, ← ep] at h2
  have e1 : ∀ (A : GrothGL k) (y : IrrGL k), Ψ.symm (Ψ A - SupportRing.bas Ψ y) y = A y - 1 := by
    intro A y
    rw [SupportRing.bas, ← map_sub, Ψ.symm_apply_apply, Finsupp.sub_apply, Finsupp.single_eq_same]
  rw [e1] at h2
  intro h3
  rw [h3] at h2
  exact absurd h2 (by norm_num)

/- English proof (translation)
Introduce `E _ _ _ _ n σ q hσ V _ _ π hi ω hω hinv h A hA`. Take `⟨hs, hn, hf, hm⟩` from `jFacts E n V π hi ω hω h`. Take `⟨μ, l, c, hl, hμ, hlt, hlA⟩` from `hE _ _ (jacB π) (fun t i => Units.map (σ : E →* E) (t i)) (jacA hA) (hJ E n σ hσ.isom V π A hA) fun μ hμ t => by`. Take `⟨w, rfl⟩` from `hm μ hμ`. Simplify using `only [torusChar_apply]`.

Conclude with `Finset.prod_congr rfl fun i _ => hinv _ _`. Take `⟨χ, hχ, hχl⟩` from `hB E n σ hσ.isom V π μ hμ l hlt`. Use `⟨c, hC E n σ q hσ V π hs hi A hA χ hχ (l ∘ₗ Submodule.mkQ _) c (fun e => hl ?_) hχl fun v => hlA (Submodule.Quotient.mk v)⟩` and prove the remaining obligations. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`.

Conclude with `LinearMap.congr_fun e v`.
-/
theorem scalar_of (hE : Eig) (hB : ToBorel) (hJ : JacSemi) (hC : Core) : Scalar := by
  intro E _ _ _ _ n σ q hσ V _ _ π hi ω hω hinv h A hA
  obtain ⟨hs, hn, hf, hm⟩ := jFacts E n V π hi ω hω h
  obtain ⟨μ, l, c, hl, hμ, hlt, hlA⟩ := hE _ _ (jacB π) (fun t i => Units.map (σ : E →* E) (t i)) (jacA hA)
    (hJ E n σ hσ.isom V π A hA) fun μ hμ t => by
      obtain ⟨w, rfl⟩ := hm μ hμ
      simp only [torusChar_apply]
      exact Finset.prod_congr rfl fun i _ => hinv _ _
  obtain ⟨χ, hχ, hχl⟩ := hB E n σ hσ.isom V π μ hμ l hlt
  refine ⟨c, hC E n σ q hσ V π hs hi A hA χ hχ (l ∘ₗ Submodule.mkQ _) c (fun e => hl ?_) hχl fun v => hlA (Submodule.Quotient.mk v)⟩
  refine LinearMap.ext fun y => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact LinearMap.congr_fun e v

/- English proof (translation)
Introduce `E _ _ _ _ n σ q hσ V _ _ π hi ω hω hinv h A hA h0`. Take `⟨hs, hn, hf, hm⟩` from `jFacts E n V π hi ω hω h`. Take `⟨c, hc, hψ⟩` from `hS E n σ q hσ V π hi ω hω hinv h A hA`. Establish `hw : whitChar (1 : AddChar E Circle) n = 1`. Use extensionality with `u`.

Simplify using `[whitChar]`. Establish `hj : jacA hA = c • LinearMap.id`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Use `hψ 1 continuous_const (fun _ => rfl) v` as an intermediate fact.

Rewrite `this` using `[hw]`. Conclude with `(Submodule.Quotient.eq _).2 this`. Use `⟨hn, hf, hm, c, hc h0, hj, fun ψ h1 h2 l a hl hu ha => ?_, fun U hU hst t k₀ => ?_⟩` and prove the remaining obligations. Establish `hk : twKer π (unipB E (Fin n)) (whitChar ψ n) ≤ LinearMap.ker l`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨u, v, rfl⟩`. Simplify using `[hu]`. Take `⟨v, hv⟩ : ∃ v, l v ≠ 0` from `by by_contra! e`. Conclude with `hl (LinearMap.ext e)`. Use `hk (hψ ψ h1 h2 v)` as an intermediate fact.

Rewrite `this` using `[LinearMap.mem_ker, map_sub, map_smul, ha, smul_eq_mul, sub_eq_zero]`. Conclude with `(mul_right_cancel₀ hv this).symm`. Use `haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU`. Set `φ : U →ₗ[ℂ] U` to `(jacB π t).restrict (hst t)`. Establish `hφ : Function.Injective φ` using `fun a b e => by`.

Establish `e' : jacB π t a = jacB π t b` using `congrArg Subtype.val e`. Use `congrArg (jacB π t⁻¹) e'` as an intermediate fact. Rewrite `this` using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]`. Conclude with `Subtype.ext this`. Take `⟨k, hk, hne⟩` from `hT U φ hφ k₀`.

Establish `hmem : ∀ y ∈ U, (jacB π (t ^ k) ∘ₗ jacA hA) y ∈ U` using `fun y hy => by`. Rewrite using `[hj]`. Conclude with `hst _ _ (U.smul_mem c hy)`. Use `⟨k, hk, hmem, ?_⟩` and prove the remaining obligations. Establish `: (jacB π (t ^ k) ∘ₗ jacA hA).restrict hmem = c • φ ^ k`.

Use extensionality with `y`. Simplify using `only [φ, Module.End.pow_restrict k (hst t), LinearMap.restrict_apply, LinearMap.smul_apply, Submodule.coe_smul, LinearMap.comp_apply, hj, LinearMap.id_apply, map_smul, map_pow]`. Rewrite using `[this, map_smul, smul_eq_mul]`. Conclude with `mul_ne_zero (hc h0) hne`.
-/
theorem locDesc_of (hS : Scalar) (hT : TracePow) : LocDesc := by
  intro E _ _ _ _ n σ q hσ V _ _ π hi ω hω hinv h A hA h0
  obtain ⟨hs, hn, hf, hm⟩ := jFacts E n V π hi ω hω h
  obtain ⟨c, hc, hψ⟩ := hS E n σ q hσ V π hi ω hω hinv h A hA
  have hw : whitChar (1 : AddChar E Circle) n = 1 := by
    ext u
    simp [whitChar]
  have hj : jacA hA = c • LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have := hψ 1 continuous_const (fun _ => rfl) v
    rw [hw] at this
    exact (Submodule.Quotient.eq _).2 this
  refine ⟨hn, hf, hm, c, hc h0, hj, fun ψ h1 h2 l a hl hu ha => ?_, fun U hU hst t k₀ => ?_⟩
  · have hk : twKer π (unipB E (Fin n)) (whitChar ψ n) ≤ LinearMap.ker l := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      simp [hu]
    obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
      by_contra! e
      exact hl (LinearMap.ext e)
    have := hk (hψ ψ h1 h2 v)
    rw [LinearMap.mem_ker, map_sub, map_smul, ha, smul_eq_mul, sub_eq_zero] at this
    exact (mul_right_cancel₀ hv this).symm
  · haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU
    let φ : U →ₗ[ℂ] U := (jacB π t).restrict (hst t)
    have hφ : Function.Injective φ := fun a b e => by
      have e' : jacB π t a = jacB π t b := congrArg Subtype.val e
      have := congrArg (jacB π t⁻¹) e'
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at this
      exact Subtype.ext this
    obtain ⟨k, hk, hne⟩ := hT U φ hφ k₀
    have hmem : ∀ y ∈ U, (jacB π (t ^ k) ∘ₗ jacA hA) y ∈ U := fun y hy => by
      rw [hj]
      exact hst _ _ (U.smul_mem c hy)
    refine ⟨k, hk, hmem, ?_⟩
    have : (jacB π (t ^ k) ∘ₗ jacA hA).restrict hmem = c • φ ^ k := by
      ext y
      simp only [φ, Module.End.pow_restrict k (hst t), LinearMap.restrict_apply, LinearMap.smul_apply,
        Submodule.coe_smul, LinearMap.comp_apply, hj, LinearMap.id_apply, map_smul, map_pow]
    rw [this, map_smul, smul_eq_mul]
    exact mul_ne_zero (hc h0) hne

end UpperTheory.Gal.LocD
