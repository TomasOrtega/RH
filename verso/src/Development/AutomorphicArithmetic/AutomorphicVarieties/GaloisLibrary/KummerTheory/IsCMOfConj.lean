import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

/- English proof (translation)
Use `choose c hc using h`. Set `φ : K →+* ℂ` to `Classical.choice (inferInstance : Nonempty _)`. Establish `hcc : ∀ x, c (c x) = x` using `fun x => φ.injective (by rw [hc, hc, Complex.conj_conj])`. Set `τ : K ≃+* K` to `{ toFun := c invFun := c left_inv := hcc right_inv := hcc map_mul' := fun x y => φ.injective (by simp only [hc, map_mul]) map_add' := fun x y => φ.injective (by simp only [hc, map_add]) }`. Set `σ : K ≃ₐ[ℚ] K` to `AlgEquiv.ofRingEquiv (f := τ) (fun q => by simp)`.

Establish `hσ : ∀ ψ : K →+* ℂ, ComplexEmbedding.IsConj ψ σ` using `fun ψ => by`. Use extensionality with `x`. Conclude with `(hc x ψ).symm`. Establish `hσ' : Nat.card (Subgroup.zpowers σ) = 2`. Rewrite using `[Nat.card_zpowers, ComplexEmbedding.orderOf_isConj_two_of_ne_one (hσ φ)]`.

Conclude with `(ComplexEmbedding.isConj_ne_one_iff (hσ φ)).mpr <| IsTotallyComplex.complexEmbedding_not_isReal φ`. Set `L` to `(FixedPoints.intermediateField (Subgroup.zpowers σ) : IntermediateField ℚ K)`. Establish `: IsTotallyReal L` using `⟨fun w ↦ by`. Take `⟨W, rfl⟩` from `w.comap_surjective (K := K)`. Simplify using `only`.

Rewrite using `[← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Establish `hx : c x.1 = x.1` using `x.2 ⟨σ, Subgroup.mem_zpowers σ⟩`. Use `hc x.1 W.embedding` as an intermediate fact. Rewrite `this` using `[hx]`.

Conclude with `this.symm⟩`. Establish `: Algebra.IsQuadraticExtension L K` using `⟨by`. Establish `: Fintype (Subgroup.zpowers σ)` using `Fintype.ofFinite _`. Rewrite using `[← hσ', Nat.card_eq_fintype_card]`. Conclude with `FixedPoints.finrank_eq_card (Subgroup.zpowers σ) K⟩`.

Conclude with `IsCMField.ofCMExtension L K`.
-/
private theorem isCM_of_conj (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h : ∀ x : K, ∃ y : K, ∀ φ : K →+* ℂ, φ y = starRingEnd ℂ (φ x)) : IsCMField K := by
  classical
  choose c hc using h
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hcc : ∀ x, c (c x) = x := fun x => φ.injective (by rw [hc, hc, Complex.conj_conj])
  let τ : K ≃+* K :=
    { toFun := c
      invFun := c
      left_inv := hcc
      right_inv := hcc
      map_mul' := fun x y => φ.injective (by simp only [hc, map_mul])
      map_add' := fun x y => φ.injective (by simp only [hc, map_add]) }
  let σ : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := τ) (fun q => by simp)
  have hσ : ∀ ψ : K →+* ℂ, ComplexEmbedding.IsConj ψ σ := fun ψ => by
    ext x
    exact (hc x ψ).symm
  have hσ' : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers, ComplexEmbedding.orderOf_isConj_two_of_ne_one (hσ φ)]
    exact (ComplexEmbedding.isConj_ne_one_iff (hσ φ)).mpr <| IsTotallyComplex.complexEmbedding_not_isReal φ
  let L := (FixedPoints.intermediateField (Subgroup.zpowers σ) : IntermediateField ℚ K)
  have : IsTotallyReal L := ⟨fun w ↦ by
    obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
    dsimp only
    rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
      ComplexEmbedding.isReal_iff]
    ext x
    have hx : c x.1 = x.1 := x.2 ⟨σ, Subgroup.mem_zpowers σ⟩
    have := hc x.1 W.embedding
    rw [hx] at this
    exact this.symm⟩
  have : Algebra.IsQuadraticExtension L K := ⟨by
    have : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
    rw [← hσ', Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card (Subgroup.zpowers σ) K⟩
  exact IsCMField.ofCMExtension L K

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ _ l _ n`. Establish `: IsTotallyComplex (Fn F Ω l n)` using `isTotallyComplex_of_algebra F (Fn F Ω l n)`. Use `isCM_of_conj _ ?_` and prove the remaining obligations. Introduce and unpack `⟨x, hx⟩`. Establish `hN0 : l ^ n ≠ 0` using `pow_ne_zero _ (Fact.out : l.Prime).ne_zero`.

Proceed by induction on `hx using IntermediateField.adjoin_induction with`. Consider the case `mem x hx`. Establish `hx1 : x ^ l ^ n = 1`. Use `Polynomial.aeval_eq_zero_of_mem_rootSet hx` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`.

Set `z : Fn F Ω l n` to `⟨x, IntermediateField.subset_adjoin F _ hx⟩`. Establish `hz : z ^ l ^ n = 1` using `Subtype.ext hx1`. Use `⟨z⁻¹, fun φ => ?_⟩` and prove the remaining obligations. Establish `: ‖φ z‖ = 1` using `Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hz, map_one]) hN0`. Rewrite using `[map_inv₀, Complex.inv_eq_conj this]`.

Consider the case `algebraMap a`. Conclude with `⟨algebraMap F _ (IsCMField.complexConj F a), fun φ => IsCMField.complexEmbedding_complexConj F (φ.comp (algebraMap F (Fn F Ω l n))) a⟩`. Consider the case `add x y hx hy ihx ihy`. Take `⟨a, ha⟩` from `ihx`. Take `⟨b, hb⟩` from `ihy`.

Use `⟨a + b, fun φ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ha, hb, ← map_add, ← map_add]`. Both sides reduce to the same expression. Consider the case `inv x hx ihx`. Take `⟨a, ha⟩` from `ihx`.

Use `⟨a⁻¹, fun φ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv₀, ha, ← map_inv₀, ← map_inv₀]`. Both sides reduce to the same expression. Consider the case `mul x y hx hy ihx ihy`. Take `⟨a, ha⟩` from `ihx`.

Take `⟨b, hb⟩` from `ihy`. Use `⟨a * b, fun φ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ha, hb, ← map_mul, ← map_mul]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Kum.fnCM :
    ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), IsCMField (Fn F Ω l n) := by
  intro F Ω _ _ _ _ _ _ l _ n
  have : IsTotallyComplex (Fn F Ω l n) := isTotallyComplex_of_algebra F (Fn F Ω l n)
  refine isCM_of_conj _ ?_
  rintro ⟨x, hx⟩
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    have hx1 : x ^ l ^ n = 1 := by
      have := Polynomial.aeval_eq_zero_of_mem_rootSet hx
      simpa [sub_eq_zero] using this
    let z : Fn F Ω l n := ⟨x, IntermediateField.subset_adjoin F _ hx⟩
    have hz : z ^ l ^ n = 1 := Subtype.ext hx1
    refine ⟨z⁻¹, fun φ => ?_⟩
    have : ‖φ z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hz, map_one]) hN0
    rw [map_inv₀, Complex.inv_eq_conj this]
  | algebraMap a =>
    exact ⟨algebraMap F _ (IsCMField.complexConj F a), fun φ =>
      IsCMField.complexEmbedding_complexConj F (φ.comp (algebraMap F (Fn F Ω l n))) a⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    refine ⟨a + b, fun φ => ?_⟩
    rw [map_add, ha, hb, ← map_add, ← map_add]
    rfl
  | inv x hx ihx =>
    obtain ⟨a, ha⟩ := ihx
    refine ⟨a⁻¹, fun φ => ?_⟩
    rw [map_inv₀, ha, ← map_inv₀, ← map_inv₀]
    rfl
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    refine ⟨a * b, fun φ => ?_⟩
    rw [map_mul, ha, hb, ← map_mul, ← map_mul]
    rfl
