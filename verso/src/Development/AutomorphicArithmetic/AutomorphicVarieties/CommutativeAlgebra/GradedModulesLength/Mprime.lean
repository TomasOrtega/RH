import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.CardOfIsFiniteLength

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

/- English proof (translation)
Take `⟨c, hc, hcf⟩` from `hf`. Establish `hD' : ∀ f g, D (f * g) = x f • D g + x g • D f` using `hD`. Establish `key : ∀ g ∈ RingHom.ker x ^ 2, D g = 0`. Introduce `g hg`. Rewrite `hg` using `[sq]`.

Use `Submodule.mul_induction_on hg ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`. Establish `ha' : x a = 0` using `ha`. Establish `hb' : x b = 0` using `hb`. Rewrite using `[hD', ha', hb']`.

Simplify using the standard rewrite rules. Introduce `a b ha hb`. Rewrite using `[map_add, ha, hb, add_zero]`. Use `key _ hcf` as an intermediate fact. Rewrite `this` using `[map_smul, smul_eq_mul]`.

Conclude with `(mul_eq_zero.1 this).resolve_left hc`.
-/
private theorem der_satSq {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] (x : A →ₐ[O] O)
    (D : A →ₗ[O] O) (hD : D ∈ PtDer x O) (f : A) (hf : f ∈ satSq x) : D f = 0 := by
  obtain ⟨c, hc, hcf⟩ := hf
  have hD' : ∀ f g, D (f * g) = x f • D g + x g • D f := hD
  have key : ∀ g ∈ RingHom.ker x ^ 2, D g = 0 := by
    intro g hg
    rw [sq] at hg
    refine Submodule.mul_induction_on hg ?_ ?_
    · intro a ha b hb
      have ha' : x a = 0 := ha
      have hb' : x b = 0 := hb
      rw [hD', ha', hb']; simp
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero]
  have := key _ hcf
  rw [map_smul, smul_eq_mul] at this
  exact (mul_eq_zero.1 this).resolve_left hc

/- English proof (translation)
Take `⟨hfN, n, hn, hcn⟩` from `Formalism.MainNotions.V.Pf.V2.card_of_isFiniteLength (Module.length_ne_top_iff.1 hN)`. Establish `hfM : Finite M` using `Finite.of_injective ψ hψ`. Establish `hM : IsFiniteLength O M` using `isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩`. Take `⟨_, m, hm, hcm⟩` from `Formalism.MainNotions.V.Pf.V2.card_of_isFiniteLength hM`. Establish `hle` using `Nat.card_le_card_of_injective ψ hψ`.

Rewrite `hle` using `[hcm, hcn]`. Establish `h1 : 1 < Nat.card (ResidueField O)` using `Finite.one_lt_card`. Rewrite using `[hm, hn]`. Conclude with `(Nat.pow_le_pow_iff_right h1).1 hle` after adjusting the coercions.
-/
private theorem len_le_of_inj {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
    {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (hN : Module.length O N ≠ ⊤) (ψ : M → N) (hψ : Function.Injective ψ) :
    Module.length O M ≤ Module.length O N := by
  obtain ⟨hfN, n, hn, hcn⟩ := Formalism.MainNotions.V.Pf.V2.card_of_isFiniteLength (Module.length_ne_top_iff.1 hN)
  have hfM : Finite M := Finite.of_injective ψ hψ
  have hM : IsFiniteLength O M := isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
  obtain ⟨_, m, hm, hcm⟩ := Formalism.MainNotions.V.Pf.V2.card_of_isFiniteLength hM
  have hle := Nat.card_le_card_of_injective ψ hψ
  rw [hcm, hcn] at hle
  have h1 : 1 < Nat.card (ResidueField O) := Finite.one_lt_card
  rw [hm, hn]
  exact_mod_cast (Nat.pow_le_pow_iff_right h1).1 hle

/- English proof (translation)
Introduce `O _ _ _ _ A X _ _ _ _ 𝒜 _ x j hx ι F hF c hc M _ _ D hD hDF hlift`. Distinguish the cases in `htop : cotLen x 𝒜 j F = ⊤`. Rewrite using `[htop]`. Conclude with `le_top`. Establish `hsat : ∀ μ, satSq x ≤ LinearMap.ker (D μ)`.

Introduce `μ f hf`. Take `⟨D', hD', -, h⟩` from `hlift μ`. Rewrite using `[LinearMap.mem_ker, h, der_satSq x D' hD' f hf, map_zero]`. Establish `hspan : ∀ μ, (cotSpan x F).comap (cotLat x 𝒜 j).subtype ≤ LinearMap.ker (((satSq x).liftQ (D μ) (hsat μ)) ∘ₗ (cotLat x 𝒜 j).subtype)`. Introduce `μ`.

Rewrite using `[LinearMap.ker_comp]`. Use `Submodule.comap_mono ?_` and prove the remaining obligations. Rewrite using `[cotSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hDF μ i`.

Set `ψ : M → ((cotLat x 𝒜 j ⧸ (cotSpan x F).comap (cotLat x 𝒜 j).subtype) →ₗ[O] O ⧸ Ideal.span {c})` to `fun μ => Submodule.liftQ _ _ (hspan μ)`. Establish `hψ : Function.Injective ψ`. Introduce `μ ν h`. Apply `hD` to reduce the goal to its premises. Establish `hj : ∀ f ∈ 𝒜 j, D μ f = D ν f` using `fun f hf => LinearMap.congr_fun h (Submodule.Quotient.mk ⟨(satSq x).mkQ f, f, ⟨hf, hx f hf⟩, rfl⟩)`.

Establish `hi : ∀ μ i, i ≠ j → ∀ f ∈ 𝒜 i, D μ f = 0`. Introduce `μ i hi f hf`. Take `⟨D', -, hw, h⟩` from `hlift μ`. Rewrite using `[h, hw i hi f hf, map_zero]`. Use `LinearMap.ext fun f => ?_` and prove the remaining obligations.

Proceed by induction on `f using DirectSum.Decomposition.inductionOn 𝒜 with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `@homogeneous i m`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Conclude with `hj _ m.2`. Rewrite using `[hi μ i hij _ m.2, hi ν i hij _ m.2]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`. Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨k, hk⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hc hp`.

Establish `hQ : Module.length O ((O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {c})) ≤ 1`. Rewrite using `[Ideal.span_singleton_eq_span_singleton.2 hk]`. Conclude with `Formalism.MainNotions.V.Pf.V2.length_hom_residue_le p hp.maximalIdeal_eq hp.ne_zero k`. Establish `hle` using `Formalism.MainNotions.V.Pf.V2.length_hom_le hQ (Module.length_ne_top_iff.1 htop)`. Conclude with `(len_le_of_inj (ne_top_of_le_ne_top htop hle) ψ hψ).trans hle`.
-/
theorem UpperTheory.V.Alg.M.mprime_holds :
    LemmaM' := by
  intro O _ _ _ _ A X _ _ _ _ 𝒜 _ x j hx ι F hF c hc M _ _ D hD hDF hlift
  by_cases htop : cotLen x 𝒜 j F = ⊤
  · rw [htop]; exact le_top
  have hsat : ∀ μ, satSq x ≤ LinearMap.ker (D μ) := by
    intro μ f hf
    obtain ⟨D', hD', -, h⟩ := hlift μ
    rw [LinearMap.mem_ker, h, der_satSq x D' hD' f hf, map_zero]
  have hspan : ∀ μ, (cotSpan x F).comap (cotLat x 𝒜 j).subtype ≤
      LinearMap.ker (((satSq x).liftQ (D μ) (hsat μ)) ∘ₗ (cotLat x 𝒜 j).subtype) := by
    intro μ
    rw [LinearMap.ker_comp]
    refine Submodule.comap_mono ?_
    rw [cotSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hDF μ i
  let ψ : M → ((cotLat x 𝒜 j ⧸ (cotSpan x F).comap (cotLat x 𝒜 j).subtype) →ₗ[O] O ⧸ Ideal.span {c}) :=
    fun μ => Submodule.liftQ _ _ (hspan μ)
  have hψ : Function.Injective ψ := by
    intro μ ν h
    apply hD
    have hj : ∀ f ∈ 𝒜 j, D μ f = D ν f := fun f hf =>
      LinearMap.congr_fun h (Submodule.Quotient.mk ⟨(satSq x).mkQ f, f, ⟨hf, hx f hf⟩, rfl⟩)
    have hi : ∀ μ i, i ≠ j → ∀ f ∈ 𝒜 i, D μ f = 0 := by
      intro μ i hi f hf
      obtain ⟨D', -, hw, h⟩ := hlift μ
      rw [h, hw i hi f hf, map_zero]
    refine LinearMap.ext fun f => ?_
    induction f using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [map_zero, map_zero]
    | @homogeneous i m =>
      by_cases hij : i = j
      · subst hij; exact hj _ m.2
      · rw [hi μ i hij _ m.2, hi ν i hij _ m.2]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc hp
  have hQ : Module.length O ((O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {c})) ≤ 1 := by
    rw [Ideal.span_singleton_eq_span_singleton.2 hk]
    exact Formalism.MainNotions.V.Pf.V2.length_hom_residue_le p hp.maximalIdeal_eq hp.ne_zero k
  have hle := Formalism.MainNotions.V.Pf.V2.length_hom_le hQ (Module.length_ne_top_iff.1 htop)
  exact (len_le_of_inj (ne_top_of_le_ne_top htop hle) ψ hψ).trans hle
