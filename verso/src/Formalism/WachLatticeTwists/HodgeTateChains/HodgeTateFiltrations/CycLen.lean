import Formalism.WachLatticeTwists.HodgeTateChains.XiAdicFiltrationData
import Formalism.WachLatticeTwists.TorsionLengthCounts.SubmoduleLengthBoundStatement

open Module IsDiscreteValuationRing

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

/- English proof (translation)
Set `φ : O →ₗ[O] Cy` to `LinearMap.toSpanSingleton O Cy c0`. Take `⟨b, hb⟩` from `(IsPrincipalIdealRing.principal (P.comap φ : Ideal O)).principal`. Establish `hbmem : b • c0 ∈ P`. Establish `: b ∈ (P.comap φ : Ideal O)` using `by rw [hb]; exact Submodule.mem_span_singleton_self b`. Conclude with `this`.

Set `ψ : O →ₗ[O] P` to `LinearMap.toSpanSingleton O P ⟨b • c0, hbmem⟩`. Establish `hψ : Function.Surjective ψ`. Introduce and unpack `⟨p, hp⟩`. Take `⟨r, rfl⟩` from `hc0 p`. Establish `hr : r ∈ (P.comap φ : Ideal O)` using `hp`.

Rewrite `hr` using `[hb, Submodule.mem_span_singleton]`. Take `⟨r', rfl⟩` from `hr`. Use `⟨r', Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `[ψ, LinearMap.toSpanSingleton_apply, smul_smul]`. Establish `hker : (Ideal.span {a} : Submodule O O) ≤ LinearMap.ker ψ`.

Rewrite using `[Ideal.span, Submodule.span_le, Set.singleton_subset_iff]`. Use `show ψ a = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify `hP _ hbmem` using `[ψ, LinearMap.toSpanSingleton_apply]`. Conclude with `Module.length_le_of_surjective (Submodule.liftQ _ ψ hker) (fun p => by`.

Take `⟨r, hr⟩` from `hψ p`. Conclude with `⟨Submodule.Quotient.mk r, by rw [Submodule.liftQ_apply]; exact hr⟩)`.
-/
lemma cyc_len (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Cy : Type)
    [AddCommGroup Cy] [Module O Cy] (c0 : Cy) (hc0 : ∀ y : Cy, ∃ a : O, y = a • c0)
    (P : Submodule O Cy) (a : O) (hP : ∀ x ∈ P, a • x = 0) :
    Module.length O P ≤ Module.length O (O ⧸ Ideal.span {a}) := by
  let φ : O →ₗ[O] Cy := LinearMap.toSpanSingleton O Cy c0
  obtain ⟨b, hb⟩ := (IsPrincipalIdealRing.principal (P.comap φ : Ideal O)).principal
  have hbmem : b • c0 ∈ P := by
    have : b ∈ (P.comap φ : Ideal O) := by rw [hb]; exact Submodule.mem_span_singleton_self b
    exact this
  let ψ : O →ₗ[O] P := LinearMap.toSpanSingleton O P ⟨b • c0, hbmem⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨p, hp⟩
    obtain ⟨r, rfl⟩ := hc0 p
    have hr : r ∈ (P.comap φ : Ideal O) := hp
    rw [hb, Submodule.mem_span_singleton] at hr
    obtain ⟨r', rfl⟩ := hr
    refine ⟨r', Subtype.ext ?_⟩
    simp [ψ, LinearMap.toSpanSingleton_apply, smul_smul]
  have hker : (Ideal.span {a} : Submodule O O) ≤ LinearMap.ker ψ := by
    rw [Ideal.span, Submodule.span_le, Set.singleton_subset_iff]
    show ψ a = 0
    apply Subtype.ext
    simpa [ψ, LinearMap.toSpanSingleton_apply] using hP _ hbmem
  exact Module.length_le_of_surjective (Submodule.liftQ _ ψ hker)
    (fun p => by
      obtain ⟨r, hr⟩ := hψ p
      exact ⟨Submodule.Quotient.mk r, by rw [Submodule.liftQ_apply]; exact hr⟩)

/- English proof (translation)
Introduce `O _ _ _ n _ Q Cy _ _ _ _ ι π hι hex ⟨c0, hc0⟩ N ℓ c hN`. Set `N1 : Submodule O (n → Formalism.NG.KO O)` to `N.comap ι`. Establish `hN1 : ∀ x ∈ N1, ((ℓ : O) ^ c) • x = 0`. Introduce `x hx`. Apply `hι` to reduce the goal to its premises.

Rewrite using `[map_smul, map_zero]`. Conclude with `hN _ hx`. Establish `hl1` using `Formalism.RepresentationBoundsCohomology.submoduleLengthBound_statement O n N1 ℓ c hN1`. Set `f : N1 →ₗ[O] N` to `(ι.comp N1.subtype).codRestrict N (fun x => x.2)`. Set `πN : N →ₗ[O] Cy` to `π.comp N.subtype`.

Set `g : N →ₗ[O] LinearMap.range πN` to `πN.rangeRestrict`. Establish `hf : Function.Injective f`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hι` to reduce the goal to its premises.

Conclude with `congrArg Subtype.val hxy`. Establish `hg : Function.Surjective g` using `LinearMap.surjective_rangeRestrict _`. Establish `hfg : Function.Exact f g`. Introduce `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Establish `hx' : π x.1 = 0` using `congrArg Subtype.val hx`. Take `⟨t, ht⟩` from `(hex _).1 hx'`. Conclude with `⟨⟨t, by show ι t ∈ N; rw [ht]; exact x.2⟩, Subtype.ext ht⟩`. Introduce and unpack `⟨t, rfl⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(hex _).2 ⟨t.1, rfl⟩`. Establish `hadd` using `Module.length_eq_add_of_exact f g hf hg hfg`. Establish `hl2 : Module.length O (LinearMap.range πN) ≤ Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ c})`. Apply `cyc_len O Cy c0 hc0` to reduce the goal to its premises.

Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[← map_smul]`. Establish `: ((ℓ : O) ^ c) • x = 0` using `Subtype.ext (hN _ x.2)`. Rewrite using `[this, map_zero]`. Establish `hl3 : Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ c}) = (c : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})`.

Rewrite using `[Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, addVal_pow, nsmul_eq_mul]`. Rewrite using `[hadd, add_mul, one_mul]`. Conclude with `add_le_add hl1 (hl3 ▸ hl2)`.
-/
theorem tbLen : StatTBLen := by
  intro O _ _ _ n _ Q Cy _ _ _ _ ι π hι hex ⟨c0, hc0⟩ N ℓ c hN
  let N1 : Submodule O (n → Formalism.NG.KO O) := N.comap ι
  have hN1 : ∀ x ∈ N1, ((ℓ : O) ^ c) • x = 0 := by
    intro x hx
    apply hι
    rw [map_smul, map_zero]
    exact hN _ hx
  have hl1 := Formalism.RepresentationBoundsCohomology.submoduleLengthBound_statement O n N1 ℓ c hN1
  let f : N1 →ₗ[O] N := (ι.comp N1.subtype).codRestrict N (fun x => x.2)
  let πN : N →ₗ[O] Cy := π.comp N.subtype
  let g : N →ₗ[O] LinearMap.range πN := πN.rangeRestrict
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply hι
    exact congrArg Subtype.val hxy
  have hg : Function.Surjective g := LinearMap.surjective_rangeRestrict _
  have hfg : Function.Exact f g := by
    intro x
    constructor
    · intro hx
      have hx' : π x.1 = 0 := congrArg Subtype.val hx
      obtain ⟨t, ht⟩ := (hex _).1 hx'
      exact ⟨⟨t, by show ι t ∈ N; rw [ht]; exact x.2⟩, Subtype.ext ht⟩
    · rintro ⟨t, rfl⟩
      apply Subtype.ext
      exact (hex _).2 ⟨t.1, rfl⟩
  have hadd := Module.length_eq_add_of_exact f g hf hg hfg
  have hl2 : Module.length O (LinearMap.range πN) ≤ Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ c}) := by
    apply cyc_len O Cy c0 hc0
    rintro _ ⟨x, rfl⟩
    rw [← map_smul]
    have : ((ℓ : O) ^ c) • x = 0 := Subtype.ext (hN _ x.2)
    rw [this, map_zero]
  have hl3 : Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ c})
      = (c : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := by
    rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, addVal_pow, nsmul_eq_mul]
  rw [hadd, add_mul, one_mul]
  exact add_le_add hl1 (hl3 ▸ hl2)

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
