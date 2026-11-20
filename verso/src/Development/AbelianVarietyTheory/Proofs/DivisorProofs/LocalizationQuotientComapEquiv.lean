import Mathlib
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `S B _ _ φ hφ p q _`. Set `ψ` to `Localization.localRingHom (q.comap φ) q φ rfl`. Set `f` to `(Ideal.Quotient.mk (p.map (algebraMap B (Localization.AtPrime q)))).comp ψ`. Establish `hψ : Function.Surjective ψ`. Introduce `z`.

Take `⟨⟨b, t⟩, rfl⟩` from `IsLocalization.mk'_surjective q.primeCompl z`. Take `⟨a, rfl⟩` from `hφ b`. Take `⟨t₀, ht₀⟩` from `hφ (t : B)`. Establish `ht₀' : t₀ ∈ (q.comap φ).primeCompl` using `by show t₀ ∉ q.comap φ`. Rewrite using `[Ideal.mem_comap, ht₀]`.

Conclude with `t.2`. Use `⟨IsLocalization.mk' (Localization.AtPrime (q.comap φ)) a ⟨t₀, ht₀'⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Localization.localRingHom_mk']`. Use `congr 1`. Conclude with `Subtype.ext ht₀`.

Establish `hf : Function.Surjective f` using `Ideal.Quotient.mk_surjective.comp hψ`. Establish `hker : RingHom.ker f = (p.comap φ).map (algebraMap S (Localization.AtPrime (q.comap φ)))`. Use extensionality with `x`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (q.comap φ).primeCompl x`. Simplify using `only [RingHom.mem_ker, f, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ψ, Localization.localRingHom_mk']`.

Rewrite using `[IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, hta⟩`. Take `⟨t₀, rfl⟩` from `hφ t`. Use `⟨t₀, ?_, ?_⟩` and prove the remaining obligations.

Use `show t₀ ∉ q.comap φ`. Simplify `ht` using `[Ideal.mem_comap]`. Simplify `hta` using `[Ideal.mem_comap, map_mul]`. Introduce and unpack `⟨t₀, ht, hta⟩`. Use `⟨φ t₀, ?_, ?_⟩` and prove the remaining obligations.

Use `show φ t₀ ∉ q`. Simplify `ht` using `[Ideal.mem_comap]`. Simplify `hta` using `[Ideal.mem_comap, map_mul]`. Conclude with `⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hf)⟩`.
-/
theorem localization_quotient_comap_equiv :
    ∀ (S B : Type) [CommRing S] [CommRing B] (φ : S →+* B), Function.Surjective φ →
      ∀ (p q : Ideal B) [q.IsPrime],
        Nonempty ((Localization.AtPrime (q.comap φ) ⧸
            (p.comap φ).map (algebraMap S (Localization.AtPrime (q.comap φ)))) ≃+*
          (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) := by
  intro S B _ _ φ hφ p q _
  let ψ := Localization.localRingHom (q.comap φ) q φ rfl
  let f := (Ideal.Quotient.mk (p.map (algebraMap B (Localization.AtPrime q)))).comp ψ
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨a, rfl⟩ := hφ b
    obtain ⟨t₀, ht₀⟩ := hφ (t : B)
    have ht₀' : t₀ ∈ (q.comap φ).primeCompl := by
      show t₀ ∉ q.comap φ
      rw [Ideal.mem_comap, ht₀]
      exact t.2
    refine ⟨IsLocalization.mk' (Localization.AtPrime (q.comap φ)) a ⟨t₀, ht₀'⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht₀
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hψ
  have hker : RingHom.ker f = (p.comap φ).map (algebraMap S (Localization.AtPrime (q.comap φ))) := by
    ext x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (q.comap φ).primeCompl x
    simp only [RingHom.mem_ker, f, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ψ,
      Localization.localRingHom_mk']
    rw [IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]
    constructor
    · rintro ⟨t, ht, hta⟩
      obtain ⟨t₀, rfl⟩ := hφ t
      refine ⟨t₀, ?_, ?_⟩
      · show t₀ ∉ q.comap φ
        simpa [Ideal.mem_comap] using ht
      · simpa [Ideal.mem_comap, map_mul] using hta
    · rintro ⟨t₀, ht, hta⟩
      refine ⟨φ t₀, ?_, ?_⟩
      · show φ t₀ ∉ q
        simpa [Ideal.mem_comap] using ht
      · simpa [Ideal.mem_comap, map_mul] using hta
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hf)⟩

end GlobalTheory
