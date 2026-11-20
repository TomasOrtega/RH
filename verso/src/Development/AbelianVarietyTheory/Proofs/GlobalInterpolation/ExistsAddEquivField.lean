import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.OverResidue

/- English proof (translation)
Establish `: Fact T.Prime` using `⟨hT⟩`. Establish `: Finite M` using `Nat.finite_of_card_ne_zero (hc ▸ hT.ne_zero)`. Establish `: Nontrivial M` using `Finite.one_lt_card_iff_nontrivial.1 (hc ▸ hT.one_lt)`. Take `⟨m₀, hm₀⟩` from `exists_ne (0 : M)`. Set `f : R →ₗ[R] M` to `LinearMap.toSpanSingleton R M m₀`.

Establish `hsur : Function.Surjective f`. Introduce `m`. Take `⟨n, rfl⟩` from `AddSubgroup.mem_zmultiples_iff.1 (mem_zmultiples_of_prime_card hc hm₀ (g' := m))`. Conclude with `⟨(n : R), by simp [f, Int.cast_smul_eq_zsmul]⟩`. Establish `hker : I = LinearMap.ker f`.

Use `hI.eq_of_le ?_ fun a ha => h0 a ha m₀` and prove the remaining obligations. Rewrite using `[Ideal.ne_top_iff_one]`. Simplify `hm₀` using `[f]`. Substitute `hker` using the available equality. Conclude with `⟨(f.quotKerEquivOfSurjective hsur).symm⟩`.
-/
theorem nonempty_equiv_quot {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (hI : I.IsMaximal) (T : ℕ) (hT : T.Prime) (hc : Nat.card M = T)
    (h0 : ∀ a ∈ I, ∀ m : M, a • m = 0) : Nonempty (M ≃ₗ[R] (R ⧸ I)) := by
  have : Fact T.Prime := ⟨hT⟩
  have : Finite M := Nat.finite_of_card_ne_zero (hc ▸ hT.ne_zero)
  have : Nontrivial M := Finite.one_lt_card_iff_nontrivial.1 (hc ▸ hT.one_lt)
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  let f : R →ₗ[R] M := LinearMap.toSpanSingleton R M m₀
  have hsur : Function.Surjective f := by
    intro m
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (mem_zmultiples_of_prime_card hc hm₀ (g' := m))
    exact ⟨(n : R), by simp [f, Int.cast_smul_eq_zsmul]⟩
  have hker : I = LinearMap.ker f := by
    refine hI.eq_of_le ?_ fun a ha => h0 a ha m₀
    rw [Ideal.ne_top_iff_one]
    simpa [f] using hm₀
  subst hker
  exact ⟨(f.quotKerEquivOfSurjective hsur).symm⟩

/- English proof (translation)
Use `⟨e.toAddEquiv.trans (RingHom.quotientKerEquivOfSurjective hρ).toAddEquiv, fun a m => ?_⟩` and prove the remaining obligations. Use `show RingHom.quotientKerEquivOfSurjective hρ (e (a • m)) = ρ a * RingHom.quotientKerEquivOfSurjective hρ (e m)`. Rewrite using `[map_smul, Algebra.smul_def, map_mul]`. Both sides reduce to the same expression.
-/
theorem exists_addEquiv_field {R M k : Type} [CommRing R] [AddCommGroup M] [Module R M] [Field k]
    (ρ : R →+* k) (hρ : Function.Surjective ρ) (e : M ≃ₗ[R] (R ⧸ RingHom.ker ρ)) :
    ∃ ε : M ≃+ k, ∀ (a : R) (m : M), ε (a • m) = ρ a * ε m := by
  refine ⟨e.toAddEquiv.trans (RingHom.quotientKerEquivOfSurjective hρ).toAddEquiv, fun a m => ?_⟩
  show RingHom.quotientKerEquivOfSurjective hρ (e (a • m)) =
      ρ a * RingHom.quotientKerEquivOfSurjective hρ (e m)
  rw [map_smul, Algebra.smul_def, map_mul]
  rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)}

/- English proof (translation)
Set `q : intV E v →+* v.adicCompletionIntegers F` to `(p.comp (intV E v).subtype).codRestrict (v.adicCompletionIntegers F) fun x => hp x x.2`. Establish `hq : Function.Surjective q`. Introduce `a`. Take `⟨x, hx, hxa⟩` from `hsur a a.2`. Conclude with `⟨⟨x, hx⟩, Subtype.ext hxa⟩`.

Establish `hk : ∀ a : intV E v, a ∈ RingHom.ker ((IsLocalRing.residue _).comp q) ↔ Valued.v (p a) < 1`. Introduce `a`. Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]`. Conclude with `Valuation.mem_maximalIdeal_iff (v := Valued.v) (a := q a)`. Use `⟨(IsLocalRing.residue _).comp q, IsLocalRing.residue_surjective.comp hq, ?_, hk, ?_⟩` and prove the remaining obligations.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[primeOf, Ideal.span_le]`. Conclude with `fun a ha => (hk a).2 ha`. Conclude with `fun a ha => Ideal.subset_span ((hk a).1 ha)`. Introduce `a a' h`.

Establish `: q a = a'` using `Subtype.ext h.symm`. Rewrite using `[RingHom.comp_apply, this]`.
-/
theorem exists_red (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (hp : ∀ x ∈ intV E v, p x ∈ v.adicCompletionIntegers F)
    (hsur : ∀ a ∈ v.adicCompletionIntegers F, ∃ x ∈ intV E v, p x = a) :
    ∃ ρ : intV E v →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F),
      Function.Surjective ρ ∧ primeOf p = RingHom.ker ρ ∧
      (∀ a : intV E v, a ∈ RingHom.ker ρ ↔ Valued.v (p a) < 1) ∧
      ∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = p a →
        ρ a = IsLocalRing.residue _ a' := by
  let q : intV E v →+* v.adicCompletionIntegers F :=
    (p.comp (intV E v).subtype).codRestrict (v.adicCompletionIntegers F) fun x => hp x x.2
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨x, hx, hxa⟩ := hsur a a.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxa⟩
  have hk : ∀ a : intV E v, a ∈ RingHom.ker ((IsLocalRing.residue _).comp q) ↔
      Valued.v (p a) < 1 := by
    intro a
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    exact Valuation.mem_maximalIdeal_iff (v := Valued.v) (a := q a)
  refine ⟨(IsLocalRing.residue _).comp q, IsLocalRing.residue_surjective.comp hq, ?_, hk, ?_⟩
  · apply le_antisymm
    · rw [primeOf, Ideal.span_le]
      exact fun a ha => (hk a).2 ha
    · exact fun a ha => Ideal.subset_span ((hk a).1 ha)
  · intro a a' h
    have : q a = a' := Subtype.ext h.symm
    rw [RingHom.comp_apply, this]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ v s hs M _ _ T hT hc h0`. Take `⟨ρ, hρ, hρk, hρm, hρa⟩` from `exists_red (prP s) (fun x hx => ((hs.2.2 x).1 hx).1) (GlobalTheory.OverCompare.sur_prP hs)`. Take `⟨ρ', hρ', hρk', -, -⟩` from `exists_red (prPbar s) (fun x hx => ((hs.2.2 x).1 hx).2) (GlobalTheory.OverCompare.sur_prPbar hs)`. Rewrite using `[hρk, hρk']`. Take `⟨e⟩` from `nonempty_equiv_quot (M := M) (RingHom.ker ρ) (RingHom.ker_isMaximal_of_surjective ρ hρ) T hT hc fun a ha m => h0 a m ((hρm a).1 ha)`.

Take `⟨ε, hε⟩` from `exists_addEquiv_field ρ hρ e`. Use `⟨⟨ε, fun a a' h m => ?_⟩, ⟨e⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hε, hρa a a' h]`. Both sides reduce to the same expression. Rewrite using `[Nat.card_congr (RingHom.quotientKerEquivOfSurjective hρ').toEquiv, ← hc]`.

Conclude with `(Nat.card_congr ε.toEquiv).symm`.
-/
theorem residue_of_prime_card : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), IsSplitting σ v s → ∀ (M : Type) [AddCommGroup M] [Module (intV E v) M] (T : ℕ), T.Prime → Nat.card M = T → (∀ (a : intV E v) (m : M), Valued.v (prP s a) < 1 → a • m = 0) → (∃ ε : M ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F), ∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = prP s a → ∀ m, ε (a • m) = a' • ε m) ∧ Nonempty (M ≃ₗ[intV E v] (intV E v ⧸ primeOf (prP s))) ∧ Nat.card (intV E v ⧸ primeOf (prPbar s)) = T := by
  intro F E _ _ _ _ _ σ v s hs M _ _ T hT hc h0
  obtain ⟨ρ, hρ, hρk, hρm, hρa⟩ := exists_red (prP s) (fun x hx => ((hs.2.2 x).1 hx).1)
    (GlobalTheory.OverCompare.sur_prP hs)
  obtain ⟨ρ', hρ', hρk', -, -⟩ := exists_red (prPbar s) (fun x hx => ((hs.2.2 x).1 hx).2)
    (GlobalTheory.OverCompare.sur_prPbar hs)
  rw [hρk, hρk']
  obtain ⟨e⟩ := nonempty_equiv_quot (M := M) (RingHom.ker ρ) (RingHom.ker_isMaximal_of_surjective ρ hρ)
    T hT hc fun a ha m => h0 a m ((hρm a).1 ha)
  obtain ⟨ε, hε⟩ := exists_addEquiv_field ρ hρ e
  refine ⟨⟨ε, fun a a' h m => ?_⟩, ⟨e⟩, ?_⟩
  · rw [hε, hρa a a' h]
    rfl
  · rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective hρ').toEquiv, ← hc]
    exact (Nat.card_congr ε.toEquiv).symm

end GlobalTheory.OverResidue
