import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
open ReciprocityTheory.Gal Pointwise NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ p hp A hpA`. Use `set f : 𝓞 F →+* Ω := (algebraMap F Ω).comp (algebraMap (𝓞 F) F) with hf`. Establish `fA : ∀ r : 𝓞 F, f r ∈ A` using `fun r => mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe r).map (algebraMap F Ω).toIntAlgHom)`. Set `I : Ideal (𝓞 F)` to `(IsLocalRing.maximalIdeal A).comap (f.codRestrict A fA)`. Establish `memI : ∀ r, r ∈ I ↔ A.valuation (algebraMap F Ω (r : F)) < 1` using `fun r => by`.

Simplify using `only [I, Ideal.mem_comap]`. Conclude with `A.valuation_lt_one_iff _`. Establish `hIp : I.IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hpI : (p : 𝓞 F) ∈ I`. Rewrite using `[memI]`.

Simplify using `using hpA`. Establish `hIne : I ≠ ⊥` using `fun h => by`. Establish `h'` using `hpI`. Rewrite `h'` using `[h, Ideal.mem_bot]`. Conclude with `hp.out.ne_zero (by exact_mod_cast h')`.

Set `v : HeightOneSpectrum (𝓞 F)` to `⟨I, hIp, hIne⟩`. Take `⟨σ, hσA, hσ⟩` from `exists_frob_over (F := F) (A := A) (v := v) (fun x => (memI x).symm)`. Use `⟨σ, hσA, Nat.card (𝓞 F ⧸ v.asIdeal), fun h1 => ?_, hσ⟩` and prove the remaining obligations. Establish `hss : Subsingleton (𝓞 F ⧸ v.asIdeal)` using `by haveI : Finite (𝓞 F ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [h1]; exact one_ne_zero)`. Conclude with `Finite.card_le_one_iff_subsingleton.mp h1.le`.

Establish `: (1 : 𝓞 F) ∈ v.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Subsingleton.elim _ _`. Conclude with `hIp.ne_top ((Ideal.eq_top_iff_one _).2 this)`.
-/
theorem exists_frob_at_place_over_prime : ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω),
    A.valuation (p : Ω) < 1 → ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∃ q : ℕ, q ≠ 1 ∧
      ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1 := by
  intro F Ω _ _ _ _ _ p hp A hpA
  set f : 𝓞 F →+* Ω := (algebraMap F Ω).comp (algebraMap (𝓞 F) F) with hf
  have fA : ∀ r : 𝓞 F, f r ∈ A := fun r =>
    mem_of_isIntegral_int A ((RingOfIntegers.isIntegral_coe r).map (algebraMap F Ω).toIntAlgHom)
  let I : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal A).comap (f.codRestrict A fA)
  have memI : ∀ r, r ∈ I ↔ A.valuation (algebraMap F Ω (r : F)) < 1 := fun r => by
    simp only [I, Ideal.mem_comap]; exact A.valuation_lt_one_iff _
  have hIp : I.IsPrime := Ideal.comap_isPrime _ _
  have hpI : (p : 𝓞 F) ∈ I := by
    rw [memI]; simpa using hpA
  have hIne : I ≠ ⊥ := fun h => by
    have h' := hpI
    rw [h, Ideal.mem_bot] at h'
    exact hp.out.ne_zero (by exact_mod_cast h')
  let v : HeightOneSpectrum (𝓞 F) := ⟨I, hIp, hIne⟩
  obtain ⟨σ, hσA, hσ⟩ := exists_frob_over (F := F) (A := A) (v := v) (fun x => (memI x).symm)
  refine ⟨σ, hσA, Nat.card (𝓞 F ⧸ v.asIdeal), fun h1 => ?_, hσ⟩
  have hss : Subsingleton (𝓞 F ⧸ v.asIdeal) := by
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [h1]; exact one_ne_zero)
    exact Finite.card_le_one_iff_subsingleton.mp h1.le
  have : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]; exact Subsingleton.elim _ _
  exact hIp.ne_top ((Ideal.eq_top_iff_one _).2 this)

end GlobalTheory
