import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory

open NumberField IsDedekindDomain in

/- English proof (translation)
Establish `hP : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Take `⟨Q, hQm, hQ⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) (Ideal.span {(p : ℤ)}) (by`. Introduce `x hx`. Rewrite `hx` using `[RingHom.mem_ker, (algebraMap ℤ (𝓞 L)).injective_int.eq_iff' (map_zero _)]`. Simplify using `[hx])`.

Establish `hmem : ((p : ℕ) : 𝓞 L) ∈ Q`. Establish `: (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 L))` using `hQ ▸ Ideal.mem_span_singleton_self _`. Simplify using `using this`. Use `⟨⟨Q, hQm.isPrime, ?_⟩, hmem⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Establish `: (p : ℤ) ∈ (⊥ : Ideal (𝓞 L)).comap (algebraMap ℤ (𝓞 L))` using `by simpa using hmem`. Rewrite `this` using `[Ideal.mem_comap, Ideal.mem_bot]`. Conclude with `hp.ne_zero (by simpa using this)`.
-/
theorem _root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem (L : Type*) [Field L] [NumberField L] {p : ℕ}
    (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := by
  have hP : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨Q, hQm, hQ⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) (Ideal.span {(p : ℤ)})
      (by
        intro x hx
        rw [RingHom.mem_ker, (algebraMap ℤ (𝓞 L)).injective_int.eq_iff' (map_zero _)] at hx
        simp [hx])
  have hmem : ((p : ℕ) : 𝓞 L) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 L)) := hQ ▸ Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQm.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : (p : ℤ) ∈ (⊥ : Ideal (𝓞 L)).comap (algebraMap ℤ (𝓞 L)) := by simpa using hmem
  rw [Ideal.mem_comap, Ideal.mem_bot] at this
  exact hp.ne_zero (by simpa using this)

open NumberField IsDedekindDomain in
/- English proof (translation)
Use `set n := Nat.card (ZMod p)ˣ`. Establish `hn : NeZero n` using `⟨Nat.card_pos.ne'⟩`. Establish `hc : Nat.card (ZMod p)ˣ = Nat.card (rootsOfUnity n ℂ)`. Rewrite using `[Complex.card_rootsOfUnity]`. Conclude with `⟨(rootsOfUnity n ℂ).subtype.comp (mulEquivOfCyclicCardEq hc).toMonoidHom, Subtype.val_injective.comp (mulEquivOfCyclicCardEq hc).injective⟩`.
-/
private theorem exists_injective_units_zmod_hom_units_complex (p : ℕ) [Fact p.Prime] :
    ∃ f : (ZMod p)ˣ →* ℂˣ, Function.Injective f := by
  set n := Nat.card (ZMod p)ˣ
  have hn : NeZero n := ⟨Nat.card_pos.ne'⟩
  have hc : Nat.card (ZMod p)ˣ = Nat.card (rootsOfUnity n ℂ) := by
    rw [Complex.card_rootsOfUnity]
  exact ⟨(rootsOfUnity n ℂ).subtype.comp (mulEquivOfCyclicCardEq hc).toMonoidHom,
    Subtype.val_injective.comp (mulEquivOfCyclicCardEq hc).injective⟩

open NumberField IsDedekindDomain in
open Classical in

/- English proof (translation)
Introduce `R H`. Use `⟨⟨⟨fun k => (_root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem H.K (H.g_prime k)).choose, fun k => (_root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem H.K (H.g_prime k)).choose_spec⟩⟩, ?_⟩` and prove the remaining obligations. Establish `: ∀ k : Fin 2, ∃ f : (ZMod (H.g k))ˣ →* ℂˣ, Function.Injective f` using `fun k => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩ exists_injective_units_zmod_hom_units_complex (H.g k)`. Conclude with `⟨⟨fun k => (this k).choose, fun k => (this k).choose_spec⟩⟩`.
-/
theorem _root_.GlobalTheory.nonempty_piBar_and_omg :
    ∀ (R : _root_.Formalism.BasicNotions.Ranks) (H : _root_.Formalism.BasicNotions.Host R), Nonempty (_root_.Formalism.L2.Host.PiBar H) ∧ Nonempty (_root_.Formalism.L2.Host.Omg H) := by
  intro R H
  refine ⟨⟨⟨fun k => (_root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem H.K (H.g_prime k)).choose,
    fun k => (_root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem H.K (H.g_prime k)).choose_spec⟩⟩, ?_⟩
  have : ∀ k : Fin 2, ∃ f : (ZMod (H.g k))ˣ →* ℂˣ, Function.Injective f := fun k =>
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    exists_injective_units_zmod_hom_units_complex (H.g k)
  exact ⟨⟨fun k => (this k).choose, fun k => (this k).choose_spec⟩⟩

end GlobalTheory
