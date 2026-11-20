import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.Host

namespace GlobalTheory.MuConj

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_conjP, mem_conjP, cO_cO]`.
-/
theorem conjP_involutive (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext x
  rw [mem_conjP, mem_conjP, cO_cO]

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

noncomputable def starAlg (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) : E ≃ₐ[F] E :=
  { (starRingAut : E ≃+* E) with commutes' := hF }

/- English proof (translation)
Establish `hc : starAlg hF ≠ 1`. Introduce `h`. Apply `hP` to reduce the goal to its premises. Use extensionality with `x`. Establish `e : cO E x = x`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `congrArg (fun σ : E ≃ₐ[F] E => σ (x : E)) h`. Rewrite using `[mem_conjP, e]`. Rewrite using `[GlobalTheory.Mem.Chr.under_eq_iff_conjPl (starAlg hF) hr hc P Q, GlobalTheory.Mem.Chr.conjPl_iff_mem]`. Use `or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations.

Use extensionality with `y`. Rewrite using `[mem_conjP]`. Use `(h (cO E y) y ?_).symm` and prove the remaining obligations. Conclude with `(star_star (y : E)).symm`. Substitute `h` using the available equality.

Introduce `x y hxy`. Establish `e : y = cO E x` using `RingOfIntegers.ext hxy`. Rewrite using `[e, mem_conjP, cO_cO]`.
-/
theorem mem_above_iff (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (P : HeightOneSpectrum (𝓞 E)) (hP : conjPrime₂ P ≠ P) (Q : HeightOneSpectrum (𝓞 E)) :
    Q.under (𝓞 F) = P.under (𝓞 F) ↔ (Q = P ∨ Q = conjPrime₂ P) := by
  have hc : starAlg hF ≠ 1 := by
    intro h
    apply hP
    ext x
    have e : cO E x = x := by
      apply RingOfIntegers.ext
      exact congrArg (fun σ : E ≃ₐ[F] E => σ (x : E)) h
    rw [mem_conjP, e]
  rw [GlobalTheory.Mem.Chr.under_eq_iff_conjPl (starAlg hF) hr hc P Q, GlobalTheory.Mem.Chr.conjPl_iff_mem]
  refine or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · ext y
    rw [mem_conjP]
    refine (h (cO E y) y ?_).symm
    exact (star_star (y : E)).symm
  · subst h
    intro x y hxy
    have e : y = cO E x := RingOfIntegers.ext hxy
    rw [e, mem_conjP, cO_cO]

omit [StarRing E] in

/- English proof (translation)
Establish `: Q.asIdeal.LiesOver (Q.under (𝓞 F)).asIdeal` using `⟨rfl⟩`. Establish `he : Ideal.ramificationIdx' (Q.under (𝓞 F)).asIdeal Q.asIdeal = 1`. Assume the negation of the conclusion as `hne`. Conclude with `h ((Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).1 hne)`. Rewrite using `[← HeightOneSpectrum.valuation_liesOver E (Q.under (𝓞 F)) Q, he, pow_one]`.
-/
theorem valuation_up (Q : HeightOneSpectrum (𝓞 E))
    (h : ¬ (Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q.asIdeal ^ 2) (x : F) :
    Q.valuation E (algebraMap F E x) = (Q.under (𝓞 F)).valuation F x := by
  have : Q.asIdeal.LiesOver (Q.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have he : Ideal.ramificationIdx' (Q.under (𝓞 F)).asIdeal Q.asIdeal = 1 := by
    by_contra hne
    exact h ((Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).1 hne)
  rw [← HeightOneSpectrum.valuation_liesOver E (Q.under (𝓞 F)) Q, he, pow_one]

end General

/- English proof (translation)
Establish `hfin : {P : HeightOneSpectrum A | a ∈ P.asIdeal}.Finite`. Establish `h1` using `Ideal.finite_factors (I := Ideal.span {a}) (by`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `ha)`. Use `h1.subset fun Q hQ => ?_` and prove the remaining obligations.

Conclude with `Ideal.dvd_span_singleton.2 hQ`. Unfold `divs`. Rewrite using `[dif_pos hfin, Set.Finite.mem_toFinset]`. Conclude with `h`.
-/
theorem mem_divs_of_mem {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} (ha : a ≠ 0) {P : HeightOneSpectrum A}
    (h : a ∈ P.asIdeal) : P ∈ divs a := by
  have hfin : {P : HeightOneSpectrum A | a ∈ P.asIdeal}.Finite := by
    have h1 := Ideal.finite_factors (I := Ideal.span {a}) (by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha)
    refine h1.subset fun Q hQ => ?_
    exact Ideal.dvd_span_singleton.2 hQ
  unfold divs
  rw [dif_pos hfin, Set.Finite.mem_toFinset]
  exact h

/- English proof (translation)
Introduce `hm`. Establish `hg : ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0` using `Nat.cast_ne_zero.2 (h.g_prime i).ne_zero`. Rewrite `hm`, `hg` using `[← h.piG_norm i]`. Establish `hsub : ∀ Q, Q ∈ Pr.vG i → Q ∈ Pr.vGs`. Introduce `Q hQ`.

Unfold `Primes.vGs`. Rewrite using `[Finset.mem_union]`. Use `fin_cases i`. Conclude with `Or.inl hQ`. Conclude with `Or.inr hQ`.

Establish `hne : X.conjO (Pr.piG i) ≠ 0` using `right_ne_zero_of_mul hg`. Break down `P.isPrime.mem_or_mem hm with h3 | h3` into its components or cases. Use `h2 (hsub _ (mem_divs_of_mem hne ?_)) show cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal` and prove the remaining obligations. Rewrite using `[cO_cO]`. Conclude with `h3`.

Conclude with `h1 (hsub _ (mem_divs_of_mem hne h3))`.
-/
theorem g_notMem {X : Fields} {Pr : Primes X} (h : Pr.Ok) (P : HeightOneSpectrum (𝓞 X.E)) (h1 : P ∉ Pr.vGs)
    (h2 : conjPrime₂ P ∉ Pr.vGs) (i : Fin 2) : ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro hm
  have hg : ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 (h.g_prime i).ne_zero
  rw [← h.piG_norm i] at hm hg
  have hsub : ∀ Q, Q ∈ Pr.vG i → Q ∈ Pr.vGs := by
    intro Q hQ
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases i
    · exact Or.inl hQ
    · exact Or.inr hQ
  have hne : X.conjO (Pr.piG i) ≠ 0 := right_ne_zero_of_mul hg
  rcases P.isPrime.mem_or_mem hm with h3 | h3
  · refine h2 (hsub _ (mem_divs_of_mem hne ?_))
    show cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal
    rw [cO_cO]
    exact h3
  · exact h1 (hsub _ (mem_divs_of_mem hne h3))

end GlobalTheory.MuConj
