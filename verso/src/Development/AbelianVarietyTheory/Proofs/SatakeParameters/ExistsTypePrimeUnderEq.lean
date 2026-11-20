import Mathlib
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubOneMemMapOfEq
open NumberField IsDedekindDomain Formalism.L2.Col

noncomputable section
namespace GlobalTheory.GprimUnder

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show star (star (a : X.E)) = (a : X.E)`. Conclude with `star_star _`.
-/
theorem conjO_conjO (X : Fields) (a : 𝓞 X.E) : X.conjO (X.conjO a) = a := by
  apply RingOfIntegers.ext
  show star (star (a : X.E)) = (a : X.E)
  exact star_star _

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show star ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E) = ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E)`. Establish `: ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E) = algebraMap X.F X.E (x : X.F)` using `rfl`. Rewrite using `[this]`. Conclude with `hX.star_F _`.
-/
theorem conjO_algebraMap (X : Fields) (hX : X.Ok) (x : 𝓞 X.F) :
    X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) x) = algebraMap (𝓞 X.F) (𝓞 X.E) x := by
  apply RingOfIntegers.ext
  show star ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E) = ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E)
  have : ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E) = algebraMap X.F X.E (x : X.F) := rfl
  rw [this]
  exact hX.star_F _

/- English proof (translation)
Establish `hfin : {P : HeightOneSpectrum A | a ∈ P.asIdeal}.Finite`. Establish `h0 : Ideal.span {a} ≠ ⊥` using `by simpa using ha`. Use `(Ideal.finite_factors h0).subset fun v hv => ?_` and prove the remaining obligations. Conclude with `Ideal.dvd_span_singleton.2 hv`. Unfold `divs`.

Rewrite using `[dif_pos hfin, Set.Finite.mem_toFinset]`. Both sides reduce to the same expression.
-/
theorem mem_divs_iff {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} (ha : a ≠ 0) (P : HeightOneSpectrum A) :
    P ∈ divs a ↔ a ∈ P.asIdeal := by
  have hfin : {P : HeightOneSpectrum A | a ∈ P.asIdeal}.Finite := by
    have h0 : Ideal.span {a} ≠ ⊥ := by simpa using ha
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  unfold divs
  rw [dif_pos hfin, Set.Finite.mem_toFinset]
  rfl

def conjPrime (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := P.asIdeal.comap X.conjO
  isPrime := Ideal.comap_isPrime X.conjO P.asIdeal
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro h
    have h1 : X.conjO x ∈ P.asIdeal.comap X.conjO := by
      rw [Ideal.mem_comap, conjO_conjO]
      exact hx
    rw [h, Ideal.mem_bot] at h1
    apply hx0
    rw [← conjO_conjO X x, h1, map_zero]

/- English proof (translation)
The claim follows from `Ideal.mem_comap`.
-/
theorem mem_conjPrime (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) (a : 𝓞 X.E) :
    a ∈ (conjPrime X P).asIdeal ↔ X.conjO a ∈ P.asIdeal := Ideal.mem_comap

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Use `show algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ (conjPrime X P).asIdeal ↔ algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.asIdeal`. Rewrite using `[mem_conjPrime, conjO_algebraMap X hX]`.
-/
theorem under_conjPrime (X : Fields) (hX : X.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime X P).under (𝓞 X.F) = P.under (𝓞 X.F) := by
  apply HeightOneSpectrum.ext
  ext x
  show algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ (conjPrime X P).asIdeal ↔ algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.asIdeal
  rw [mem_conjPrime, conjO_algebraMap X hX]

/- English proof (translation)
Introduce `X Pr hX hPr i P hP`. Establish `hg0 : ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0` using `Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero`. Establish `hc0 : X.conjO (Pr.piG i) ≠ 0`. Introduce `h`. Establish `h1` using `hPr.piG_norm i`.

Rewrite `h1` using `[h, mul_zero]`. Conclude with `hg0 h1.symm`. Establish `hvG : ∀ v, v ∈ Pr.vG i ↔ X.conjO (Pr.piG i) ∈ v.asIdeal` using `fun v => mem_divs_iff hc0 v`. Rewrite `hP` using `[← hPr.piG_norm i]`. Break down `P.isPrime.mem_or_mem hP with h | h` into its components or cases.

Use `⟨conjPrime X P, (hvG _).2 ?_, under_conjPrime X hX P⟩` and prove the remaining obligations. Rewrite using `[mem_conjPrime, conjO_conjO]`. Conclude with `h`. Conclude with `⟨P, (hvG P).2 h, rfl⟩`.
-/
theorem exists_vG_under : ∀ (X : Fields) (Pr : Primes X), X.Ok → Pr.Ok → ∀ (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)),
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ∃ P' ∈ Pr.vG i, P'.under (𝓞 X.F) = P.under (𝓞 X.F) := by
  intro X Pr hX hPr i P hP
  have hg0 : ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero
  have hc0 : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have h1 := hPr.piG_norm i
    rw [h, mul_zero] at h1
    exact hg0 h1.symm
  have hvG : ∀ v, v ∈ Pr.vG i ↔ X.conjO (Pr.piG i) ∈ v.asIdeal := fun v => mem_divs_iff hc0 v
  rw [← hPr.piG_norm i] at hP
  rcases P.isPrime.mem_or_mem hP with h | h
  · refine ⟨conjPrime X P, (hvG _).2 ?_, under_conjPrime X hX P⟩
    rw [mem_conjPrime, conjO_conjO]
    exact h
  · exact ⟨P, (hvG P).2 h, rfl⟩

end GlobalTheory.GprimUnder
