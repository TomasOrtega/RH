import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory
namespace LevelPlaces
open Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.SplitOffPlaces

/- English proof (translation)
Use `HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top fun a ha => ?_)` and prove the remaining obligations. Take `⟨c', h1, h2⟩` from `h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha`. Establish `hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F)` using `(D.sp.cm.fixed _).2 ⟨_, rfl⟩`. Establish `e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c'` using `RingOfIntegers.ext (h2.trans hfix).symm`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal`.

Rewrite using `[e]` and apply the resulting hypothesis.
-/
theorem under_eq_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

/- English proof (translation)
Take `⟨c', h1, h2⟩` from `h _ hn`. Establish `e : (n : 𝓞 D.host.E) = c'` using `RingOfIntegers.ext (by`. Rewrite using `[h2]`. Express the relevant statement in the definitionally equal form `(n : D.host.E) = star (n : D.host.E)`. Rewrite using `[star_natCast])`.

Rewrite using `[e]` and apply the resulting hypothesis.
-/
theorem natCast_mem_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P')
    {n : ℕ} (hn : (n : 𝓞 D.host.E) ∈ P.asIdeal) : (n : 𝓞 D.host.E) ∈ P'.asIdeal := by
  obtain ⟨c', h1, h2⟩ := h _ hn
  have e : (n : 𝓞 D.host.E) = c' := RingOfIntegers.ext (by
    rw [h2]
    change (n : D.host.E) = star (n : D.host.E)
    rw [star_natCast])
  rwa [e]

/- English proof (translation)
Introduce `c hc` and use `⟨cO D.host.E c, by change cO D.host.E (cO D.host.E c) ∈ P.asIdeal rwa [cO_cO], rfl⟩`.
-/
theorem isConjPl_conjSpec {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.IndefR.Lev.IsConjPl P (conjSpec P) :=
  fun c hc => ⟨cO D.host.E c, by
    change cO D.host.E (cO D.host.E c) ∈ P.asIdeal
    rwa [cO_cO], rfl⟩

/- English proof (translation)
Introduce `h'`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)`. Apply `hI` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `e : (1 : A) = a * (q : A) + b * (p : A)`.

Conclude with `congrArg (Int.cast : ℤ → A) hab.symm` after adjusting the coercions. Rewrite using `[e]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h')`.
-/
theorem not_mem_of_prime {A : Type} [CommRing A] {I : Ideal A} (hI : I ≠ ⊤) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : q ≠ p) (h : (q : A) ∈ I) : (p : A) ∉ I := by
  intro h'
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)
  apply hI
  rw [Ideal.eq_top_iff_one]
  have e : (1 : A) = a * (q : A) + b * (p : A) := by
    exact_mod_cast congrArg (Int.cast : ℤ → A) hab.symm
  rw [e]
  exact add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h')

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Establish `h1 : Pb.pb k ≠ P.under (𝓞 D.host.K)` using `fun e => hc (Or.inl e.symm)`. Establish `h2 : Pb.pb k ≠ (conjSpec P).under (𝓞 D.host.K)` using `fun e => hc (Or.inr e.symm)`. Take `⟨x, hx, hx1, hx2⟩` from `exists_mem_not_mem h1 h2`. Take `⟨x', n, hx', hn⟩` from `exists_norm D x`.

Establish `hnP : (n : 𝓞 D.host.E) ∉ P.asIdeal`. Introduce `h`. Establish `e : (n : 𝓞 D.host.E) = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x * cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x)`. Rewrite using `[← hx', ← map_mul, hn, map_intCast]`. Rewrite `h` using `[e]`.

Break down `P.isPrime.mem_or_mem h with h | h` into its components or cases. Conclude with `hx1 h`. Conclude with `hx2 h`. Establish `hnb : (n : 𝓞 D.host.K) ∈ (Pb.pb k).asIdeal` using `hn ▸ Ideal.mul_mem_right _ _ hx`. Establish `hp : Prime (D.host.g k : ℤ)` using `Nat.prime_iff_prime_int.1 (D.host.g_prime k)`.

Distinguish the cases in `hd : (D.host.g k : ℤ) ∣ n`. Take `⟨m, rfl⟩` from `hd`. Apply `hnP` to reduce the goal to its premises. Use `push_cast`. Conclude with `Ideal.mul_mem_right _ _ hk`.

Take `⟨a, b, hab⟩` from `(hp.irreducible.coprime_iff_not_dvd).2 hd`. Apply `(Pb.pb k).isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `e : (1 : 𝓞 D.host.K) = a * ((D.host.g k : ℕ) : 𝓞 D.host.K) + b * n`. Conclude with `congrArg (Int.cast : ℤ → 𝓞 D.host.K) hab.symm` after adjusting the coercions.

Rewrite using `[e]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ (Pb.pb_over k)) (Ideal.mul_mem_left _ _ hnb)`.
-/
theorem div_or_div_conj {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : Pb.Div k P ∨ Pb.Div k (conjSpec P) := by
  by_contra hc
  have h1 : Pb.pb k ≠ P.under (𝓞 D.host.K) := fun e => hc (Or.inl e.symm)
  have h2 : Pb.pb k ≠ (conjSpec P).under (𝓞 D.host.K) := fun e => hc (Or.inr e.symm)
  obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem h1 h2
  obtain ⟨x', n, hx', hn⟩ := exists_norm D x
  have hnP : (n : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro h
    have e : (n : 𝓞 D.host.E) = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x * cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) := by
      rw [← hx', ← map_mul, hn, map_intCast]
    rw [e] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact hx1 h
    · exact hx2 h
  have hnb : (n : 𝓞 D.host.K) ∈ (Pb.pb k).asIdeal := hn ▸ Ideal.mul_mem_right _ _ hx
  have hp : Prime (D.host.g k : ℤ) := Nat.prime_iff_prime_int.1 (D.host.g_prime k)
  by_cases hd : (D.host.g k : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hd
    apply hnP
    push_cast
    exact Ideal.mul_mem_right _ _ hk
  · obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).2 hd
    apply (Pb.pb k).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 D.host.K) = a * ((D.host.g k : ℕ) : 𝓞 D.host.K) + b * n := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) hab.symm
    rw [e]
    exact add_mem (Ideal.mul_mem_left _ _ (Pb.pb_over k)) (Ideal.mul_mem_left _ _ hnb)

/- English proof (translation)
Establish `h1` using `Pb.pb_over k`. Rewrite `h1` using `[← (show P.under (𝓞 D.host.K) = Pb.pb k from h)]`. Establish `h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal` using `h1`. Rewrite `h2` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem mem_of_div {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (P : HeightOneSpectrum (𝓞 D.host.E))
    (h : Pb.Div k P) : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  have h1 := Pb.pb_over k
  rw [← (show P.under (𝓞 D.host.K) = Pb.pb k from h)] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal := h1
  rwa [map_natCast] at h2

/- English proof (translation)
Take `⟨⟨q, hq, hcard, -, hne⟩, -⟩` from `hQ P hP`. Use `not_mem_of_prime P.isPrime.ne_top (D.host.g_prime k) hq (hne k) ?_` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hcard, ← nsmul_one]`. Conclude with `card_nsmul_eq_zero' (G := 𝓞 D.host.E ⧸ P.asIdeal)`.
-/
theorem not_mem_of_twist {D : D7} {Q : Finset (Pl D.host.E)} (hQ : Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q)
    {P : Pl D.host.E} (hP : P ∈ Q) (k : Fin 2) : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hQ P hP
  refine not_mem_of_prime P.isPrime.ne_top (D.host.g_prime k) hq (hne k) ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hcard, ← nsmul_one]
  exact card_nsmul_eq_zero' (G := 𝓞 D.host.E ⧸ P.asIdeal)

end LevelPlaces

open LevelPlaces SplitOffPlaces in

/- English proof (translation)
Introduce `D T0 L μ0 hL t`. Establish `hPg : ∀ PP ∈ L.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal` using `fun PP h => by`. Take `⟨k, hk⟩` from `(hL.Pg PP).1 h`. Conclude with `⟨k, mem_of_div _ k PP hk⟩`. Establish `hQ : ∀ PP ∈ L.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal` using `fun PP h k => not_mem_of_twist (hL.Q_pl t) h k`.

Use `⟨Finset.disjoint_left.2 fun PP h h' => ?_, fun PP h => ?_, fun PP h j => ?_, fun P hP => ⟨?_, fun j => ?_⟩⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hPg PP h`. Conclude with `hQ PP h' k hk`. Take `⟨k, hk⟩` from `hPg PP h`. Assume the negation of the conclusion as `hc`.

Break down `(hL.Q_ram t PP).1 hc with h' | ⟨PP', h', hc'⟩` into its components or cases. Conclude with `hQ PP h' k hk`. Take `⟨⟨q, hq, hcard, -, hne⟩, -⟩` from `hL.Q_pl t PP' h'`. Establish `hq' : (q : 𝓞 D.host.E) ∈ PP'.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hcard, ← nsmul_one]`.

Conclude with `card_nsmul_eq_zero' (G := 𝓞 D.host.E ⧸ PP'.asIdeal)`. Conclude with `not_mem_of_prime PP.isPrime.ne_top (D.host.g_prime k) hq (hne k) (natCast_mem_of_isConjPl hc' hq') hk`. Conclude with `(L.C.isMu0 j).unr PP fun k => hQ PP h k`. Assume the negation of the conclusion as `hc`. Break down `(hL.Q_ram t P).1 hc with h' | ⟨PP', h', hc'⟩` into its components or cases.

Conclude with `hP P (Or.inr h') rfl`. Conclude with `hP PP' (Or.inr h') (under_eq_of_isConjPl hc')`. Use `(L.C.isMu0 j).unr P fun k hk => ?_` and prove the remaining obligations. Break down `div_or_div_conj L.C.P k P hk with h | h` into its components or cases. Conclude with `hP P (Or.inl ((hL.Pg P).2 ⟨k, h⟩)) rfl`.

Conclude with `hP _ (Or.inl ((hL.Pg _).2 ⟨k, h⟩)) (under_eq_of_isConjPl (isConjPl_conjSpec P)).symm`.
-/
theorem levCh_unramified_places : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ t : T0, Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ (∀ PP ∈ L.Q t, ∀ j, (L.C.mu0 j).UnrAt PP) ∧ ∀ P : Pl D.host.E, (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → PP.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F)) → (L.xiH t).UnrAt P ∧ ∀ j, (L.C.mu0 j).UnrAt P := by
  intro D T0 L μ0 hL t
  have hPg : ∀ PP ∈ L.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP h => by
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
    exact ⟨k, mem_of_div _ k PP hk⟩
  have hQ : ∀ PP ∈ L.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP h k =>
    not_mem_of_twist (hL.Q_pl t) h k
  refine ⟨Finset.disjoint_left.2 fun PP h h' => ?_, fun PP h => ?_, fun PP h j => ?_, fun P hP => ⟨?_, fun j => ?_⟩⟩
  · obtain ⟨k, hk⟩ := hPg PP h
    exact hQ PP h' k hk
  · obtain ⟨k, hk⟩ := hPg PP h
    by_contra hc
    rcases (hL.Q_ram t PP).1 hc with h' | ⟨PP', h', hc'⟩
    · exact hQ PP h' k hk
    · obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t PP' h'
      have hq' : (q : 𝓞 D.host.E) ∈ PP'.asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hcard, ← nsmul_one]
        exact card_nsmul_eq_zero' (G := 𝓞 D.host.E ⧸ PP'.asIdeal)
      exact not_mem_of_prime PP.isPrime.ne_top (D.host.g_prime k) hq (hne k) (natCast_mem_of_isConjPl hc' hq') hk
  · exact (L.C.isMu0 j).unr PP fun k => hQ PP h k
  · by_contra hc
    rcases (hL.Q_ram t P).1 hc with h' | ⟨PP', h', hc'⟩
    · exact hP P (Or.inr h') rfl
    · exact hP PP' (Or.inr h') (under_eq_of_isConjPl hc')
  · refine (L.C.isMu0 j).unr P fun k hk => ?_
    rcases div_or_div_conj L.C.P k P hk with h | h
    · exact hP P (Or.inl ((hL.Pg P).2 ⟨k, h⟩)) rfl
    · exact hP _ (Or.inl ((hL.Pg _).2 ⟨k, h⟩)) (under_eq_of_isConjPl (isConjPl_conjSpec P)).symm

end GlobalTheory
