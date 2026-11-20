import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRamif

variable {D : D7}

/- English proof (translation)
Establish `hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E)` using `Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)`. Take `⟨a, b, hab⟩` from `hc`. Apply `PP.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)`.
-/
theorem not_two_primes (PP : Pl D.host.E) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h1 : (p : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : (q : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

/- English proof (translation)
Take `⟨c', hc', e⟩` from `h _ hn`. Establish `e2 : c' = (n : 𝓞 D.host.E)`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `e3 : (((n : 𝓞 D.host.E)) : D.host.E) = (n : D.host.E)` using `map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n`. Rewrite using `[e, e3, star_natCast]`.

Rewrite `hc'` using `[e2]`. Then use the resulting hypothesis.
-/
theorem natCast_mem_conj {PP PP' : Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl PP PP') {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ PP.asIdeal) : (n : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  obtain ⟨c', hc', e⟩ := h _ hn
  have e2 : c' = (n : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    have e3 : (((n : 𝓞 D.host.E)) : D.host.E) = (n : D.host.E) := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n
    rw [e, e3, star_natCast]
  rwa [e2] at hc'

/- English proof (translation)
Take `⟨⟨q, hq, hc, -, hne⟩, -⟩` from `hQ PP h`. Use `⟨q, hq, ?_, hne⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]`. Conclude with `card_nsmul_eq_zero'`.
-/
theorem exists_prime_mem {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) {PP : Pl D.host.E}
    (h : PP ∈ Q) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ∀ i, q ≠ D.host.g i := by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := hQ PP h
  refine ⟨q, hq, ?_, hne⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
  exact card_nsmul_eq_zero'

/- English proof (translation)
Establish `h1` using `P.pb_over k`. Establish `h2 : PP.under (𝓞 D.host.K) = P.pb k` using `h`. Rewrite `h1` using `[← h2]`. Establish `h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal` using `h1`. Rewrite `h3` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem typePrime_mem {P : Formalism.L2.Host.PiBar D.host} {k : Fin 2} {PP : Pl D.host.E} (h : P.Div k PP) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  have h1 := P.pb_over k
  have h2 : PP.under (𝓞 D.host.K) = P.pb k := h
  rw [← h2] at h1
  have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
  rwa [map_natCast] at h3

/- English proof (translation)
Introduce `c hc`. Rewrite `hc` using `[h, Formalism.L2.Col.mem_conjIdeal]`. Conclude with `⟨_, hc, rfl⟩`.
-/
theorem isConjPl_of_eq {w w' : Pl D.host.E}
    (h : w'.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) w.asIdeal) : Formalism.IndefR.Lev.IsConjPl w' w := by
  intro c hc
  rw [h, Formalism.L2.Col.mem_conjIdeal] at hc
  exact ⟨_, hc, rfl⟩

/- English proof (translation)
Introduce `D T0 L μ0 hL t j`. Establish `hoff : ∀ (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, Formalism.IndefR.Lev.IsConjPl PP' PP`. Introduce `k PP hk`. Use `⟨fun hQ => ?_, fun ⟨PP', hQ, hc⟩ => ?_⟩` and prove the remaining obligations. Take `⟨q, hq, hm, hne⟩` from `exists_prime_mem (hL.Q_pl t) hQ`.

Conclude with `not_two_primes PP hq (D.host.g_prime k) (hne k) hm hk`. Take `⟨q, hq, hm, hne⟩` from `exists_prime_mem (hL.Q_pl t) hQ`. Conclude with `not_two_primes PP hq (D.host.g_prime k) (hne k) (natCast_mem_conj hc hm) hk`. Establish `hPg : ∀ PP ∈ L.Pg, PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, Formalism.IndefR.Lev.IsConjPl PP' PP`. Introduce `PP h`.

Take `⟨k, hk⟩` from `(hL.Pg PP).1 h`. Conclude with `hoff k PP (typePrime_mem hk)`. Establish `hM` using `L.C.isMu0 j`. Use `⟨Finset.disjoint_left.2 fun PP h => (hPg PP h).1, fun PP hQ => ?_, fun PP h => ?_, fun PP h1 h2 => ?_⟩` and prove the remaining obligations. Conclude with `hM.unr PP fun k hk => (hoff k PP hk).1 hQ`.

Assume the negation of the conclusion as `hn`. Break down `(hL.Q_ram t PP).1 hn with h' | h'` into its components or cases. Conclude with `(hPg PP h).1 h'`. Conclude with `(hPg PP h).2 h'`. Use `hM.unr PP fun k hk => ?_` and prove the remaining obligations.

Break down `GlobalTheory.ConjOverQuad.div_or_conj_div D L.C.P k PP hk with h | ⟨PP', h, hc⟩` into its components or cases. Conclude with `h1 ((hL.Pg PP).2 ⟨k, h⟩)`. Conclude with `h2 PP' ((hL.Pg PP').2 ⟨k, h⟩) (isConjPl_of_eq hc)`.
-/
theorem ramif_at_levels : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (t : T0) (j : Fin D.R.m), Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Q t, (L.C.mu0 j).UnrAt PP) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ ∀ PP', PP' ∉ L.Pg → (∀ PP ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → (L.C.mu0 j).UnrAt PP' := by
  classical
  intro D T0 L μ0 hL t j
  have hoff : ∀ (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal →
      PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, Formalism.IndefR.Lev.IsConjPl PP' PP := by
    intro k PP hk
    refine ⟨fun hQ => ?_, fun ⟨PP', hQ, hc⟩ => ?_⟩
    · obtain ⟨q, hq, hm, hne⟩ := exists_prime_mem (hL.Q_pl t) hQ
      exact not_two_primes PP hq (D.host.g_prime k) (hne k) hm hk
    · obtain ⟨q, hq, hm, hne⟩ := exists_prime_mem (hL.Q_pl t) hQ
      exact not_two_primes PP hq (D.host.g_prime k) (hne k) (natCast_mem_conj hc hm) hk
  have hPg : ∀ PP ∈ L.Pg, PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, Formalism.IndefR.Lev.IsConjPl PP' PP := by
    intro PP h
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
    exact hoff k PP (typePrime_mem hk)
  have hM := L.C.isMu0 j
  refine ⟨Finset.disjoint_left.2 fun PP h => (hPg PP h).1, fun PP hQ => ?_, fun PP h => ?_, fun PP h1 h2 => ?_⟩
  · exact hM.unr PP fun k hk => (hoff k PP hk).1 hQ
  · by_contra hn
    rcases (hL.Q_ram t PP).1 hn with h' | h'
    · exact (hPg PP h).1 h'
    · exact (hPg PP h).2 h'
  · refine hM.unr PP fun k hk => ?_
    rcases GlobalTheory.ConjOverQuad.div_or_conj_div D L.C.P k PP hk with h | ⟨PP', h, hc⟩
    · exact h1 ((hL.Pg PP).2 ⟨k, h⟩)
    · exact h2 PP' ((hL.Pg PP').2 ⟨k, h⟩) (isConjPl_of_eq hc)

end GlobalTheory.LevelRamif
