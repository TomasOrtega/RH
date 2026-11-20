import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.AdeleSquarefree

/- English proof (translation)
Establish `h0 : (Ideal.span {x} : Ideal A) ≠ ⊥`. Simplify `hx` using `[Ideal.span_singleton_eq_bot]`. Establish `hsf : Squarefree (Ideal.span {x} : Ideal A)`. Use `(squarefree_iff_irreducible_sq_not_dvd_of_ne_zero h0).2 fun P hP hd => ?_` and prove the remaining obligations. Establish `hPp : Prime P` using `hP.prime`.

Establish `hPb : P ≠ ⊥` using `hPp.ne_zero`. Establish `hle : Ideal.span {x} ≤ P ^ 2`. Rewrite using `[pow_two]`. Conclude with `Ideal.dvd_iff_le.1 hd`. Establish `hx2 : x ∈ P ^ 2` using `hle (Ideal.mem_span_singleton_self x)`.

Conclude with `hsq ⟨P, (Ideal.prime_iff_isPrime hPb).1 hPp, hPb⟩ (Ideal.pow_le_self two_ne_zero hx2) hx2`. Establish `hrad : a ∈ (Ideal.span {x} : Ideal A).radical`. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`. Introduce and unpack `J ⟨hJ, hJp⟩`. Establish `hJb : J ≠ ⊥` using `fun h => h0 (le_bot_iff.1 (h ▸ hJ))`.

Conclude with `ha ⟨J, hJp, hJb⟩ (hJ (Ideal.mem_span_singleton_self x))`. Take `⟨n, hn⟩` from `hrad`. Establish `hd : (Ideal.span {x} : Ideal A) ∣ (Ideal.span {a}) ^ n`. Rewrite using `[Ideal.span_singleton_pow, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hn`.

Establish `h2` using `hsf.isRadical n _ hd`. Rewrite `h2` using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `h2`.
-/
theorem mem_span_of_forall_prime {A : Type} [CommRing A] [IsDedekindDomain A] (x : A) (hx : x ≠ 0)
    (hsq : ∀ Q : HeightOneSpectrum A, x ∈ Q.asIdeal → x ∉ Q.asIdeal ^ 2) (a : A)
    (ha : ∀ Q : HeightOneSpectrum A, x ∈ Q.asIdeal → a ∈ Q.asIdeal) : a ∈ Ideal.span {x} := by
  have h0 : (Ideal.span {x} : Ideal A) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hx
  have hsf : Squarefree (Ideal.span {x} : Ideal A) := by
    refine (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero h0).2 fun P hP hd => ?_
    have hPp : Prime P := hP.prime
    have hPb : P ≠ ⊥ := hPp.ne_zero
    have hle : Ideal.span {x} ≤ P ^ 2 := by
      rw [pow_two]; exact Ideal.dvd_iff_le.1 hd
    have hx2 : x ∈ P ^ 2 := hle (Ideal.mem_span_singleton_self x)
    exact hsq ⟨P, (Ideal.prime_iff_isPrime hPb).1 hPp, hPb⟩ (Ideal.pow_le_self two_ne_zero hx2) hx2
  have hrad : a ∈ (Ideal.span {x} : Ideal A).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    have hJb : J ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hJ))
    exact ha ⟨J, hJp, hJb⟩ (hJ (Ideal.mem_span_singleton_self x))
  obtain ⟨n, hn⟩ := hrad
  have hd : (Ideal.span {x} : Ideal A) ∣ (Ideal.span {a}) ^ n := by
    rw [Ideal.span_singleton_pow, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hn
  have h2 := hsf.isRadical n _ hd
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h2
  exact h2

/- English proof (translation)
Introduce `I g hg hsq s hs`. Establish `hg' : (g : 𝓞 I.E) ≠ 0` using `by exact_mod_cast hg`. Establish `h0 : (Ideal.span {(g : 𝓞 I.E)} : Ideal (𝓞 I.E)) ≠ ⊥`. Simplify `hg` using `[Ideal.span_singleton_eq_bot]`. Establish `hid : idS I.F (Ideal.span {(g : 𝓞 I.E)}) = Ideal.span {oToS I.F I.E (g : 𝓞 I.E)}`.

Rewrite using `[idS, Ideal.map_span, Set.image_singleton]`. Take `⟨q, hq⟩` from `(cmpS_bij (F := I.F) _ h0).2 (Ideal.Quotient.mk _ s)`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Establish `hq' : Ideal.Quotient.mk (idS I.F (Ideal.span {(g : 𝓞 I.E)})) (oToS I.F I.E a) = Ideal.Quotient.mk (idS I.F (Ideal.span {(g : 𝓞 I.E)})) s` using `hq`. Establish `hm` using `Ideal.Quotient.eq.1 hq'.symm`.

Rewrite `hm` using `[hid, Ideal.mem_span_singleton]`. Take `⟨u, hu⟩` from `hm`. Establish `hsu : s = oToS I.F I.E a + oToS I.F I.E (g : 𝓞 I.E) * u` using `by rw [← hu]; ring`. Establish `ha : a ∈ Ideal.span {(g : 𝓞 I.E)}`. Use `mem_span_of_forall_prime _ hg' hsq a fun Q hQ => ?_` and prove the remaining obligations.

Establish `h1` using `hs Q hQ`. Rewrite `h1` using `[hsu, map_add, map_mul, resS_oToS, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hQ, zero_mul, add_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h1`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton.1 ha`. Establish `hfin : s = (g : Formalism.L2.Herm.intAf I.F I.E) * (oToS I.F I.E b + u)`.

Rewrite using `[hsu, hb, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨((oToS I.F I.E b + u : Formalism.L2.Herm.intAf I.F I.E) : I.E ⊗[I.F] Af I.F), (oToS I.F I.E b + u).2, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [hfin]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem zmod_of_forall_resS_eq_zero : ∀ (I : AutInst) (g : ℕ), g ≠ 0 →
    (∀ Q : Pl I.E, (g : 𝓞 I.E) ∈ Q.asIdeal → (g : 𝓞 I.E) ∉ Q.asIdeal ^ 2) →
    ∀ s : Formalism.L2.Herm.intAf I.F I.E, (∀ Q : Pl I.E, (g : 𝓞 I.E) ∈ Q.asIdeal → resS I.F Q s = 0) → ZMod' I g s := by
  intro I g hg hsq s hs
  have hg' : (g : 𝓞 I.E) ≠ 0 := by exact_mod_cast hg
  have h0 : (Ideal.span {(g : 𝓞 I.E)} : Ideal (𝓞 I.E)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hg
  have hid : idS I.F (Ideal.span {(g : 𝓞 I.E)}) = Ideal.span {oToS I.F I.E (g : 𝓞 I.E)} := by
    rw [idS, Ideal.map_span, Set.image_singleton]
  obtain ⟨q, hq⟩ := (cmpS_bij (F := I.F) _ h0).2 (Ideal.Quotient.mk _ s)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hq' : Ideal.Quotient.mk (idS I.F (Ideal.span {(g : 𝓞 I.E)})) (oToS I.F I.E a) =
      Ideal.Quotient.mk (idS I.F (Ideal.span {(g : 𝓞 I.E)})) s := hq
  have hm := Ideal.Quotient.eq.1 hq'.symm
  rw [hid, Ideal.mem_span_singleton] at hm
  obtain ⟨u, hu⟩ := hm
  have hsu : s = oToS I.F I.E a + oToS I.F I.E (g : 𝓞 I.E) * u := by rw [← hu]; ring
  have ha : a ∈ Ideal.span {(g : 𝓞 I.E)} := by
    refine mem_span_of_forall_prime _ hg' hsq a fun Q hQ => ?_
    have h1 := hs Q hQ
    rw [hsu, map_add, map_mul, resS_oToS, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hQ, zero_mul, add_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 ha
  have hfin : s = (g : Formalism.L2.Herm.intAf I.F I.E) * (oToS I.F I.E b + u) := by
    rw [hsu, hb, map_mul, map_natCast]; ring
  refine ⟨((oToS I.F I.E b + u : Formalism.L2.Herm.intAf I.F I.E) : I.E ⊗[I.F] Af I.F), (oToS I.F I.E b + u).2, ?_⟩
  conv_lhs => rw [hfin]
  push_cast
  rfl

end GlobalTheory.AdeleSquarefree
