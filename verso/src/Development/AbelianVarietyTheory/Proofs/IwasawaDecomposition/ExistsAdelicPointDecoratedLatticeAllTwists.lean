import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.PtTwist

open GlobalTheory.Mem.Col2.PtExist

/- English proof (translation)
Introduce `B X I hI u n p`. Establish `hPr` using `(GlobalTheory.BasePrimes.primes_ok B X).1`. Take `⟨hlev, hGQ, -⟩` from `GlobalTheory.Mem.LevTwist.levOk_twists B X I hI`. Establish `hT0 : (B.primes X).piT u ≠ 0` using `fun h => by`. Use `hPr.piT_norm u` as an intermediate fact.

Rewrite `this` using `[h, zero_mul]`. Conclude with `(hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)`. Establish `hTin : ∀ P ∈ (B.primes X).vT u, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal` using `fun P hP => by`. Establish `h1 : (B.primes X).piT u ∈ P.asIdeal` using `(mem_divs hT0 P).1 hP`. Rewrite using `[← hPr.piT_norm u]`.

Conclude with `Ideal.mul_mem_right _ _ h1`. Establish `hcj : ∀ (P : HeightOneSpectrum (𝓞 B.fields.E)) (m : ℕ), ((m : ℕ) : 𝓞 B.fields.E) ∈ (conjPrime₂ P).asIdeal ↔ ((m : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal` using `fun P m => by`. Rewrite using `[mem_conjP, map_natCast]`. Establish `hG : ∀ P ∈ (B.primes X).vGs, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal` using `fun P hP => T_notMem_vGs hPr u ⟨P, hP⟩`. Establish `hQ : ∀ P ∈ I.SQ, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal` using `fun P hP h => by`.

Establish `hg` using `(GlobalTheory.Mem.LevTwist.good_of_mem hI hP).2`. Establish `e` using `(ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.T_prime u)).2 h`. Use `hg.2.2 ?_` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `hI.T_mem u`.

Establish `hTG : Disjoint ((B.primes X).vT u) (B.primes X).vGs` using `Finset.disjoint_left.2 fun P h1 h2 => hG P h2 (hTin P h1)`. Establish `hTQ : Disjoint ((B.primes X).vT u) I.SQ` using `Finset.disjoint_left.2 fun P h1 h2 => hQ P h2 (hTin P h1)`. Establish `hout : ∀ P ∈ uSG (B.primes X).vGs I.SQ, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal` using `fun P hP => by`. Break down `Finset.mem_union.1 hP with h | h` into its components or cases. Use `exacts [hG P h, hQ P h]`.

Use `PtExist.exists_isPtOf_cm _ n _ _ _ p hTG hTQ hGQ fun P hP hP' => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases Finset.mem_union.1 hP with h1 | h1 <;> rcases Finset.mem_union.1 hP' with h2 | h2`. Establish `a1 : (B.primes X).piT u ∈ P.asIdeal` using `(mem_divs hT0 P).1 h1`. Establish `a2 : (B.primes X).piT u ∈ (conjPrime₂ P).asIdeal` using `(mem_divs hT0 _).1 h2`. Rewrite `a2` using `[mem_conjP]`.

Take `⟨a, b, hab⟩` from `hPr.piT_cop u`. Establish `: (1 : 𝓞 B.fields.E) ∈ P.asIdeal`. Rewrite using `[← hab]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ a1) (Ideal.mul_mem_left _ _ a2)`. Conclude with `P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)`.

Conclude with `hout _ h2 ((hcj P _).2 (hTin P h1))`. Conclude with `hout P h1 ((hcj P _).1 (hTin _ h2))`. Conclude with `hlev.split P h1 h2`.
-/
theorem exists_ptOf_twists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (n : ℕ)
    (p : DecoF B.fields.E n ((B.primes X).vT u) (B.primes X).vGs I.SQ), ∃ g : GA B n, PtOf g p := by
  classical
  intro B X I hI u n p
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  obtain ⟨hlev, hGQ, -⟩ := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hT0 : (B.primes X).piT u ≠ 0 := fun h => by
    have := hPr.piT_norm u
    rw [h, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)

  have hTin : ∀ P ∈ (B.primes X).vT u, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := fun P hP => by
    have h1 : (B.primes X).piT u ∈ P.asIdeal := (mem_divs hT0 P).1 hP
    rw [← hPr.piT_norm u]
    exact Ideal.mul_mem_right _ _ h1

  have hcj : ∀ (P : HeightOneSpectrum (𝓞 B.fields.E)) (m : ℕ),
      ((m : ℕ) : 𝓞 B.fields.E) ∈ (conjPrime₂ P).asIdeal ↔ ((m : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := fun P m => by
    rw [mem_conjP, map_natCast]

  have hG : ∀ P ∈ (B.primes X).vGs, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP =>
    T_notMem_vGs hPr u ⟨P, hP⟩

  have hQ : ∀ P ∈ I.SQ, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP h => by
    have hg := (GlobalTheory.Mem.LevTwist.good_of_mem hI hP).2
    have e := (ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.T_prime u)).2 h
    refine hg.2.2 ?_
    rw [e]
    exact hI.T_mem u
  have hTG : Disjoint ((B.primes X).vT u) (B.primes X).vGs :=
    Finset.disjoint_left.2 fun P h1 h2 => hG P h2 (hTin P h1)
  have hTQ : Disjoint ((B.primes X).vT u) I.SQ :=
    Finset.disjoint_left.2 fun P h1 h2 => hQ P h2 (hTin P h1)
  have hout : ∀ P ∈ uSG (B.primes X).vGs I.SQ, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP => by
    rcases Finset.mem_union.1 hP with h | h
    exacts [hG P h, hQ P h]
  refine PtExist.exists_isPtOf_cm _ n _ _ _ p hTG hTQ hGQ fun P hP hP' => ?_
  rcases Finset.mem_union.1 hP with h1 | h1 <;> rcases Finset.mem_union.1 hP' with h2 | h2
  ·
    have a1 : (B.primes X).piT u ∈ P.asIdeal := (mem_divs hT0 P).1 h1
    have a2 : (B.primes X).piT u ∈ (conjPrime₂ P).asIdeal := (mem_divs hT0 _).1 h2
    rw [mem_conjP] at a2
    obtain ⟨a, b, hab⟩ := hPr.piT_cop u
    have : (1 : 𝓞 B.fields.E) ∈ P.asIdeal := by
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ a1) (Ideal.mul_mem_left _ _ a2)
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  · exact hout _ h2 ((hcj P _).2 (hTin P h1))
  · exact hout P h1 ((hcj P _).1 (hTin _ h2))
  · exact hlev.split P h1 h2

end GlobalTheory.Mem.Col2.PtTwist
