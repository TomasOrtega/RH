import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemLevelOfLocalDepth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastNotMemOfPrimeNe
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.TwistPlaces

/- English proof (translation)
The claim follows from `_root_.GlobalTheory.NatCastNotMemPrime.natCast_notMem_of_prime_ne P hp hl hne hpP`.
-/
theorem natPrime_not_mem {A : Type} [CommRing A] (P : Ideal A) [hP : P.IsPrime] {p l : ℕ} (hp : p.Prime) (hl : l.Prime)
    (hne : l ≠ p) (hpP : (p : A) ∈ P) : (l : A) ∉ P :=
  _root_.GlobalTheory.NatCastNotMemPrime.natCast_notMem_of_prime_ne P hp hl hne hpP

/- English proof (translation)
Introduce `X px I hI a hU`. Establish `htw` using `(GlobalTheory.Mem.ReadTwist.isTwist_of_reads X.B.R X.B.host _ X.B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1`. Establish `key` using `fun PP (hPP : PP ∈ I.Q a) => htw.2.2.2 PP (hU PP hPP)`. Establish `hstar : ∀ x : X.B.host.E, star x = X.B.host.conj x` using `bridge_star_holds X.B.R X.B.host`. Establish `off : ∀ PP ∈ I.Q a, ∀ l : ℕ, l.Prime → l ∈ I.S → ((l : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal`.

Introduce `PP hPP l hl hS`. Take `⟨-, hp, -, hpS⟩` from `key PP hPP`. Conclude with `natPrime_not_mem PP.asIdeal hp hl (fun e => hpS (e ▸ hS)) (Ideal.absNorm_mem PP.asIdeal)`. Use `⟨fun PP hPP => ⟨?_, fun PP' hPP' hc => ?_⟩, fun PP hPP => ⟨?_, fun u => ?_⟩⟩` and prove the remaining obligations. Take `⟨-, hp, hsq, hpS⟩` from `key PP hPP`.

Use `⟨Ideal.absNorm PP.asIdeal, hp, ?_, hsq, fun i e => hpS (e ▸ hI.g_mem i)⟩` and prove the remaining obligations. Use `show Nat.card (𝓞 X.B.host.E ⧸ PP.asIdeal) = Ideal.absNorm PP.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression. Take `⟨v, -, rfl, -⟩` from `I.exists_of_mem_Q hPP`.

Take `⟨v', -, rfl, -⟩` from `I.exists_of_mem_Q hPP'`. Establish `hle : v.asIdeal ≤ v'.asIdeal`. Introduce `c hc'`. Establish `h1 : algebraMap (𝓞 X.B.host.F) (𝓞 X.B.host.E) c ∈ (I.sel v).asIdeal`. Use `hI.sel_ok v` as an intermediate fact.

Rewrite `hc'` using `[← this]`. Conclude with `hc'`. Take `⟨c', h2, h3⟩` from `hc _ h1`. Establish `h4 : c' = algebraMap (𝓞 X.B.host.F) (𝓞 X.B.host.E) c`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Rewrite using `[h3]`. Use `show star (algebraMap X.B.host.F X.B.host.E (c : X.B.host.F)) = algebraMap X.B.host.F X.B.host.E (c : X.B.host.F)`. Rewrite using `[hstar, ← X.B.conjF_eq, AlgHom.commutes]`. Rewrite `h2` using `[h4]`. Rewrite using `[← hI.sel_ok v']`.

Conclude with `h2`. Establish `hv : v = v'` using `HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle)`. Substitute `hv` using the available equality. Take `⟨⟨x, hx, hy⟩, -⟩` from `key _ hPP`. Take `⟨c', h2, h3⟩` from `hc x hx`.

Conclude with `hy c' (h3.trans (hstar _)) h2`. Establish `hp2 : ((X.B.host.QS : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal` using `fun h => by`. Rewrite `h` using `[← Nat.prod_primeFactorsList X.B.host.QS_pos.ne', Nat.cast_list_prod]`. Use `PP.isPrime` as an intermediate fact. Take `⟨a, ha, h'⟩` from `(Ideal.IsPrime.multiset_prod_mem_iff_exists_mem PP.isPrime ((X.B.host.QS.primeFactorsList.map Nat.cast : List (𝓞 X.B.host.E)) : Multiset _)).1 (by simpa using h)`.

Take `⟨l, hl, rfl⟩` from `List.mem_map.1 (Multiset.mem_coe.1 ha)`. Conclude with `off PP hPP l (Nat.prime_of_mem_primeFactorsList hl) (hI.mem_of_dvd_QS (Nat.prime_of_mem_primeFactorsList hl) (Nat.dvd_of_mem_primeFactorsList hl)) h'`. Establish `hq : ((X.B.host.q : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal` using `off PP hPP _ X.B.host.hyp.1 hI.two_q_d_mem.2.1`. Establish `hd : ((X.B.host.d : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal` using `off PP hPP _ X.B.host.hyp.2.1 hI.two_q_d_mem.2.2`. Establish `hT : ((X.B.T X.B.u₀ : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal` using `off PP hPP _ (X.B.T_prime X.B.u₀) (hI.T_mem X.B.u₀)`.

Establish `hsp : X.toD7.sp.T = X.B.T X.B.u₀` using `X.B.sp_T`. Rewrite using `[hsp]`. Use `show ((X.B.host.QS * X.B.host.q * X.B.host.d * X.B.T X.B.u₀ : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal`. Establish `hPr` using `PP.isPrime`. Use `push_cast`.

Introduce `h`. Break down `hPr.mem_or_mem h with h | h` into its components or cases. Break down `hPr.mem_or_mem h with h | h` into its components or cases. Break down `hPr.mem_or_mem h with h | h` into its components or cases. Conclude with `hp2 (by exact_mod_cast h)`.

Conclude with `hq h`. Conclude with `hd h`. Conclude with `hT h`. Establish `hA : (X.toD7.mem u).A.T = X.B.T u` using `X.C.A_T u`. Rewrite using `[hA]`.

Conclude with `off PP hPP _ (X.B.T_prime u) (hI.T_mem u)`.
-/
theorem twistPlaces : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ a : I.ι,
    (∀ PP ∈ I.Q a, ¬ (I.xi a).UnrAt PP) → Formalism.IndefR.Lev.IsTwistPlaces (D := X.toD7) X.toD7.host.g (I.Q a) ∧
    ∀ PP ∈ I.Q a, ((X.toD7.host.QS * X.toD7.host.q * X.toD7.host.d * X.toD7.sp.T : ℕ) : 𝓞 X.toD7.host.E) ∉ PP.asIdeal ∧
      ∀ u : X.toD7.what₂.Word, (((X.toD7.mem u).A.T : ℕ) : 𝓞 X.toD7.host.E) ∉ PP.asIdeal := by
  intro X px I hI a hU
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads X.B.R X.B.host _ X.B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have key := fun PP (hPP : PP ∈ I.Q a) => htw.2.2.2 PP (hU PP hPP)
  have hstar : ∀ x : X.B.host.E, star x = X.B.host.conj x := bridge_star_holds X.B.R X.B.host

  have off : ∀ PP ∈ I.Q a, ∀ l : ℕ, l.Prime → l ∈ I.S → ((l : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := by
    intro PP hPP l hl hS
    obtain ⟨-, hp, -, hpS⟩ := key PP hPP
    exact natPrime_not_mem PP.asIdeal hp hl (fun e => hpS (e ▸ hS)) (Ideal.absNorm_mem PP.asIdeal)
  refine ⟨fun PP hPP => ⟨?_, fun PP' hPP' hc => ?_⟩, fun PP hPP => ⟨?_, fun u => ?_⟩⟩
  · obtain ⟨-, hp, hsq, hpS⟩ := key PP hPP
    refine ⟨Ideal.absNorm PP.asIdeal, hp, ?_, hsq, fun i e => hpS (e ▸ hI.g_mem i)⟩
    show Nat.card (𝓞 X.B.host.E ⧸ PP.asIdeal) = Ideal.absNorm PP.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  · obtain ⟨v, -, rfl, -⟩ := I.exists_of_mem_Q hPP
    obtain ⟨v', -, rfl, -⟩ := I.exists_of_mem_Q hPP'
    have hle : v.asIdeal ≤ v'.asIdeal := by
      intro c hc'
      have h1 : algebraMap (𝓞 X.B.host.F) (𝓞 X.B.host.E) c ∈ (I.sel v).asIdeal := by
        have := hI.sel_ok v
        rw [← this] at hc'
        exact hc'
      obtain ⟨c', h2, h3⟩ := hc _ h1
      have h4 : c' = algebraMap (𝓞 X.B.host.F) (𝓞 X.B.host.E) c := by
        apply RingOfIntegers.ext
        rw [h3]
        show star (algebraMap X.B.host.F X.B.host.E (c : X.B.host.F)) = algebraMap X.B.host.F X.B.host.E (c : X.B.host.F)
        rw [hstar, ← X.B.conjF_eq, AlgHom.commutes]
      rw [h4] at h2
      rw [← hI.sel_ok v']
      exact h2
    have hv : v = v' := HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle)
    subst hv
    obtain ⟨⟨x, hx, hy⟩, -⟩ := key _ hPP
    obtain ⟨c', h2, h3⟩ := hc x hx
    exact hy c' (h3.trans (hstar _)) h2
  · have hp2 : ((X.B.host.QS : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := fun h => by
      rw [← Nat.prod_primeFactorsList X.B.host.QS_pos.ne', Nat.cast_list_prod] at h
      have := PP.isPrime
      obtain ⟨a, ha, h'⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem PP.isPrime
        ((X.B.host.QS.primeFactorsList.map Nat.cast : List (𝓞 X.B.host.E)) : Multiset _)).1 (by simpa using h)
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 ha)
      exact off PP hPP l (Nat.prime_of_mem_primeFactorsList hl)
        (hI.mem_of_dvd_QS (Nat.prime_of_mem_primeFactorsList hl) (Nat.dvd_of_mem_primeFactorsList hl)) h'
    have hq : ((X.B.host.q : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := off PP hPP _ X.B.host.hyp.1 hI.two_q_d_mem.2.1
    have hd : ((X.B.host.d : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := off PP hPP _ X.B.host.hyp.2.1 hI.two_q_d_mem.2.2
    have hT : ((X.B.T X.B.u₀ : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal :=
      off PP hPP _ (X.B.T_prime X.B.u₀) (hI.T_mem X.B.u₀)
    have hsp : X.toD7.sp.T = X.B.T X.B.u₀ := X.B.sp_T
    rw [hsp]
    show ((X.B.host.QS * X.B.host.q * X.B.host.d * X.B.T X.B.u₀ : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal
    have hPr := PP.isPrime
    push_cast
    intro h
    rcases hPr.mem_or_mem h with h | h
    · rcases hPr.mem_or_mem h with h | h
      · rcases hPr.mem_or_mem h with h | h
        · exact hp2 (by exact_mod_cast h)
        · exact hq h
      · exact hd h
    · exact hT h
  · have hA : (X.toD7.mem u).A.T = X.B.T u := X.C.A_T u
    rw [hA]
    exact off PP hPP _ (X.B.T_prime u) (hI.T_mem u)

end GlobalTheory.Mem.TwistPlaces
