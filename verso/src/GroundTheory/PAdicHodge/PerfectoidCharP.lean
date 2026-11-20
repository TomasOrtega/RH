import Mathlib
import GroundTheory.PAdicHodge.PerfectoidField
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/- English proof (translation)
Break down `CharP.char_is_prime_or_zero K (ringChar K) with hq | hq` into its components or cases. Use `right`. Establish `hq' : Fact (ringChar K).Prime` using `⟨hq⟩`. Assume the negation of the conclusion as `hne`. Establish `hpq : p ≠ ringChar K` using `fun h => hne (h ▸ ringChar.charP K)`.

Establish `hpz : ((p : ZMod (ringChar K))) ≠ 0`. Rewrite using `[Ne, ZMod.natCast_eq_zero_iff]`. Introduce `hdvd`. Conclude with `hpq ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).1 hdvd).symm`. Establish `hferm` using `ZMod.pow_card_sub_one_eq_one hpz`.

Establish `hK : (p : K) ^ (ringChar K - 1) = 1`. Use `congrArg (ZMod.castHom (dvd_refl (ringChar K)) K) hferm` as an intermediate fact. Simplify using `using this`. Establish `hn` using `congrArg norm hK`. Rewrite `hn` using `[norm_pow, norm_one]`.

Establish `hlt` using `IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)`. Establish `hpos : ringChar K - 1 ≠ 0` using `by have := hq.two_le; omega`. Establish `: ‖(p : K)‖ = 1` using `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos).1 hn`. Combine the linear equalities and inequalities to obtain the conclusion. Use `left`.

Establish `: CharP K 0` using `by rw [← hq]; exact ringChar.charP K`. Conclude with `CharP.charP_to_charZero K`.
-/
theorem charZero_or_charP (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] :
    CharZero K ∨ CharP K p := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | hq
  · right
    have hq' : Fact (ringChar K).Prime := ⟨hq⟩
    by_contra hne
    have hpq : p ≠ ringChar K := fun h => hne (h ▸ ringChar.charP K)

    have hpz : ((p : ZMod (ringChar K))) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact hpq ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).1 hdvd).symm
    have hferm := ZMod.pow_card_sub_one_eq_one hpz
    have hK : (p : K) ^ (ringChar K - 1) = 1 := by
      have := congrArg (ZMod.castHom (dvd_refl (ringChar K)) K) hferm
      simpa using this
    have hn := congrArg norm hK
    rw [norm_pow, norm_one] at hn
    have hlt := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
    have hpos : ringChar K - 1 ≠ 0 := by have := hq.two_le; omega
    have : ‖(p : K)‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos).1 hn
    linarith
  · left
    have : CharP K 0 := by rw [← hq]; exact ringChar.charP K
    exact CharP.charP_to_charZero K

/- English proof (translation)
Use `IsPerfectoidField.completeSpace (K := K) p` as an intermediate fact. Establish `: CompleteSpace L` using `FiniteDimensional.complete K L`. Establish `: PerfectRing K p` using `IsPerfectoidField.perfectRing p`. Establish `: PerfectField K` using `PerfectRing.toPerfectField K p`. Establish `: PerfectField L` using `Algebra.IsAlgebraic.perfectField (K := K)`.

Establish `: CharP L p` using `charP_of_injective_algebraMap (algebraMap K L).injective p`. Establish `: PerfectRing L p` using `PerfectField.toPerfectRing p`. Use `IsPerfectoidField.of_perfectRing p fun r hr => ?_` and prove the remaining obligations. Take `⟨x, hx1, hx2⟩` from `IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) r hr`. Conclude with `⟨algebraMap K L x, by rwa [norm_algebraMap'], by rwa [norm_algebraMap']⟩`.
-/
theorem of_finiteDimensional_of_charP (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] [CharP K p]
    (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
    [FiniteDimensional K L] : IsPerfectoidField L p := by
  have := IsPerfectoidField.completeSpace (K := K) p
  have : CompleteSpace L := FiniteDimensional.complete K L
  have : PerfectRing K p := IsPerfectoidField.perfectRing p
  have : PerfectField K := PerfectRing.toPerfectField K p
  have : PerfectField L := Algebra.IsAlgebraic.perfectField (K := K)
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have : PerfectRing L p := PerfectField.toPerfectRing p
  refine IsPerfectoidField.of_perfectRing p fun r hr => ?_
  obtain ⟨x, hx1, hx2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) r hr
  exact ⟨algebraMap K L x, by rwa [norm_algebraMap'], by rwa [norm_algebraMap']⟩

end IsPerfectoidField

end GroundTheory.PAdicHodge
