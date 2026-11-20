import Mathlib

namespace GlobalTheory

/- English proof (translation)
Use `set I := P.map (algebraMap B A) with hI`. Distinguish the cases in `htop : I = ⊤`. Rewrite using `[htop]`. Conclude with `le_top`. Establish `hrad : I.radical = Q`.

Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal I htop`. Establish `hMQ : M = Q` using `hQ M hM.isPrime hIM`. Rewrite using `[Ideal.radical_eq_sInf]`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `sInf_le ⟨hMQ ▸ hIM, hMQ ▸ hM.isPrime⟩`.

Use `le_sInf ?_` and prove the remaining obligations. Introduce and unpack `J ⟨hJ1, hJ2⟩`. Conclude with `(hQ J hJ2 hJ1).ge`. Use `haveI := hP`. Use `letI : Field (B ⧸ P) := Ideal.Quotient.field P`.

Use `haveI : Algebra.FormallyUnramified B (A ⧸ I) := Algebra.FormallyUnramified.comp B A (A ⧸ I)`. Use `haveI : Algebra.FormallyUnramified (B ⧸ P) (A ⧸ I) := Algebra.FormallyUnramified.of_restrictScalars B (B ⧸ P) (A ⧸ I)`. Use `haveI : Algebra.EssFiniteType B (A ⧸ I) := Algebra.EssFiniteType.comp B A (A ⧸ I)`. Use `haveI : Algebra.EssFiniteType (B ⧸ P) (A ⧸ I) := Algebra.EssFiniteType.of_comp B (B ⧸ P) (A ⧸ I)`. Use `haveI : IsReduced (A ⧸ I) := Algebra.FormallyUnramified.isReduced_of_field (B ⧸ P) (A ⧸ I)`.

Introduce `x hx`. Rewrite `hx` using `[← hrad]`. Take `⟨n, hn⟩` from `hx`. Establish `h0 : (Ideal.Quotient.mk I x) ^ n = 0`. Rewrite using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hn`. Establish `: Ideal.Quotient.mk I x = 0` using `IsReduced.eq_zero _ ⟨n, h0⟩`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp this`.
-/
theorem etale_prime_le_map_of_unique (B A : Type) [CommRing B] [CommRing A] [Algebra B A]
    [Algebra.Etale B A] (P : Ideal B) (hP : P.IsMaximal) (Q : Ideal A)
    (hQ : ∀ Q' : Ideal A, Q'.IsPrime → P.map (algebraMap B A) ≤ Q' → Q' = Q) :
    Q ≤ P.map (algebraMap B A) := by
  set I := P.map (algebraMap B A) with hI
  by_cases htop : I = ⊤
  · rw [htop]; exact le_top

  have hrad : I.radical = Q := by
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop
    have hMQ : M = Q := hQ M hM.isPrime hIM
    rw [Ideal.radical_eq_sInf]
    apply le_antisymm
    · exact sInf_le ⟨hMQ ▸ hIM, hMQ ▸ hM.isPrime⟩
    · refine le_sInf ?_
      rintro J ⟨hJ1, hJ2⟩
      exact (hQ J hJ2 hJ1).ge

  haveI := hP
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Algebra.FormallyUnramified B (A ⧸ I) :=
    Algebra.FormallyUnramified.comp B A (A ⧸ I)
  haveI : Algebra.FormallyUnramified (B ⧸ P) (A ⧸ I) :=
    Algebra.FormallyUnramified.of_restrictScalars B (B ⧸ P) (A ⧸ I)
  haveI : Algebra.EssFiniteType B (A ⧸ I) := Algebra.EssFiniteType.comp B A (A ⧸ I)
  haveI : Algebra.EssFiniteType (B ⧸ P) (A ⧸ I) := Algebra.EssFiniteType.of_comp B (B ⧸ P) (A ⧸ I)
  haveI : IsReduced (A ⧸ I) := Algebra.FormallyUnramified.isReduced_of_field (B ⧸ P) (A ⧸ I)
  intro x hx
  rw [← hrad] at hx
  obtain ⟨n, hn⟩ := hx
  have h0 : (Ideal.Quotient.mk I x) ^ n = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn
  have : Ideal.Quotient.mk I x = 0 := IsReduced.eq_zero _ ⟨n, h0⟩
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

end GlobalTheory
